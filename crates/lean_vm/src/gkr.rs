//! The grand product via GKR (§4.3): given leaves `v_0…v_{2^μ-1}`, prove the
//! root `P = ∏ v_k` of the binary product tree, reducing one claim per layer down
//! to a single leaf evaluation `Ṽ_0(ζ)`. Layer relation (low-bit split): `V_i(x)
//! = V_{i-1}(0,x)·V_{i-1}(1,x)`; each layer's sumcheck uses the eq-trick, so its
//! round univariate is degree 2 (3 evaluations) plus a degree-1 fold-back line.
//! Leaves and every layer are `E`-valued (the bus fingerprints mix `K`-columns
//! into `E` upstream, [`crate::leaf`]).

use crate::PAR_THRESHOLD;
use crate::transcript::{ProverState, VerifierState};
use primitives::field::{F192, F192Unreduced, mul_by_g_e};
use primitives::multilinear::lagrange_eval;
use primitives::multilinear::{eq_table, interp, tri_nodes, xor3};
use rayon::prelude::*;

/// Bind the lowest variable of `src` into `dst` (in parallel for large tables):
/// `dst[i] = interp(src[2i], src[2i+1], rho)`. Writing into a caller-owned
/// scratch buffer instead of a fresh Vec lets each layer's rounds ping-pong two
/// allocations instead of allocating (and page-faulting) per round.
/// Deliberately scalar: pairing adjacent outputs through [`F192::mul2`]
/// measures slower (2.14 vs 1.75 ns/output). The mul has the loop-invariant
/// `rho` on one side, the OoO core already overlaps the independent
/// iterations, and the pair kernel's third NEON fold outweighs its 2-PMULL
/// saving once nothing is latency-bound.
fn par_fold_into(src: &[F192], rho: F192, dst: &mut Vec<F192>) {
    let half = src.len() / 2;
    if half >= PAR_THRESHOLD {
        (0..half)
            .into_par_iter()
            .map(|i| interp(src[2 * i], src[2 * i + 1], rho))
            .collect_into_vec(dst);
    } else {
        dst.clear();
        dst.extend((0..half).map(|i| interp(src[2 * i], src[2 * i + 1], rho)));
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GkrError {
    Truncated,
    SumcheckInconsistent { layer: usize, round: usize },
    LayerMismatch { layer: usize },
}

/// Build every product-tree layer: `layers[0]` = leaves, `layers[μ]` = `[root]`.
/// Deliberately scalar: routing adjacent output pairs through [`F192::mul2`]
/// wins ~4% single-threaded but loses ~2% end to end (interleaved A/B: 1339 vs
/// 1370 ms bus-GKR at `LEANVM_XMSS_N=1024`, 10 threads); at full parallelism
/// this loop is memory-bandwidth-bound and the paired form only adds overhead.
fn build_layers(leaves: Vec<F192>) -> Vec<Vec<F192>> {
    let mut layers = vec![leaves];
    while layers.last().unwrap().len() > 1 {
        let cur = layers.last().unwrap();
        let half = cur.len() / 2;
        let next: Vec<F192> = if half >= PAR_THRESHOLD {
            (0..half).into_par_iter().map(|j| cur[2 * j] * cur[2 * j + 1]).collect()
        } else {
            (0..half).map(|j| cur[2 * j] * cur[2 * j + 1]).collect()
        };
        layers.push(next);
    }
    layers
}

/// One tree's per-layer sumcheck state: the strided even/odd tables plus the
/// ping-pong fold scratch (allocated once per layer, reused every round).
struct LayerState {
    even: Vec<F192>,
    odd: Vec<F192>,
    even_next: Vec<F192>,
    odd_next: Vec<F192>,
}

impl LayerState {
    fn new(below: &[F192], width: usize) -> Self {
        let strided_copy = |off: usize| -> Vec<F192> {
            if width >= PAR_THRESHOLD {
                (0..width).into_par_iter().map(|j| below[2 * j + off]).collect()
            } else {
                (0..width).map(|j| below[2 * j + off]).collect()
            }
        };
        Self {
            even: strided_copy(0),
            odd: strided_copy(1),
            even_next: Vec::new(),
            odd_next: Vec::new(),
        }
    }

    /// The layer sumcheck's degree-2 round univariate at nodes `{0, 1, g}`.
    fn round_message(&self, eqr: &[F192]) -> [F192; 3] {
        let half = self.even.len() / 2;
        let (even, odd) = (&self.even, &self.odd);
        let summand = |idx: usize| -> [F192Unreduced; 3] {
            let (lo, hi) = (2 * idx, 2 * idx + 1);
            let eq = eqr[idx];
            let t0 = even[lo] * odd[lo];
            let t1 = even[hi] * odd[hi];
            // Node 2 is the generator `g = x`, so `g·diff = mul_by_g_e(diff)` — two
            // shift-folds, not a carry-less mul (bit-identical to `nodes[2] * diff`).
            let (even_diff, odd_diff) = (even[lo] + even[hi], odd[lo] + odd[hi]);
            let (even_at2, odd_at2) = (even[lo] + mul_by_g_e(even_diff), odd[lo] + mul_by_g_e(odd_diff));
            let t2 = even_at2 * odd_at2;
            // Defer the mod-P reduction of the outer eq·(…) products:
            // XOR-accumulate the unreduced Karatsuba parts (3 PMULL per
            // term, no reduction tail) and reduce once per accumulator
            // after the sum — reduction commutes with XOR, so the round
            // message is bit-identical.
            [eq.mul_unreduced(t0), eq.mul_unreduced(t1), eq.mul_unreduced(t2)]
        };
        let acc_u = if half >= PAR_THRESHOLD {
            (0..half)
                .into_par_iter()
                .map(summand)
                .reduce(|| [F192Unreduced::ZERO; 3], xor3)
        } else {
            (0..half).map(summand).fold([F192Unreduced::ZERO; 3], xor3)
        };
        [acc_u[0].reduce(), acc_u[1].reduce(), acc_u[2].reduce()]
    }

    /// Bind this round's variable at the (shared) challenge `rk`.
    fn fold(&mut self, rk: F192) {
        par_fold_into(&self.even, rk, &mut self.even_next);
        std::mem::swap(&mut self.even, &mut self.even_next);
        par_fold_into(&self.odd, rk, &mut self.odd_next);
        std::mem::swap(&mut self.odd, &mut self.odd_next);
    }
}

/// Shrink `eqr` to the next round's suffix table (in place: the read cursor
/// `2·idx` stays ahead of the write cursor `idx`). `eq(r_j,0) + eq(r_j,1) = 1`,
/// so summing adjacent entries marginalizes the bound variable with no
/// multiplies (vs rebuilding with ~2^{k-j} muls per round).
fn shrink_eq(eqr: &mut Vec<F192>) {
    let eq_half = eqr.len() / 2;
    for idx in 0..eq_half {
        eqr[idx] = eqr[2 * idx] + eqr[2 * idx + 1];
    }
    eqr.truncate(eq_half);
}

/// The result of a batched grand-product proof: the per-tree roots and leaf
/// values, all reduced to one shared evaluation point.
pub struct ProductBatch<const N: usize> {
    pub roots: [F192; N],
    pub point: Vec<F192>,
    pub values: [F192; N],
}

fn combine<const N: usize>(values: &[F192; N], lambda: F192) -> F192 {
    values.iter().rev().fold(F192::ZERO, |acc, &value| value + lambda * acc)
}

/// Prove equal-size grand products as one RLC-batched GKR: the roots
/// are bound, a combiner λ is sampled, and each layer runs a SINGLE sumcheck
/// on the combined summand `eq·Σ_t λᵗ·eᵗ·oᵗ` (one message triple per round,
/// one shared challenge), so all trees reduce to leaf claims at the SAME
/// point. Each layer binds the tail evaluations and then samples a FRESH
/// λ for the next layer, which pins the individual values inside the bound
/// combination (Schwartz–Zippel); the last layer's individuals are pinned by
/// the decompose identities.
pub fn prove_product_batch<const N: usize>(leaves: [Vec<F192>; N], ps: &mut ProverState) -> ProductBatch<N> {
    assert!(N > 0, "a product batch must contain at least one tree");
    let mu = crate::log2_strict_usize(leaves[0].len());
    assert!(
        leaves.iter().all(|l| l.len() == 1 << mu),
        "batched trees must have equal size"
    );
    let layers = leaves.map(build_layers);
    let roots = std::array::from_fn(|t| layers[t][mu][0]);
    for root in roots {
        ps.add_scalar(root);
    }
    let mut lambda = ps.sample();

    let mut r: Vec<F192> = Vec::new();
    let mut values = roots;

    for i in (1..=mu).rev() {
        let k = mu - i;
        let width = 1usize << k;
        let mut trees: [LayerState; N] = std::array::from_fn(|t| LayerState::new(&layers[t][i - 1], width));
        // The challenges are shared, so ONE eq table serves all trees.
        let mut eqr: Vec<F192> = if k > 0 { eq_table(&r[1..]) } else { Vec::new() };

        let mut rho = Vec::with_capacity(k);
        for _ in 0..k {
            let msgs: [[F192; 3]; N] = std::array::from_fn(|t| trees[t].round_message(&eqr));
            let combined: [F192; 3] = std::array::from_fn(|n| {
                let values: [F192; N] = std::array::from_fn(|t| msgs[t][n]);
                combine(&values, lambda)
            });
            ps.add_scalars(&combined);
            let rk = ps.sample();
            rho.push(rk);
            for tree in &mut trees {
                tree.fold(rk);
            }
            shrink_eq(&mut eqr);
        }

        for tree in &trees {
            ps.add_scalar(tree.even[0]);
            ps.add_scalar(tree.odd[0]);
        }
        let c = ps.sample();
        for (value, tree) in values.iter_mut().zip(&trees) {
            *value = interp(tree.even[0], tree.odd[0], c);
        }
        lambda = ps.sample(); // fresh combiner: pins the individual tail values

        let mut next_point = Vec::with_capacity(k + 1);
        next_point.push(c);
        next_point.extend_from_slice(&rho);
        r = next_point;
    }

    ProductBatch {
        roots,
        point: r,
        values,
    }
}

/// Verify an RLC-batched product proof: the roots, a combiner λ, then per layer
/// one standard sumcheck on the combined claim, tail evaluations checked as
/// `eq·Σ_t λᵗ·e₀ᵗ·e₁ᵗ`, a line challenge, and
/// a fresh λ. Returns the roots and the shared-point leaf claims.
pub fn verify_product_batch<const N: usize>(mu: usize, vs: &mut VerifierState) -> Result<ProductBatch<N>, GkrError> {
    assert!(N > 0, "a product batch must contain at least one tree");
    let mut roots = [F192::ZERO; N];
    for root in &mut roots {
        *root = vs.next_scalar().map_err(|_| GkrError::Truncated)?;
    }
    let mut lambda = vs.sample();
    let nodes = tri_nodes();
    let mut r: Vec<F192> = Vec::new();
    let mut values = roots;

    for i in (1..=mu).rev() {
        let k = mu - i;
        let mut claim = combine(&values, lambda);
        let mut rho = Vec::with_capacity(k);
        let mut eq_acc = F192::ONE; // ∏_{l<round} eq(r_l, ρ_l)
        for (round, &rj) in r.iter().enumerate().take(k) {
            let msg = vs.next_scalars(3).map_err(|_| GkrError::Truncated)?;
            if eq_acc * ((F192::ONE + rj) * msg[0] + rj * msg[1]) != claim {
                return Err(GkrError::SumcheckInconsistent { layer: i, round });
            }
            let rk = vs.sample();
            rho.push(rk);
            eq_acc *= F192::ONE + rj + rk;
            claim = eq_acc * lagrange_eval(&nodes, &msg, rk);
        }
        let mut evals = [[F192::ZERO; 2]; N];
        for eval in evals.iter_mut().flatten() {
            *eval = vs.next_scalar().map_err(|_| GkrError::Truncated)?;
        }
        let products = evals.map(|[e0, e1]| e0 * e1);
        if claim != eq_acc * combine(&products, lambda) {
            return Err(GkrError::LayerMismatch { layer: i });
        }
        let c = vs.sample();
        for (value, [e0, e1]) in values.iter_mut().zip(evals) {
            *value = interp(e0, e1, c);
        }
        lambda = vs.sample(); // fresh combiner: pins the individual tail values

        let mut next_point = Vec::with_capacity(k + 1);
        next_point.push(c);
        next_point.extend_from_slice(&rho);
        r = next_point;
    }

    Ok(ProductBatch {
        roots,
        point: r,
        values,
    })
}

pub type ProductPair = ProductBatch<2>;

pub fn prove_product_pair(leaves: [Vec<F192>; 2], ps: &mut ProverState) -> ProductPair {
    prove_product_batch(leaves, ps)
}

pub fn verify_product_pair(mu: usize, vs: &mut VerifierState) -> Result<ProductPair, GkrError> {
    verify_product_batch(mu, vs)
}
