//! The grand product via GKR (§4.3): given leaves `v_0…v_{2^μ-1}`, prove the
//! root `P = ∏ v_k` of the binary product tree, reducing one claim per layer down
//! to a single leaf evaluation `Ṽ_0(ζ)`. Layer relation (low-bit split): `V_i(x)
//! = V_{i-1}(0,x)·V_{i-1}(1,x)`; each layer's sumcheck uses the eq-trick, so its
//! round univariate is degree 2 (3 evaluations) plus a degree-1 fold-back line.

use crate::PAR_THRESHOLD;
use primitives::field::{F128, F256Unreduced, mul_by_x};
use primitives::multilinear::lagrange_eval;
use primitives::multilinear::{eq_table, interp, tri_nodes};
use crate::transcript::{ProverState, VerifierState};
use rayon::prelude::*;

/// Bind the lowest variable of `src` into `dst` (in parallel for large tables):
/// `dst[i] = interp(src[2i], src[2i+1], rho)`. Writing into a caller-owned
/// scratch buffer instead of a fresh Vec lets each layer's rounds ping-pong two
/// allocations instead of allocating (and page-faulting) per round.
fn par_fold_into(src: &[F128], rho: F128, dst: &mut Vec<F128>) {
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
fn build_layers(leaves: Vec<F128>) -> Vec<Vec<F128>> {
    let mut layers = vec![leaves];
    while layers.last().unwrap().len() > 1 {
        let cur = layers.last().unwrap();
        let half = cur.len() / 2;
        let next: Vec<F128> = if half >= PAR_THRESHOLD {
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
    even: Vec<F128>,
    odd: Vec<F128>,
    even_next: Vec<F128>,
    odd_next: Vec<F128>,
}

impl LayerState {
    fn new(below: &[F128], width: usize) -> Self {
        let strided_copy = |off: usize| -> Vec<F128> {
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
    fn round_message(&self, eqr: &[F128]) -> [F128; 3] {
        let half = self.even.len() / 2;
        let (even, odd) = (&self.even, &self.odd);
        let summand = |idx: usize| -> [F256Unreduced; 3] {
            let (lo, hi) = (2 * idx, 2 * idx + 1);
            let eq = eqr[idx];
            let t0 = even[lo] * odd[lo];
            let t1 = even[hi] * odd[hi];
            // Node 2 is the generator `g = x`, so `g·diff = mul_by_x(diff)` — a
            // shift-fold, not a carry-less mul (bit-identical to `nodes[2] * diff`).
            let (even_diff, odd_diff) = (even[lo] + even[hi], odd[lo] + odd[hi]);
            let (even_at2, odd_at2) = (even[lo] + mul_by_x(even_diff), odd[lo] + mul_by_x(odd_diff));
            let t2 = even_at2 * odd_at2;
            // Defer the mod-p reduction of the outer eq·(…) products:
            // XOR-accumulate the 256-bit unreduced products and reduce once
            // per accumulator after the sum (reduction commutes with XOR).
            [eq.mul_unreduced(t0), eq.mul_unreduced(t1), eq.mul_unreduced(t2)]
        };
        let xor3 = |mut x: [F256Unreduced; 3], y: [F256Unreduced; 3]| {
            x[0] ^= y[0];
            x[1] ^= y[1];
            x[2] ^= y[2];
            x
        };
        let acc_u = if half >= PAR_THRESHOLD {
            (0..half).into_par_iter().map(summand).reduce(|| [F256Unreduced::ZERO; 3], xor3)
        } else {
            (0..half).map(summand).fold([F256Unreduced::ZERO; 3], xor3)
        };
        [acc_u[0].reduce(), acc_u[1].reduce(), acc_u[2].reduce()]
    }

    /// Bind this round's variable at the (shared) challenge `rk`.
    fn fold(&mut self, rk: F128) {
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
fn shrink_eq(eqr: &mut Vec<F128>) {
    let eq_half = eqr.len() / 2;
    for idx in 0..eq_half {
        eqr[idx] = eqr[2 * idx] + eqr[2 * idx + 1];
    }
    eqr.truncate(eq_half);
}

/// The result of a batched grand-product proof ([`prove_product_triple`]):
/// the per-tree roots and leaf values, all reduced to ONE shared evaluation
/// point (`Ṽ_t(point) = values[t]`).
pub struct ProductTriple {
    pub roots: [F128; 3],
    pub point: Vec<F128>,
    pub values: [F128; 3],
}

/// Prove THREE equal-size grand products as ONE RLC-batched GKR: the roots
/// are bound, a combiner λ is sampled, and each layer runs a SINGLE sumcheck
/// on the combined summand `eq·Σ_t λᵗ·eᵗ·oᵗ` (one message triple per round,
/// one shared challenge), so all trees reduce to leaf claims at the SAME
/// point. Each layer binds the six tail evaluations and then samples a FRESH
/// λ for the next layer, which pins the individual values inside the bound
/// combination (Schwartz–Zippel); the last layer's individuals are pinned by
/// the decompose identities. Used for the bus push/pull/count trees: push and
/// pull match block-for-block, and the caller pads the count tree with
/// identity leaves up to their μ.
pub fn prove_product_triple(leaves: [Vec<F128>; 3], ps: &mut ProverState) -> ProductTriple {
    let mu = crate::log2_strict_usize(leaves[0].len());
    assert!(leaves.iter().all(|l| l.len() == 1 << mu), "batched trees must have equal size");
    let layers = leaves.map(build_layers);
    let roots = [layers[0][mu][0], layers[1][mu][0], layers[2][mu][0]];
    for root in roots {
        ps.add_scalar(root);
    }
    let mut lambda = ps.sample();

    let mut r: Vec<F128> = Vec::new();
    let mut values = roots;

    for i in (1..=mu).rev() {
        let k = mu - i;
        let width = 1usize << k;
        let mut trees = [0, 1, 2].map(|t| LayerState::new(&layers[t][i - 1], width));
        // The challenges are shared, so ONE eq table serves all trees.
        let mut eqr: Vec<F128> = if k > 0 { eq_table(&r[1..]) } else { Vec::new() };

        let mut rho = Vec::with_capacity(k);
        for _ in 0..k {
            let msgs = [0, 1, 2].map(|t| trees[t].round_message(&eqr));
            ps.add_scalars(&[0, 1, 2].map(|n| msgs[0][n] + lambda * (msgs[1][n] + lambda * msgs[2][n])));
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

    ProductTriple { roots, point: r, values }
}

/// Verify an RLC-batched triple proof ([`prove_product_triple`]): the roots,
/// a combiner λ, then per layer ONE standard sumcheck on the combined claim,
/// six tail evaluations checked as `eq·Σ_t λᵗ·e₀ᵗ·e₁ᵗ`, a line challenge, and
/// a fresh λ. Returns the roots and the shared-point leaf claims.
pub fn verify_product_triple(mu: usize, vs: &mut VerifierState) -> Result<ProductTriple, GkrError> {
    let mut roots = [F128::ZERO; 3];
    for root in &mut roots {
        *root = vs.next_scalar().map_err(|_| GkrError::Truncated)?;
    }
    let mut lambda = vs.sample();
    let nodes = tri_nodes();
    let mut r: Vec<F128> = Vec::new();
    let mut values = roots;

    for i in (1..=mu).rev() {
        let k = mu - i;
        let mut claim = values[0] + lambda * (values[1] + lambda * values[2]);
        let mut rho = Vec::with_capacity(k);
        let mut eq_acc = F128::ONE; // ∏_{l<round} eq(r_l, ρ_l)
        for (round, &rj) in r.iter().enumerate().take(k) {
            let msg = vs.next_scalars(3).map_err(|_| GkrError::Truncated)?;
            if eq_acc * ((F128::ONE + rj) * msg[0] + rj * msg[1]) != claim {
                return Err(GkrError::SumcheckInconsistent { layer: i, round });
            }
            let rk = vs.sample();
            rho.push(rk);
            eq_acc *= F128::ONE + rj + rk;
            claim = eq_acc * lagrange_eval(&nodes, &msg, rk);
        }
        let mut evals = [[F128::ZERO; 2]; 3];
        for eval in evals.iter_mut().flatten() {
            *eval = vs.next_scalar().map_err(|_| GkrError::Truncated)?;
        }
        let products = evals.map(|[e0, e1]| e0 * e1);
        if claim != eq_acc * (products[0] + lambda * (products[1] + lambda * products[2])) {
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

    Ok(ProductTriple { roots, point: r, values })
}
