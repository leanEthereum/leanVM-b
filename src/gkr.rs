//! The grand product via GKR (§4.3): given leaves `v_0…v_{2^μ-1}`, prove the
//! root `P = ∏ v_k` of the binary product tree, reducing one claim per layer down
//! to a single leaf evaluation `Ṽ_0(ζ)`. Layer relation (low-bit split): `V_i(x)
//! = V_{i-1}(0,x)·V_{i-1}(1,x)`; each layer's sumcheck uses the eq-trick, so its
//! round univariate is degree 2 (3 evaluations) plus a degree-1 fold-back line.

use crate::PAR_THRESHOLD;
use crate::field::{F128, F256Unreduced, mul_by_x};
use crate::multilinear::lagrange_eval;
use crate::multilinear::{eq_table, interp, tri_nodes};
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

/// The single evaluation claim the proof reduces to: `Ṽ_0(point) = value`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeafClaim {
    pub point: Vec<F128>,
    pub value: F128,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GkrError {
    Truncated,
    SumcheckInconsistent { layer: usize, round: usize },
    LayerMismatch { layer: usize },
}

/// Pad a leaf vector up to a power of two with the multiplicative identity `1`
/// (so the product is unchanged), returning `(padded, μ)`.
pub fn pad_to_pow2(mut leaves: Vec<F128>) -> (Vec<F128>, usize) {
    if leaves.is_empty() {
        leaves.push(F128::ONE);
    }
    let mu = crate::log2_ceil_usize(leaves.len());
    leaves.resize(1 << mu, F128::ONE);
    (leaves, mu)
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

/// Prove `root = ∏ leaves` for a power-of-two leaf vector. Returns the product and
/// the leaf claim `Ṽ₀(ζ)`, which the leaf decomposition (§4.4) settles.
pub fn prove_product(leaves: Vec<F128>, ps: &mut ProverState) -> (F128, LeafClaim) {
    let mu = crate::log2_strict_usize(leaves.len());
    let layers = build_layers(leaves);
    let root = layers[mu][0];
    ps.add_scalar(root);

    let mut r: Vec<F128> = Vec::new();
    // Each layer's connecting line at `c` is `Ṽ_0` at the new point, so the last
    // one is `Ṽ_0(r)` — no final re-evaluation of the whole leaf table needed.
    let mut value = root;

    for i in (1..=mu).rev() {
        let k = mu - i; // sumcheck variables this layer
        let mut tree = LayerState::new(&layers[i - 1], 1usize << k);
        // `eqr` at round j is eq over the variables after the one bound that
        // round (the eq-trick keeps the per-row product `eq·even·odd` at degree
        // 2). Build it ONCE per layer for r[1..]; later rounds shrink it.
        let mut eqr: Vec<F128> = if k > 0 { eq_table(&r[1..]) } else { Vec::new() };

        let mut rho = Vec::with_capacity(k);
        for _ in 0..k {
            ps.add_scalars(&tree.round_message(&eqr));
            let rk = ps.sample();
            rho.push(rk);
            tree.fold(rk);
            shrink_eq(&mut eqr);
        }

        let (eval0, eval1) = (tree.even[0], tree.odd[0]);
        ps.add_scalar(eval0);
        ps.add_scalar(eval1);
        let c = ps.sample();
        value = interp(eval0, eval1, c); // Ṽ_{i-1}(c, ρ)

        let mut next_point = Vec::with_capacity(k + 1);
        next_point.push(c);
        next_point.extend_from_slice(&rho);
        r = next_point;
    }

    (root, LeafClaim { point: r, value })
}

/// Prove TWO equal-size grand products in lockstep: both roots are bound, then
/// every layer round sends tree A's message triple, tree B's, and samples ONE
/// shared challenge (likewise one shared line challenge per layer), so both
/// trees reduce to leaf claims at the SAME point. Sound by the usual union
/// bound (two degree-2 differences per shared challenge). Used for the bus
/// push/pull pair, whose matched blocks give equal μ — the shared point then
/// needs a single bytecode opening and one ζ buffer.
pub fn prove_product_pair(
    leaves_a: Vec<F128>,
    leaves_b: Vec<F128>,
    ps: &mut ProverState,
) -> ((F128, LeafClaim), (F128, LeafClaim)) {
    assert_eq!(leaves_a.len(), leaves_b.len(), "paired trees must have equal size");
    let mu = crate::log2_strict_usize(leaves_a.len());
    let (layers_a, layers_b) = rayon::join(|| build_layers(leaves_a), || build_layers(leaves_b));
    let (root_a, root_b) = (layers_a[mu][0], layers_b[mu][0]);
    ps.add_scalar(root_a);
    ps.add_scalar(root_b);

    let mut r: Vec<F128> = Vec::new();
    let (mut value_a, mut value_b) = (root_a, root_b);

    for i in (1..=mu).rev() {
        let k = mu - i;
        let width = 1usize << k;
        let mut tree_a = LayerState::new(&layers_a[i - 1], width);
        let mut tree_b = LayerState::new(&layers_b[i - 1], width);
        // The challenges are shared, so ONE eq table serves both trees.
        let mut eqr: Vec<F128> = if k > 0 { eq_table(&r[1..]) } else { Vec::new() };

        let mut rho = Vec::with_capacity(k);
        for _ in 0..k {
            ps.add_scalars(&tree_a.round_message(&eqr));
            ps.add_scalars(&tree_b.round_message(&eqr));
            let rk = ps.sample();
            rho.push(rk);
            tree_a.fold(rk);
            tree_b.fold(rk);
            shrink_eq(&mut eqr);
        }

        ps.add_scalar(tree_a.even[0]);
        ps.add_scalar(tree_a.odd[0]);
        ps.add_scalar(tree_b.even[0]);
        ps.add_scalar(tree_b.odd[0]);
        let c = ps.sample();
        value_a = interp(tree_a.even[0], tree_a.odd[0], c);
        value_b = interp(tree_b.even[0], tree_b.odd[0], c);

        let mut next_point = Vec::with_capacity(k + 1);
        next_point.push(c);
        next_point.extend_from_slice(&rho);
        r = next_point;
    }

    (
        (root_a, LeafClaim { point: r.clone(), value: value_a }),
        (root_b, LeafClaim { point: r, value: value_b }),
    )
}

/// Verify a product proof, returning the product `root` and the leaf claim `Ṽ₀(ζ)`.
pub fn verify_product(mu: usize, vs: &mut VerifierState) -> Result<(F128, LeafClaim), GkrError> {
    let root = vs.next_scalar().map_err(|_| GkrError::Truncated)?;
    let nodes = tri_nodes();
    let mut r: Vec<F128> = Vec::new();
    let mut claim = root;

    for i in (1..=mu).rev() {
        let k = mu - i;
        let mut rho = Vec::with_capacity(k);
        let mut eq_acc = F128::ONE; // ∏_{l<round} eq(r_l, ρ_l)
        for (round, &rj) in r.iter().enumerate().take(k) {
            let msg = vs.next_scalars(3).map_err(|_| GkrError::Truncated)?;
            // Full round univariate `q(t) = eq_acc·eq(r_round, t)·h(t)`, so
            // `q(0)+q(1)` must equal the claim.
            if eq_acc * ((F128::ONE + rj) * msg[0] + rj * msg[1]) != claim {
                return Err(GkrError::SumcheckInconsistent { layer: i, round });
            }
            let rk = vs.sample();
            rho.push(rk);
            eq_acc *= F128::ONE + rj + rk;
            claim = eq_acc * lagrange_eval(&nodes, &msg, rk);
        }
        let eval0 = vs.next_scalar().map_err(|_| GkrError::Truncated)?;
        let eval1 = vs.next_scalar().map_err(|_| GkrError::Truncated)?;
        // `claim = eq(r,ρ)·V_{i-1}(0,ρ)·V_{i-1}(1,ρ)`; bind the sent evals.
        if claim != eq_acc * eval0 * eval1 {
            return Err(GkrError::LayerMismatch { layer: i });
        }
        let c = vs.sample();
        claim = interp(eval0, eval1, c);

        let mut next_point = Vec::with_capacity(k + 1);
        next_point.push(c);
        next_point.extend_from_slice(&rho);
        r = next_point;
    }

    Ok((root, LeafClaim { point: r, value: claim }))
}

/// Verify a lockstep pair proof ([`prove_product_pair`]): both roots, then per
/// round both message triples against their own running claims with ONE shared
/// challenge. Returns the two (root, claim) pairs; the claims share the point.
pub fn verify_product_pair(
    mu: usize,
    vs: &mut VerifierState,
) -> Result<((F128, LeafClaim), (F128, LeafClaim)), GkrError> {
    let root_a = vs.next_scalar().map_err(|_| GkrError::Truncated)?;
    let root_b = vs.next_scalar().map_err(|_| GkrError::Truncated)?;
    let nodes = tri_nodes();
    let mut r: Vec<F128> = Vec::new();
    let (mut claim_a, mut claim_b) = (root_a, root_b);

    for i in (1..=mu).rev() {
        let k = mu - i;
        let mut rho = Vec::with_capacity(k);
        let mut eq_acc = F128::ONE; // ∏_{l<round} eq(r_l, ρ_l), shared
        for (round, &rj) in r.iter().enumerate().take(k) {
            let msg_a = vs.next_scalars(3).map_err(|_| GkrError::Truncated)?;
            let msg_b = vs.next_scalars(3).map_err(|_| GkrError::Truncated)?;
            let line = |m: &[F128]| eq_acc * ((F128::ONE + rj) * m[0] + rj * m[1]);
            if line(&msg_a) != claim_a || line(&msg_b) != claim_b {
                return Err(GkrError::SumcheckInconsistent { layer: i, round });
            }
            let rk = vs.sample();
            rho.push(rk);
            eq_acc *= F128::ONE + rj + rk;
            claim_a = eq_acc * lagrange_eval(&nodes, &msg_a, rk);
            claim_b = eq_acc * lagrange_eval(&nodes, &msg_b, rk);
        }
        let eval0_a = vs.next_scalar().map_err(|_| GkrError::Truncated)?;
        let eval1_a = vs.next_scalar().map_err(|_| GkrError::Truncated)?;
        let eval0_b = vs.next_scalar().map_err(|_| GkrError::Truncated)?;
        let eval1_b = vs.next_scalar().map_err(|_| GkrError::Truncated)?;
        if claim_a != eq_acc * eval0_a * eval1_a || claim_b != eq_acc * eval0_b * eval1_b {
            return Err(GkrError::LayerMismatch { layer: i });
        }
        let c = vs.sample();
        claim_a = interp(eval0_a, eval1_a, c);
        claim_b = interp(eval0_b, eval1_b, c);

        let mut next_point = Vec::with_capacity(k + 1);
        next_point.push(c);
        next_point.extend_from_slice(&rho);
        r = next_point;
    }

    Ok((
        (root_a, LeafClaim { point: r.clone(), value: claim_a }),
        (root_b, LeafClaim { point: r, value: claim_b }),
    ))
}
