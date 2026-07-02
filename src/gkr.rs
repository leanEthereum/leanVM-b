//! The grand product via GKR (§4.3 of doc.tex).
//!
//! Given a leaf vector `v_0, …, v_{2^μ-1}`, GKR proves the root `P = ∏_k v_k` of
//! the binary product tree, reducing one claim per layer down to a single
//! evaluation claim `Ṽ_0(ζ)` on the leaf multilinear. The bus uses two passes —
//! one per side of the balance equation — and accepts when the roots agree and
//! each leaf claim ties back to the committed columns (the leaf decomposition,
//! §4.4, lives in the `bus` layer; here we expose the raw product argument).
//!
//! Layer relation (low-bit split, little-endian): `V_i(x) = V_{i-1}(0,x)·
//! V_{i-1}(1,x)`. The per-layer sumcheck `Ṽ_i(r) = Σ_x eq(r,x) V_{i-1}(0,x)
//! V_{i-1}(1,x)` is degree 3, sent as 4 evaluations; a degree-1 line then folds
//! the split variable back in.

use crate::PAR_THRESHOLD;
use crate::field::F128;
use crate::multilinear::lagrange_eval;
use crate::multilinear::{add3, eq_table, interp, tri_nodes};
use crate::transcript::{ProverState, VerifierState};
use rayon::prelude::*;

/// Bind the lowest variable of `table` to `rho`, in parallel for large tables.
/// (A GKR-local variant of `fold_low`, tuned for the big per-layer arrays.)
fn par_fold(table: &[F128], rho: F128) -> Vec<F128> {
    let half = table.len() / 2;
    if half >= PAR_THRESHOLD {
        (0..half)
            .into_par_iter()
            .map(|i| interp(table[2 * i], table[2 * i + 1], rho))
            .collect()
    } else {
        (0..half).map(|i| interp(table[2 * i], table[2 * i + 1], rho)).collect()
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
    /// The proof stream ended before the layer it described.
    Truncated,
    SumcheckInconsistent {
        layer: usize,
        round: usize,
    },
    LayerMismatch {
        layer: usize,
    },
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

/// Build every product-tree layer: `layers[0]` = leaves (consumed), `layers[μ]`
/// = `[root]`.
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

/// Prove `root = ∏ leaves` for a power-of-two leaf vector, writing the proof into
/// `ps`. Returns the product `root` and the prover's leaf claim `Ṽ₀(ζ)` (the
/// verifier reconstructs the same `ζ`), which the leaf decomposition (§4.4)
/// settles against the columns.
pub fn prove_product(leaves: Vec<F128>, ps: &mut ProverState) -> (F128, LeafClaim) {
    let mu = crate::log2_strict_usize(leaves.len());
    let layers = build_layers(leaves); // layers[0] is the (moved) leaf table
    let root = layers[mu][0];
    ps.add_scalar(root);

    let nodes = tri_nodes();
    let mut r: Vec<F128> = Vec::new();
    // The leaf claim value, tracked across layers: each layer's connecting line
    // at `c` is exactly `Ṽ_0` at the new point, so the final one is `Ṽ_0(r)` (no
    // need to re-evaluate the whole 2^μ leaf table at the end). For μ=0 it is the
    // root.
    let mut value = root;

    // Reduce claim about V_i to claim about V_{i-1}, for i = μ … 1.
    for i in (1..=mu).rev() {
        let below = &layers[i - 1];
        let k = mu - i; // sumcheck variables this layer
        let width = 1usize << k;
        let mut even: Vec<F128> = (0..width).map(|j| below[2 * j]).collect();
        let mut odd: Vec<F128> = (0..width).map(|j| below[2 * j + 1]).collect();

        let mut rho = Vec::with_capacity(k);
        for j in 0..k {
            let half = even.len() / 2;
            let node2 = nodes[2]; // the third interpolation node, γ
            // The eq weight factors out (Gruen): the round message is the
            // degree-2 `h(t) = Σ_{x'} eq(r_{>j}, x')·even(t,x')·odd(t,x')` at the 3
            // nodes; the verifier multiplies back `eq(r_{≤j}, t)`. `eqr` is eq over
            // the variables *after* the one bound this round (one fewer than
            // `even`/`odd`), so the per-row product is degree 2, not 3.
            let eqr = eq_table(&r[j + 1..]);
            let summand = |idx: usize| -> [F128; 3] {
                let (lo, hi) = (2 * idx, 2 * idx + 1);
                let eq = eqr[idx];
                let prod0 = eq * even[lo] * odd[lo];
                let prod1 = eq * even[hi] * odd[hi];
                let (even_diff, odd_diff) = (even[lo] + even[hi], odd[lo] + odd[hi]);
                let (even_at2, odd_at2) = (even[lo] + node2 * even_diff, odd[lo] + node2 * odd_diff);
                let prod2 = eq * even_at2 * odd_at2;
                [prod0, prod1, prod2]
            };
            let acc = if half >= PAR_THRESHOLD {
                (0..half).into_par_iter().map(summand).reduce(|| [F128::ZERO; 3], add3)
            } else {
                (0..half).map(summand).fold([F128::ZERO; 3], add3)
            };
            ps.add_scalars(&acc);
            let rk = ps.sample();
            rho.push(rk);
            even = par_fold(&even, rk);
            odd = par_fold(&odd, rk);
        }

        let (eval0, eval1) = (even[0], odd[0]);
        ps.add_scalar(eval0);
        ps.add_scalar(eval1);
        let c = ps.sample();
        value = interp(eval0, eval1, c); // Ṽ_{i-1}(c, ρ) = Ṽ_0(r) on the last layer

        // New claim point for V_{i-1}: split var (= c) is the new low bit.
        let mut next_point = Vec::with_capacity(k + 1);
        next_point.push(c);
        next_point.extend_from_slice(&rho);
        r = next_point;
    }

    (root, LeafClaim { point: r, value })
}

/// Verify a product proof read from `vs`, returning the product `root` and the
/// leaf evaluation claim `Ṽ₀(ζ)` for the caller to settle against the columns.
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
            // The prover sent only `h`; the full round univariate is
            // `q(t) = eq_acc·eq(r_round, t)·h(t)`, so `q(0)+q(1)` must equal the
            // claim (`eq(r_round,0)=1+r_round`, `eq(r_round,1)=r_round`).
            if eq_acc * ((F128::ONE + rj) * msg[0] + rj * msg[1]) != claim {
                return Err(GkrError::SumcheckInconsistent { layer: i, round });
            }
            let rk = vs.sample();
            rho.push(rk);
            eq_acc *= F128::ONE + rj + rk; // ·= eq(r_round, ρ_round)
            claim = eq_acc * lagrange_eval(&nodes, &msg, rk); // = q(ρ_round)
        }
        let eval0 = vs.next_scalar().map_err(|_| GkrError::Truncated)?;
        let eval1 = vs.next_scalar().map_err(|_| GkrError::Truncated)?;
        // Now `claim = eq(r,ρ)·V_{i-1}(0,ρ)·V_{i-1}(1,ρ)` (eq_acc = eq(r,ρ)); bind
        // the prover's sent evals.
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
