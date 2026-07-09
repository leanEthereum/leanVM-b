//! The grand product via GKR (§4.3): given leaves `v_0…v_{2^μ-1}`, prove the
//! root `P = ∏ v_k` of the binary product tree, reducing one claim per layer down
//! to a single leaf evaluation `Ṽ_0(ζ)`. Layer relation (low-bit split): `V_i(x)
//! = V_{i-1}(0,x)·V_{i-1}(1,x)`; each layer's sumcheck uses the eq-trick, so its
//! round univariate is degree 2 (3 evaluations) plus a degree-1 fold-back line.
//! Leaves and every layer are `E`-valued (the bus fingerprints mix `K`-columns
//! into `E` upstream, [`crate::leaf`]).

use crate::PAR_THRESHOLD;
use crate::field::{F128T, mul_by_g_e};
use crate::multilinear::lagrange_eval;
use crate::multilinear::{add3, eq_table, interp, tri_nodes};
use crate::transcript::{ProverState, VerifierState};
use rayon::prelude::*;

/// Bind the lowest variable of `src` into `dst` (in parallel for large tables):
/// `dst[i] = interp(src[2i], src[2i+1], rho)`. Writing into a caller-owned
/// scratch buffer instead of a fresh Vec lets each layer's rounds ping-pong two
/// allocations instead of allocating (and page-faulting) per round.
/// Deliberately scalar: pairing adjacent outputs through [`F128T::mul2`]
/// measures slower (2.14 vs 1.75 ns/output). The mul has the loop-invariant
/// `rho` on one side, the OoO core already overlaps the independent
/// iterations, and the pair kernel's third NEON fold outweighs its 2-PMULL
/// saving once nothing is latency-bound.
fn par_fold_into(src: &[F128T], rho: F128T, dst: &mut Vec<F128T>) {
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
    pub point: Vec<F128T>,
    pub value: F128T,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GkrError {
    Truncated,
    SumcheckInconsistent { layer: usize, round: usize },
    LayerMismatch { layer: usize },
}

/// Pad a leaf vector up to a power of two with the multiplicative identity `1`
/// (so the product is unchanged), returning `(padded, μ)`.
pub fn pad_to_pow2(mut leaves: Vec<F128T>) -> (Vec<F128T>, usize) {
    if leaves.is_empty() {
        leaves.push(F128T::ONE);
    }
    let mu = crate::log2_ceil_usize(leaves.len());
    leaves.resize(1 << mu, F128T::ONE);
    (leaves, mu)
}

/// Build every product-tree layer: `layers[0]` = leaves, `layers[μ]` = `[root]`.
/// Deliberately scalar: routing adjacent output pairs through [`F128T::mul2`]
/// wins ~4% single-threaded but loses ~2% end to end (interleaved A/B: 1339 vs
/// 1370 ms bus-GKR at `LEANVM_XMSS_N=1024`, 10 threads); at full parallelism
/// this loop is memory-bandwidth-bound and the paired form only adds overhead.
fn build_layers(leaves: Vec<F128T>) -> Vec<Vec<F128T>> {
    let mut layers = vec![leaves];
    while layers.last().unwrap().len() > 1 {
        let cur = layers.last().unwrap();
        let half = cur.len() / 2;
        let next: Vec<F128T> = if half >= PAR_THRESHOLD {
            (0..half).into_par_iter().map(|j| cur[2 * j] * cur[2 * j + 1]).collect()
        } else {
            (0..half).map(|j| cur[2 * j] * cur[2 * j + 1]).collect()
        };
        layers.push(next);
    }
    layers
}

/// Prove `root = ∏ leaves` for a power-of-two leaf vector. Returns the product and
/// the leaf claim `Ṽ₀(ζ)`, which the leaf decomposition (§4.4) settles.
pub fn prove_product(leaves: Vec<F128T>, ps: &mut ProverState) -> (F128T, LeafClaim) {
    let mu = crate::log2_strict_usize(leaves.len());
    let layers = build_layers(leaves);
    let root = layers[mu][0];
    ps.add_scalar(root);

    let mut r: Vec<F128T> = Vec::new();
    // Each layer's connecting line at `c` is `Ṽ_0` at the new point, so the last
    // one is `Ṽ_0(r)` — no final re-evaluation of the whole leaf table needed.
    let mut value = root;

    for i in (1..=mu).rev() {
        let below = &layers[i - 1];
        let k = mu - i; // sumcheck variables this layer
        let width = 1usize << k;
        let strided_copy = |off: usize| -> Vec<F128T> {
            if width >= PAR_THRESHOLD {
                (0..width).into_par_iter().map(|j| below[2 * j + off]).collect()
            } else {
                (0..width).map(|j| below[2 * j + off]).collect()
            }
        };
        let mut even = strided_copy(0);
        let mut odd = strided_copy(1);
        // Ping-pong fold scratch, allocated once per layer, reused every round.
        let mut even_next: Vec<F128T> = Vec::new();
        let mut odd_next: Vec<F128T> = Vec::new();

        // `eqr` at round j is eq over the variables after the one bound that
        // round (the eq-trick keeps the per-row product `eq·even·odd` at degree
        // 2). Build it ONCE per layer for r[1..]; each later round's table is
        // the pair-wise XOR fold of the previous one — `eq(r_j,0) + eq(r_j,1)
        // = 1`, so summing adjacent entries marginalizes the bound variable
        // with no multiplies (vs rebuilding with ~2^{k-j} muls per round).
        let mut eqr: Vec<F128T> = if k > 0 { eq_table(&r[1..]) } else { Vec::new() };

        let mut rho = Vec::with_capacity(k);
        for _ in 0..k {
            let half = even.len() / 2;
            // Deliberately scalar: batching the row's independent muls through
            // [`F128T::mul2`] (within a row or across two adjacent rows)
            // measures no better or worse (16.7 scalar vs 18.4 / 16.8
            // ns/idx); the closure's live values plus the 2-wide dataflow eat
            // the kernel's small throughput edge.
            let summand = |idx: usize| -> [F128T; 3] {
                let (lo, hi) = (2 * idx, 2 * idx + 1);
                let eq = eqr[idx];
                let prod0 = eq * even[lo] * odd[lo];
                let prod1 = eq * even[hi] * odd[hi];
                // The degree-2 round univariate is sent at nodes {0, 1, g}; node 2
                // is the generator `g = x`, so `g·diff = mul_by_g_e(diff)` — two
                // shift-folds, not a carry-less mul (bit-identical to `nodes[2] * diff`).
                let (even_diff, odd_diff) = (even[lo] + even[hi], odd[lo] + odd[hi]);
                let (even_at2, odd_at2) = (even[lo] + mul_by_g_e(even_diff), odd[lo] + mul_by_g_e(odd_diff));
                let prod2 = eq * even_at2 * odd_at2;
                [prod0, prod1, prod2]
            };
            let acc = if half >= PAR_THRESHOLD {
                (0..half).into_par_iter().map(summand).reduce(|| [F128T::ZERO; 3], add3)
            } else {
                (0..half).map(summand).fold([F128T::ZERO; 3], add3)
            };
            ps.add_scalars(&acc);
            let rk = ps.sample();
            rho.push(rk);
            par_fold_into(&even, rk, &mut even_next);
            std::mem::swap(&mut even, &mut even_next);
            par_fold_into(&odd, rk, &mut odd_next);
            std::mem::swap(&mut odd, &mut odd_next);
            // Shrink eq to the next round's suffix table (in place: the read
            // cursor `2·idx` stays ahead of the write cursor `idx`).
            let eq_half = eqr.len() / 2;
            for idx in 0..eq_half {
                eqr[idx] = eqr[2 * idx] + eqr[2 * idx + 1];
            }
            eqr.truncate(eq_half);
        }

        let (eval0, eval1) = (even[0], odd[0]);
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

/// Verify a product proof, returning the product `root` and the leaf claim `Ṽ₀(ζ)`.
pub fn verify_product(mu: usize, vs: &mut VerifierState) -> Result<(F128T, LeafClaim), GkrError> {
    let root = vs.next_scalar().map_err(|_| GkrError::Truncated)?;
    let nodes = tri_nodes();
    let mut r: Vec<F128T> = Vec::new();
    let mut claim = root;

    for i in (1..=mu).rev() {
        let k = mu - i;
        let mut rho = Vec::with_capacity(k);
        let mut eq_acc = F128T::ONE; // ∏_{l<round} eq(r_l, ρ_l)
        for (round, &rj) in r.iter().enumerate().take(k) {
            let msg = vs.next_scalars(3).map_err(|_| GkrError::Truncated)?;
            // Full round univariate `q(t) = eq_acc·eq(r_round, t)·h(t)`, so
            // `q(0)+q(1)` must equal the claim.
            if eq_acc * ((F128T::ONE + rj) * msg[0] + rj * msg[1]) != claim {
                return Err(GkrError::SumcheckInconsistent { layer: i, round });
            }
            let rk = vs.sample();
            rho.push(rk);
            eq_acc *= F128T::ONE + rj + rk;
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
