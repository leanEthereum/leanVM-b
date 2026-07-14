// Credit: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Zerocheck PIOP: prove a(y) · b(y) ⊕ c(y) = 0 for all y ∈ {0,1}^m.
//!
//! Inputs are three bit vectors of length 2^m. Output is an evaluation claim
//! on the multilinear extensions â, b̂, ĉ at the protocol-derived point.
//!
//! Protocol shape (m = log_n, k_skip = [`K_SKIP`] = 6):
//!   1. Verifier samples `r ∈ F_{2^128}^m` (the zerocheck challenge).
//!   2. Prover sends `P^{AB}(λ)` and `P^C(λ)` for λ ∈ Λ, |Λ| = 2^k_skip.
//!   3. Verifier samples `z ∈ F_{2^128}` (univariate-skip fold point).
//!   4. For each of the `m - k_skip` multilinear rounds, prover sends
//!      `(P_r(1), P_r(∞))` and verifier samples `ρ_r`.
//!   5. Prover sends final MLE evaluations `(â, b̂, ĉ)` at the resulting point.
//!
//! Both `prove` and `verify` are wired end-to-end. The prove→verify roundtrip
//! is tested on honest witnesses; verify also rejects byte-mutated proofs and
//! shape-corrupted ones.

use fiat_shamir::transcript::{ProverState, VerifierState};
use pcs::{as_e, as_ghash};
use primitives::field::{F8, F128};
use pcs::ntt::{AdditiveNttGf8, InvNttTableByteSingleGf8};

pub mod multilinear;
pub mod univariate_skip;
pub mod univariate_skip_optimized;

use multilinear::{
    UniSkipFoldTable, fold_and_compute_round_pair_into, fold_in_place_pair,
    interpolate_at_z_combined, interpolate_at_z_on_lambda, round_pair_naive,
    uni_skip_fold_and_round_pair_optimized_packed_padded,
};
use univariate_skip_optimized::{
    c_s_f128, medium_challenges_ghash, round1_shift_reduce_extract_c_packed_padded,
    small_challenges_ghash,
};

/// Number of variables folded in round 1 via the additive-NTT univariate skip.
/// |Λ| = 2^K_SKIP = 64 elements; the round-1 prover message is two length-64
/// vectors of F128.
pub const K_SKIP: usize = 6;
const N_INNER: usize = 7; // 3 small + 4 medium fixed-constant eq dimensions

/// Build the zerocheck challenge vector in the shared prover/verifier order:
/// sampled skip coordinates, fixed inner coordinates, then sampled outer ones.
fn challenge_vector(m: usize, mut sample_vec: impl FnMut(usize) -> Vec<F128>) -> Vec<F128> {
    let skip = sample_vec(K_SKIP);
    let outer = sample_vec(m - K_SKIP - N_INNER);
    skip.into_iter()
        .chain(small_challenges_ghash())
        .chain(medium_challenges_ghash())
        .chain(outer)
        .collect()
}

/// Witness padding descriptor for URM work-skipping.
///
/// The witness is a sequence of `2^(m - k_log)` blocks of `2^k_log` bits each;
/// inside each block, bits `[0, useful_bits_per_block)` carry real data and
/// bits `[useful_bits_per_block, 2^k_log)` are zero padding. URM contributions
/// from a chunk of all-zero bits are themselves zero, so we can skip those
/// chunks and produce byte-identical output.
///
pub use pcs::pack::PaddingSpec;

// ---------------------------------------------------------------------------
// Public types: claim, proof, error.
// ---------------------------------------------------------------------------

/// Evaluation claims on the multilinear extensions of a, b, c. **Note that
/// `a_eval`/`b_eval` and `c_eval` are claimed at *different points*** —
/// extract_c separates C from the AB sumcheck:
///
/// - `a_eval`, `b_eval` are at `(z, mlv_challenges)` — the AB sumcheck binds
///   the rest variables one at a time to fresh `ρ_r` challenges.
/// - `c_eval` is at `(z, r_rest)` — C is linear, so its eq-weighted sum
///   collapses immediately to an MLE evaluation at the original eq weights;
///   no per-round folding needed. Here `r_rest = r[K_SKIP..m]` from the
///   zerocheck challenge.
///
/// The downstream caller (R1CS prover + PCS) opens each commitment at its
/// own claim point. Two openings for a, b at the same point; one for c at
/// a different point.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZerocheckClaim {
    /// Univariate-skip challenge sampled after round 1 (binds the K_SKIP
    /// skip variables).
    pub z: F128,
    /// AB sumcheck bind challenges, one per multilinear round; length = `m - K_SKIP`.
    pub mlv_challenges: Vec<F128>,
    /// Eq weights for the rest variables = the zerocheck challenge restricted
    /// to `r[K_SKIP..m]`. This is the *rest part of the c-claim's point*.
    /// Length = `m - K_SKIP`.
    pub r_rest: Vec<F128>,
    /// `â(z, mlv_challenges)`.
    pub a_eval: F128,
    /// `b̂(z, mlv_challenges)`.
    pub b_eval: F128,
    /// `ĉ(z, r_rest)` — at a *different point* than a_eval, b_eval.
    pub c_eval: F128,
}

// (No ZerocheckProof struct: every round message rides the shared transcript
// stream, in protocol order.)

/// Reasons the verifier may reject a proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifyError {
    /// `log_n` doesn't satisfy `log_n >= K_SKIP`.
    LogNTooSmall { log_n: usize, k_skip: usize },
    /// The proof stream ran out while reading a message.
    Transcript(fiat_shamir::transcript::Error),
    /// The AB sumcheck final consistency check failed: the inner running
    /// claim after all rounds should equal `final_a_eval · final_b_eval`.
    /// Any inconsistency in `round1_ab`, in a multilinear round's
    /// `(P_r(1), P_r(∞))`, or in `final_a_eval` / `final_b_eval` propagates
    /// to this check.
    SumcheckFinalFailed,
}

// ---------------------------------------------------------------------------
// API: prove / verify.
// ---------------------------------------------------------------------------

/// THE zerocheck prover entry: proves `a·b ⊕ c = 0` over the padded cube and
/// ALSO returns the canonical `s_hat_v_c` produced by the fused two-bank
/// round-1 kernel
/// ([`univariate_skip_optimized::round1_shift_reduce_extract_c_packed_padded_with_s_hat_v`]),
/// which the downstream PCS open consumes to skip `fold_1b_rows` for the
/// c-claim.
pub fn prove_packed_padded_capture_s_hat_v_c<O>(
    a_packed: &[u8],
    b_packed: &[u8],
    c_packed: &[u8],
    m: usize,
    padding: &PaddingSpec,
    ps: &mut ProverState<O>,
) -> (ZerocheckClaim, Vec<F128>) {
    let (claim, captured) =
        prove_packed_padded_inner(a_packed, b_packed, c_packed, m, padding, true, ps);
    (claim, captured.expect("capture=true must produce s_hat_v_c"))
}

#[allow(clippy::too_many_arguments)]
fn prove_packed_padded_inner<O>(
    a_packed: &[u8],
    b_packed: &[u8],
    c_packed: &[u8],
    m: usize,
    padding: &PaddingSpec,
    capture_s_hat_v_c: bool,
    ps: &mut ProverState<O>,
) -> (ZerocheckClaim, Option<Vec<F128>>) {
    let k_skip = K_SKIP;
    assert!(
        m >= k_skip + N_INNER,
        "prove requires m >= k_skip + N_INNER (= {})",
        k_skip + N_INNER
    );
    let expected_bytes = (1usize << m) / 8;
    assert_eq!(a_packed.len(), expected_bytes);
    assert_eq!(b_packed.len(), expected_bytes);
    assert_eq!(c_packed.len(), expected_bytes);
    let n_mlv = m - k_skip;

    // ---- 1. Sample r (with protocol-fixed constants in the inner 7 dims) ----
    //
    // r layout:
    //   r[0..k_skip]                — sampled (used by verifier for the
    //                                  final check at S; not by the URM)
    //   r[k_skip..k_skip+3]         — protocol small-eq constants φ_8(0xF7..)
    //   r[k_skip+3..k_skip+7]       — protocol medium-eq constants β_i
    //   r[k_skip+7..m]              — sampled (the "outer" eq weights for
    //                                  the URM and multilinear rounds)
    let r = challenge_vector(m, |n| ps.sample_vec(n).into_iter().map(as_ghash).collect());

    // ---- 3. Round 1: URM (extract_c, parallel) ----
    //
    // The optimized URM drops a `C_s = φ_8(0x1C)` scalar from its accumulators
    // (a prover-side optimization tied to the small-eq trick — see the
    // C_s factor analysis in `univariate_skip_optimized`). The wire format
    // must be in "naive" convention so the verifier doesn't need to know
    // about this internal optimization; we restore the C_s factor here.
    let zc_timing = std::env::var_os("FLOCK_ZC_TIMING").is_some();
    let t_round1 = std::time::Instant::now();
    let ntt_s = AdditiveNttGf8::new(k_skip, F8::ZERO);
    let ntt_l = AdditiveNttGf8::new(k_skip, F8(1u8 << k_skip));
    let inv_table = InvNttTableByteSingleGf8::new(&ntt_s, &ntt_l);
    let (round1_ab_opt, round1_c_opt, s_hat_v_c) = if capture_s_hat_v_c {
        let (ab, c, s) =
            crate::zerocheck::univariate_skip_optimized::round1_shift_reduce_extract_c_packed_padded_with_s_hat_v(
                a_packed,
                b_packed,
                c_packed,
                m,
                k_skip,
                &r,
                &inv_table,
                padding,
            );
        (ab, c, Some(s))
    } else {
        let (ab, c) = round1_shift_reduce_extract_c_packed_padded(
            a_packed, b_packed, c_packed, m, k_skip, &r, &inv_table, padding,
        );
        (ab, c, None)
    };
    let c_s = c_s_f128();
    let round1_ab: Vec<F128> = round1_ab_opt.iter().map(|x| c_s * *x).collect();
    let round1_c: Vec<F128> = round1_c_opt.iter().map(|x| c_s * *x).collect();
    if zc_timing {
        eprintln!(
            "[zc-timing] round1 URM: {:.2} ms",
            t_round1.elapsed().as_secs_f64() * 1e3
        );
    }

    // ---- 4. Transmit + bind round-1 message on the stream, sample z ----
    for &x in round1_ab.iter() {
        ps.add_scalar(as_e(x));
    }
    for &x in round1_c.iter() {
        ps.add_scalar(as_e(x));
    }
    let z = as_ghash(ps.sample());

    // ---- 5. c_eval = ĉ(z, r_rest) via interpolation of round1_c at z ----
    //
    // round1_c (now in naive convention) carries `P^C(λ) = Σ_x eq(r_rest, x) · ĉ(λ, x)`
    // as its 2^k_skip evaluations on Λ. Interpolating to λ=z gives
    // `ĉ(z, r_rest)` directly (the eq-weighted sum collapses to the MLE
    // evaluation because ĉ is linear). This is **the c-claim** — at point
    // `(z, r_rest)`, *not* `(z, ρ-values)`. ~64 F128 muls + Lagrange weights.
    let final_c_eval = interpolate_at_z_on_lambda(&round1_c, k_skip, z);

    // ---- 6. Round 2: fused fold + first multilinear message ----
    //
    // Convention A wrapping: pass `mlv_arg[0] = ONE` so the function's output
    // `mlv_arg[0] · G(1)` becomes the bare `G(1)` we send on the wire. The
    // verifier samples ρ_1 after observing this message.
    let t_round2 = std::time::Instant::now();
    let fold_table = UniSkipFoldTable::new(k_skip, z);
    let mut mlv_arg = vec![F128::ONE; n_mlv];
    mlv_arg[1..].copy_from_slice(&r[k_skip + 1..]);
    let (mut a_mlv, mut b_mlv, msg_1, msg_inf) =
        uni_skip_fold_and_round_pair_optimized_packed_padded(
            a_packed,
            b_packed,
            m,
            k_skip,
            &fold_table,
            &mlv_arg,
            padding,
        );

    if zc_timing {
        eprintln!(
            "[zc-timing] round2 fused fold: {:.2} ms",
            t_round2.elapsed().as_secs_f64() * 1e3
        );
    }
    let t_tail = std::time::Instant::now();
    let mut multilinear_msgs = Vec::with_capacity(n_mlv);
    multilinear_msgs.push((msg_1, msg_inf));
    ps.add_scalar(as_e(msg_1));
    ps.add_scalar(as_e(msg_inf));
    let mut mlv_rhos: Vec<F128> = Vec::with_capacity(n_mlv);
    mlv_rhos.push(as_ghash(ps.sample()));

    // ---- 7. Rounds 3..(n_mlv + 1) — AB only (c is done) ----
    //
    // Iter i: fold (a, b) at ρ_{i+1}, compute round (i+3) message, sample
    // ρ_{i+2}. Use the fused parallel path while log_n ≥ 10; below that the
    // SplitEqGhash inner can't form lo_size ≥ 2, so we fall back to
    // fold_in_place_pair + round_pair_naive.
    //
    // Ping-pong scratch buffers for the fused path: each fused round folds
    // (a_mlv, b_mlv) of size N into size N/2. Rather than allocating — and,
    // worse, `munmap`-ing, which is single-threaded and caps the tail's
    // parallel speedup — a fresh 64 MB buffer per round, we alternate between
    // two persistent buffers. Scratch capacity = N/2 (the largest fused
    // output); only needed when the first round is actually fused.
    let n_in = a_mlv.len();
    let (mut a_nxt, mut b_nxt) = if n_in >= 1024 {
        (
            primitives::scratch::take_f128(n_in / 2),
            primitives::scratch::take_f128(n_in / 2),
        )
    } else {
        (Vec::new(), Vec::new())
    };

    for i in 0..(n_mlv - 1) {
        let rho_prev = mlv_rhos[i];
        let log_n_before = a_mlv.len().trailing_zeros() as usize;

        // r_next for the next round's message: length log_n_before - 1.
        // r_next[0] = ONE (Convention A factor); r_next[1..] are the eq
        // weights for the remaining variables = r[k_skip + i + 2..m].
        let mut r_next = vec![F128::ONE; log_n_before - 1];
        r_next[1..].copy_from_slice(&r[k_skip + i + 2..]);

        let (m1, mi) = if log_n_before >= 10 {
            let half = a_mlv.len() / 2;
            let (m1, mi) = fold_and_compute_round_pair_into(
                &a_mlv,
                &b_mlv,
                &mut a_nxt[..half],
                &mut b_nxt[..half],
                rho_prev,
                &r_next,
            );
            // Swap current <-> scratch, then shrink the new current to the
            // folded size. The old (larger) buffer becomes scratch; we only
            // ever write its leading `half` slots next round, so its stale
            // length is harmless.
            std::mem::swap(&mut a_mlv, &mut a_nxt);
            std::mem::swap(&mut b_mlv, &mut b_nxt);
            a_mlv.truncate(half);
            b_mlv.truncate(half);
            (m1, mi)
        } else {
            fold_in_place_pair(&mut a_mlv, &mut b_mlv, rho_prev);
            round_pair_naive(&a_mlv, &b_mlv, &r_next)
        };

        multilinear_msgs.push((m1, mi));
        ps.add_scalar(as_e(m1));
        ps.add_scalar(as_e(mi));
        mlv_rhos.push(as_ghash(ps.sample()));
    }

    // ---- 8. Final binding at ρ_{n_mlv} (the last challenge) ----
    let rho_last = *mlv_rhos.last().expect("at least one ρ sampled");
    fold_in_place_pair(&mut a_mlv, &mut b_mlv, rho_last);
    debug_assert_eq!(a_mlv.len(), 1);
    debug_assert_eq!(b_mlv.len(), 1);

    let final_a_eval = a_mlv[0];
    let final_b_eval = b_mlv[0];

    // ---- Fiat–Shamir: bind the final â, b̂ claims into the transcript ----
    //
    // These two claims are reduced downstream by lincheck via a *single*
    // random-linear-combination check with coefficient α (`target = α·v_a + v_b`,
    // see `lincheck`). That batching is only sound if α is sampled *after*
    // (v_a, v_b) are committed to the transcript — otherwise a prover that knows
    // α can pick (v_a, v_b) to satisfy the one batched equation while violating
    // the individual checks. So observe them here, before any later challenge
    // (the next one drawn is lincheck's α). `final_c_eval` is NOT transmitted —
    // the verifier recomputes it from the already-absorbed `round1_c`/`z`, so it
    // is already transcript-bound and carrying it would be redundant transport.
    ps.add_scalar(as_e(final_a_eval));
    ps.add_scalar(as_e(final_b_eval));

    // Recycle the four tail buffers (the two len-1 survivors still own their
    // full round-2 capacity) for the next phase/prove.
    primitives::scratch::give_f128(a_mlv);
    primitives::scratch::give_f128(b_mlv);
    primitives::scratch::give_f128(a_nxt);
    primitives::scratch::give_f128(b_nxt);

    if zc_timing {
        eprintln!(
            "[zc-timing] rounds 3+ tail: {:.2} ms",
            t_tail.elapsed().as_secs_f64() * 1e3
        );
    }

    let r_rest: Vec<F128> = r[k_skip..].to_vec();

    let claim = ZerocheckClaim {
        z,
        mlv_challenges: mlv_rhos,
        r_rest,
        a_eval: final_a_eval,
        b_eval: final_b_eval,
        c_eval: final_c_eval,
    };
    (claim, s_hat_v_c)
}

/// Verify a zerocheck proof for an instance over `{0,1}^log_n`.
///
/// Walks the sponge in lockstep with the prover, samples the same
/// challenges, and checks every round's consistency equation.
///
/// On accept: returns the [`ZerocheckClaim`] the caller must check against
/// its PCS opening of `â`, `b̂`, `ĉ`.
/// On reject: returns a [`VerifyError`] indicating which check failed.
pub fn verify<O>(
    log_n: usize,
    vs: &mut VerifierState<'_, O>,
) -> Result<ZerocheckClaim, VerifyError> {
    let m = log_n;
    let k_skip = K_SKIP;

    if m < k_skip + N_INNER {
        return Err(VerifyError::LogNTooSmall { log_n: m, k_skip });
    }
    let n_mlv = m - k_skip;
    let ell = 1usize << k_skip;

    // ---- Re-derive r (in lockstep with prove_packed) ----
    let r = challenge_vector(m, |n| vs.sample_vec(n).into_iter().map(as_ghash).collect());

    // ---- Read + bind round-1 messages off the stream, sample z ----
    let round1_ab = vs.next_scalars(ell).map_err(VerifyError::Transcript)?.into_iter().map(as_ghash).collect::<Vec<_>>();
    let round1_c = vs.next_scalars(ell).map_err(VerifyError::Transcript)?.into_iter().map(as_ghash).collect::<Vec<_>>();
    let z = as_ghash(vs.sample());

    // ---- Reconstruct ĉ(z, r_rest) from round1_c ----
    //
    // P^C has degree < 2^k_skip in λ (C is linear, summed against eq); ell
    // evaluations on Λ uniquely interpolate to z. round1_c is in naive
    // convention (the prover restored the C_s factor before sending), so
    // `ĉ(z, r_rest) = P^C(z)` directly.
    let final_c_eval = interpolate_at_z_on_lambda(&round1_c, k_skip, z);

    // ---- Reconstruct the initial AB running claim ----
    //
    // P^{AB}(z) requires the polynomial in λ of degree < 2·ell to be evaluated
    // at z. The prover sent only ell evaluations on Λ — not enough on its own.
    // The verifier uses the **zerocheck assumption** `P^{AB}(λ) + P^C(λ) = 0`
    // for `λ ∈ S`. Together with the ell Λ-evaluations of the combined
    // polynomial, that's 2·ell evaluations — enough to interpolate the
    // combined polynomial at z. Then `P^{AB}(z) = P^{combined}(z) − P^C(z)`,
    // which in char-2 is `P^{combined}(z) + P^C(z)`.
    //
    // If the prover's witness is dishonest the S-zero assumption fails, the
    // reconstructed c_0 is wrong, and the running-claim chain ends at a value
    // inconsistent with `â · b̂`. We catch that at the final sumcheck check.
    let combined_at_lambda: Vec<F128> = round1_ab
        .iter()
        .zip(&round1_c)
        .map(|(x, y)| *x + *y)
        .collect();
    let combined_at_z = interpolate_at_z_combined(&combined_at_lambda, k_skip, z);
    let p_c_at_z = interpolate_at_z_on_lambda(&round1_c, k_skip, z);
    let mut c_running = combined_at_z + p_c_at_z;

    // ---- Multilinear sumcheck chain ----
    //
    // The propagated running claim is the *inner* polynomial value G(ρ),
    // not the full per-round polynomial P(ρ) = eq(r_eq, ρ) · G(ρ). The eq
    // factor for the just-bound variable is absorbed by the next round's
    // consistency check via the identity
    //   G_{r-1}(ρ_{r-1}) = (1 + r_eq_r) · G_r(0) + r_eq_r · G_r(1).
    //
    // Round r (0-indexed i = r − 2) binds the i-th rest variable with eq weight
    // r[k_skip + i]. The prover sends `(G(1), G(∞))` (Convention A — no
    // factor). Verifier:
    //   1. reconstruct G(0) from consistency `c_running = (1+r_eq)·G(0) + r_eq·G(1)`,
    //   2. observe message, sample ρ_i,
    //   3. update `c_running ← G(ρ_i)`,
    //      where `G(X) = G(0)·(1+X) + G(1)·X + G(∞)·X·(X+1)` (char-2 quadratic
    //      interpolation through G(0), G(1), G(∞)).
    let mut mlv_rhos: Vec<F128> = Vec::with_capacity(n_mlv);
    let mut multilinear_rounds: Vec<(F128, F128)> = Vec::with_capacity(n_mlv);
    for i in 0..n_mlv {
        let msg_1 = as_ghash(vs.next_scalar().map_err(VerifyError::Transcript)?);
        let msg_inf = as_ghash(vs.next_scalar().map_err(VerifyError::Transcript)?);
        multilinear_rounds.push((msg_1, msg_inf));
        let r_eq = r[k_skip + i];
        let one_plus_r_eq = F128::ONE + r_eq;

        let g1 = msg_1;
        let g_inf = msg_inf;
        let g0 = (c_running + r_eq * g1) * one_plus_r_eq.inv();

        let rho = as_ghash(vs.sample());
        mlv_rhos.push(rho);

        let one_plus_rho = F128::ONE + rho;
        // G(ρ) = G(0)·(1+ρ) + G(1)·ρ + G(∞)·ρ·(1+ρ).
        c_running = g0 * one_plus_rho + g1 * rho + g_inf * rho * one_plus_rho;
    }

    // ---- AB sumcheck final consistency ----
    //
    // After all variables are bound, the inner running claim is just the
    // polynomial without the eq weighting:
    //   G_final(ρ_all) = â(z, ρ) · b̂(z, ρ) = final_a_eval · final_b_eval.
    // (The eq factors were absorbed round-by-round into the consistency checks,
    // never accumulating into the running claim.)
    // Read + bind the final â, b̂ claims off the stream (mirrors
    // `prove_packed_padded_inner`): binding must land before the next challenge
    // (lincheck's α) is drawn, so the α-batched reduction of these two claims is
    // sound. `final_c_eval` is the verifier's OWN interpolation of the
    // already-bound `round1_c` at `z` — never transported.
    let r_rest: Vec<F128> = r[k_skip..].to_vec();
    let final_a_eval = as_ghash(vs.next_scalar().map_err(VerifyError::Transcript)?);
    let final_b_eval = as_ghash(vs.next_scalar().map_err(VerifyError::Transcript)?);
    if c_running != final_a_eval * final_b_eval {
        return Err(VerifyError::SumcheckFinalFailed);
    }

    Ok(ZerocheckClaim {
        z,
        mlv_challenges: mlv_rhos,
        r_rest,
        a_eval: final_a_eval,
        b_eval: final_b_eval,
        c_eval: final_c_eval,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_rng::Rng;

    /// Test shim for the old dense-prove entry: the capture variant with the
    /// captured `s_hat_v_c` discarded.
    fn prove_packed(
        a_packed: &[u8],
        b_packed: &[u8],
        c_packed: &[u8],
        m: usize,
        ps: &mut pcs::ProverState,
    ) -> ZerocheckClaim {
        let (claim, _) = prove_packed_padded_capture_s_hat_v_c(
            a_packed,
            b_packed,
            c_packed,
            m,
            &PaddingSpec::dense(m),
            ps,
        );
        claim
    }

    /// Pack three Boolean vectors into the (a_packed, b_packed, c_packed)
    /// shape that `prove_packed` consumes.
    fn pack_abc(a: &[bool], b: &[bool], c: &[bool]) -> (Vec<u8>, Vec<u8>, Vec<u8>) {
        use univariate_skip::pack_bits;
        (pack_bits(a), pack_bits(b), pack_bits(c))
    }

    /// `prove` runs end-to-end at the smallest valid m (= k_skip + N_INNER = 13)
    /// without panicking, and produces output of the right shape.
    ///
    /// structural sanity here catches:
    ///   - mismatched sponge observe/sample sequence
    ///   - wrong slice lengths in r / mlv_arg / r_next at any round
    ///   - any unreachable assert in the underlying functions
    #[test]
    fn prove_runs_end_to_end() {
        for &m in &[13usize, 14, 15, 16] {
            let mut rng = Rng::new(m as u64);
            let a = rng.bits(1 << m);
            let b = rng.bits(1 << m);
            // Honest witness: c = a AND b, so a·b ⊕ c = 0 on the hypercube.
            let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();

            let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
            let mut sponge = pcs::ProverState::new(b"flock-test-v0", &[]);
            let claim = prove_packed(&a_p, &b_p, &c_p, m, &mut sponge);

            // Shape checks: the streamed proof is round1_ab ‖ round1_c ‖
            // (m − K_SKIP) message pairs ‖ (final_a, final_b).
            let stream = sponge.into_proof().stream;
            assert_eq!(stream.len(), 2 * (1 << K_SKIP) + 2 * (m - K_SKIP) + 2, "m={m}");
            assert_eq!(claim.mlv_challenges.len(), m - K_SKIP, "m={m}");

            // Claim's eval fields agree with the streamed final evals.
            assert_eq!(claim.a_eval, as_ghash(stream[stream.len() - 2]), "m={m}");
            assert_eq!(claim.b_eval, as_ghash(stream[stream.len() - 1]), "m={m}");
        }
    }

    /// **Prove→verify roundtrip**: an honest proof verifies cleanly, and the
    /// claim returned by `verify` is byte-for-byte equal to the claim returned
    /// by `prove`.
    #[test]
    fn prove_verify_roundtrip_honest() {
        for &m in &[13usize, 14, 15, 16] {
            let mut rng = Rng::new(1000 + m as u64);
            let a = rng.bits(1 << m);
            let b = rng.bits(1 << m);
            let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();

            let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
            let mut ch_prove = pcs::ProverState::new(b"flock-test-v0", &[]);
            let claim_p = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);

            let proof_t = ch_prove.into_proof();
            let mut ch_verify = pcs::VerifierState::new(b"flock-test-v0", &proof_t, &[]);
            let result = verify(m, &mut ch_verify);
            let claim_v = result.unwrap_or_else(|e| panic!("verify rejected at m={m}: {e:?}"));

            assert_eq!(claim_p, claim_v, "claim mismatch at m={m}");
        }
    }

    /// **Verify rejects byte-mutated proofs.** Walk each component of the
    /// proof and flip one F128 entry; the verifier must return an `Err`
    /// (rather than panicking or silently accepting).
    #[test]
    fn verify_rejects_mutations() {
        let m = 14;
        let mut rng = Rng::new(5050);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();

        let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
        let mut ch_prove = pcs::ProverState::new(b"flock-test-v0", &[]);
        let _ = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);
        let proof_t = ch_prove.into_proof();

        // Stream layout: round1_ab (64) ‖ round1_c (64) ‖ (m−6)×(e1, einf) ‖
        // final_a ‖ final_b. Flip one word per region; verify must reject.
        let ell = 1usize << K_SKIP;
        let n_mlv = m - K_SKIP;
        let mutations: [(&str, usize); 6] = [
            ("round1_ab[0]", 0),
            ("round1_c[5]", ell + 5),
            ("multilinear_rounds[0].0", 2 * ell),
            ("multilinear_rounds[mid].1", 2 * ell + 2 * (n_mlv / 2) + 1),
            ("final_a_eval", 2 * ell + 2 * n_mlv),
            ("final_b_eval", 2 * ell + 2 * n_mlv + 1),
        ];
        for (label, word) in mutations {
            let mut bad = proof_t.clone();
            bad.stream[word].c0 ^= 1;
            let mut ch = pcs::VerifierState::new(b"flock-test-v0", &bad, &[]);
            let result = verify(m, &mut ch);
            assert!(
                result.is_err(),
                "verify accepted mutated proof ({label}) — should have rejected"
            );
        }
    }

    /// Shape rejections: a truncated stream and a too-small instance.
    #[test]
    fn verify_rejects_shape_errors() {
        let m = 14;
        let mut rng = Rng::new(606);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
        let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
        let mut ch_prove = pcs::ProverState::new(b"flock-test-v0", &[]);
        let _ = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);
        let proof_t = ch_prove.into_proof();

        // Truncated stream: a clean Transcript error, not a panic.
        let mut bad = proof_t.clone();
        bad.stream.truncate(bad.stream.len() - 3);
        let mut ch = pcs::VerifierState::new(b"flock-test-v0", &bad, &[]);
        assert!(matches!(
            verify(m, &mut ch),
            Err(VerifyError::Transcript(_))
        ));

        // log_n too small.
        let mut ch = pcs::VerifierState::new(b"flock-test-v0", &proof_t, &[]);
        assert!(matches!(
            verify(K_SKIP + 6, &mut ch),
            Err(VerifyError::LogNTooSmall { .. })
        ));
    }

    /// AUDIT: a FALSE statement (c ≠ a·b at some hypercube point) must be
    /// rejected, even though the prover follows the honest algorithm on its
    /// (dishonest) witness.
    #[test]
    fn audit_false_statement_rejected() {
        for &m in &[13usize, 14, 15] {
            let mut rng = Rng::new(7777 + m as u64);
            let a = rng.bits(1 << m);
            let b = rng.bits(1 << m);
            // Correct c, then corrupt ONE bit so a·b ⊕ c ≠ 0 somewhere.
            let mut c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
            c[3] = !c[3];

            let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
            let mut ch_prove = pcs::ProverState::new(b"flock-test-v0", &[]);
            let _ = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);
            let proof_t = ch_prove.into_proof();

            let mut ch_verify = pcs::VerifierState::new(b"flock-test-v0", &proof_t, &[]);
            let res = verify(m, &mut ch_verify);
            assert!(
                res.is_err(),
                "verify ACCEPTED a false statement at m={m}: {res:?}"
            );
        }
    }

    /// AUDIT: flipping any round's `msg_inf` (the degree-2 / ∞ coefficient)
    /// must be rejected. `msg_inf` is observed into the transcript, so the
    /// tamper both reshuffles subsequent ρ challenges and breaks the
    /// running-claim chain — either way the final check fails.
    #[test]
    fn audit_round_msg_inf_tamper_rejected() {
        let m = 14;
        let mut rng = Rng::new(424242);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
        let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
        let mut ch_prove = pcs::ProverState::new(b"flock-test-v0", &[]);
        let _ = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);
        let proof_t = ch_prove.into_proof();

        // For each round, flip msg_inf (stream word 2·64 + 2·idx + 1). Because
        // the word is bound at read, this reshuffles subsequent rho's; a sound
        // verifier should reject (overwhelming probability).
        for idx in 0..(m - K_SKIP) {
            let mut bad = proof_t.clone();
            bad.stream[2 * (1 << K_SKIP) + 2 * idx + 1] += as_e(F128::ONE);
            let mut ch = pcs::VerifierState::new(b"flock-test-v0", &bad, &[]);
            let res = verify(m, &mut ch);
            assert!(res.is_err(), "msg_inf tamper at round {idx} ACCEPTED");
        }
    }

    /// AUDIT: the LAST round's `msg_inf` must be constrained — a common
    /// off-by-one is to leave the final round's leading coefficient unchecked.
    /// Kept separate from the all-rounds loop above so a regression here points
    /// straight at the final-round binding.
    #[test]
    fn audit_last_round_inf_constrained() {
        let m = 13;
        let mut rng = Rng::new(98765);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
        let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
        let mut ch_prove = pcs::ProverState::new(b"flock-test-v0", &[]);
        let _ = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);
        let proof_t = ch_prove.into_proof();

        let last = m - K_SKIP - 1;
        let mut bad = proof_t.clone();
        bad.stream[2 * (1 << K_SKIP) + 2 * last + 1] += as_e(F128::ONE);
        let mut ch = pcs::VerifierState::new(b"flock-test-v0", &bad, &[]);
        assert!(
            verify(m, &mut ch).is_err(),
            "last-round msg_inf unconstrained"
        );
    }

    /// AUDIT (Fiat–Shamir binding of the final â, b̂ claims). Regression test
    /// for the gap where `final_a_eval`/`final_b_eval` were not observed into
    /// the transcript.
    ///
    /// Downstream, lincheck reduces these two claims via a *single* random-
    /// linear-combination check (`target = α·v_a + v_b`). That batching is only
    /// sound if α is sampled *after* the claims are bound to the transcript —
    /// otherwise a prover that already knows α can pick (v_a, v_b) to satisfy
    /// the one batched equation while violating the individual ties.
    ///
    /// A *product-preserving* tamper `(â, b̂) → (â·t, b̂·t⁻¹)` leaves the
    /// zerocheck's own final check `c_running == â·b̂` satisfied, so `verify`
    /// still returns `Ok` — the zerocheck alone is blind to it. The defense is
    /// that both claims are now observed last in the transcript, so the next
    /// challenge (the slot lincheck draws α from) must diverge from the honest
    /// run. This assertion FAILS before the observe was added (identical
    /// post-state) and passes now.
    #[test]
    fn audit_final_ab_claims_bound_to_transcript() {
        let m = 14;
        let mut rng = Rng::new(0xF1A7_5A11);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
        let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);

        let mut ch_prove = pcs::ProverState::new(b"flock-test-v0", &[]);
        let claim_p = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);
        let proof_t = ch_prove.into_proof();

        // Honest verify, then capture the next challenge the transcript feeds
        // downstream — this is exactly the slot lincheck samples α from.
        let mut ch_honest = pcs::VerifierState::new(b"flock-test-v0", &proof_t, &[]);
        assert!(
            verify(m, &mut ch_honest).is_ok(),
            "honest verify rejected"
        );
        let alpha_honest = ch_honest.sample();

        // Product-preserving tamper: â' = â·t, b̂' = b̂·t⁻¹ ⇒ â'·b̂' = â·b̂, so the
        // zerocheck's `c_running == â·b̂` check still holds for the tampered pair.
        let t = F128 {
            lo: 0x0123_4567_89ab_cdef,
            hi: 0xfedc_ba98_7654_3210,
        };
        assert!(t != F128::ZERO && t != F128::ONE, "t must be nontrivial");
        // The finals are the LAST two stream words of this standalone proof.
        let n = proof_t.stream.len();
        let mut bad = proof_t.clone();
        bad.stream[n - 2] = as_e(as_ghash(bad.stream[n - 2]) * t);
        bad.stream[n - 1] = as_e(as_ghash(bad.stream[n - 1]) * t.inv());
        assert_ne!(bad.stream[n - 2], proof_t.stream[n - 2], "tamper must change â");
        assert_ne!(bad.stream[n - 1], proof_t.stream[n - 1], "tamper must change b̂");
        assert_eq!(
            as_ghash(bad.stream[n - 2]) * as_ghash(bad.stream[n - 1]),
            claim_p.a_eval * claim_p.b_eval,
            "tamper must preserve the product",
        );

        // The zerocheck's own checks are blind to a product-preserving tamper:
        // verify still ACCEPTS. This is precisely the gap the FS binding closes —
        // the tamper is caught only because the claims move the transcript.
        let mut ch_tampered = pcs::VerifierState::new(b"flock-test-v0", &bad, &[]);
        assert!(
            verify(m, &mut ch_tampered).is_ok(),
            "product-preserving tamper rejected by zerocheck's own checks (unexpected)",
        );
        let alpha_tampered = ch_tampered.sample();

        // The fix: observing â, b̂ makes the downstream challenge depend on them,
        // so lincheck's α (and everything after) diverges and rejects the
        // tampered pair. Before the fix these challenges were equal.
        assert_ne!(
            alpha_honest, alpha_tampered,
            "final â/b̂ claims are NOT bound into the transcript: a product-preserving \
             tamper leaves the downstream challenge unchanged, breaking lincheck's \
             α-batched reduction of (v_a, v_b)",
        );
    }

    /// AUDIT: many random false witnesses must all be rejected. Stronger than a
    /// single corruption — exercises the full prove→verify path on statements
    /// that are false at varying numbers of hypercube points.
    #[test]
    fn audit_many_false_statements_rejected() {
        let m = 13;
        for seed in 0..20u64 {
            let mut rng = Rng::new(0xBADC0DE ^ seed);
            let a = rng.bits(1 << m);
            let b = rng.bits(1 << m);
            let mut c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
            // Flip a random number of bits (1..=4).
            let nflip = 1 + (rng.next_u64() as usize % 4);
            for _ in 0..nflip {
                let idx = rng.next_u64() as usize % c.len();
                c[idx] = !c[idx];
            }
            let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
            let mut ch_prove = pcs::ProverState::new(b"flock-test-v0", &[]);
            let _ = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);
            let proof_t = ch_prove.into_proof();
            let mut ch_verify = pcs::VerifierState::new(b"flock-test-v0", &proof_t, &[]);
            let res = verify(m, &mut ch_verify);
            assert!(
                res.is_err(),
                "false statement (seed={seed}) ACCEPTED: {res:?}"
            );
        }
    }

    /// AUDIT: tamper msg_1 in each round; must reject.
    #[test]
    fn audit_round_msg_1_tamper_rejected() {
        let m = 14;
        let mut rng = Rng::new(31415);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();
        let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
        let mut ch_prove = pcs::ProverState::new(b"flock-test-v0", &[]);
        let _ = prove_packed(&a_p, &b_p, &c_p, m, &mut ch_prove);
        let proof_t = ch_prove.into_proof();
        for idx in 0..(m - K_SKIP) {
            let mut bad = proof_t.clone();
            bad.stream[2 * (1 << K_SKIP) + 2 * idx] += as_e(F128::ONE);
            let mut ch = pcs::VerifierState::new(b"flock-test-v0", &bad, &[]);
            assert!(
                verify(m, &mut ch).is_err(),
                "msg_1 tamper round {idx} ACCEPTED"
            );
        }
    }

    /// Determinism: same witness + same sponge seed → same proof.
    #[test]
    fn prove_deterministic() {
        let m = 14;
        let mut rng = Rng::new(99);
        let a = rng.bits(1 << m);
        let b = rng.bits(1 << m);
        let c: Vec<bool> = a.iter().zip(&b).map(|(x, y)| *x & *y).collect();

        let (a_p, b_p, c_p) = pack_abc(&a, &b, &c);
        let mut ch1 = pcs::ProverState::new(b"flock-test-v0", &[]);
        let mut ch2 = pcs::ProverState::new(b"flock-test-v0", &[]);
        let claim1 = prove_packed(&a_p, &b_p, &c_p, m, &mut ch1);
        let claim2 = prove_packed(&a_p, &b_p, &c_p, m, &mut ch2);

        assert_eq!(ch1.into_proof().stream, ch2.into_proof().stream);
        assert_eq!(claim1.z, claim2.z);
        assert_eq!(claim1.mlv_challenges, claim2.mlv_challenges);
    }
}
