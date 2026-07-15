// Credit: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Stacked batch-mixed opening for the K-committed PCS (64-bit transition).
//!
//! The committed witness is a stack of `2^log_n` [`F64`] words (committed via
//! [`super::ligerito_k::commit_k`]), and one Ligerito-K run discharges
//!
//! - **point claims** ([`StackClaimK`]): plain multilinear evaluations of
//!   aligned sub-slices of the stack (a `Point` claim's weight is
//!   `eq(low_point, .)` supported on `[offset, offset + 2^|low_point|)`; a
//!   `Strided` claim freezes the low `stride_log` in-block coords to `slot`'s
//!   bits, so its weight is nonzero only at `offset + slot + j * 2^stride_log`),
//! - **ring-switched claims** ([`RingSwitchOpenK`]): bit-MLE evaluation claims
//!   on the packed sub-block `q_pkd = stack[offset .. offset + 2^qpkd_vars]`,
//!   reduced per claim by [`super::ring_switch_k::prove`] to an inner-product
//!   claim `<q_pkd, rs_eq_ind> = sumcheck_claim` against the transparent
//!   E-valued weight `rs_eq_ind`.
//!
//! All claims are gamma-folded into ONE combined weight `b_stack` over the
//! whole stack plus one `target`, then proved by
//! [`super::ligerito_k::recursive_prover_with_basis_k`]. The verifier replays
//! the ring-switch reductions succinctly ([`super::ring_switch_k::verify_succinct`],
//! no dense `rs_eq_ind`) and drives
//! [`super::ligerito_k::recursive_verifier_with_basis_succinct_k`] with a
//! residual evaluator that reconstructs `MLE(b_stack)` at each residual point
//! in closed form: eq / stride-selector products for the point claims, and the
//! DP24 tensor-algebra prefix + binary-suffix finish
//! ([`super::ring_switch_k::eval_rs_eq_prefix_k`] /
//! [`super::ring_switch_k::eval_rs_eq_finish_from_prefix_binary_q_k`]) for the
//! ring-switched part.
//!
//! ## Transcript order (identical on both sides)
//!
//! label -> per ring-switched claim ([`super::ring_switch_k`]'s own label +
//! `s_hat_v_i` observed + `r''_i` sampled) -> gamma_rs (one per claim) ->
//! per point claim (label + value observed) -> gamma_pd (one per claim) ->
//! Ligerito-K, with domain-separated labels for every phase.
//!
//! ## The combined weight
//!
//! With `sel = offset >> qpkd_vars` the selector coords of the q_pkd slice,
//! the lifted weight at a full-stack point `x = (x_lo, x_hi)` (split at
//! `qpkd_vars`, LSB-first) is
//!
//! ```text
//! b(x) = eq(sel, x_hi) * sum_i gamma_rs_i * MLE(rs_eq_ind_i)(x_lo)
//!      + sum_j gamma_pd_j * eq(claim_j, x)
//! ```
//!
//! which is exactly what the dense `b_stack` scatter produces (each claim's
//! weight lives on its aligned slice, so scattering the low-dimensional eq /
//! rs_eq_ind tensor at the slice offset IS multiplying by the boolean
//! selector eq).

use fiat_shamir::Sponge;
use primitives::field::{F64, F128T};
use crate::merkle::Hash;
use serde::{Deserialize, Serialize};

use super::ligerito::{ProverConfig, VerifierConfig};
use super::ligerito_k::{
    LigeritoProofK, ProverDataK, build_eq_table_ext, build_eq_table_ext_seeded_into,
    recursive_prover_with_basis_k, recursive_verifier_with_basis_succinct_k_with_squeezes,
};
use super::pack_k::PACKING_WIDTH_K;
use super::ring_switch_k::{
    self, RingSwitchProofK, eval_rs_eq_finish_from_prefix_binary_q_k, eval_rs_eq_prefix_k,
};
use super::tensor_algebra_k::TensorAlgebraE;

// ---------------------------------------------------------------------------
// Sponge helpers (same convention as ligerito_k): E-scalars straight off
// the shared Fiat-Shamir sponge.
// sponge scalars ARE E-elements; the helpers keep call sites uniform; every
// 16-byte pattern is a valid F128T, so sampling reinterprets bytes and
// observing ferries the two tower lanes through the transcript.
// ---------------------------------------------------------------------------

fn sample_ext_vec(sponge: &mut Sponge, n: usize) -> Vec<F128T> {
    sponge.sample_vec(n)
}

#[inline]
fn observe_ext(sponge: &mut Sponge, e: F128T) {
    sponge.observe(e);
}

/// Multilinear eq at two E-points (char 2: each factor is `1 + r_i + x_i`).
/// Mirror of `zerocheck::multilinear::eq_eval` retyped to the tower.
fn eq_eval_ext(r: &[F128T], x: &[F128T]) -> F128T {
    assert_eq!(r.len(), x.len());
    let mut acc = F128T::ONE;
    for (&a, &b) in r.iter().zip(x.iter()) {
        acc *= F128T::ONE + a + b;
    }
    acc
}

// ---------------------------------------------------------------------------
// Claim types
// ---------------------------------------------------------------------------

/// A point claim folded into the stacked mixed opening. K analog of the extension-field
/// [`super::StackClaim`] (owning variant, mirroring the main crate's
/// `SlotClaim` shape).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StackClaimK {
    /// `eq(low_point, .)` on the aligned slice
    /// `[offset, offset + 2^|low_point|)`; `offset` must be a multiple of
    /// `2^|low_point|`.
    Point {
        offset: usize,
        low_point: Vec<F128T>,
        value: F128T,
    },
    /// A boolean-selector claim on a packed column: the low `stride_log`
    /// in-block coords are frozen to `slot`'s bits (so the weight is nonzero
    /// only at `offset + slot + j * 2^stride_log`) and `point` is the high
    /// part. Equivalent to a `Point` with `low_point = slot_bits ++ point`,
    /// folded in `O(2^|point|)` instead of `O(2^(stride_log + |point|))`.
    /// `offset` must be a multiple of `2^(stride_log + |point|)` and
    /// `slot < 2^stride_log`.
    Strided {
        offset: usize,
        slot: usize,
        stride_log: usize,
        point: Vec<F128T>,
        value: F128T,
    },
}

impl StackClaimK {
    #[inline]
    pub fn value(&self) -> F128T {
        match self {
            StackClaimK::Point { value, .. } | StackClaimK::Strided { value, .. } => *value,
        }
    }
}

/// One ring-switched evaluation claim on the q_pkd sub-block: the consumed
/// claim is `value == sum_i prefix_weights[i] * s_hat_v[i]` where `s_hat_v`
/// are the 64 bit-slice MLEs of q_pkd at `suffix_point` (see
/// [`super::ring_switch_k`]). `prefix_weights` has [`PACKING_WIDTH_K`] = 64
/// entries ([`super::ring_switch_k::eq_prefix_weights`] for a plain point
/// claim; phi_8 Lagrange weights for flock's
/// univariate-skip claim); `suffix_point` has `qpkd_vars` coords.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingSwitchClaimK {
    pub prefix_weights: Vec<F128T>,
    pub suffix_point: Vec<F128T>,
    pub value: F128T,
    /// Prover-side optional precomputed `s_hat_v` (the 64 bit-slice MLE
    /// values at `suffix_point`, e.g. captured inside flock's reduction).
    /// When present, [`super::ring_switch_k::prove`] skips its
    /// `fold_1b_rows` recomputation; the values are checked against the
    /// claim (`claim_check`) and the transcript is identical either way.
    /// Verifier-side bundles leave it `None`.
    pub s_hat_v: Option<Vec<F128T>>,
}

/// Prover-side bundle of the ring-switched claims discharged in the same
/// stacked opening as the [`StackClaimK`]s. K analog of the main crate's
/// `RingSwitchOpen`; each claim may carry its precomputed `s_hat_v`.
#[derive(Clone, Debug)]
pub struct RingSwitchOpenK {
    /// q_pkd's offset inside the committed stack; must be a multiple of
    /// `2^qpkd_vars` (an aligned slice).
    pub offset: usize,
    /// log2 of q_pkd's length in F64 words; the opener slices
    /// `q_pkd = stack[offset .. offset + 2^qpkd_vars]` (no separate copy).
    pub qpkd_vars: usize,
    pub claims: Vec<RingSwitchClaimK>,
}

/// Verifier counterpart of [`RingSwitchOpenK`]: identical statement data
/// (the proof travels separately as [`BatchOpeningProofK`]).
#[derive(Clone, Debug)]
pub struct RingSwitchVerifyK {
    /// q_pkd's offset inside the committed stack.
    pub offset: usize,
    /// log2 of q_pkd's length in F64 words.
    pub qpkd_vars: usize,
    pub claims: Vec<RingSwitchClaimK>,
}

/// Batched stacked opening proof: one ring-switch message per ring-switched
/// claim plus ONE Ligerito-K proof over the combined claim. K analog of
/// [`super::BatchOpeningProofLigerito`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BatchOpeningProofK {
    pub ring_switches: Vec<RingSwitchProofK>,
    pub ligerito: LigeritoProofK,
}

/// What the K stacked-opening verifier hands back on accept — the recursion
/// harness's hook for the Ligerito fold/query data (mirror of the extension-field
/// `StackedOpeningSummary`). The K verifier does not yet surface its query
/// squeezes (the sampler rejection-samples and discards the raw words);
/// porting the recursion guest to the 64-bit field fills this in.
#[derive(Clone, Debug, Default)]
pub struct StackedOpeningSummaryK {
    pub lig: LigVerifierSummaryK,
}

/// See [`StackedOpeningSummaryK`].
#[derive(Clone, Debug, Default)]
pub struct LigVerifierSummaryK {
    /// The raw query-sampling squeezes, per level in transcript order.
    /// EMPTY until the K verifier surfaces them (recursion-guest port).
    pub query_squeezes: Vec<Vec<F128T>>,
}

// ---------------------------------------------------------------------------
// Shared claim folding / evaluation
// ---------------------------------------------------------------------------

/// Fold the gamma-weighted point claims into the stack weight `b_stack` and
/// running `target` (pure: the caller has already observed the claim values
/// and sampled `gammas` in transcript order). Mirror of the extension-field
/// `fold_stacked_point_claims`: a `Point` builds eq over ONLY its aligned
/// slice, a `Strided` scatters the eq of its high coords at the slot's
/// stride. Both scatter with `+=`, so overlapping slices accumulate
/// correctly; the OUTER loop therefore stays serial (several bus claims can
/// land on one column region), and parallelism lives inside each claim: the
/// gamma-seeded eq build ([`build_eq_table_ext_seeded_into`], parallel above
/// its level floor, into one scratch buffer reused across claims) and the
/// slice add. Small slices stay fully serial (with many tiny point claims,
/// rayon dispatch would cost more than the fold itself). The gamma seeding
/// and the serial/parallel splits are exact-field/order-preserving, so
/// `b_stack`'s bytes (and hence the proof) are unchanged relative to the
/// build-then-multiply form.
fn fold_stacked_point_claims_k(
    b_stack: &mut [F128T],
    target: &mut F128T,
    claims: &[StackClaimK],
    gammas: &[F128T],
) {
    use rayon::prelude::*;
    const PAR_FOLD_THRESHOLD: usize = 1 << 14;
    // One reusable eq scratch sized to the largest Point claim: a fresh
    // multi-MB allocation per claim would pay the first-touch page faults
    // anew every time. Uninit is fine: the seeded build writes every slot of
    // its prefix before any is read.
    let max_len = claims
        .iter()
        .map(|c| match c {
            StackClaimK::Point { low_point, .. } => 1usize << low_point.len(),
            StackClaimK::Strided { .. } => 0,
        })
        .max()
        .unwrap_or(0);
    let mut scratch: Vec<F128T> = primitives::alloc_uninit_vec(max_len);
    for (claim, g) in claims.iter().zip(gammas.iter()) {
        let g = *g;
        match claim {
            StackClaimK::Point {
                offset,
                low_point,
                value,
            } => {
                let len = 1usize << low_point.len();
                assert!(
                    offset % len == 0,
                    "StackClaimK::Point: offset must be 2^|low_point|-aligned"
                );
                build_eq_table_ext_seeded_into(low_point, g, &mut scratch[..len]);
                let eq = &scratch[..len];
                let dst = &mut b_stack[*offset..*offset + len];
                if len < PAR_FOLD_THRESHOLD {
                    for (bi, ei) in dst.iter_mut().zip(eq.iter()) {
                        *bi += *ei;
                    }
                } else {
                    dst.par_iter_mut()
                        .zip(eq.par_iter())
                        .for_each(|(bi, ei)| *bi += *ei);
                }
                *target += g * *value;
            }
            StackClaimK::Strided {
                offset,
                slot,
                stride_log,
                point,
                value,
            } => {
                // Sparse: eq over the instance `point` (2^|point| entries),
                // scattered at stride 2^stride_log from the slot's position.
                // Identical b_stack contribution to the dense Point with
                // low_point = slot_bits ++ point, at ~2^stride_log x less work.
                let stride = 1usize << stride_log;
                let block = 1usize << (stride_log + point.len());
                assert!(*slot < stride, "StackClaimK::Strided: slot must fit the stride");
                assert!(
                    offset % block == 0,
                    "StackClaimK::Strided: offset must be 2^(stride_log + |point|)-aligned"
                );
                let base = *offset + *slot;
                let eq = build_eq_table_ext(point);
                for (j, &ej) in eq.iter().enumerate() {
                    b_stack[base + j * stride] += g * ej;
                }
                *target += g * *value;
            }
        }
    }
}

/// The claim's weight `eq(full claim point, x)` at an arbitrary point `x` of
/// the full stack cube. A `Point`'s full point is `[low_point, sel_bits]`, a
/// `Strided`'s is `[slot_bits, point, sel_bits]`; neither is materialized.
/// Mirror of the extension-field `stack_claim_eq_at`.
fn stack_claim_eq_at_k(claim: &StackClaimK, x: &[F128T]) -> F128T {
    match claim {
        StackClaimK::Point {
            offset, low_point, ..
        } => {
            let n = low_point.len();
            let mut e = eq_eval_ext(low_point, &x[..n]);
            let sel = offset >> n;
            for (k, &xi) in x[n..].iter().enumerate() {
                e *= if (sel >> k) & 1 == 1 { xi } else { F128T::ONE + xi };
            }
            e
        }
        StackClaimK::Strided {
            offset,
            slot,
            stride_log,
            point,
            ..
        } => {
            let mut e = F128T::ONE;
            for (k, &xi) in x[..*stride_log].iter().enumerate() {
                e *= if (slot >> k) & 1 == 1 { xi } else { F128T::ONE + xi };
            }
            let block_vars = stride_log + point.len();
            e *= eq_eval_ext(point, &x[*stride_log..block_vars]);
            let sel = offset >> block_vars;
            for (k, &xi) in x[block_vars..].iter().enumerate() {
                e *= if (sel >> k) & 1 == 1 { xi } else { F128T::ONE + xi };
            }
            e
        }
    }
}

// ---------------------------------------------------------------------------
// Prover
// ---------------------------------------------------------------------------

/// Open the committed K-stack: discharge every `point_claims` slice
/// evaluation AND the ring-switched q_pkd claims (`ring`) in ONE Ligerito-K
/// run, reusing the caller's [`super::ligerito_k::commit_k`] output as L0.
/// K analog of [`super::open_batch_mixed_ligerito_stacked`].
///
/// `stack` is the committed message (the caller retains it; it is not stored
/// in [`ProverDataK`]); `config.initial_k` / `config.log_inv_rates[0]` must
/// match the commit's `log_batch_size` / `log_inv_rate` (enforced by shape
/// asserts inside the Ligerito prover).
pub fn open_batch_mixed_ligerito_stacked_k(
    sponge: &mut Sponge,
    stack: &[F64],
    prover_data: &ProverDataK,
    config: &ProverConfig,
    point_claims: &[StackClaimK],
    ring: &RingSwitchOpenK,
) -> BatchOpeningProofK {
    let qpkd_len = 1usize << ring.qpkd_vars;
    assert!(
        ring.offset % qpkd_len == 0,
        "q_pkd offset must be 2^qpkd_vars-aligned"
    );
    assert!(
        ring.offset + qpkd_len <= stack.len(),
        "q_pkd slice must fit inside the stack"
    );
    assert!(
        !ring.claims.is_empty(),
        "stacked K opening carries at least one ring-switched claim"
    );
    // Optional phase timing, answering to the same env var as the Ligerito-K
    // prover/commit tracing (one env lookup per open, no work when unset).
    let trace = std::env::var_os("LIG_K_TRACE").is_some();
    let mut t = std::time::Instant::now();
    let mark = |label: &str, t: &mut std::time::Instant| {
        if trace {
            eprintln!("[stack-open-k] {label}: {:7.2} ms", t.elapsed().as_secs_f64() * 1e3);
        }
        *t = std::time::Instant::now();
    };

    // 1. Ring-switch reduction: observe EVERY claim's s_hat_v first, then sample
    //    ONE shared r'' (matches the extension-field opener + the recursion guest), then
    //    finish each claim's sumcheck/weight against the shared eq tensor.
    let qpkd = &stack[ring.offset..ring.offset + qpkd_len];
    let mut rs_proofs = Vec::with_capacity(ring.claims.len());
    let mut rs_states = Vec::with_capacity(ring.claims.len());
    for claim in &ring.claims {
        assert_eq!(
            claim.suffix_point.len(),
            ring.qpkd_vars,
            "ring-switch suffix point must have qpkd_vars coords"
        );
        let (proof, state) = ring_switch_k::prove_observe(
            qpkd,
            &claim.prefix_weights,
            &claim.suffix_point,
            claim.value,
            claim.s_hat_v.as_deref(),
            sponge,
        );
        rs_proofs.push(proof);
        rs_states.push(state);
    }
    let r_dprime = sample_ext_vec(sponge, ring_switch_k::LOG_DEGREE_E);
    let eq_r_dprime = build_eq_table_ext(&r_dprime);
    let rs_outputs: Vec<_> = rs_states
        .iter()
        .map(|s| ring_switch_k::prove_finish(s, &eq_r_dprime))
        .collect();
    mark("ring-switch proves", &mut t);
    // Per-claim batching gammas, sampled AFTER all ring-switch messages are
    // bound (mirror of the extension-field layer's gamma_rs pattern).
    let gammas_rs = sample_ext_vec(sponge, ring.claims.len());

    // 2. Observe point-claim values + sample their gammas (Schwartz-Zippel
    //    sound: every gamma_pd is sampled after all values are observed).
    for claim in point_claims {
        observe_ext(sponge, claim.value());
    }
    let gammas_pd = sample_ext_vec(sponge, point_claims.len());

    // 3. Combined target and lifted stack weight b_stack: the gamma-weighted
    //    rs_eq_ind sum scattered at the q_pkd slice, plus the point-claim
    //    eq tensors scattered at their offsets.
    let mut target = F128T::ZERO;
    for (out, g) in rs_outputs.iter().zip(gammas_rs.iter()) {
        target += *g * out.sumcheck_claim;
    }
    // Uninit alloc + parallel zero fill: `vec![F128T::ZERO; n]` does not hit
    // the calloc zero-page specialization (F128T is not a byte pattern the
    // allocator recognizes), so at large stacks it is a multi-GB
    // single-threaded write. The additive scatters below RELY on the zeroed
    // start; every position is written here before any is read.
    let mut b_stack: Vec<F128T> = primitives::alloc_uninit_vec(stack.len());
    {
        use rayon::prelude::*;
        const ZERO_CHUNK: usize = 1 << 16;
        b_stack
            .par_chunks_mut(ZERO_CHUNK)
            .for_each(|c| c.fill(F128T::ZERO));
    }
    mark("b_stack zero fill", &mut t);
    {
        use rayon::prelude::*;
        let dst = &mut b_stack[ring.offset..ring.offset + qpkd_len];
        dst.par_iter_mut().enumerate().for_each(|(j, b)| {
            let mut acc = F128T::ZERO;
            for (out, g) in rs_outputs.iter().zip(gammas_rs.iter()) {
                acc += *g * out.rs_eq_ind[j];
            }
            *b = acc;
        });
    }
    mark("rs_eq_ind scatter", &mut t);
    fold_stacked_point_claims_k(&mut b_stack, &mut target, point_claims, &gammas_pd);
    mark("point-claim folds", &mut t);

    // 4. One Ligerito-K over the full stack against the combined claim (the
    //    stack is borrowed by the prover; no copy).
    let ligerito = recursive_prover_with_basis_k(
        config,
        stack,
        b_stack,
        target,
        &prover_data.codeword,
        &prover_data.merkle_tree,
        sponge,
    );
    BatchOpeningProofK {
        ring_switches: rs_proofs,
        ligerito,
    }
}

// ---------------------------------------------------------------------------
// Verifier
// ---------------------------------------------------------------------------

/// Verifier mirror of [`open_batch_mixed_ligerito_stacked_k`]: replay the
/// ring-switch reductions succinctly, recompute the combined target, then
/// drive the succinct Ligerito-K verifier with a residual evaluator for the
/// lifted weight. `log_n` is the committed stack's log size in F64 words and
/// `root` the L0 commitment root ([`super::ligerito_k::CommitmentK::root`]).
///
/// Residual evaluator: at each residual point `x = ris ++ y_bits` the
/// ring-switch part is `eq(sel, x_hi) * sum_i gamma_i * MLE(rs_eq_ind_i)(x_lo)`
/// with `x` split at `qpkd_vars`. The tensor-algebra prefix over the `ris`
/// portion of `x_lo` is shared across all `2^yr_log_n` positions and finished
/// per position with the binary suffix; the `y` coords that land on selector
/// bits are binary, so they contribute an exact indicator (only matching `y`
/// positions get a nonzero ring-switch part, which also caps the number of
/// tensor finishes at `2^(qpkd coords covered by y)`). Point-claim weights
/// are evaluated per position in closed form via [`stack_claim_eq_at_k`].
pub fn verify_opening_batch_mixed_ligerito_stacked_k(
    sponge: &mut Sponge,
    config: &VerifierConfig,
    log_n: usize,
    root: &Hash,
    point_claims: &[StackClaimK],
    ring: &RingSwitchVerifyK,
    proof: &BatchOpeningProofK,
) -> Option<StackedOpeningSummaryK> {
    let n_rs = ring.claims.len();
    let qpkd_vars = ring.qpkd_vars;
    // Caller (statement) invariants: panic on misuse, like the extension-field layer.
    assert!(qpkd_vars <= log_n);
    assert!(
        ring.offset % (1usize << qpkd_vars) == 0,
        "q_pkd offset must be 2^qpkd_vars-aligned"
    );
    assert!(n_rs > 0, "stacked K opening carries at least one ring-switched claim");
    for claim in &ring.claims {
        assert_eq!(claim.prefix_weights.len(), PACKING_WIDTH_K);
        assert_eq!(claim.suffix_point.len(), qpkd_vars);
    }
    // `proof` is attacker-controlled (deserialized): validate its shape and
    // reject rather than panicking (`verify_succinct` asserts the
    // s_hat_v length internally).
    if proof.ring_switches.len() != n_rs
        || proof
            .ring_switches
            .iter()
            .any(|rs| rs.s_hat_v.len() != PACKING_WIDTH_K)
    {
        return None;
    }

    // 1. Ring-switch succinct verify: observe EVERY claim's s_hat_v first, then
    //    sample ONE shared r'', then finish each claim (mirrors the prover +
    //    the extension-field opener + the recursion guest).
    for (claim, rs_proof) in ring.claims.iter().zip(proof.ring_switches.iter()) {
        if ring_switch_k::verify_observe(claim.value, &claim.prefix_weights, rs_proof, sponge).is_err() {
            return None;
        }
    }
    let r_dprime = sample_ext_vec(sponge, ring_switch_k::LOG_DEGREE_E);
    let eq_r_dprime = build_eq_table_ext(&r_dprime);
    let rs_outputs: Vec<_> = proof
        .ring_switches
        .iter()
        .map(|rs_proof| ring_switch_k::verify_finish(rs_proof, &eq_r_dprime))
        .collect();
    let gammas_rs = sample_ext_vec(sponge, n_rs);
    let mut target = F128T::ZERO;
    for (out, g) in rs_outputs.iter().zip(gammas_rs.iter()) {
        target += *g * out.sumcheck_claim;
    }

    // 2. Point-claim values + gammas; fold into the target.
    for claim in point_claims {
        observe_ext(sponge, claim.value());
    }
    let gammas_pd = sample_ext_vec(sponge, point_claims.len());
    for (claim, g) in point_claims.iter().zip(gammas_pd.iter()) {
        target += *g * claim.value();
    }

    // 3. Residual evaluator of the lifted weight, called once by the succinct
    //    Ligerito verifier with the full folded `ris` and the residual cube
    //    log-size; returns b's MLE at `ris ++ y_bits` for every y.
    let sel = ring.offset >> qpkd_vars;
    let eval_b_residual = |ris: &[F128T], yr_log_n: usize| -> Vec<F128T> {
        use rayon::prelude::*;
        debug_assert!(yr_log_n <= 32, "yr_log_n > 32 not supported by binary path");
        let n_ris = ris.len();
        // The q_pkd coords x_lo = x[..qpkd_vars] split into a ris part
        // (shared prefix) and up to `n_qpkd_from_y` binary y coords.
        let split = qpkd_vars.min(n_ris);
        let n_qpkd_from_y = qpkd_vars - split;

        // Shared tensor prefixes over the ris part of the q_pkd coords.
        let rs_prefixes: Vec<TensorAlgebraE> = ring
            .claims
            .iter()
            .map(|c| eval_rs_eq_prefix_k(&c.suffix_point, &ris[..split]))
            .collect();

        // Selector eq over the ris coords above the q_pkd slice (E-valued
        // part; the y-covered selector coords are handled per position).
        let mut sel_prefix = F128T::ONE;
        for (k, &xi) in ris[split..].iter().enumerate() {
            sel_prefix *= if (sel >> k) & 1 == 1 { xi } else { F128T::ONE + xi };
        }

        (0..1usize << yr_log_n)
            .into_par_iter()
            .map(|y| {
                // Full point x = ris ++ y_bits for the point-claim weights.
                let mut x = Vec::with_capacity(n_ris + yr_log_n);
                x.extend_from_slice(ris);
                for k in 0..yr_log_n {
                    x.push(if (y >> k) & 1 == 1 { F128T::ONE } else { F128T::ZERO });
                }

                // Selector coords covered by y are binary: an indicator.
                let mut sel_ok = true;
                for k in n_qpkd_from_y..yr_log_n {
                    if (sel >> (n_ris + k - qpkd_vars)) & 1 != (y >> k) & 1 {
                        sel_ok = false;
                        break;
                    }
                }
                let mut acc = F128T::ZERO;
                if sel_ok {
                    // Finish each claim's tensor prefix with the binary
                    // query suffix (the q_pkd coords covered by y).
                    let y_low = (y & ((1usize << n_qpkd_from_y) - 1)) as u32;
                    let mut rs_part = F128T::ZERO;
                    for ((claim, prefix), (g, out)) in ring
                        .claims
                        .iter()
                        .zip(rs_prefixes.iter())
                        .zip(gammas_rs.iter().zip(rs_outputs.iter()))
                    {
                        rs_part += *g
                            * eval_rs_eq_finish_from_prefix_binary_q_k(
                                prefix,
                                &claim.suffix_point[split..],
                                y_low,
                                &out.eq_r_dprime,
                            );
                    }
                    acc = rs_part * sel_prefix;
                }
                for (claim, g) in point_claims.iter().zip(gammas_pd.iter()) {
                    acc += *g * stack_claim_eq_at_k(claim, &x);
                }
                acc
            })
            .collect()
    };

    let mut query_squeezes: Vec<Vec<F128T>> = Vec::new();
    let ok = recursive_verifier_with_basis_succinct_k_with_squeezes(
        config,
        &proof.ligerito,
        log_n,
        target,
        root,
        eval_b_residual,
        sponge,
        &mut query_squeezes,
    );
    ok.then(|| StackedOpeningSummaryK {
        lig: LigVerifierSummaryK { query_squeezes },
    })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ligerito::{default_config, default_verifier_config};
    use crate::ligerito_k::{commit_k, inner_product_base_ext, k_configs_for};
    use crate::pack_k::{LOG_PACKING_K, pack_witness_k};
    use crate::ring_switch_k::{claim_check, eq_prefix_weights, fold_1b_rows_k};

    fn splitmix64(state: &mut u64) -> u64 {
        *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = *state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn rand_ext(s: &mut u64) -> F128T {
        F128T::new(splitmix64(s), splitmix64(s))
    }

    /// Configs for a K-stack of `2^log_n` words: prefer the production
    /// Secure-profile derivation; fall back to the ad-hoc default_config
    /// shape below its feasibility floor (same fallback the sibling K test
    /// modules use).
    fn configs_for(log_n: usize) -> (ProverConfig, VerifierConfig) {
        match k_configs_for(log_n) {
            Ok(pv) => pv,
            Err(_) => {
                let pc = default_config(log_n, 5, 1).unwrap();
                let vc = default_verifier_config(log_n, 5, 1).unwrap();
                (pc, vc)
            }
        }
    }

    const DOMAIN: &[u8] = b"stack-open-k-test";

    struct Instance {
        vc: VerifierConfig,
        log_n: usize,
        root: Hash,
        point_claims: Vec<StackClaimK>,
        ring: RingSwitchOpenK,
        proof: BatchOpeningProofK,
    }

    /// Synthetic stack of 2^14 F64 words: three aligned 2^12-word columns
    /// plus a q_pkd region (a random bit-witness packed by pack_k) at the
    /// top slice, padded with random filler. Pool: one point claim per
    /// column at a random E point, one strided claim into q_pkd, one
    /// ring-switched claim with plain eq prefix weights.
    ///
    /// q_pkd is kept SMALL (2^8 words) so the succinct verifier's residual
    /// cube sits entirely above the q_pkd coords (the production regime:
    /// shared tensor prefix folded once, y coords all selector-indicator,
    /// nonempty E-valued selector prefix from ris); the crossing regime is
    /// exercised by `stacked_open_residual_crosses_qpkd`.
    fn build_instance(seed: u64) -> Instance {
        let log_n = 14usize;
        let col_vars = 12usize;
        let col_len = 1usize << col_vars;
        let qpkd_vars = 8usize;
        let qpkd_offset = 3 * col_len;
        let mut s = seed;

        // Three random columns, the packed bit-witness region, then filler.
        let mut stack: Vec<F64> = (0..3 * col_len).map(|_| F64(splitmix64(&mut s))).collect();
        let bits: Vec<bool> = (0..1usize << (qpkd_vars + LOG_PACKING_K))
            .map(|_| splitmix64(&mut s) & 1 == 1)
            .collect();
        stack.extend(pack_witness_k(&bits, qpkd_vars + LOG_PACKING_K));
        while stack.len() < 1 << log_n {
            stack.push(F64(splitmix64(&mut s)));
        }
        assert_eq!(stack.len(), 1 << log_n);

        // One point claim per column, at a random E point.
        let mut point_claims: Vec<StackClaimK> = (0..3)
            .map(|c| {
                let offset = c * col_len;
                let low_point: Vec<F128T> = (0..col_vars).map(|_| rand_ext(&mut s)).collect();
                let eq = build_eq_table_ext(&low_point);
                let value = inner_product_base_ext(&stack[offset..offset + col_len], &eq);
                StackClaimK::Point {
                    offset,
                    low_point,
                    value,
                }
            })
            .collect();

        // One strided claim into the q_pkd region: freeze the low 3 in-block
        // coords to slot 5, eq over the remaining coords of the slice.
        {
            let stride_log = 3usize;
            let slot = 5usize;
            let point: Vec<F128T> = (0..qpkd_vars - stride_log).map(|_| rand_ext(&mut s)).collect();
            let eq = build_eq_table_ext(&point);
            let mut value = F128T::ZERO;
            for (j, &ej) in eq.iter().enumerate() {
                value += ej.mul_base(stack[qpkd_offset + slot + (j << stride_log)]);
            }
            point_claims.push(StackClaimK::Strided {
                offset: qpkd_offset,
                slot,
                stride_log,
                point,
                value,
            });
        }

        // One ring-switched claim on q_pkd (plain eq prefix weights).
        let qpkd = &stack[qpkd_offset..qpkd_offset + (1 << qpkd_vars)];
        let r_prefix: Vec<F128T> = (0..LOG_PACKING_K).map(|_| rand_ext(&mut s)).collect();
        let prefix_weights = eq_prefix_weights(&r_prefix);
        let suffix_point: Vec<F128T> = (0..qpkd_vars).map(|_| rand_ext(&mut s)).collect();
        let s_hat_v = fold_1b_rows_k(qpkd, &build_eq_table_ext(&suffix_point));
        let value = claim_check(&prefix_weights, &s_hat_v);
        let ring = RingSwitchOpenK {
            offset: qpkd_offset,
            qpkd_vars,
            claims: vec![RingSwitchClaimK {
                prefix_weights,
                suffix_point,
                value,
                // Exercise the fold path (no precompute).
                s_hat_v: None,
            }],
        };

        let (pc, vc) = configs_for(log_n);
        // Pin the intended residual regime: the residual cube must sit
        // entirely above the q_pkd coords, with at least one selector coord
        // covered by ris (the E-valued sel prefix) and the rest by y bits.
        let yr_log_n = log_n - pc.initial_k - pc.level_ks.iter().sum::<usize>();
        assert!(
            qpkd_vars < log_n - yr_log_n,
            "test shape must keep the residual cube above q_pkd (yr_log_n = {yr_log_n})"
        );
        let (cm, pd) = commit_k(&stack, pc.initial_k, pc.log_inv_rates[0]);
        let mut ch = Sponge::new(DOMAIN, &[]);
        let proof =
            open_batch_mixed_ligerito_stacked_k(&mut ch, &stack, &pd, &pc, &point_claims, &ring);

        Instance {
            vc,
            log_n,
            root: cm.root,
            point_claims,
            ring,
            proof,
        }
    }

    fn verify_instance(
        inst: &Instance,
        point_claims: &[StackClaimK],
        ring_claims: &[RingSwitchClaimK],
        proof: &BatchOpeningProofK,
    ) -> bool {
        let ring = RingSwitchVerifyK {
            offset: inst.ring.offset,
            qpkd_vars: inst.ring.qpkd_vars,
            claims: ring_claims.to_vec(),
        };
        let mut ch = Sponge::new(DOMAIN, &[]);
        verify_opening_batch_mixed_ligerito_stacked_k(
            &mut ch,
            &inst.vc,
            inst.log_n,
            &inst.root,
            point_claims,
            &ring,
            proof,
        )
        .is_some()
    }

    #[test]
    fn stacked_open_roundtrip_and_tampering() {
        let inst = build_instance(1);
        assert!(
            verify_instance(&inst, &inst.point_claims, &inst.ring.claims, &inst.proof),
            "honest stacked opening rejected"
        );

        // Wrong point-claim value (dense column claim).
        let mut bad_points = inst.point_claims.clone();
        if let StackClaimK::Point { value, .. } = &mut bad_points[0] {
            *value += F128T::ONE;
        } else {
            unreachable!()
        }
        assert!(
            !verify_instance(&inst, &bad_points, &inst.ring.claims, &inst.proof),
            "tampered Point value accepted"
        );

        // Wrong strided-claim value.
        let mut bad_points = inst.point_claims.clone();
        if let StackClaimK::Strided { value, .. } = &mut bad_points[3] {
            *value += F128T::ONE;
        } else {
            unreachable!()
        }
        assert!(
            !verify_instance(&inst, &bad_points, &inst.ring.claims, &inst.proof),
            "tampered Strided value accepted"
        );

        // Wrong ring-switched claim value: rejected by the claim check.
        let mut bad_ring = inst.ring.claims.clone();
        bad_ring[0].value += F128T::ONE;
        assert!(
            !verify_instance(&inst, &inst.point_claims, &bad_ring, &inst.proof),
            "tampered ring-switch value accepted"
        );

        // Tampered s_hat_v: breaks the claim check.
        let mut bad_proof = inst.proof.clone();
        bad_proof.ring_switches[0].s_hat_v[17].c0 ^= 1;
        assert!(
            !verify_instance(&inst, &inst.point_claims, &inst.ring.claims, &bad_proof),
            "tampered s_hat_v accepted"
        );

        // Tampered Ligerito proof scalars.
        let mut bad_proof = inst.proof.clone();
        bad_proof.ligerito.sumcheck_transcript[0].u_0.c0 ^= 1;
        assert!(
            !verify_instance(&inst, &inst.point_claims, &inst.ring.claims, &bad_proof),
            "tampered sumcheck u_0 accepted"
        );
        let mut bad_proof = inst.proof.clone();
        bad_proof.ligerito.final_proof.yr[0].c1 ^= 1;
        assert!(
            !verify_instance(&inst, &inst.point_claims, &inst.ring.claims, &bad_proof),
            "tampered final yr accepted"
        );

        // Proof-shape tamper: dropping the ring-switch message must return
        // false (not panic).
        let mut bad_proof = inst.proof.clone();
        bad_proof.ring_switches[0].s_hat_v.pop();
        assert!(
            !verify_instance(&inst, &inst.point_claims, &inst.ring.claims, &bad_proof),
            "short s_hat_v accepted"
        );
    }

    #[test]
    fn stacked_open_proof_is_deterministic() {
        let a = build_instance(2);
        let b = build_instance(2);
        assert_eq!(a.proof, b.proof, "same inputs must yield identical proofs");
        let bytes_a = bincode::serialize(&a.proof).unwrap();
        let bytes_b = bincode::serialize(&b.proof).unwrap();
        assert_eq!(bytes_a, bytes_b, "proof bytes must be deterministic");
    }

    /// Residual cube crossing INTO the q_pkd slice (case split = n_ris in the
    /// verifier closure): q_pkd occupies half a 2^14 stack (qpkd_vars = 13),
    /// and the fallback config's residual cube (yr_log_n = 3) is wider than
    /// the single selector coordinate, so some q_pkd coords are covered by
    /// binary y bits and the tensor finish runs with a nonempty suffix.
    #[test]
    fn stacked_open_residual_crosses_qpkd() {
        let log_n = 14usize;
        let qpkd_vars = 13usize;
        let qpkd_offset = 1usize << 13;
        let mut s = 3u64;

        let mut stack: Vec<F64> = (0..1usize << 13).map(|_| F64(splitmix64(&mut s))).collect();
        let bits: Vec<bool> = (0..1usize << (qpkd_vars + LOG_PACKING_K))
            .map(|_| splitmix64(&mut s) & 1 == 1)
            .collect();
        stack.extend(pack_witness_k(&bits, qpkd_vars + LOG_PACKING_K));
        assert_eq!(stack.len(), 1 << log_n);

        // One point claim on the low column.
        let low_point: Vec<F128T> = (0..12).map(|_| rand_ext(&mut s)).collect();
        let eq = build_eq_table_ext(&low_point);
        let value = inner_product_base_ext(&stack[..1 << 12], &eq);
        let point_claims = vec![StackClaimK::Point {
            offset: 0,
            low_point,
            value,
        }];

        // One ring-switched claim on the wide q_pkd.
        let qpkd = &stack[qpkd_offset..];
        let r_prefix: Vec<F128T> = (0..LOG_PACKING_K).map(|_| rand_ext(&mut s)).collect();
        let prefix_weights = eq_prefix_weights(&r_prefix);
        let suffix_point: Vec<F128T> = (0..qpkd_vars).map(|_| rand_ext(&mut s)).collect();
        let s_hat_v = fold_1b_rows_k(qpkd, &build_eq_table_ext(&suffix_point));
        let rs_value = claim_check(&prefix_weights, &s_hat_v);
        let claims = vec![RingSwitchClaimK {
            prefix_weights,
            suffix_point,
            value: rs_value,
            // Exercise the precomputed path (transcript must be identical).
            s_hat_v: Some(s_hat_v.clone()),
        }];

        // Fixed fallback config so the residual cube size is known: the
        // crossing regime needs qpkd_vars > log_n - yr_log_n.
        let pc = default_config(log_n, 5, 1).unwrap();
        let vc = default_verifier_config(log_n, 5, 1).unwrap();
        let yr_log_n = log_n - pc.initial_k - pc.level_ks.iter().sum::<usize>();
        assert!(
            qpkd_vars > log_n - yr_log_n,
            "test shape must exercise the crossing regime (yr_log_n = {yr_log_n})"
        );

        let (cm, pd) = commit_k(&stack, pc.initial_k, pc.log_inv_rates[0]);
        let ring = RingSwitchOpenK {
            offset: qpkd_offset,
            qpkd_vars,
            claims,
        };
        let mut ch = Sponge::new(DOMAIN, &[]);
        let proof =
            open_batch_mixed_ligerito_stacked_k(&mut ch, &stack, &pd, &pc, &point_claims, &ring);

        let ring_v = RingSwitchVerifyK {
            offset: qpkd_offset,
            qpkd_vars,
            claims: ring.claims.clone(),
        };
        let mut ch = Sponge::new(DOMAIN, &[]);
        assert!(
            verify_opening_batch_mixed_ligerito_stacked_k(
                &mut ch,
                &vc,
                log_n,
                &cm.root,
                &point_claims,
                &ring_v,
                &proof,
            )
            .is_some(),
            "honest crossing-regime opening rejected"
        );

        // And the crossing-regime ring claim is still bound: flip its value.
        let mut bad_ring = ring_v;
        bad_ring.claims[0].value += F128T::ONE;
        let mut ch = Sponge::new(DOMAIN, &[]);
        assert!(
            verify_opening_batch_mixed_ligerito_stacked_k(
                &mut ch,
                &vc,
                log_n,
                &cm.root,
                &point_claims,
                &bad_ring,
                &proof,
            )
            .is_none(),
            "tampered crossing-regime ring value accepted"
        );
    }
}
