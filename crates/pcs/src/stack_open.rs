// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Stacked batch-mixed opening for the F64-committed PCS.
//!
//! The committed witness is a stack of `2^log_n` [`F64`] words (committed via
//! [`super::whir::commit`]), and one WHIR run discharges
//!
//! - **point claims** ([`StackClaim`]): plain multilinear evaluations of
//!   aligned sub-slices of the stack (a `Point` claim's weight is
//!   `eq(low_point, .)` supported on `[offset, offset + 2^|low_point|)`; a
//!   `Strided` claim freezes the low `stride_log` in-block coords to `slot`'s
//!   bits, so its weight is nonzero only at `offset + slot + j * 2^stride_log`),
//! - **ring-switched claims** ([`RingSwitchOpen`]): bit-MLE evaluation claims
//!   on the packed sub-block `q_pkd = stack[offset .. offset + 2^qpkd_vars]`,
//!   reduced per claim by [`super::ring_switch::prove_observe`] and the
//!   deferred finish path to an inner-product
//!   claim `<q_pkd, rs_eq_ind> = sumcheck_claim` against the transparent
//!   E-valued weight `rs_eq_ind`.
//!
//! All claims are gamma-folded into ONE combined weight `b_stack` over the
//! whole stack plus one `target`, then proved by
//! [`super::whir::recursive_prover_with_basis`]. The verifier replays
//! the ring-switch reductions succinctly ([`super::ring_switch::verify_observe`]
//! and [`super::ring_switch::verify_finish`], with no dense `rs_eq_ind`) and drives
//! [`super::whir::recursive_verifier_with_basis_succinct`] with a
//! terminal evaluator that reconstructs `MLE(b_stack)` once, at the final fold
//! point, using closed-form eq / stride selectors and
//! [`super::ring_switch::eval_rs_eq`].
//!
//! ## Transcript order (identical on both sides)
//!
//! label -> per ring-switched claim ([`super::ring_switch`]'s own label +
//! `s_hat_v_i` observed + shared linear map sampled) -> gamma_rs (one per claim) ->
//! per point claim (label + value observed) -> gamma_pd (one per claim) ->
//! WHIR, with domain-separated labels for every phase.
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

use crate::merkle::Hash;
use fiat_shamir::sponge::Sponge;
use primitives::field::{F64, F192};
use primitives::multilinear::eq_eval;
use serde::{Deserialize, Serialize};

use super::pack::PACKING_WIDTH;
use super::ring_switch::{self, RingSwitchProof};
use super::whir::{ProverConfig, VerifierConfig};
use super::whir::{
    ProverData, WhirProof, build_eq_table_ext, recursive_prover_with_basis,
    recursive_verifier_with_basis_succinct_with_squeezes,
};

// ---------------------------------------------------------------------------
// Claim types
// ---------------------------------------------------------------------------

/// An owning point claim folded into the stacked mixed opening.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StackClaim {
    /// `eq(low_point, .)` on the aligned slice
    /// `[offset, offset + 2^|low_point|)`; `offset` must be a multiple of
    /// `2^|low_point|`.
    Point {
        offset: usize,
        low_point: Vec<F192>,
        value: F192,
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
        point: Vec<F192>,
        value: F192,
    },
}

impl StackClaim {
    #[inline]
    pub fn value(&self) -> F192 {
        match self {
            StackClaim::Point { value, .. } | StackClaim::Strided { value, .. } => *value,
        }
    }
}

/// One ring-switched evaluation claim on the q_pkd sub-block: the consumed
/// claim is `value == sum_i prefix_weights[i] * s_hat_v[i]` where `s_hat_v`
/// are the 64 bit-slice MLEs of q_pkd at `suffix_point` (see
/// [`super::ring_switch`]). `prefix_weights` has [`PACKING_WIDTH`] = 64
/// entries (the eq tensor of the 6 prefix coords for a plain point claim;
/// phi_8 Lagrange weights for flock's
/// univariate-skip claim); `suffix_point` has `qpkd_vars` coords.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingSwitchClaim {
    pub prefix_weights: Vec<F192>,
    pub suffix_point: Vec<F192>,
    pub value: F192,
    /// Prover-side optional precomputed `s_hat_v` (the 64 bit-slice MLE
    /// values at `suffix_point`, e.g. captured inside flock's reduction).
    /// When present, [`super::ring_switch::prove_observe`] skips its
    /// `fold_1b_rows` recomputation; the values are checked against the
    /// claim (`claim_check`) and the transcript is identical either way.
    /// Verifier-side bundles leave it `None`.
    pub s_hat_v: Option<Vec<F192>>,
}

/// Prover-side bundle of the ring-switched claims discharged in the same
/// stacked opening as the [`StackClaim`]s. Each claim may carry its
/// precomputed `s_hat_v`.
#[derive(Clone, Debug)]
pub struct RingSwitchOpen {
    /// q_pkd's offset inside the committed stack; must be a multiple of
    /// `2^qpkd_vars` (an aligned slice).
    pub offset: usize,
    /// log2 of q_pkd's length in F64 words; the opener slices
    /// `q_pkd = stack[offset .. offset + 2^qpkd_vars]` (no separate copy).
    pub qpkd_vars: usize,
    pub claims: Vec<RingSwitchClaim>,
}

/// Verifier counterpart of [`RingSwitchOpen`]: identical statement data
/// (the proof travels separately as [`BatchOpeningProof`]).
#[derive(Clone, Debug)]
pub struct RingSwitchVerify {
    /// q_pkd's offset inside the committed stack.
    pub offset: usize,
    /// log2 of q_pkd's length in F64 words.
    pub qpkd_vars: usize,
    pub claims: Vec<RingSwitchClaim>,
}

/// Batched stacked opening proof: one ring-switch message per ring-switched
/// claim plus one WHIR proof over the combined claim.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BatchOpeningProof {
    pub ring_switches: Vec<RingSwitchProof>,
    pub whir: WhirProof,
}

/// What the stacked-opening verifier hands back on accept: the recursion
/// harness's hook for the WHIR fold/query data.
#[derive(Clone, Debug, Default)]
pub struct StackedOpeningSummary {
    pub lig: LigVerifierSummary,
}

/// See [`StackedOpeningSummary`].
#[derive(Clone, Debug, Default)]
pub struct LigVerifierSummary {
    /// The raw query-sampling squeezes, per level in transcript order.
    pub query_squeezes: Vec<Vec<F192>>,
}

// ---------------------------------------------------------------------------
// Shared claim folding / evaluation
// ---------------------------------------------------------------------------

/// Fold the gamma-weighted point claims into the stack weight `b_stack` and
/// running `target` (pure: the caller has already observed the claim values
/// and sampled `gammas` in transcript order). A `Point` builds eq over ONLY
/// its aligned slice, a `Strided` scatters the eq of its high coords at the
/// slot's stride. Both scatter with `+=`, so overlapping slices accumulate
/// correctly; the OUTER loop therefore stays serial (several bus claims can
/// land on one column region), and parallelism lives inside each claim: the
/// gamma-seeded eq build ([`super::whir::add_eq_table_ext_seeded`], parallel
/// above its level floor, expanding its last coordinate straight into
/// `b_stack` so the table's largest level is never staged in scratch) and the
/// strided scatter. Small slices stay fully serial (with many tiny point
/// claims, pool dispatch would cost more than the fold itself). The gamma
/// seeding and the serial/parallel splits are exact-field/order-preserving,
/// so `b_stack`'s bytes (and hence the proof) are unchanged relative to the
/// build-then-multiply form.
fn fold_stacked_point_claims(b_stack: &mut [F192], target: &mut F192, claims: &[StackClaim], gammas: &[F192]) {
    // One reusable eq scratch, sized to half the largest Point claim, since
    // `add_eq_table_ext_seeded` expands the last coordinate straight into
    // `b_stack`. A fresh multi-MB allocation per claim would pay the first-touch
    // page faults anew.
    let max_half = claims
        .iter()
        .map(|c| match c {
            StackClaim::Point { low_point, .. } => 1usize << low_point.len().saturating_sub(1),
            StackClaim::Strided { .. } => 0,
        })
        .max()
        .unwrap_or(0);
    let mut scratch = zk_alloc::alloc_uninit(max_half);
    for (claim, g) in claims.iter().zip(gammas.iter()) {
        let g = *g;
        match claim {
            StackClaim::Point {
                offset,
                low_point,
                value,
            } => {
                let len = 1usize << low_point.len();
                assert!(
                    offset % len == 0,
                    "StackClaim::Point: offset must be 2^|low_point|-aligned"
                );
                let dst = &mut b_stack[*offset..*offset + len];
                super::whir::add_eq_table_ext_seeded(low_point, g, &mut scratch, dst);
                *target += g * *value;
            }
            StackClaim::Strided {
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
                assert!(*slot < stride, "StackClaim::Strided: slot must fit the stride");
                assert!(
                    offset % block == 0,
                    "StackClaim::Strided: offset must be 2^(stride_log + |point|)-aligned"
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
fn stack_claim_eq_at(claim: &StackClaim, x: &[F192]) -> F192 {
    match claim {
        StackClaim::Point { offset, low_point, .. } => {
            let n = low_point.len();
            let mut e = eq_eval(low_point, &x[..n]);
            let sel = offset >> n;
            for (k, &xi) in x[n..].iter().enumerate() {
                e *= if (sel >> k) & 1 == 1 { xi } else { F192::ONE + xi };
            }
            e
        }
        StackClaim::Strided {
            offset,
            slot,
            stride_log,
            point,
            ..
        } => {
            let mut e = F192::ONE;
            for (k, &xi) in x[..*stride_log].iter().enumerate() {
                e *= if (slot >> k) & 1 == 1 { xi } else { F192::ONE + xi };
            }
            let block_vars = stride_log + point.len();
            e *= eq_eval(point, &x[*stride_log..block_vars]);
            let sel = offset >> block_vars;
            for (k, &xi) in x[block_vars..].iter().enumerate() {
                e *= if (sel >> k) & 1 == 1 { xi } else { F192::ONE + xi };
            }
            e
        }
    }
}

// ---------------------------------------------------------------------------
// Prover
// ---------------------------------------------------------------------------

/// Open the committed `F64` stack: discharge every `point_claims` slice
/// evaluation AND the ring-switched q_pkd claims (`ring`) in ONE WHIR
/// run, reusing the caller's [`super::whir::commit`] output as L0.
///
/// `stack` is the committed message (the caller retains it; it is not stored
/// in [`ProverData`]); `config.initial_k` / `config.log_inv_rates[0]` must
/// match the commit's `log_batch_size` / `log_inv_rate` (enforced by shape
/// asserts inside the WHIR prover).
pub fn open_batch_mixed_whir_stacked(
    sponge: &mut Sponge,
    stack: &[F64],
    prover_data: &ProverData,
    config: &ProverConfig,
    point_claims: &[StackClaim],
    ring: &RingSwitchOpen,
) -> BatchOpeningProof {
    let qpkd_len = 1usize << ring.qpkd_vars;
    assert!(
        ring.offset.is_multiple_of(qpkd_len),
        "q_pkd offset must be 2^qpkd_vars-aligned"
    );
    assert!(
        ring.offset + qpkd_len <= stack.len(),
        "q_pkd slice must fit inside the stack"
    );
    assert!(
        !ring.claims.is_empty(),
        "stacked PCS opening carries at least one ring-switched claim"
    );
    // Optional phase timing, answering to the same env var as the WHIR
    // prover/commit tracing (one env lookup per open, no work when unset).
    let trace = std::env::var_os("WHIR_TRACE").is_some();
    let mut t = std::time::Instant::now();
    let mark = |label: &str, t: &mut std::time::Instant| {
        if trace {
            eprintln!("[stack-open-k] {label}: {:7.2} ms", t.elapsed().as_secs_f64() * 1e3);
        }
        *t = std::time::Instant::now();
    };

    // 1. Ring-switch reduction: observe every claim's s_hat_v, sample one
    //    shared linear map, then finish each claim against that map.
    let qpkd = &stack[ring.offset..ring.offset + qpkd_len];
    let mut rs_proofs = Vec::with_capacity(ring.claims.len());
    let mut rs_states = Vec::with_capacity(ring.claims.len());
    for claim in &ring.claims {
        assert_eq!(
            claim.suffix_point.len(),
            ring.qpkd_vars,
            "ring-switch suffix point must have qpkd_vars coords"
        );
        let (proof, state) = ring_switch::prove_observe(
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
    let map_challenges = ring_switch::sample_map_challenges(sponge);
    let coordinate_weights = ring_switch::build_coordinate_weights(&map_challenges);
    // Per-claim batching gammas, sampled AFTER all ring-switch messages are
    // bound.
    let gammas_rs = sponge.sample_vec(ring.claims.len());
    let rs_outputs: Vec<_> = rs_states
        .into_iter()
        .zip(gammas_rs)
        .map(|(state, gamma)| ring_switch::prove_finish_deferred(state, &coordinate_weights, gamma))
        .collect();
    mark("ring-switch proves", &mut t);

    // 2. Observe point-claim values + sample their gammas (Schwartz-Zippel
    //    sound: every gamma_pd is sampled after all values are observed).
    for claim in point_claims {
        sponge.observe(claim.value());
    }
    let gammas_pd = sponge.sample_vec(point_claims.len());

    // 3. Combined target and lifted stack weight b_stack: the gamma-weighted
    //    rs_eq_ind sum scattered at the q_pkd slice, plus the point-claim
    //    eq tensors scattered at their offsets.
    let mut target = rs_outputs
        .iter()
        .fold(F192::ZERO, |acc, out| acc + out.batched_sumcheck_claim);
    // Parallel first-touch wins for the tower stack: its many scattered point
    // claims otherwise fault pages one claim at a time. The scatters that follow
    // accumulate, so their slots have to start at zero, with one exception:
    // `combine_deferred_into` writes the whole q_pkd block, so zeroing it first
    // would be a quarter of a gigabyte of stores thrown away.
    //
    // SAFETY: every slot is written before it is read: the fill covers everything
    // outside the q_pkd block, and `combine_deferred_into` writes the block.
    let mut b_stack = unsafe { zk_alloc::ArenaVec::<F192>::uninitialized(stack.len()) };
    {
        const ZERO_CHUNK: usize = 1 << 16;
        let (head, rest) = b_stack.split_at_mut(ring.offset);
        let (block, tail) = rest.split_at_mut(qpkd_len);
        for part in [head, tail] {
            parallel::chunks_mut(part, ZERO_CHUNK, |_, chunk| chunk.fill(F192::ZERO));
        }
        mark("b_stack zero fill", &mut t);
        ring_switch::combine_deferred_into(&rs_outputs, block);
        mark("rs_eq_ind scatter", &mut t);
    }
    fold_stacked_point_claims(&mut b_stack, &mut target, point_claims, &gammas_pd);
    mark("point-claim folds", &mut t);

    // 4. One WHIR over the full stack against the combined claim (the
    //    stack is borrowed by the prover; no copy).
    let whir = recursive_prover_with_basis(
        config,
        stack,
        b_stack,
        target,
        &prover_data.codeword,
        &prover_data.merkle_tree,
        sponge,
    );
    BatchOpeningProof {
        ring_switches: rs_proofs,
        whir,
    }
}

// ---------------------------------------------------------------------------
// Verifier
// ---------------------------------------------------------------------------

/// Verifier mirror of [`open_batch_mixed_whir_stacked`]: replay the
/// ring-switch reductions succinctly, recompute the combined target, then
/// drive the succinct WHIR verifier with one terminal evaluation of the
/// lifted weight. `log_n` is the committed stack's log size in F64 words and
/// `root` the L0 commitment root ([`super::whir::Commitment::root`]).
pub fn verify_opening_batch_mixed_whir_stacked(
    sponge: &mut Sponge,
    config: &VerifierConfig,
    log_n: usize,
    root: &Hash,
    point_claims: &[StackClaim],
    ring: &RingSwitchVerify,
    proof: &BatchOpeningProof,
) -> Option<StackedOpeningSummary> {
    let n_rs = ring.claims.len();
    let qpkd_vars = ring.qpkd_vars;
    // Caller (statement) invariants: panic on misuse, like the extension-field layer.
    assert!(qpkd_vars <= log_n);
    assert!(
        ring.offset.is_multiple_of(1usize << qpkd_vars),
        "q_pkd offset must be 2^qpkd_vars-aligned"
    );
    assert!(n_rs > 0, "stacked PCS opening carries at least one ring-switched claim");
    for claim in &ring.claims {
        assert_eq!(claim.prefix_weights.len(), PACKING_WIDTH);
        assert_eq!(claim.suffix_point.len(), qpkd_vars);
    }
    // `proof` is attacker-controlled (deserialized): validate its shape and
    // reject rather than panicking (`verify_succinct` asserts the
    // s_hat_v length internally).
    if proof.ring_switches.len() != n_rs || proof.ring_switches.iter().any(|rs| rs.s_hat_v.len() != PACKING_WIDTH) {
        return None;
    }

    // 1. Ring-switch succinct verify: observe every claim's s_hat_v, sample one
    //    shared linear map, then finish each claim (mirrors the prover and guest).
    for (claim, rs_proof) in ring.claims.iter().zip(proof.ring_switches.iter()) {
        if ring_switch::verify_observe(claim.value, &claim.prefix_weights, rs_proof, sponge).is_err() {
            return None;
        }
    }
    let map_challenges = ring_switch::sample_map_challenges(sponge);
    let coordinate_weights = ring_switch::build_coordinate_weights(&map_challenges);
    let rs_outputs: Vec<_> = proof
        .ring_switches
        .iter()
        .map(|rs_proof| ring_switch::verify_finish(rs_proof, &coordinate_weights))
        .collect();
    let gammas_rs = sponge.sample_vec(n_rs);
    let mut target = F192::ZERO;
    for (out, g) in rs_outputs.iter().zip(gammas_rs.iter()) {
        target += *g * out.sumcheck_claim;
    }

    // 2. Point-claim values + gammas; fold into the target.
    for claim in point_claims {
        sponge.observe(claim.value());
    }
    let gammas_pd = sponge.sample_vec(point_claims.len());
    for (claim, g) in point_claims.iter().zip(gammas_pd.iter()) {
        target += *g * claim.value();
    }

    // 3. Evaluate the lifted weight once, at the terminal sumcheck point.
    let sel = ring.offset >> qpkd_vars;
    let eval_b_at = |x: &[F192]| -> F192 {
        let (x_lo, x_hi) = x.split_at(qpkd_vars);
        let mut sel_eq = F192::ONE;
        for (k, &xi) in x_hi.iter().enumerate() {
            sel_eq *= if (sel >> k) & 1 == 1 { xi } else { F192::ONE + xi };
        }
        let mut rs_part = F192::ZERO;
        for ((claim, g), out) in ring.claims.iter().zip(gammas_rs.iter()).zip(rs_outputs.iter()) {
            rs_part += *g * ring_switch::eval_rs_eq(&claim.suffix_point, x_lo, &out.coordinate_weights);
        }
        let mut acc = rs_part * sel_eq;
        for (claim, g) in point_claims.iter().zip(gammas_pd.iter()) {
            acc += *g * stack_claim_eq_at(claim, x);
        }
        acc
    };

    let mut query_squeezes: Vec<Vec<F192>> = Vec::new();
    let ok = recursive_verifier_with_basis_succinct_with_squeezes(
        config,
        &proof.whir,
        log_n,
        target,
        root,
        eval_b_at,
        sponge,
        &mut query_squeezes,
    );
    ok.then_some(StackedOpeningSummary {
        lig: LigVerifierSummary { query_squeezes },
    })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pack::{LOG_PACKING, pack_witness};
    use crate::ring_switch::{claim_check, fold_1b_rows};
    use crate::whir::{commit, configs_for, inner_product_base_ext};
    use crate::whir::{default_config, default_verifier_config};
    use primitives::test_rng::Rng;

    /// Configs for a K-stack of `2^log_n` words: prefer the production
    /// Secure-profile derivation; fall back to the ad-hoc default_config
    /// shape below its feasibility floor (same fallback the sibling K test
    /// modules use).
    fn test_configs_for(log_n: usize) -> (ProverConfig, VerifierConfig) {
        match configs_for(log_n) {
            Ok(pv) => pv,
            Err(_) => {
                let pc = default_config(log_n, 5, 1).unwrap();
                let vc = default_verifier_config(log_n, 5, 1).unwrap();
                (pc, vc)
            }
        }
    }

    const DOMAIN: &[u8] = b"stack-open-test";

    struct Instance {
        vc: VerifierConfig,
        log_n: usize,
        root: Hash,
        point_claims: Vec<StackClaim>,
        ring: RingSwitchOpen,
        proof: BatchOpeningProof,
    }

    /// Synthetic stack of 2^14 F64 words: three aligned 2^12-word columns
    /// plus a q_pkd region (a random bit-witness packed by pack) at the
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
        let mut rng = Rng::new(seed);

        // Three random columns, the packed bit-witness region, then filler.
        let mut stack: Vec<F64> = (0..3 * col_len).map(|_| F64(rng.next_u64())).collect();
        let bits = rng.bits(1usize << (qpkd_vars + LOG_PACKING));
        stack.extend(pack_witness(&bits, qpkd_vars + LOG_PACKING));
        while stack.len() < 1 << log_n {
            stack.push(F64(rng.next_u64()));
        }
        assert_eq!(stack.len(), 1 << log_n);

        // One point claim per column, at a random E point.
        let mut point_claims: Vec<StackClaim> = (0..3)
            .map(|c| {
                let offset = c * col_len;
                let low_point = rng.ext_vec(col_vars);
                let eq = build_eq_table_ext(&low_point);
                let value = inner_product_base_ext(&stack[offset..offset + col_len], &eq);
                StackClaim::Point {
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
            let point = rng.ext_vec(qpkd_vars - stride_log);
            let eq = build_eq_table_ext(&point);
            let mut value = F192::ZERO;
            for (j, &ej) in eq.iter().enumerate() {
                value += ej.mul_base(stack[qpkd_offset + slot + (j << stride_log)]);
            }
            point_claims.push(StackClaim::Strided {
                offset: qpkd_offset,
                slot,
                stride_log,
                point,
                value,
            });
        }

        // One ring-switched claim on q_pkd (plain eq prefix weights).
        let qpkd = &stack[qpkd_offset..qpkd_offset + (1 << qpkd_vars)];
        let r_prefix = rng.ext_vec(LOG_PACKING);
        let prefix_weights = build_eq_table_ext(&r_prefix);
        let suffix_point = rng.ext_vec(qpkd_vars);
        let s_hat_v = fold_1b_rows(qpkd, &build_eq_table_ext(&suffix_point));
        let value = claim_check(&prefix_weights, &s_hat_v);
        let ring = RingSwitchOpen {
            offset: qpkd_offset,
            qpkd_vars,
            claims: vec![RingSwitchClaim {
                prefix_weights,
                suffix_point,
                value,
                // Exercise the fold path (no precompute).
                s_hat_v: None,
            }],
        };

        let (pc, vc) = test_configs_for(log_n);
        // Pin the intended residual regime: the residual cube must sit
        // entirely above the q_pkd coords, with at least one selector coord
        // covered by ris (the E-valued sel prefix) and the rest by y bits.
        let yr_log_n = log_n - pc.initial_k - pc.level_ks.iter().sum::<usize>();
        assert!(
            qpkd_vars < log_n - yr_log_n,
            "test shape must keep the residual cube above q_pkd (yr_log_n = {yr_log_n})"
        );
        let (cm, pd) = commit(&stack, pc.initial_k, pc.log_inv_rates[0]);
        let mut ch = Sponge::new(DOMAIN, &[]);
        let proof = open_batch_mixed_whir_stacked(&mut ch, &stack, &pd, &pc, &point_claims, &ring);

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
        point_claims: &[StackClaim],
        ring_claims: &[RingSwitchClaim],
        proof: &BatchOpeningProof,
    ) -> bool {
        let ring = RingSwitchVerify {
            offset: inst.ring.offset,
            qpkd_vars: inst.ring.qpkd_vars,
            claims: ring_claims.to_vec(),
        };
        let mut ch = Sponge::new(DOMAIN, &[]);
        verify_opening_batch_mixed_whir_stacked(&mut ch, &inst.vc, inst.log_n, &inst.root, point_claims, &ring, proof)
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
        if let StackClaim::Point { value, .. } = &mut bad_points[0] {
            *value += F192::ONE;
        } else {
            unreachable!()
        }
        assert!(
            !verify_instance(&inst, &bad_points, &inst.ring.claims, &inst.proof),
            "tampered Point value accepted"
        );

        // Wrong strided-claim value.
        let mut bad_points = inst.point_claims.clone();
        if let StackClaim::Strided { value, .. } = &mut bad_points[3] {
            *value += F192::ONE;
        } else {
            unreachable!()
        }
        assert!(
            !verify_instance(&inst, &bad_points, &inst.ring.claims, &inst.proof),
            "tampered Strided value accepted"
        );

        // Wrong ring-switched claim value: rejected by the claim check.
        let mut bad_ring = inst.ring.claims.clone();
        bad_ring[0].value += F192::ONE;
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

        // Tampered WHIR proof scalars.
        let mut bad_proof = inst.proof.clone();
        bad_proof.whir.sumcheck_transcript[0].u_0.c0 ^= 1;
        assert!(
            !verify_instance(&inst, &inst.point_claims, &inst.ring.claims, &bad_proof),
            "tampered sumcheck u_0 accepted"
        );
        let mut bad_proof = inst.proof.clone();
        bad_proof.whir.final_proof.yr[0].c1 ^= 1;
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
        let mut rng = Rng::new(3);

        let mut stack: Vec<F64> = (0..1usize << 13).map(|_| F64(rng.next_u64())).collect();
        let bits = rng.bits(1usize << (qpkd_vars + LOG_PACKING));
        stack.extend(pack_witness(&bits, qpkd_vars + LOG_PACKING));
        assert_eq!(stack.len(), 1 << log_n);

        // One point claim on the low column.
        let low_point = rng.ext_vec(12);
        let eq = build_eq_table_ext(&low_point);
        let value = inner_product_base_ext(&stack[..1 << 12], &eq);
        let point_claims = vec![StackClaim::Point {
            offset: 0,
            low_point,
            value,
        }];

        // One ring-switched claim on the wide q_pkd.
        let qpkd = &stack[qpkd_offset..];
        let r_prefix = rng.ext_vec(LOG_PACKING);
        let prefix_weights = build_eq_table_ext(&r_prefix);
        let suffix_point = rng.ext_vec(qpkd_vars);
        let s_hat_v = fold_1b_rows(qpkd, &build_eq_table_ext(&suffix_point));
        let rs_value = claim_check(&prefix_weights, &s_hat_v);
        let claims = vec![RingSwitchClaim {
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

        let (cm, pd) = commit(&stack, pc.initial_k, pc.log_inv_rates[0]);
        let ring = RingSwitchOpen {
            offset: qpkd_offset,
            qpkd_vars,
            claims,
        };
        let mut ch = Sponge::new(DOMAIN, &[]);
        let proof = open_batch_mixed_whir_stacked(&mut ch, &stack, &pd, &pc, &point_claims, &ring);

        let ring_v = RingSwitchVerify {
            offset: qpkd_offset,
            qpkd_vars,
            claims: ring.claims.clone(),
        };
        let mut ch = Sponge::new(DOMAIN, &[]);
        assert!(
            verify_opening_batch_mixed_whir_stacked(&mut ch, &vc, log_n, &cm.root, &point_claims, &ring_v, &proof,)
                .is_some(),
            "honest crossing-regime opening rejected"
        );

        // And the crossing-regime ring claim is still bound: flip its value.
        let mut bad_ring = ring_v;
        bad_ring.claims[0].value += F192::ONE;
        let mut ch = Sponge::new(DOMAIN, &[]);
        assert!(
            verify_opening_batch_mixed_whir_stacked(&mut ch, &vc, log_n, &cm.root, &point_claims, &bad_ring, &proof,)
                .is_none(),
            "tampered crossing-regime ring value accepted"
        );
    }
}
