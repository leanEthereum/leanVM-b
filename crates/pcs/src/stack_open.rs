// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Stacked batch-mixed opening for the F64-committed PCS.
//!
//! The committed witness is a stack of `2^log_n` [`F64`] words (committed via
//! [`super::ligerito::commit`]), and one Ligerito run discharges
//!
//! - **point claims** ([`StackClaim`]): multilinear evaluations of sub-slices
//!   of the stack. A `Jagged` claim covers the tight, arbitrary-height
//!   interval `[offset, offset + height)` and weights it with the
//!   branching-program indicator of [`super::jagged`]; a `Point` claim's
//!   weight is `eq(low_point, .)` on the aligned slice
//!   `[offset, offset + 2^|low_point|)`; a `Strided` claim freezes the low
//!   `stride_log` in-block coords to `slot`'s bits, so its weight is nonzero
//!   only at `offset + slot + j * 2^stride_log`,
//! - **ring-switched claims** ([`RingSwitchOpen`]): bit-MLE evaluation claims
//!   on the packed sub-block `q_pkd = stack[offset .. offset + 2^qpkd_vars]`,
//!   reduced per claim by [`super::ring_switch::prove_observe`] and the
//!   deferred finish path to an inner-product
//!   claim `<q_pkd, rs_eq_ind> = sumcheck_claim` against the transparent
//!   E-valued weight `rs_eq_ind`.
//!
//! All claims are gamma-folded into ONE combined weight `b_stack` over the
//! whole stack plus one `target`, then proved by
//! [`super::ligerito::recursive_prover_with_basis`]. The verifier replays
//! the ring-switch reductions succinctly ([`super::ring_switch::verify_observe`]
//! and [`super::ring_switch::verify_finish`], with no dense `rs_eq_ind`) and drives
//! [`super::ligerito::recursive_verifier_with_basis_succinct`] with a
//! residual evaluator that reconstructs `MLE(b_stack)` at each residual point
//! in closed form: eq / stride-selector products for the point claims, and the
//! DP24 tensor-algebra prefix + binary-suffix finish
//! ([`super::ring_switch::eval_rs_eq_prefix`] /
//! [`super::ring_switch::eval_rs_eq_finish_from_prefix_binary_q`]) for the
//! ring-switched part.
//!
//! ## Transcript order (identical on both sides)
//!
//! label -> per ring-switched claim ([`super::ring_switch`]'s own label +
//! `s_hat_v_i` observed + shared `rho` sampled) -> gamma_rs (one per claim) ->
//! per point claim (label + value observed) -> ONE gamma_pd -> Ligerito, with
//! domain-separated labels for every phase.
//!
//! The point claims take consecutive POWERS of that single `gamma_pd`
//! (`geometric_claim_weights`) rather than independent challenges. The
//! ordering puts a row-major block's columns on adjacent exponents, so the
//! verifier collapses the whole block into one indicator evaluation; the cost
//! is at most `claims.len() / |E|` soundness, negligible against a 192-bit
//! `E`.
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
use fiat_shamir::Sponge;
use primitives::field::{F64, F192};
use serde::{Deserialize, Serialize};

use super::ligerito::{
    LigeritoProof, ProverData, build_eq_table_ext, build_eq_table_ext_parallel, recursive_prover_with_basis,
    recursive_verifier_with_basis_succinct_with_squeezes,
};
use super::ligerito::{ProverConfig, VerifierConfig};
use super::pack::PACKING_WIDTH;
use super::ring_switch::{self, RingSwitchProof, eval_rs_eq_finish_from_prefix_binary_q, eval_rs_eq_prefix};
use super::tensor_algebra::TensorAlgebraE;

// ---------------------------------------------------------------------------
// Sponge helpers (same convention as ligerito): E-scalars straight off
// the shared Fiat-Shamir sponge.
// Sponge scalars ARE E-elements; the helpers keep call sites uniform. Every
// 24-byte pattern is a valid F192, and observing ferries all three limbs
// through the transcript.
// ---------------------------------------------------------------------------

fn sample_ext_vec(sponge: &mut Sponge, n: usize) -> Vec<F192> {
    sponge.sample_vec(n)
}

#[inline]
fn observe_ext(sponge: &mut Sponge, e: F192) {
    sponge.observe(e);
}

/// Multilinear eq at two E-points (char 2: each factor is `1 + r_i + x_i`).
/// Mirror of `zerocheck::multilinear::eq_eval` retyped to the tower.
fn eq_eval_ext(r: &[F192], x: &[F192]) -> F192 {
    assert_eq!(r.len(), x.len());
    let mut acc = F192::ONE;
    for (&a, &b) in r.iter().zip(x.iter()) {
        acc *= F192::ONE + a + b;
    }
    acc
}

// ---------------------------------------------------------------------------
// Claim types
// ---------------------------------------------------------------------------

/// An owning point claim folded into the stacked mixed opening.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StackClaim {
    /// A column occupying the arbitrary interval `[offset, offset + height)`
    /// of the dense commitment (the Jagged layout: columns are packed tightly
    /// rather than padded up to aligned power-of-two blocks). `row_point`
    /// evaluates the column after its real prefix has been zero-padded to
    /// `2^|row_point|` rows. The weight is the width-four branching-program
    /// indicator of [`super::jagged`], supported only on the real prefix.
    Jagged {
        offset: usize,
        height: usize,
        /// Low coordinates selecting a column inside a row-major block; zero
        /// for a singleton column.
        selector_len: usize,
        row_point: Vec<F192>,
        value: F192,
    },
    /// `eq(low_point, .)` on the aligned slice
    /// `[offset, offset + 2^|low_point|)`; `offset` must be a multiple of
    /// `2^|low_point|`. (Upstream calls this variant `Slot`.)
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
            StackClaim::Jagged { value, .. } | StackClaim::Point { value, .. } | StackClaim::Strided { value, .. } => {
                *value
            }
        }
    }

    /// The claim's evaluation point, which doubles as the cache key for the
    /// shared equality tensors built in [`fold_stacked_point_claims`].
    #[inline]
    fn point(&self) -> &[F192] {
        match self {
            StackClaim::Jagged { row_point, .. } => row_point,
            StackClaim::Point { low_point, .. } => low_point,
            StackClaim::Strided { point, .. } => point,
        }
    }
}

/// A run of Jagged claims that together cover every column of one row-major
/// block, assigned consecutive powers of the batching challenge in selector
/// order so their weighted sum collapses to a single indicator evaluation.
#[derive(Debug)]
struct JaggedClaimBatch {
    members: Vec<usize>,
    offset: usize,
    height: usize,
    selector_len: usize,
    row_weights: Vec<[F192; 2]>,
    scale: F192,
}

/// Assign the powers of one batching challenge so that complete row-major
/// blocks receive consecutive exponents in selector order. Their weighted
/// residual evaluations then collapse to one Basic-Jagged evaluation:
/// `sum_c gamma^(base+c) eq(z,c) = gamma^base * D * eq(z_gamma, c)`, with
/// `z_gamma[b] = gamma^(2^b) / (1 + gamma^(2^b))` and
/// `D = prod_b (1 + gamma^(2^b))`. Passing the unnormalized pairs
/// `(1, gamma^(2^b))` straight to
/// [`super::jagged::indicator_eval_with_row_weights`] absorbs `D` and avoids
/// the inversions entirely.
///
/// Claims that do not complete a block keep a plain distinct power. Using
/// powers rather than independent challenges costs at most
/// `claims.len() / |E|` soundness, negligible against a 192-bit `E`.
fn geometric_claim_weights(claims: &[StackClaim], gamma: F192) -> (Vec<F192>, Vec<JaggedClaimBatch>) {
    let n = claims.len();
    let mut rank = vec![usize::MAX; n];
    let mut batch_members: Vec<(Vec<usize>, usize, usize, usize)> = Vec::new();
    let mut next_rank = 0usize;

    for i in 0..n {
        if rank[i] != usize::MAX {
            continue;
        }
        let StackClaim::Jagged {
            offset,
            height,
            selector_len,
            row_point,
            ..
        } = &claims[i]
        else {
            rank[i] = next_rank;
            next_rank += 1;
            continue;
        };
        if *selector_len == 0 {
            rank[i] = next_rank;
            next_rank += 1;
            continue;
        }
        let width = 1usize << selector_len;
        let mut by_slot = vec![None; width];
        for (j, other) in claims.iter().enumerate().skip(i) {
            if rank[j] != usize::MAX {
                continue;
            }
            let StackClaim::Jagged {
                offset: other_offset,
                height: other_height,
                selector_len: other_selector_len,
                row_point: other_point,
                ..
            } = other
            else {
                continue;
            };
            if other_offset != offset
                || other_height != height
                || other_selector_len != selector_len
                || other_point[*selector_len..] != row_point[*selector_len..]
            {
                continue;
            }
            // Only a Boolean selector prefix can be folded into the geometric
            // block; anything else keeps its own power.
            let mut slot = 0usize;
            let mut boolean = true;
            for (bit, &x) in other_point[..*selector_len].iter().enumerate() {
                if x == F192::ONE {
                    slot |= 1 << bit;
                } else if x != F192::ZERO {
                    boolean = false;
                    break;
                }
            }
            if boolean && by_slot[slot].is_none() {
                by_slot[slot] = Some(j);
            }
        }
        if by_slot.iter().all(Option::is_some) {
            let members: Vec<usize> = by_slot.into_iter().map(Option::unwrap).collect();
            for (slot, &j) in members.iter().enumerate() {
                rank[j] = next_rank + slot;
            }
            batch_members.push((members, *offset, *height, *selector_len));
            next_rank += width;
        } else {
            rank[i] = next_rank;
            next_rank += 1;
        }
    }
    assert_eq!(next_rank, n, "geometric ranking must be a permutation");

    let mut powers = vec![F192::ONE; n];
    for k in 1..n {
        powers[k] = powers[k - 1] * gamma;
    }
    let weights: Vec<F192> = rank.iter().map(|&r| powers[r]).collect();
    let mut batches = Vec::new();
    for (members, offset, height, selector_len) in batch_members {
        let scale = powers[rank[members[0]]];
        let StackClaim::Jagged { row_point, .. } = &claims[members[0]] else {
            unreachable!("batch members are Jagged claims")
        };
        let mut a = gamma;
        let mut row_weights = Vec::with_capacity(row_point.len());
        for _ in 0..selector_len {
            row_weights.push([F192::ONE, a]);
            a *= a;
        }
        row_weights.extend(row_point[selector_len..].iter().map(|&r| [F192::ONE + r, r]));
        batches.push(JaggedClaimBatch {
            members,
            offset,
            height,
            selector_len,
            row_weights,
            scale,
        });
    }
    (weights, batches)
}

/// One ring-switched evaluation claim on the q_pkd sub-block: the consumed
/// claim is `value == sum_i prefix_weights[i] * s_hat_v[i]` where `s_hat_v`
/// are the 64 bit-slice MLEs of q_pkd at `suffix_point` (see
/// [`super::ring_switch`]). `prefix_weights` has [`PACKING_WIDTH`] = 64
/// entries ([`super::ring_switch::eq_prefix_weights`] for a plain point
/// claim; phi_8 Lagrange weights for flock's
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
/// claim plus one Ligerito proof over the combined claim.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BatchOpeningProof {
    pub ring_switches: Vec<RingSwitchProof>,
    pub ligerito: LigeritoProof,
}

/// What the stacked-opening verifier hands back on accept—the recursion
/// harness's hook for the Ligerito fold/query data.
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
/// and sampled `gammas` in transcript order). A `Jagged` claim scatters its
/// row eq over the tight interval `[offset, offset + height)`, a `Point`
/// builds eq over ONLY its aligned slice, and a `Strided` scatters the eq of
/// its high coords at the slot's stride. All scatter with `+=`, so
/// overlapping slices accumulate correctly and the OUTER loop stays serial
/// (several bus claims can land on one column region); parallelism lives
/// inside each claim's slice add. Small slices stay fully serial: with many
/// tiny point claims, rayon dispatch would cost more than the fold itself.
///
/// Equality tensors are built once per DISTINCT point and shared. Under the
/// Jagged layout each table contributes one claim per column and they all
/// share that table's challenge point, so the cache turns what was one eq
/// build per column into one per table. That replaces the previous
/// gamma-seeded build ([`build_eq_table_ext_seeded_into`], which baked a
/// single claim's gamma into the tensor and so could not be shared); the
/// scatter multiplies by gamma instead, which is exact-field-equal, so
/// `b_stack`'s bytes and hence the proof are unchanged.
fn fold_stacked_point_claims(
    b_stack: &mut [F192],
    target: &mut F192,
    claims: &[StackClaim],
    gammas: &[F192],
    jagged_batches: &[JaggedClaimBatch],
) {
    use rayon::prelude::*;
    const PAR_FOLD_THRESHOLD: usize = 1 << 14;
    const PAR_EQ_THRESHOLD: usize = 14;

    // Claims covered by a geometric block fold are handled together below.
    let mut grouped = vec![false; claims.len()];
    for batch in jagged_batches {
        for &member in &batch.members {
            grouped[member] = true;
        }
    }

    let build_eq = |point: &[F192]| -> Vec<F192> {
        if point.len() < PAR_EQ_THRESHOLD {
            build_eq_table_ext(point)
        } else {
            build_eq_table_ext_parallel(point)
        }
    };
    let mut eq_tables: Vec<(&[F192], Vec<F192>)> = Vec::new();
    for (j, claim) in claims.iter().enumerate() {
        if grouped[j] {
            continue;
        }
        let point = claim.point();
        if eq_tables.iter().any(|(cached, _)| *cached == point) {
            continue;
        }
        let eq = build_eq(point);
        eq_tables.push((point, eq));
    }
    for batch in jagged_batches {
        let point = &claims[batch.members[0]].point()[batch.selector_len..];
        if !eq_tables.iter().any(|(cached, _)| *cached == point) {
            let eq = build_eq(point);
            eq_tables.push((point, eq));
        }
    }
    let eq_for = |point: &[F192]| -> &[F192] {
        eq_tables
            .iter()
            .find(|(cached, _)| *cached == point)
            .map(|(_, eq)| eq.as_slice())
            .expect("claim equality tensor was cached")
    };
    for (claim, g) in claims.iter().zip(gammas.iter()) {
        *target += *g * claim.value();
    }

    // Whole row-major blocks: one eq over the shared row point, with each
    // column's own power applied per lane.
    for batch in jagged_batches {
        let width = 1usize << batch.selector_len;
        let rows = batch.height / width;
        let eq = eq_for(&claims[batch.members[0]].point()[batch.selector_len..]);
        let slot_weights: Vec<F192> = batch.members.iter().map(|&member| gammas[member]).collect();
        let dst = &mut b_stack[batch.offset..batch.offset + batch.height];
        if dst.len() >= PAR_FOLD_THRESHOLD {
            dst.par_chunks_mut(width)
                .zip(eq[..rows].par_iter())
                .for_each(|(row, &er)| {
                    for (cell, &weight) in row.iter_mut().zip(&slot_weights) {
                        *cell += weight * er;
                    }
                });
        } else {
            for (row, &er) in dst.chunks_mut(width).zip(&eq[..rows]) {
                for (cell, &weight) in row.iter_mut().zip(&slot_weights) {
                    *cell += weight * er;
                }
            }
        }
    }

    for (j, (claim, g)) in claims.iter().zip(gammas.iter()).enumerate() {
        if grouped[j] {
            continue;
        }
        let g = *g;
        match claim {
            StackClaim::Jagged {
                offset,
                height,
                row_point,
                ..
            } => {
                if *height != 0 {
                    let eq = eq_for(row_point);
                    let dst = &mut b_stack[*offset..*offset + *height];
                    if *height < PAR_FOLD_THRESHOLD {
                        for (bi, ei) in dst.iter_mut().zip(eq.iter()) {
                            *bi += g * *ei;
                        }
                    } else {
                        dst.par_iter_mut()
                            .zip(eq[..*height].par_iter())
                            .for_each(|(bi, ei)| *bi += g * *ei);
                    }
                }
            }
            StackClaim::Point { offset, low_point, .. } => {
                let len = 1usize << low_point.len();
                assert!(
                    offset % len == 0,
                    "StackClaim::Point: offset must be 2^|low_point|-aligned"
                );
                let eq = eq_for(low_point);
                let dst = &mut b_stack[*offset..*offset + len];
                if len < PAR_FOLD_THRESHOLD {
                    for (bi, ei) in dst.iter_mut().zip(eq.iter()) {
                        *bi += g * *ei;
                    }
                } else {
                    dst.par_iter_mut()
                        .zip(eq.par_iter())
                        .for_each(|(bi, ei)| *bi += g * *ei);
                }
            }
            StackClaim::Strided {
                offset,
                slot,
                stride_log,
                point,
                ..
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
                let eq = eq_for(point);
                for (j, &ej) in eq.iter().enumerate() {
                    b_stack[base + j * stride] += g * ej;
                }
            }
        }
    }
}

/// The claim's weight `eq(full claim point, x)` at an arbitrary point `x` of
/// the full stack cube. A `Point`'s full point is `[low_point, sel_bits]`, a
/// `Strided`'s is `[slot_bits, point, sel_bits]`; neither is materialized.
/// Mirror of the extension-field `stack_claim_eq_at`.
fn stack_claim_eq_at(claim: &StackClaim, x: &[F192]) -> F192 {
    match claim {
        StackClaim::Jagged {
            offset,
            height,
            row_point,
            ..
        } => super::jagged::indicator_eval(row_point, *offset, *offset + *height, x),
        StackClaim::Point { offset, low_point, .. } => {
            let n = low_point.len();
            let mut e = eq_eval_ext(low_point, &x[..n]);
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
            e *= eq_eval_ext(point, &x[*stride_log..block_vars]);
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
/// evaluation AND the ring-switched q_pkd claims (`ring`) in ONE Ligerito
/// run, reusing the caller's [`super::ligerito::commit`] output as L0.
///
/// `stack` is the committed message (the caller retains it; it is not stored
/// in [`ProverData`]); `config.initial_k` / `config.log_inv_rates[0]` must
/// match the commit's `log_batch_size` / `log_inv_rate` (enforced by shape
/// asserts inside the Ligerito prover).
pub fn open_batch_mixed_ligerito_stacked(
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
    // Optional phase timing, answering to the same env var as the Ligerito
    // prover/commit tracing (one env lookup per open, no work when unset).
    let trace = std::env::var_os("LIGERITO_TRACE").is_some();
    let mut t = std::time::Instant::now();
    let mark = |label: &str, t: &mut std::time::Instant| {
        if trace {
            eprintln!("[stack-open-k] {label}: {:7.2} ms", t.elapsed().as_secs_f64() * 1e3);
        }
        *t = std::time::Instant::now();
    };

    // 1. Ring-switch reduction: observe EVERY claim's s_hat_v first, then sample
    //    ONE shared rho (matches the recursion guest), then
    //    finish each claim's sumcheck/weight against the shared powers.
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
    let rho = sponge.sample();
    let coordinate_weights = ring_switch::build_coordinate_weights(rho);
    // Per-claim batching gammas, sampled AFTER all ring-switch messages are
    // bound (mirror of the extension-field layer's gamma_rs pattern).
    let gammas_rs = sample_ext_vec(sponge, ring.claims.len());
    let rs_outputs: Vec<_> = rs_states
        .into_iter()
        .zip(gammas_rs)
        .map(|(state, gamma)| ring_switch::prove_finish_deferred(state, &coordinate_weights, gamma))
        .collect();
    mark("ring-switch proves", &mut t);

    // 2. Observe point-claim values + derive their gammas (Schwartz-Zippel
    //    sound: gamma is sampled after all values are observed). ONE challenge
    //    suffices: the claims take its consecutive powers, ordered so that a
    //    complete row-major block's columns are adjacent and their weighted
    //    indicators collapse to a single Jagged evaluation for the verifier.
    for claim in point_claims {
        observe_ext(sponge, claim.value());
    }
    let gamma_pd = sponge.sample();
    let (gammas_pd, jagged_batches) = geometric_claim_weights(point_claims, gamma_pd);

    // 3. Combined target and lifted stack weight b_stack: the gamma-weighted
    //    rs_eq_ind sum scattered at the q_pkd slice, plus the point-claim
    //    eq tensors scattered at their offsets.
    let mut target = rs_outputs
        .iter()
        .fold(F192::ZERO, |acc, out| acc + out.batched_sumcheck_claim);
    // Parallel first-touch wins for the tower stack: its many scattered point
    // claims otherwise fault pages one claim at a time.
    let mut b_stack = primitives::alloc_uninit(stack.len());
    {
        use rayon::prelude::*;
        const ZERO_CHUNK: usize = 1 << 16;
        b_stack.par_chunks_mut(ZERO_CHUNK).for_each(|chunk| {
            for value in chunk {
                value.write(F192::ZERO);
            }
        });
    }
    // SAFETY: the parallel fill initializes every stack weight to zero.
    let mut b_stack = unsafe { primitives::assume_init(b_stack) };
    mark("b_stack zero fill", &mut t);
    ring_switch::combine_deferred_into(&rs_outputs, &mut b_stack[ring.offset..ring.offset + qpkd_len]);
    mark("rs_eq_ind scatter", &mut t);
    fold_stacked_point_claims(&mut b_stack, &mut target, point_claims, &gammas_pd, &jagged_batches);
    mark("point-claim folds", &mut t);

    // 4. One Ligerito over the full stack against the combined claim (the
    //    stack is borrowed by the prover; no copy).
    let ligerito = recursive_prover_with_basis(
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
        ligerito,
    }
}

// ---------------------------------------------------------------------------
// Verifier
// ---------------------------------------------------------------------------

/// Verifier mirror of [`open_batch_mixed_ligerito_stacked`]: replay the
/// ring-switch reductions succinctly, recompute the combined target, then
/// drive the succinct Ligerito verifier with a residual evaluator for the
/// lifted weight. `log_n` is the committed stack's log size in F64 words and
/// `root` the L0 commitment root ([`super::ligerito::Commitment::root`]).
///
/// Residual evaluator: at each residual point `x = ris ++ y_bits` the
/// ring-switch part is `eq(sel, x_hi) * sum_i gamma_i * MLE(rs_eq_ind_i)(x_lo)`
/// with `x` split at `qpkd_vars`. The tensor-algebra prefix over the `ris`
/// portion of `x_lo` is shared across all `2^yr_log_n` positions and finished
/// per position with the binary suffix; the `y` coords that land on selector
/// bits are binary, so they contribute an exact indicator (only matching `y`
/// positions get a nonzero ring-switch part, which also caps the number of
/// tensor finishes at `2^(qpkd coords covered by y)`). Point-claim weights
/// are evaluated per position in closed form via `stack_claim_eq_at`.
pub fn verify_opening_batch_mixed_ligerito_stacked(
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

    // 1. Ring-switch succinct verify: observe EVERY claim's s_hat_v first, then
    //    sample ONE shared rho, then finish each claim (mirrors the prover
    //    and the recursion guest).
    for (claim, rs_proof) in ring.claims.iter().zip(proof.ring_switches.iter()) {
        if ring_switch::verify_observe(claim.value, &claim.prefix_weights, rs_proof, sponge).is_err() {
            return None;
        }
    }
    let rho = sponge.sample();
    let coordinate_weights = ring_switch::build_coordinate_weights(rho);
    let rs_outputs: Vec<_> = proof
        .ring_switches
        .iter()
        .map(|rs_proof| ring_switch::verify_finish(rs_proof, &coordinate_weights))
        .collect();
    let gammas_rs = sample_ext_vec(sponge, n_rs);
    let mut target = F192::ZERO;
    for (out, g) in rs_outputs.iter().zip(gammas_rs.iter()) {
        target += *g * out.sumcheck_claim;
    }

    // 2. Point-claim values + gammas; fold into the target. Mirrors the
    //    prover: one sample, then consecutive powers assigned by
    //    [`geometric_claim_weights`].
    for claim in point_claims {
        observe_ext(sponge, claim.value());
    }
    let gamma_pd = sponge.sample();
    let (gammas_pd, jagged_batches) = geometric_claim_weights(point_claims, gamma_pd);
    for (claim, g) in point_claims.iter().zip(gammas_pd.iter()) {
        target += *g * claim.value();
    }
    let mut jagged_grouped = vec![false; point_claims.len()];
    for batch in &jagged_batches {
        for &member in &batch.members {
            jagged_grouped[member] = true;
        }
    }

    // 3. Residual evaluator of the lifted weight, called once by the succinct
    //    Ligerito verifier with the full folded `ris` and the residual cube
    //    log-size; returns b's MLE at `ris ++ y_bits` for every y.
    let sel = ring.offset >> qpkd_vars;
    let eval_b_residual = |ris: &[F192], yr_log_n: usize| -> Vec<F192> {
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
            .map(|c| eval_rs_eq_prefix(&c.suffix_point, &ris[..split]))
            .collect();

        // Selector eq over the ris coords above the q_pkd slice (E-valued
        // part; the y-covered selector coords are handled per position).
        let mut sel_prefix = F192::ONE;
        for (k, &xi) in ris[split..].iter().enumerate() {
            sel_prefix *= if (sel >> k) & 1 == 1 { xi } else { F192::ONE + xi };
        }

        (0..1usize << yr_log_n)
            .into_par_iter()
            .map(|y| {
                // Full point x = ris ++ y_bits for the point-claim weights.
                let mut x = Vec::with_capacity(n_ris + yr_log_n);
                x.extend_from_slice(ris);
                for k in 0..yr_log_n {
                    x.push(if (y >> k) & 1 == 1 { F192::ONE } else { F192::ZERO });
                }

                // Selector coords covered by y are binary: an indicator.
                let mut sel_ok = true;
                for k in n_qpkd_from_y..yr_log_n {
                    if (sel >> (n_ris + k - qpkd_vars)) & 1 != (y >> k) & 1 {
                        sel_ok = false;
                        break;
                    }
                }
                let mut acc = F192::ZERO;
                if sel_ok {
                    // Finish each claim's tensor prefix with the binary
                    // query suffix (the q_pkd coords covered by y).
                    let y_low = (y & ((1usize << n_qpkd_from_y) - 1)) as u32;
                    let mut rs_part = F192::ZERO;
                    for ((claim, prefix), (g, out)) in ring
                        .claims
                        .iter()
                        .zip(rs_prefixes.iter())
                        .zip(gammas_rs.iter().zip(rs_outputs.iter()))
                    {
                        rs_part += *g
                            * eval_rs_eq_finish_from_prefix_binary_q(
                                prefix,
                                &claim.suffix_point[split..],
                                y_low,
                                &out.coordinate_weights,
                            );
                    }
                    acc = rs_part * sel_prefix;
                }
                // A complete row-major block is ONE indicator evaluation with
                // the unnormalized geometric selector weights, instead of one
                // branching-program run per physical column.
                for batch in &jagged_batches {
                    acc += batch.scale
                        * super::jagged::indicator_eval_with_row_weights(
                            &batch.row_weights,
                            batch.offset,
                            batch.offset + batch.height,
                            &x,
                        );
                }
                for (j, (claim, g)) in point_claims.iter().zip(gammas_pd.iter()).enumerate() {
                    if !jagged_grouped[j] {
                        acc += *g * stack_claim_eq_at(claim, &x);
                    }
                }
                acc
            })
            .collect()
    };

    let mut query_squeezes: Vec<Vec<F192>> = Vec::new();
    let ok = recursive_verifier_with_basis_succinct_with_squeezes(
        config,
        &proof.ligerito,
        log_n,
        target,
        root,
        eval_b_residual,
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
    use crate::ligerito::{commit, configs_for, inner_product_base_ext};
    use crate::ligerito::{default_config, default_verifier_config};
    use crate::pack::{LOG_PACKING, pack_witness};
    use crate::ring_switch::{claim_check, eq_prefix_weights, fold_1b_rows};

    fn splitmix64(state: &mut u64) -> u64 {
        *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = *state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn rand_ext(s: &mut u64) -> F192 {
        F192::new(splitmix64(s), splitmix64(s), splitmix64(s))
    }

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
        let mut s = seed;

        // Three random columns, the packed bit-witness region, then filler.
        let mut stack: Vec<F64> = (0..3 * col_len).map(|_| F64(splitmix64(&mut s))).collect();
        let bits: Vec<bool> = (0..1usize << (qpkd_vars + LOG_PACKING))
            .map(|_| splitmix64(&mut s) & 1 == 1)
            .collect();
        stack.extend(pack_witness(&bits, qpkd_vars + LOG_PACKING));
        while stack.len() < 1 << log_n {
            stack.push(F64(splitmix64(&mut s)));
        }
        assert_eq!(stack.len(), 1 << log_n);

        // One point claim per column, at a random E point.
        let mut point_claims: Vec<StackClaim> = (0..3)
            .map(|c| {
                let offset = c * col_len;
                let low_point: Vec<F192> = (0..col_vars).map(|_| rand_ext(&mut s)).collect();
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
            let point: Vec<F192> = (0..qpkd_vars - stride_log).map(|_| rand_ext(&mut s)).collect();
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
        let r_prefix: Vec<F192> = (0..LOG_PACKING).map(|_| rand_ext(&mut s)).collect();
        let prefix_weights = eq_prefix_weights(&r_prefix);
        let suffix_point: Vec<F192> = (0..qpkd_vars).map(|_| rand_ext(&mut s)).collect();
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
        let proof = open_batch_mixed_ligerito_stacked(&mut ch, &stack, &pd, &pc, &point_claims, &ring);

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
        verify_opening_batch_mixed_ligerito_stacked(
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
        let bits: Vec<bool> = (0..1usize << (qpkd_vars + LOG_PACKING))
            .map(|_| splitmix64(&mut s) & 1 == 1)
            .collect();
        stack.extend(pack_witness(&bits, qpkd_vars + LOG_PACKING));
        assert_eq!(stack.len(), 1 << log_n);

        // One point claim on the low column.
        let low_point: Vec<F192> = (0..12).map(|_| rand_ext(&mut s)).collect();
        let eq = build_eq_table_ext(&low_point);
        let value = inner_product_base_ext(&stack[..1 << 12], &eq);
        let point_claims = vec![StackClaim::Point {
            offset: 0,
            low_point,
            value,
        }];

        // One ring-switched claim on the wide q_pkd.
        let qpkd = &stack[qpkd_offset..];
        let r_prefix: Vec<F192> = (0..LOG_PACKING).map(|_| rand_ext(&mut s)).collect();
        let prefix_weights = eq_prefix_weights(&r_prefix);
        let suffix_point: Vec<F192> = (0..qpkd_vars).map(|_| rand_ext(&mut s)).collect();
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
        let proof = open_batch_mixed_ligerito_stacked(&mut ch, &stack, &pd, &pc, &point_claims, &ring);

        let ring_v = RingSwitchVerify {
            offset: qpkd_offset,
            qpkd_vars,
            claims: ring.claims.clone(),
        };
        let mut ch = Sponge::new(DOMAIN, &[]);
        assert!(
            verify_opening_batch_mixed_ligerito_stacked(&mut ch, &vc, log_n, &cm.root, &point_claims, &ring_v, &proof,)
                .is_some(),
            "honest crossing-regime opening rejected"
        );

        // And the crossing-regime ring claim is still bound: flip its value.
        let mut bad_ring = ring_v;
        bad_ring.claims[0].value += F192::ONE;
        let mut ch = Sponge::new(DOMAIN, &[]);
        assert!(
            verify_opening_batch_mixed_ligerito_stacked(
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

#[cfg(test)]
mod jagged_batch_tests {
    use super::*;

    fn f(x: u64) -> F192 {
        F192::new(x, x.rotate_left(23), x.rotate_left(41))
    }

    /// The geometric block fold must agree, both in the dense `b_stack` it
    /// scatters and in the single batched indicator the verifier evaluates,
    /// with treating each column of the block as an independent Jagged claim.
    #[test]
    fn geometric_batch_matches_individual_jagged_claims() {
        let row = [f(3), f(5), f(7)];
        // Deliberately shuffle the four selector slots: batching must assign
        // powers by Boolean slot, not by input order.
        let block_point = |b0: F192, b1: F192| vec![b0, b1, row[0], row[1], row[2]];
        let singleton_point = vec![f(11), f(13), f(17), f(19), f(23)];
        let jagged = |row_point: Vec<F192>, offset, height, selector_len, value| StackClaim::Jagged {
            offset,
            height,
            selector_len,
            row_point,
            value,
        };
        let claims = [
            jagged(block_point(F192::ONE, F192::ZERO), 3, 20, 2, f(29)),
            jagged(block_point(F192::ZERO, F192::ZERO), 3, 20, 2, f(31)),
            jagged(block_point(F192::ONE, F192::ONE), 3, 20, 2, f(37)),
            jagged(block_point(F192::ZERO, F192::ONE), 3, 20, 2, f(41)),
            jagged(singleton_point, 29, 7, 0, f(43)),
        ];
        let gamma = f(47);
        let (weights, batches) = geometric_claim_weights(&claims, gamma);
        assert_eq!(batches.len(), 1, "the four block columns form one batch");

        let mut folded = vec![F192::ZERO; 64];
        let mut target = F192::ZERO;
        fold_stacked_point_claims(&mut folded, &mut target, &claims, &weights, &batches);

        let expected_target = claims
            .iter()
            .zip(&weights)
            .fold(F192::ZERO, |acc, (claim, &weight)| acc + weight * claim.value());
        assert_eq!(target, expected_target);

        for index in 0..64usize {
            let point: Vec<F192> = (0..6)
                .map(|bit| if (index >> bit) & 1 == 1 { F192::ONE } else { F192::ZERO })
                .collect();
            let expected = claims.iter().zip(&weights).fold(F192::ZERO, |acc, (claim, &weight)| {
                acc + weight * stack_claim_eq_at(claim, &point)
            });
            assert_eq!(folded[index], expected, "dense index {index}");
        }

        let residual_point = [f(53), f(59), f(61), f(67), f(71), f(73)];
        let batch_eval = batches.iter().fold(F192::ZERO, |acc, batch| {
            acc + batch.scale
                * super::super::jagged::indicator_eval_with_row_weights(
                    &batch.row_weights,
                    batch.offset,
                    batch.offset + batch.height,
                    &residual_point,
                )
        });
        let grouped_eval = batches[0].members.iter().fold(F192::ZERO, |acc, &member| {
            acc + weights[member] * stack_claim_eq_at(&claims[member], &residual_point)
        });
        assert_eq!(batch_eval, grouped_eval, "batched indicator must equal the column sum");
    }
}
