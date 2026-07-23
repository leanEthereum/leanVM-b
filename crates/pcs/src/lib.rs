// CREDIT: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Polynomial commitment scheme for the bit-MLE witness `ẑ` over GF(2).
//!
//! Construction: Binius-style packing with a Ligerito opening.
//!
//! - **Commit**: pack the 2^m Boolean witness into 2^(m−7) F_{2^128} elements
//!   (one bit per polynomial-basis coordinate of F_{2^128}), batch RS-encode
//!   via additive NTT, Merkle-commit the codeword.
//! - **Open** ([`open_batch_mixed_ligerito_stacked`]): γ-combine the
//!   ring-switched `q_pkd` claims ([`ring_switch`]) with the caller's stacked
//!   point claims ([`StackClaim`]) into ONE basis vector + target, discharged
//!   by a single multilevel Ligerito ([`ligerito`]).
//! - **Verify** ([`verify_opening_batch_mixed_ligerito_stacked`]): replay the
//!   ring-switch binding, recombine the targets, and run the succinct
//!   Ligerito verifier, evaluating each claim's eq-weight at the final point.
//!
//! See [DP24](https://eprint.iacr.org/2024/504) (ring-switching) and the
//! Ligerito paper.

pub mod commit;
pub mod jagged;
pub mod ligerito;
pub mod merkle;
pub mod ntt;
pub mod pack;
pub mod ring_switch;

#[cfg(test)]
pub(crate) mod test_rng;

pub use commit::{Commitment, PcsParams, ProverData, commit};
pub use pack::{LOG_PACKING, PaddingSpec, pack_witness};

/// The transcript states, concretized with this crate's opening type: the one
/// hash-bearing artifact on the `openings` channel is a [`ligerito::LigeritoProof`].
pub type Proof = fiat_shamir::transcript::Proof<ligerito::LigeritoProof>;
pub type ProverState = fiat_shamir::transcript::ProverState<ligerito::LigeritoProof>;
pub type VerifierState<'a> = fiat_shamir::transcript::VerifierState<'a, ligerito::LigeritoProof>;

use primitives::field::F128;

// (No composite opening structs: the ring-switch `s_hat_v` slices ride the
// shared transcript stream, so an opening is just the hash-bearing
// [`ligerito::LigeritoProof`].)

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifyError {
    RingSwitch(ring_switch::VerifyError),
    /// The transmitted opening's shape is inconsistent with the claims
    /// (attacker-controlled proof data; rejected before any crypto work).
    InvalidProofShape,
    /// The Ligerito verifier rejected the opening.
    Ligerito,
}

/// What ring_switch + claim-combination produces, fed to the Ligerito opener.
struct CombinedClaim {
    b_combined: Vec<F128>,
    target_combined: F128,
}

/// Run the batched ring-switch over the `q_pkd` claims, then build
/// `b_combined` (the γ-weighted combination of the per-claim `rs_eq_ind`
/// weights) and `target_combined`.
fn compute_combined_basis_and_target(
    packed_witness: &[F128],
    x_outers: &[&[F128]],
    precomputed_s_hat_v: &[Option<&[F128]>],
    padding: &PaddingSpec,
    ps: &mut ProverState,
) -> CombinedClaim {
    let n_rs = x_outers.len();
    assert!(n_rs > 0, "need at least one ring-switched claim");
    assert!(
        precomputed_s_hat_v.is_empty() || precomputed_s_hat_v.len() == n_rs,
        "precomputed_s_hat_v: must be empty or length {n_rs}, got {}",
        precomputed_s_hat_v.len(),
    );

    // 1. Ring-switching for all x_outers.
    let (rs_results, gammas_rs) = ring_switch::prove_batched_padded_with_precomputed(
        packed_witness,
        x_outers,
        precomputed_s_hat_v,
        padding,
        ps,
    );

    use rayon::prelude::*;

    let l = rs_results[0].rs_eq_ind.dense_len();
    debug_assert!(rs_results.iter().all(|o| o.rs_eq_ind.dense_len() == l));

    let mut target_combined = F128::ZERO;
    for (output, g) in rs_results.iter().zip(gammas_rs.iter()) {
        target_combined += *g * output.sumcheck_claim;
    }

    let rs_baked: Vec<&[F128]> = rs_results
        .iter()
        .filter_map(|o| match &o.rs_eq_ind {
            ring_switch::RsEqInd::Dense(v) => Some(v.as_slice()),
            _ => None,
        })
        .collect();
    // Deferred-dense claims (fused fast path): the per-claim `γ_k·B_k` buffer
    // was never materialized — fold each slot on the fly below and accumulate
    // straight into `b_combined`, saving a 2^(m-7) materialize + readback per
    // claim. Carries (eq_lo, eq_hi, γ-baked byte table, log₂ block) per
    // deferred claim.
    type DeferredFold<'a> = (&'a [F128], &'a [F128], &'a [F128], usize);
    let rs_deferred: Vec<DeferredFold> = rs_results
        .iter()
        .filter_map(|o| match &o.rs_eq_ind {
            ring_switch::RsEqInd::DeferredDense {
                eq_lo,
                eq_hi,
                table,
            } => Some((
                eq_lo.as_slice(),
                eq_hi.as_slice(),
                table.as_slice(),
                eq_lo.len().trailing_zeros() as usize,
            )),
            _ => None,
        })
        .collect();
    // ---- Build b_combined (γ-weighted sum of all rs_eq_ind weights).
    let mut b_combined: Vec<F128> = primitives::scratch::take_f128(l);

    // Fast path (the standard open: claims ab, c): every RS claim is a fused
    // DeferredDense fold. Fold all claims block-by-block straight into
    // b_combined — each claim's `e_hi` hoisted once per block, exactly as in
    // `fold_b128_elems_split`. The per-claim `γ_k·B_k` buffer is never
    // materialized (saves ~2·L writes + 2·L reads of the 2^(m-7) basis).
    let use_fast = !rs_deferred.is_empty() && rs_deferred.len() == rs_results.len();

    if use_fast {
        let b = rs_deferred[0].0.len(); // eq_lo.len(); shared across claims (same split)
        debug_assert!(b >= 2 && b.is_multiple_of(2));
        debug_assert!(rs_deferred.iter().all(|d| d.0.len() == b));
        b_combined.par_chunks_mut(b).enumerate().for_each(|(hi, out_block)| {
            // Accumulate each claim's block: first claim writes, rest add.
            // `e_hi` is read once per claim per block, then swept over eq_lo.
            for (ci, (eq_lo, eq_hi, table, _)) in rs_deferred.iter().enumerate() {
                let e_hi = eq_hi[hi];
                if ci == 0 {
                    for (slot, &lo) in out_block.iter_mut().zip(eq_lo.iter()) {
                        *slot = ring_switch::fold_one_slot(lo * e_hi, table);
                    }
                } else {
                    for (slot, &lo) in out_block.iter_mut().zip(eq_lo.iter()) {
                        *slot += ring_switch::fold_one_slot(lo * e_hi, table);
                    }
                }
            }
        });
    } else {
        // General path (sparse / dense RS claims): materialize any
        // deferred-dense claims (parallel block fold), then the per-element
        // combine over all dense buffers.
        let materialized: Vec<Vec<F128>> = rs_results
            .iter()
            .filter_map(|o| match &o.rs_eq_ind {
                ring_switch::RsEqInd::DeferredDense {
                    eq_lo,
                    eq_hi,
                    table,
                } => Some(ring_switch::fold_b128_from_table(eq_lo, eq_hi, table)),
                _ => None,
            })
            .collect();
        let mut rs_dense_all: Vec<&[F128]> = rs_baked.clone();
        rs_dense_all.extend(materialized.iter().map(|v| v.as_slice()));
        b_combined.par_iter_mut().enumerate().for_each(|(i, slot)| {
            let mut acc = F128::ZERO;
            for v in rs_dense_all.iter() {
                acc += v[i];
            }
            *slot = acc;
        });
        for v in materialized {
            primitives::scratch::give_f128(v);
        }
    }
    for output in rs_results.iter() {
        if let ring_switch::RsEqInd::Sparse { entries, .. } = &output.rs_eq_ind {
            for &(idx, val) in entries {
                b_combined[idx] += val;
            }
        }
    }

    // The per-claim rs_eq_ind (L F128s) dies here — recycle it. (The s_hat_v
    // slices were already streamed inside `prove_batched_*`.)
    for o in rs_results {
        if let ring_switch::RsEqInd::Dense(v) = o.rs_eq_ind {
            primitives::scratch::give_f128(v);
        }
    }
    CombinedClaim {
        b_combined,
        target_combined,
    }
}

// ===== leanVM-b stacked opener (grafted) =====
/// A point claim folded into the stacked mixed opening ([`open_batch_mixed_ligerito_stacked`]).
/// Either a Jagged claim on a tightly packed, arbitrary-height column, a legacy
/// aligned slot claim, or a general full-stack point.  The prover builds every
/// weight only over its support; the verifier evaluates the same weight at the
/// dense PCS's residual point.
pub enum StackClaim<'a> {
    /// A column occupying the arbitrary interval `[offset, offset + height)` in
    /// the dense commitment. `row_point` evaluates the column after its real
    /// prefix has been zero-padded to `2^row_point.len()` rows.
    Jagged {
        offset: usize,
        height: usize,
        /// Low coordinates selecting a column inside a row-major block. Zero
        /// for a singleton column.
        selector_len: usize,
        row_point: &'a [F128],
        value: F128,
    },
    /// `eq(low_point,·)` on `[offset, offset + 2^low_point.len())`. `offset` must
    /// be a multiple of `2^low_point.len()` (an aligned slot).
    Slot { offset: usize, low_point: &'a [F128], value: F128 },
    /// A **boolean-selector** claim on a packed column, equivalent to a `Slot`
    /// with `low_point = slot_bits(slot, stride_log) ++ point` but folded sparsely:
    /// the low `stride_log` block coords are frozen to `slot`'s bits (so the weight
    /// is nonzero only at `offset + slot + j·2^stride_log`), and `point` is the
    /// high part. Costs `2^point.len()` instead of `2^(stride_log + point.len())`.
    /// `offset` must be a multiple of `2^(stride_log + point.len())`.
    StridedSlot { offset: usize, slot: usize, stride_log: usize, point: &'a [F128], value: F128 },
    /// `eq(point,·)` over the whole `2^m` stack.
    Point { point: &'a [F128], value: F128 },
}

impl StackClaim<'_> {
    #[inline]
    fn value(&self) -> F128 {
        match self {
            StackClaim::Jagged { value, .. }
            | StackClaim::Slot { value, .. }
            | StackClaim::StridedSlot { value, .. }
            | StackClaim::Point { value, .. } => *value,
        }
    }
}

#[derive(Debug)]
struct JaggedClaimBatch {
    members: Vec<usize>,
    offset: usize,
    height: usize,
    selector_len: usize,
    row_weights: Vec<[F128; 2]>,
    scale: F128,
}

/// Assign the powers of one batching challenge so complete row-major blocks
/// receive consecutive exponents in selector order. Their weighted residual
/// evaluations then collapse to one Basic-Jagged evaluation:
/// `Σ_c γ^(base+c) eq(z,c) = γ^base D eq(z_γ,c)`, where
/// `z_γ[b] = γ^(2^b)/(1+γ^(2^b))` and `D = Π_b(1+γ^(2^b))`.
fn geometric_claim_weights(stack_pd: &[StackClaim], gamma: F128) -> (Vec<F128>, Vec<JaggedClaimBatch>) {
    let n = stack_pd.len();
    let mut rank = vec![usize::MAX; n];
    let mut batch_members: Vec<(Vec<usize>, usize, usize, usize)> = Vec::new();
    let mut next_rank = 0usize;

    for i in 0..n {
        if rank[i] != usize::MAX {
            continue;
        }
        let StackClaim::Jagged { offset, height, selector_len, row_point, .. } = &stack_pd[i] else {
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
        for j in i..n {
            if rank[j] != usize::MAX {
                continue;
            }
            let StackClaim::Jagged {
                offset: other_offset,
                height: other_height,
                selector_len: other_selector_len,
                row_point: other_point,
                ..
            } = &stack_pd[j]
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
            let mut slot = 0usize;
            let mut boolean = true;
            for (bit, &x) in other_point[..*selector_len].iter().enumerate() {
                if x == F128::ONE {
                    slot |= 1 << bit;
                } else if x != F128::ZERO {
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
    assert_eq!(next_rank, n);

    let mut powers = vec![F128::ONE; n];
    for k in 1..n {
        powers[k] = powers[k - 1] * gamma;
    }
    let weights = rank.iter().map(|&r| powers[r]).collect::<Vec<_>>();
    let mut batches = Vec::new();
    for (members, offset, height, selector_len) in batch_members {
        let base = rank[members[0]];
        let mut a = gamma;
        let scale = powers[base];
        let StackClaim::Jagged { row_point, .. } = &stack_pd[members[0]] else { unreachable!() };
        let mut row_weights = Vec::with_capacity(row_point.len());
        for _ in 0..selector_len {
            row_weights.push([F128::ONE, a]);
            a *= a;
        }
        row_weights.extend(row_point[selector_len..].iter().map(|&r| [F128::ONE + r, r]));
        batches.push(JaggedClaimBatch { members, offset, height, selector_len, row_weights, scale });
    }
    (weights, batches)
}

/// Fold the γ-weighted point claims into the lifted stack weight `b_stack` and
/// running `target` (pure — the caller has already observed the claim values and
/// sampled `gammas_pd` in transcript order). Factored out of
/// [`open_batch_mixed_ligerito_stacked`]; produces the
/// `⟨stack, b_stack⟩ = target` inner-product claim.
fn fold_stacked_point_claims(
    b_stack: &mut [F128],
    target: &mut F128,
    stack_pd: &[StackClaim],
    gammas_pd: &[F128],
    jagged_batches: &[JaggedClaimBatch],
) {
    use rayon::prelude::*;
    // `build_eq` and `build_eq_parallel` produce the identical table and serial
    // and parallel scatter give the identical result, so the proof is
    // byte-for-byte unchanged. A `Slot` builds `eq` over ONLY its aligned
    // sub-block (leanVM's claims — `eq` is zero elsewhere), a `Point` over the
    // whole stack. Both scatter with `+=`, so overlapping slots (e.g. several
    // claims on the q_pkd column) accumulate correctly. Small slots use the
    // serial path: with hundreds of tiny point claims, rayon dispatch would
    // cost more than the fold itself.
    const PAR_FOLD_THRESHOLD: usize = 1 << 14;
    // Bus and constraint claims heavily reuse their challenge points (e.g. all
    // columns of one table share rho). Build each equality tensor once instead
    // of once per column. This also covers q_pkd's strided slot claims, which
    // commonly share the bus point with many ordinary Jagged claims.
    let mut grouped = vec![false; stack_pd.len()];
    for batch in jagged_batches {
        for &member in &batch.members {
            grouped[member] = true;
        }
    }
    let mut eq_tables: Vec<(&[F128], Vec<F128>)> = Vec::new();
    for (j, claim) in stack_pd.iter().enumerate() {
        if grouped[j] {
            continue;
        }
        let point = match claim {
            StackClaim::Jagged { row_point, .. } => *row_point,
            StackClaim::Slot { low_point, .. } => *low_point,
            StackClaim::StridedSlot { point, .. } | StackClaim::Point { point, .. } => *point,
        };
        if eq_tables.iter().any(|(cached, _)| *cached == point) {
            continue;
        }
        let eq = if point.len() < 14 {
            primitives::multilinear::build_eq(point)
        } else {
            ring_switch::build_eq_parallel(point)
        };
        eq_tables.push((point, eq));
    }
    for batch in jagged_batches {
        let StackClaim::Jagged { row_point, .. } = &stack_pd[batch.members[0]] else { unreachable!() };
        let point = &row_point[batch.selector_len..];
        if !eq_tables.iter().any(|(cached, _)| *cached == point) {
            let eq = if point.len() < 14 {
                primitives::multilinear::build_eq(point)
            } else {
                ring_switch::build_eq_parallel(point)
            };
            eq_tables.push((point, eq));
        }
    }
    let eq_for = |point: &[F128]| -> &[F128] {
        eq_tables
            .iter()
            .find(|(cached, _)| *cached == point)
            .map(|(_, eq)| eq.as_slice())
            .expect("claim equality tensor was cached")
    };
    for (claim, g) in stack_pd.iter().zip(gammas_pd.iter()) {
        *target += *g * claim.value();
    }
    for batch in jagged_batches {
        let width = 1usize << batch.selector_len;
        let rows = batch.height / width;
        let StackClaim::Jagged { row_point, .. } = &stack_pd[batch.members[0]] else { unreachable!() };
        let eq = eq_for(&row_point[batch.selector_len..]);
        let slot_weights: Vec<F128> = batch.members.iter().map(|&member| gammas_pd[member]).collect();
        let dst = &mut b_stack[batch.offset..batch.offset + batch.height];
        if dst.len() >= PAR_FOLD_THRESHOLD {
            dst.par_chunks_mut(width).zip(eq[..rows].par_iter()).for_each(|(row, &er)| {
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
    for (j, (claim, g)) in stack_pd.iter().zip(gammas_pd.iter()).enumerate() {
        if grouped[j] {
            continue;
        }
        let g = *g;
        match claim {
            StackClaim::Jagged {
                offset,
                height,
                selector_len: _,
                row_point,
                value: _,
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
            StackClaim::Slot {
                offset,
                low_point,
                value: _,
            } => {
                let len = 1usize << low_point.len();
                let dst = &mut b_stack[*offset..*offset + len];
                if len < PAR_FOLD_THRESHOLD {
                    let eq = eq_for(low_point);
                    for (bi, ei) in dst.iter_mut().zip(eq.iter()) {
                        *bi += g * *ei;
                    }
                } else {
                    let eq = eq_for(low_point);
                    dst.par_iter_mut().zip(eq.par_iter()).for_each(|(bi, ei)| *bi += g * *ei);
                }
            }
            StackClaim::StridedSlot {
                offset,
                slot,
                stride_log,
                point,
                value: _,
            } => {
                // Sparse: eq over the instance `point` (2^point.len()),
                // scattered at stride 2^stride_log into the slot's positions.
                // Identical b_stack contribution to the dense Slot with
                // low_point = slot_bits ++ point, at ~2^stride_log× less work.
                let stride = 1usize << stride_log;
                let base = *offset + *slot;
                let eq = eq_for(point);
                for (j, &ej) in eq.iter().enumerate() {
                    b_stack[base + j * stride] += g * ej;
                }
            }
            StackClaim::Point { point, value: _ } => {
                let eq = eq_for(point);
                b_stack
                    .par_iter_mut()
                    .zip(eq.par_iter())
                    .for_each(|(bi, ei)| *bi += g * *ei);
            }
        }
    }
}

/// The claim's weight `eq(full claim point, x)` at an arbitrary point `x` of the
/// full stack cube — a `Slot`'s full point is `[low_point, selector_bits]`, a
/// `StridedSlot`'s is `[slot_bits, point, selector_bits]`; neither is
/// materialized. Used by the Ligerito verifier's residual evaluator (at the
/// residual points).
fn stack_claim_eq_at(claim: &StackClaim, x: &[F128]) -> F128 {
    match claim {
        StackClaim::Jagged {
            offset,
            height,
            selector_len: _,
            row_point,
            ..
        } => jagged::indicator_eval(row_point, *offset, *offset + *height, x),
        StackClaim::Slot { offset, low_point, .. } => {
            let n = low_point.len();
            let mut e = primitives::multilinear::eq_eval(low_point, &x[..n]);
            let sel = offset >> n;
            for (k, &xi) in x[n..].iter().enumerate() {
                e *= if (sel >> k) & 1 == 1 { xi } else { F128::ONE + xi };
            }
            e
        }
        StackClaim::StridedSlot { offset, slot, stride_log, point, .. } => {
            let mut e = F128::ONE;
            for (k, &xi) in x[..*stride_log].iter().enumerate() {
                e *= if (slot >> k) & 1 == 1 { xi } else { F128::ONE + xi };
            }
            let block_vars = stride_log + point.len();
            e *= primitives::multilinear::eq_eval(point, &x[*stride_log..block_vars]);
            let sel = offset >> block_vars;
            for (k, &xi) in x[block_vars..].iter().enumerate() {
                e *= if (sel >> k) & 1 == 1 { xi } else { F128::ONE + xi };
            }
            e
        }
        StackClaim::Point { point, .. } => primitives::multilinear::eq_eval(point, x),
    }
}


/// Open ring-switched claims and full-stack point claims in ONE Ligerito
/// opening: ring-switch combine + lifted `b_stack` build, γ-folded into a
/// single `⟨stack, b_stack⟩ = target` inner-product claim discharged by the
/// Ligerito multilevel prover, reusing the caller's commit as L0.
/// `lig_config.initial_k` / `log_inv_rates[0]` must match the commit's params.
#[allow(clippy::too_many_arguments)]
pub fn open_batch_mixed_ligerito_stacked(
    qpkd: &[F128],
    x_outers: &[&[F128]],
    precomputed_s_hat_v: &[Option<&[F128]>],
    padding: &PaddingSpec,
    stack: &[F128],
    stack_offset: usize,
    stack_data: &ProverData,
    stack_commitment: &Commitment,
    stack_pd: &[StackClaim],
    lig_config: &ligerito::LigeritoConfig,
    ps: &mut ProverState,
) -> ligerito::LigeritoProof {
    assert_eq!(
        lig_config.initial_k, stack_commitment.params.log_batch_size,
        "ligerito initial_k must match PcsParams.log_batch_size for L0 reuse",
    );
    assert_eq!(
        lig_config.log_inv_rates[0], stack_commitment.params.log_inv_rate,
        "ligerito log_inv_rates[0] must match PcsParams.log_inv_rate for L0 reuse",
    );

    let combined = compute_combined_basis_and_target(qpkd, x_outers, precomputed_s_hat_v, padding, ps);
    // SAFETY: F128 is a pair of integer lanes and its all-zero byte pattern is
    // exactly F128::ZERO. A zeroed allocation leaves untouched padding on
    // demand-zero pages instead of eagerly writing the entire stack.
    let mut b_stack: Vec<F128> = unsafe { primitives::alloc_zeroed_vec(stack.len()) };
    b_stack[stack_offset..stack_offset + combined.b_combined.len()].copy_from_slice(&combined.b_combined);
    let mut target = combined.target_combined;

    for claim in stack_pd {
        ps.observe_scalar(claim.value());
    }
    // Every value is bound before this point, so one random linear-combination
    // challenge suffices. Powers lose at most `stack_pd.len() / |F|` soundness
    // (well below the target for F128) and make same-table claims tensorable.
    let gamma = ps.sample();
    let (gammas_pd, jagged_batches) = geometric_claim_weights(stack_pd, gamma);
    fold_stacked_point_claims(&mut b_stack, &mut target, stack_pd, &gammas_pd, &jagged_batches);

    ligerito::multilevel_prover_with_basis(
        lig_config,
        stack.to_vec(),
        b_stack,
        target,
        &stack_data.codeword,
        &stack_data.merkle_tree,
        ps,
    )
}

/// What the stacked opening verifier hands back on accept: the ring-switch
/// batching challenges and the Ligerito fold/query data — everything a
/// recursion harness needs, named and typed.
#[derive(Clone, Debug)]
pub struct StackedOpeningSummary {
    /// The `r''` shared by every ring-switch claim of the batch.
    pub r_dprime: Vec<F128>,
    pub lig: ligerito::LigVerifierSummary,
}

/// Verifier mirror of [`open_batch_mixed_ligerito_stacked`]: replay the
/// ring-switch reduction + γ-folds in the prover's transcript order, then
/// drive the SUCCINCT Ligerito verifier with a residual evaluator for the
/// lifted weight: at each residual point `x = ris ++ y_bits`,
/// `b(x) = eq(sel, x_hi)·Σ γ_rs·rs_eq(x_lo) + Σ γ_pd·eq(claim, x)`.
pub fn verify_opening_batch_mixed_ligerito_stacked(
    stack_commitment: &Commitment,
    stack_offset: usize,
    qpkd_vars: usize,
    claims: &[F128],
    z_skips: &[F128],
    x_outers: &[&[F128]],
    stack_pd: &[StackClaim],
    proof: &ligerito::LigeritoProof,
    lig_config: &ligerito::LigeritoConfig,
    vs: &mut VerifierState<'_>,
) -> Result<StackedOpeningSummary, VerifyError> {
    let n_rs = claims.len();
    // These are caller (leanVM) invariants.
    assert_eq!(z_skips.len(), n_rs);
    assert_eq!(x_outers.len(), n_rs);
    // (The s_hat_v slices ride the stream; `verify_bind` reads exactly
    // 2^LOG_PACKING words per claim, so there is no shape to validate here.)

    // Bind + check every claim, then sample ONE shared r'' (sound: every
    // slice is absorbed before the challenge), then form the batched claims.
    let mut rs_proofs = Vec::with_capacity(n_rs);
    for i in 0..n_rs {
        rs_proofs.push(
            ring_switch::verify_bind(claims[i], z_skips[i], x_outers[i], vs)
                .map_err(VerifyError::RingSwitch)?,
        );
    }
    // Mirror the prover: with n_rs = 0 the ring-switch batch never runs on the
    // prover side, so no r'' is sampled there — skip it here too or the two
    // transcripts diverge (the prover samples r'' inside `prove_batched_*`).
    let r_dprime = if n_rs > 0 { vs.sample_vec(LOG_PACKING) } else { Vec::new() };
    let eq_r_dprime = primitives::multilinear::build_eq(&r_dprime);
    let lin_coeffs =
        if n_rs > 0 { ring_switch::linearized_eq_coeffs(&eq_r_dprime) } else { [F128::ZERO; 128] };
    let rs_outputs: Vec<ring_switch::RingSwitchVerifierOutput> = (0..n_rs)
        .map(|i| ring_switch::RingSwitchVerifierOutput {
            sumcheck_claim: ring_switch::transposed_claim_linearized(&rs_proofs[i], &lin_coeffs),
            r_dprime: r_dprime.clone(),
            eq_r_dprime: eq_r_dprime.clone(),
        })
        .collect();
    let gammas_rs: Vec<F128> = (0..n_rs).map(|_| vs.sample()).collect();
    let mut target_combined = F128::ZERO;
    for (out, g) in rs_outputs.iter().zip(gammas_rs.iter()) {
        target_combined += *g * out.sumcheck_claim;
    }

    for claim in stack_pd {
        vs.observe_scalar(claim.value());
    }
    let gamma = vs.sample();
    let (gammas_pd, jagged_batches) = geometric_claim_weights(stack_pd, gamma);
    for (claim, g) in stack_pd.iter().zip(gammas_pd.iter()) {
        target_combined += *g * claim.value();
    }
    let mut jagged_grouped = vec![false; stack_pd.len()];
    for batch in &jagged_batches {
        for &member in &batch.members {
            jagged_grouped[member] = true;
        }
    }

    // Residual evaluator of the lifted weight: for each y over the residual cube,
    // evaluate b at the full point `ris ++ y_bits` (low coords = ris, high = y).
    let log_n = stack_commitment.params.m - LOG_PACKING;
    let sel = stack_offset >> qpkd_vars;
    let eval_b_residual = |ris: &[F128], yr_log_n: usize| -> Vec<F128> {
        use rayon::prelude::*;
        (0..1usize << yr_log_n)
            .into_par_iter()
            .map(|y| {
                let mut x = Vec::with_capacity(ris.len() + yr_log_n);
                x.extend_from_slice(ris);
                for k in 0..yr_log_n {
                    x.push(F128::new(((y >> k) & 1) as u64, 0));
                }
                let (x_lo, x_hi) = x.split_at(qpkd_vars);
                let mut sel_eq = F128::ONE;
                for (k, &xi) in x_hi.iter().enumerate() {
                    sel_eq *= if (sel >> k) & 1 == 1 { xi } else { F128::ONE + xi };
                }
                let mut rs_part = F128::ZERO;
                for (out, (g, x_outer)) in rs_outputs.iter().zip(gammas_rs.iter().zip(x_outers.iter())) {
                    rs_part += *g * ring_switch::eval_rs_eq(&x_outer[1..], x_lo, &out.eq_r_dprime);
                }
                let mut acc = rs_part * sel_eq;
                for batch in &jagged_batches {
                    acc += batch.scale
                        * jagged::indicator_eval_with_row_weights(
                            &batch.row_weights,
                            batch.offset,
                            batch.offset + batch.height,
                            &x,
                        );
                }
                for (j, (claim, g)) in stack_pd.iter().zip(gammas_pd.iter()).enumerate() {
                    if !jagged_grouped[j] {
                        acc += *g * stack_claim_eq_at(claim, &x);
                    }
                }
                acc
            })
            .collect()
    };

    let lig = ligerito::multilevel_verifier_with_basis_succinct(
        lig_config,
        proof,
        log_n,
        target_combined,
        &stack_commitment.root,
        eval_b_residual,
        vs,
    )
    .ok_or(VerifyError::Ligerito)?;
    Ok(StackedOpeningSummary {
        r_dprime,
        lig,
    })
}

#[cfg(test)]
mod jagged_batch_tests {
    use super::*;

    fn f(x: u64) -> F128 {
        F128::new(x, x.rotate_left(23))
    }

    #[test]
    fn geometric_batch_matches_individual_jagged_claims() {
        let row = [f(3), f(5), f(7)];
        // Deliberately shuffle the four selector slots: batching must assign
        // powers by Boolean slot, not by input order.
        let block_points = [
            [F128::ONE, F128::ZERO, row[0], row[1], row[2]],
            [F128::ZERO, F128::ZERO, row[0], row[1], row[2]],
            [F128::ONE, F128::ONE, row[0], row[1], row[2]],
            [F128::ZERO, F128::ONE, row[0], row[1], row[2]],
        ];
        let singleton_point = [f(11), f(13), f(17), f(19), f(23)];
        let claims = [
            StackClaim::Jagged {
                offset: 3,
                height: 20,
                selector_len: 2,
                row_point: &block_points[0],
                value: f(29),
            },
            StackClaim::Jagged {
                offset: 3,
                height: 20,
                selector_len: 2,
                row_point: &block_points[1],
                value: f(31),
            },
            StackClaim::Jagged {
                offset: 3,
                height: 20,
                selector_len: 2,
                row_point: &block_points[2],
                value: f(37),
            },
            StackClaim::Jagged {
                offset: 3,
                height: 20,
                selector_len: 2,
                row_point: &block_points[3],
                value: f(41),
            },
            StackClaim::Jagged {
                offset: 29,
                height: 7,
                selector_len: 0,
                row_point: &singleton_point,
                value: f(43),
            },
        ];
        let gamma = f(47);
        let (weights, batches) = geometric_claim_weights(&claims, gamma);
        assert_eq!(batches.len(), 1);

        let mut folded = vec![F128::ZERO; 64];
        let mut target = F128::ZERO;
        fold_stacked_point_claims(&mut folded, &mut target, &claims, &weights, &batches);

        let expected_target = claims
            .iter()
            .zip(&weights)
            .fold(F128::ZERO, |acc, (claim, &weight)| acc + weight * claim.value());
        assert_eq!(target, expected_target);

        for index in 0..64 {
            let point: Vec<_> = (0..6)
                .map(|bit| if (index >> bit) & 1 == 1 { F128::ONE } else { F128::ZERO })
                .collect();
            let expected = claims
                .iter()
                .zip(&weights)
                .fold(F128::ZERO, |acc, (claim, &weight)| {
                    acc + weight * stack_claim_eq_at(claim, &point)
                });
            assert_eq!(folded[index], expected, "dense index {index}");
        }

        let residual_point = [f(53), f(59), f(61), f(67), f(71), f(73)];
        let batch_eval = batches.iter().fold(F128::ZERO, |acc, batch| {
            acc + batch.scale
                * jagged::indicator_eval_with_row_weights(
                    &batch.row_weights,
                    batch.offset,
                    batch.offset + batch.height,
                    &residual_point,
                )
        });
        let grouped_eval = batches[0]
            .members
            .iter()
            .fold(F128::ZERO, |acc, &member| {
                acc + weights[member] * stack_claim_eq_at(&claims[member], &residual_point)
            });
        assert_eq!(batch_eval, grouped_eval);
    }
}
