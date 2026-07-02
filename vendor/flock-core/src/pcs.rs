// Credit: https://github.com/succinctlabs/flock (flock-core), MIT OR Apache-2.0.
//! Polynomial commitment scheme for the bit-MLE witness `ẑ` over GF(2).
//!
//! Construction: Binius-style PCS with F_{2^128} packing.
//!
//! - **Commit**: pack the 2^m Boolean witness into 2^(m−7) F_{2^128} elements
//!   (one bit per polynomial-basis coordinate of F_{2^128}), batch RS-encode
//!   via additive NTT, Merkle-commit the codeword.
//! - **Open**: at a QuirkyPoint (z_skip, x_outer) from the zerocheck/lincheck:
//!   1. [`ring_switch::prove`] sends 128 partial-evaluations `s_hat_v` and
//!      produces a BaseFold target `(rs_eq_ind, sumcheck_claim)`.
//!   2. [`basefold::prove`] runs the bivariate sumcheck of
//!      `⟨packed_witness, rs_eq_ind⟩ = sumcheck_claim` over m−7 rounds.
//! - **Verify**: the verifier replays both steps. After ring-switching it
//!   reconstructs `rs_eq_ind` locally and checks the sumcheck's final value,
//!   then walks the multi-arity FRI codeword folds — verifying per-query
//!   Merkle paths against the T₁ (initial) and T₂ (post-row-batch) roots and
//!   the per-epoch FRI commits, and matching the final folded value against
//!   a plaintext final codeword. See [`basefold::verify`] for the full chain.
//!
//! See [DP24](https://eprint.iacr.org/2024/504) (ring-switching) and the
//! [BaseFold paper](https://link.springer.com/chapter/10.1007/978-3-031-68403-6_5).

pub mod basefold;
pub mod commit;
pub mod ligerito;
pub mod pack;
pub mod ring_switch;
pub mod tensor_algebra;

pub use basefold::{
    BaseFoldProof, DEFAULT_FRI_QUERIES, RoundCommitment, RoundMessage, default_fri_queries,
};
pub use commit::{
    Commitment, LOG_FRI_ARITY, PcsParams, ProverData, commit, commit_into, compute_fri_arities,
    prefault_codeword_during,
};
pub use pack::{LOG_PACKING, pack_witness, unpack_witness};
pub use ring_switch::{RingSwitchProof, SparseEqTensor};

use crate::challenger::Challenger;
use crate::field::F128;
use crate::zerocheck::PaddingSpec;
use serde::{Deserialize, Serialize};

/// Composite opening proof: ring-switching message + BaseFold proof.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OpeningProof {
    pub ring_switch: RingSwitchProof,
    pub basefold: BaseFoldProof,
}

/// Batched opening proof with the **Ligerito** PCS backend instead of BaseFold.
/// Same ring-switching frontend; the combined `b_combined` + target_combined
/// feed [`ligerito::recursive_prover_with_basis`] for a smaller proof at the
/// cost of ~1.4× prover time (see ligerito module docs).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BatchOpeningProofLigerito {
    pub ring_switches: Vec<RingSwitchProof>,
    pub ligerito: ligerito::LigeritoProof,
}

/// Backend-agnostic batched opening proof, carried inside [`crate::proof::R1csProof`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum BatchOpening {
    BaseFold(BatchOpeningProof),
    Ligerito(BatchOpeningProofLigerito),
}

/// Batched opening proof: one ring-switching message per opening point,
/// plus ONE shared BaseFold proof. The BaseFold runs on a random linear
/// combination of the per-point `rs_eq_ind` weights, so a single
/// sumcheck + FRI suffices to prove all opening claims.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BatchOpeningProof {
    pub ring_switches: Vec<RingSwitchProof>,
    pub basefold: BaseFoldProof,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifyError {
    RingSwitch(ring_switch::VerifyError),
    BaseFold(basefold::VerifyError),
    /// BaseFold's `final_b` doesn't match the transparent multilinear's
    /// evaluation at the sampled challenges. Indicates the prover's BaseFold
    /// final value is inconsistent with `rs_eq_ind`.
    FinalBMismatch,
}

/// `eq_ind` representation for a packed-direct claim. The contributed value at
/// scattered index `j` is the tensor entry — for the dense variant the index
/// is the array offset; for the sparse variant it's reconstructed via
/// [`SparseEqTensor::scatter_idx`].
#[derive(Clone, Debug)]
pub enum DirectEqInd {
    /// Fully-materialized `eq_ind(point)` of length `2^L`.
    Dense(Vec<F128>),
    /// Sparse representation — non-zero entries at scattered indices.
    /// Built from a claim point with one or more exactly-zero coords via
    /// [`ring_switch::build_eq_sparse`].
    Sparse(SparseEqTensor),
}

/// A packed-MLE evaluation claim: `ẑ_packed(point) = value`. Unlike a
/// ring-switched claim, this is opened directly via BaseFold without going
/// through the bit-MLE ↔ packed-MLE bridge (no `s_hat_v`, no φ_8 weighting).
///
/// Use case: protocols whose sumcheck output is naturally a packed-MLE
/// evaluation (e.g. the chain shift sumcheck operating on packed columns
/// instead of bit-folded scalars). Skips the ring-switch step for this claim,
/// saving the `fold_1b_rows` + per-opening-tail work at the prover and the
/// ring-switch verify + φ_8 reconstruction at the verifier.
///
/// The basefold combine step adds `γ_k · eq_ind(point)` to `b_combined` and
/// `γ_k · value` to the target; the verifier's `final_b` check contributes
/// `γ_k · eq_eval(point, basefold_challenges)`.
#[derive(Clone, Debug)]
pub struct PackedDirectClaim {
    /// Multilinear point of length `L = m − 7`.
    pub point: Vec<F128>,
    /// Claimed `ẑ_packed(point)` value.
    pub value: F128,
    /// `eq_ind(point)` in dense or sparse form. Caller responsibility to
    /// match the claim's `point` — the contribution to `b_combined` is read
    /// directly from this tensor.
    pub eq_ind: DirectEqInd,
}

/// Open the committed witness at a zerocheck-style point `(z_skip, x_outer)`.
///
/// `packed_witness` is the same F_{2^128}-packed witness that was passed to
/// [`commit`] — caller must retain its own copy (it is NOT stored in
/// `ProverData`). `prover_data` is the output of [`commit`]. `x_outer` is the
/// multilinear portion of the QuirkyPoint with length `m − 6`.
pub fn open<Ch: Challenger>(
    packed_witness: &[F128],
    prover_data: &ProverData,
    commitment: &Commitment,
    x_outer: &[F128],
    challenger: &mut Ch,
) -> OpeningProof {
    challenger.observe_label(b"flock-pcs-open-v0");
    let (rs_proof, rs_output) = ring_switch::prove(packed_witness, x_outer, challenger);
    let ntt = crate::ntt::AdditiveNttF128::standard(commitment.params.k_code());
    let bf_proof = basefold::prove(
        packed_witness,
        rs_output.rs_eq_ind,
        rs_output.sumcheck_claim,
        &prover_data.codeword,
        &prover_data.merkle_tree,
        &ntt,
        commitment.params.log_inv_rate,
        commitment.params.log_batch_size,
        default_fri_queries(commitment.params.log_inv_rate),
        challenger,
    );
    OpeningProof {
        ring_switch: rs_proof,
        basefold: bf_proof,
    }
}

/// Batched open at multiple points (`x_outers[0..n]`) against the same
/// commitment. Runs ring-switching once per point, then ONE BaseFold prove
/// on the random-linear-combination of the per-point `rs_eq_ind` weights.
///
/// At m=29 this roughly halves total open cost vs calling `open` twice.
pub fn open_batch<Ch: Challenger>(
    packed_witness: &[F128],
    prover_data: &ProverData,
    commitment: &Commitment,
    x_outers: &[&[F128]],
    challenger: &mut Ch,
) -> BatchOpeningProof {
    open_batch_padded(
        packed_witness,
        prover_data,
        commitment,
        x_outers,
        &PaddingSpec::dense(commitment.params.m),
        challenger,
    )
}

/// Padding-aware variant of [`open_batch`]. Threads `padding` into
/// ring-switching's `fold_1b_rows` so per-block padding chunks are skipped.
/// Byte-identical to the dense path on honestly zero-padded witnesses.
pub fn open_batch_padded<Ch: Challenger>(
    packed_witness: &[F128],
    prover_data: &ProverData,
    commitment: &Commitment,
    x_outers: &[&[F128]],
    padding: &PaddingSpec,
    challenger: &mut Ch,
) -> BatchOpeningProof {
    open_batch_mixed(
        packed_witness,
        prover_data,
        commitment,
        x_outers,
        &[],
        padding,
        challenger,
    )
}

/// Variant of [`open_batch_padded`] that accepts a per-claim optional
/// precomputed `s_hat_v`. See [`open_batch_mixed_with_precomputed_s_hat_v`].
#[allow(clippy::too_many_arguments)]
pub fn open_batch_padded_with_precomputed_s_hat_v<Ch: Challenger>(
    packed_witness: &[F128],
    prover_data: &ProverData,
    commitment: &Commitment,
    x_outers: &[&[F128]],
    precomputed_s_hat_v: &[Option<&[F128]>],
    padding: &PaddingSpec,
    challenger: &mut Ch,
) -> BatchOpeningProof {
    open_batch_mixed_with_precomputed_s_hat_v(
        packed_witness,
        prover_data,
        commitment,
        x_outers,
        precomputed_s_hat_v,
        &[],
        padding,
        challenger,
    )
}

/// Mixed-claim batched open: supports both **ring-switched** claims (the
/// classical path — bit-MLE openings reduced via `ring_switch::prove_batched`)
/// and **packed-direct** claims (packed-MLE openings that skip ring-switch and
/// contribute directly to BaseFold).
///
/// Packed-direct claims save the chain claim's ring-switch work (no `s_hat_v`,
/// no per-opening-tail `fold_b128_elems_sparse_pairs`) when the producer of the
/// claim is already at the packed level (e.g. a column-level lincheck whose
/// sumcheck output is a packed-MLE evaluation).
///
/// Transcript order: label → ring-switched claims (each: label + `s_hat_v_i` +
/// sample `r_dprime_i`) → packed-direct claims (each: `value_k` observed) →
/// sample γ's (one per total claim, ring-switched first) → BaseFold.
#[allow(clippy::too_many_arguments)]
pub fn open_batch_mixed<Ch: Challenger>(
    packed_witness: &[F128],
    prover_data: &ProverData,
    commitment: &Commitment,
    x_outers: &[&[F128]],
    packed_direct: &[PackedDirectClaim],
    padding: &PaddingSpec,
    challenger: &mut Ch,
) -> BatchOpeningProof {
    open_batch_mixed_with_precomputed_s_hat_v(
        packed_witness,
        prover_data,
        commitment,
        x_outers,
        &[],
        packed_direct,
        padding,
        challenger,
    )
}

/// Variant of [`open_batch_mixed`] that accepts a per-ring-switched-claim
/// optional precomputed `s_hat_v`. When `Some(v)` is supplied for claim `i`,
/// ring-switch skips that claim's `fold_1b_rows` and uses `v` directly. Used
/// by the prover to reuse lincheck's pre-sumcheck `z_vec` as the source for
/// the AB-claim's `s_hat_v` — see [`ring_switch::s_hat_v_from_z_vec`].
///
/// `precomputed_s_hat_v` must be `&[]` or have length `x_outers.len()`.
#[allow(clippy::too_many_arguments)]
pub fn open_batch_mixed_with_precomputed_s_hat_v<Ch: Challenger>(
    packed_witness: &[F128],
    prover_data: &ProverData,
    commitment: &Commitment,
    x_outers: &[&[F128]],
    precomputed_s_hat_v: &[Option<&[F128]>],
    packed_direct: &[PackedDirectClaim],
    padding: &PaddingSpec,
    challenger: &mut Ch,
) -> BatchOpeningProof {
    let trace = std::env::var("PCS_TRACE").is_ok();
    let t_total = std::time::Instant::now();

    let combined = compute_combined_basis_and_target(
        packed_witness,
        x_outers,
        precomputed_s_hat_v,
        packed_direct,
        padding,
        challenger,
        trace,
    );

    // BaseFold + FRI on the combined claim.
    let t = std::time::Instant::now();
    let ntt = crate::ntt::AdditiveNttF128::standard(commitment.params.k_code());
    if trace {
        eprintln!(
            "  [open_batch] AdditiveNttF128::standard: {:6.2} ms",
            t.elapsed().as_secs_f64() * 1e3
        );
    }
    let t = std::time::Instant::now();
    let bf_proof = basefold::prove_with_precomputed_round0_prime(
        packed_witness,
        combined.b_combined,
        combined.target_combined,
        &prover_data.codeword,
        &prover_data.merkle_tree,
        &ntt,
        commitment.params.log_inv_rate,
        commitment.params.log_batch_size,
        default_fri_queries(commitment.params.log_inv_rate),
        Some(combined.round0_prime),
        challenger,
    );
    if trace {
        eprintln!(
            "  [open_batch] basefold::prove: {:6.2} ms",
            t.elapsed().as_secs_f64() * 1e3
        );
        eprintln!(
            "  [open_batch] TOTAL: {:6.2} ms",
            t_total.elapsed().as_secs_f64() * 1e3
        );
    }

    BatchOpeningProof {
        ring_switches: combined.ring_switches,
        basefold: bf_proof,
    }
}

/// Open ring-switched claims AND full-stack point claims in ONE BaseFold, when
/// the committed witness is a larger STACK whose aligned sub-block
/// `[stack_offset, stack_offset + qpkd.len())` is `qpkd` (the leanVM-b single-PCS
/// integration: `qpkd` is flock's packed BLAKE3 witness, committed inside
/// leanVM's one stacked commitment). The ring-switch combined weight is computed
/// over `qpkd` and LIFTED into the stack domain; each `stack_pd = (point, value)`
/// is a plain multilinear evaluation of the WHOLE stack (leanVM's bus /
/// constraint / binding / pinning claims). All are γ-folded into one weight and
/// the single BaseFold runs over `stack` (`a_init`). `stack_offset` must be a
/// multiple of `qpkd.len()`.
/// A point claim folded into the stacked mixed opening ([`open_batch_mixed_ligerito_stacked`]).
/// Either a **block-sparse** slot claim — weight `eq(low_point,·)` supported on the
/// aligned sub-block `[offset, offset + 2^low_point.len())`, so the opener builds
/// `eq` over just the slot instead of the whole `2^m` stack — or a **general**
/// full-stack point (`eq(point,·)` over all `2^m`). leanVM's point claims are all
/// `Slot`s (their `eq` is zero outside the slot); `Point` keeps the opener usable
/// for arbitrary claims.
pub enum StackClaim<'a> {
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
            StackClaim::Slot { value, .. }
            | StackClaim::StridedSlot { value, .. }
            | StackClaim::Point { value, .. } => *value,
        }
    }
}

/// Fold the γ-weighted point claims into the lifted stack weight `b_stack` and
/// running `target` (pure — the caller has already observed the claim values and
/// sampled `gammas_pd` in transcript order). Shared by the BaseFold and Ligerito
/// stacked openers, so both produce the identical `⟨stack, b_stack⟩ = target`
/// inner-product claim.
fn fold_stacked_point_claims(b_stack: &mut [F128], target: &mut F128, stack_pd: &[StackClaim], gammas_pd: &[F128]) {
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
    for (claim, g) in stack_pd.iter().zip(gammas_pd.iter()) {
        let g = *g;
        match claim {
            StackClaim::Slot { offset, low_point, value } => {
                let len = 1usize << low_point.len();
                let dst = &mut b_stack[*offset..*offset + len];
                if len < PAR_FOLD_THRESHOLD {
                    let eq = crate::zerocheck::univariate_skip::build_eq(low_point);
                    for (bi, ei) in dst.iter_mut().zip(eq.iter()) {
                        *bi += g * *ei;
                    }
                } else {
                    let eq = ring_switch::build_eq_parallel(low_point);
                    dst.par_iter_mut().zip(eq.par_iter()).for_each(|(bi, ei)| *bi += g * *ei);
                }
                *target += g * *value;
            }
            StackClaim::StridedSlot { offset, slot, stride_log, point, value } => {
                // Sparse: eq over the instance `point` (2^point.len()),
                // scattered at stride 2^stride_log into the slot's positions.
                // Identical b_stack contribution to the dense Slot with
                // low_point = slot_bits ++ point, at ~2^stride_log× less work.
                let stride = 1usize << stride_log;
                let base = *offset + *slot;
                let eq = if point.len() < 14 {
                    crate::zerocheck::univariate_skip::build_eq(point)
                } else {
                    ring_switch::build_eq_parallel(point)
                };
                for (j, &ej) in eq.iter().enumerate() {
                    b_stack[base + j * stride] += g * ej;
                }
                *target += g * *value;
            }
            StackClaim::Point { point, value } => {
                let eq = ring_switch::build_eq_parallel(point);
                b_stack
                    .par_iter_mut()
                    .zip(eq.par_iter())
                    .for_each(|(bi, ei)| *bi += g * *ei);
                *target += g * *value;
            }
        }
    }
}

/// The claim's weight `eq(full claim point, x)` at an arbitrary point `x` of the
/// full stack cube — a `Slot`'s full point is `[low_point, selector_bits]`, a
/// `StridedSlot`'s is `[slot_bits, point, selector_bits]`; neither is
/// materialized. Shared by the BaseFold verifier (at the folding challenges) and
/// the Ligerito verifier (at the residual points).
fn stack_claim_eq_at(claim: &StackClaim, x: &[F128]) -> F128 {
    match claim {
        StackClaim::Slot { offset, low_point, .. } => {
            let n = low_point.len();
            let mut e = crate::zerocheck::multilinear::eq_eval(low_point, &x[..n]);
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
            e *= crate::zerocheck::multilinear::eq_eval(point, &x[*stride_log..block_vars]);
            let sel = offset >> block_vars;
            for (k, &xi) in x[block_vars..].iter().enumerate() {
                e *= if (sel >> k) & 1 == 1 { xi } else { F128::ONE + xi };
            }
            e
        }
        StackClaim::Point { point, .. } => crate::zerocheck::multilinear::eq_eval(point, x),
    }
}


/// **Ligerito**-backend counterpart of [`open_batch_mixed_ligerito_stacked`]: the identical
/// ring-switch combine + lifted `b_stack` build (same transcript order, same
/// `⟨stack, b_stack⟩ = target` inner-product claim), discharged by the Ligerito
/// recursive prover instead of BaseFold, reusing the caller's commit as L0.
/// `lig_config.initial_k` / `log_inv_rates[0]` must match the commit's params.
#[allow(clippy::too_many_arguments)]
pub fn open_batch_mixed_ligerito_stacked<Ch: Challenger>(
    qpkd: &[F128],
    x_outers: &[&[F128]],
    precomputed_s_hat_v: &[Option<&[F128]>],
    padding: &PaddingSpec,
    stack: &[F128],
    stack_offset: usize,
    stack_data: &ProverData,
    stack_commitment: &Commitment,
    stack_pd: &[StackClaim],
    lig_config: &ligerito::ProverConfig,
    challenger: &mut Ch,
) -> BatchOpeningProofLigerito {
    assert_eq!(
        lig_config.initial_k, stack_commitment.params.log_batch_size,
        "ligerito initial_k must match PcsParams.log_batch_size for L0 reuse",
    );
    assert_eq!(
        lig_config.log_inv_rates[0], stack_commitment.params.log_inv_rate,
        "ligerito log_inv_rates[0] must match PcsParams.log_inv_rate for L0 reuse",
    );

    let combined = compute_combined_basis_and_target(qpkd, x_outers, precomputed_s_hat_v, &[], padding, challenger, false);
    let mut b_stack = vec![F128::ZERO; stack.len()];
    b_stack[stack_offset..stack_offset + combined.b_combined.len()].copy_from_slice(&combined.b_combined);
    let mut target = combined.target_combined;

    for claim in stack_pd {
        challenger.observe_label(b"flock-pcs-packed-direct-v0");
        challenger.observe_f128(claim.value());
    }
    let gammas_pd: Vec<F128> = (0..stack_pd.len()).map(|_| challenger.sample_f128()).collect();
    fold_stacked_point_claims(&mut b_stack, &mut target, stack_pd, &gammas_pd);

    let lig = ligerito::recursive_prover_with_basis(
        lig_config,
        stack.to_vec(),
        b_stack,
        target,
        &stack_data.codeword,
        &stack_data.merkle_tree,
        challenger,
    );
    BatchOpeningProofLigerito {
        ring_switches: combined.ring_switches,
        ligerito: lig,
    }
}

/// Verifier mirror of [`open_batch_mixed_ligerito_stacked`]: replay the
/// ring-switch reduction + γ-folds exactly as the BaseFold stacked verifier does,
/// then drive the SUCCINCT Ligerito verifier with a residual evaluator for the
/// lifted weight — at each residual point `x = ris ++ y_bits`,
/// `b(x) = eq(sel, x_hi)·Σ γ_rs·rs_eq(x_lo) + Σ γ_pd·eq(claim, x)` (the same
/// formula the BaseFold path checks once at its folding point).
#[allow(clippy::too_many_arguments)]
pub fn verify_opening_batch_mixed_ligerito_stacked<Ch: Challenger>(
    stack_commitment: &Commitment,
    stack_offset: usize,
    qpkd_vars: usize,
    claims: &[F128],
    z_skips: &[F128],
    x_outers: &[&[F128]],
    stack_pd: &[StackClaim],
    proof: &BatchOpeningProofLigerito,
    lig_config: &ligerito::VerifierConfig,
    challenger: &mut Ch,
) -> Result<(), VerifyError> {
    let n_rs = claims.len();
    // These are caller (leanVM) invariants.
    assert_eq!(z_skips.len(), n_rs);
    assert_eq!(x_outers.len(), n_rs);
    // `proof` is attacker-controlled (deserialized): validate its shape and return
    // an Err rather than panicking (verifier DoS). `verify_succinct` internally
    // asserts `s_hat_v.len() == 2^LOG_PACKING`, so check that here too.
    let shape_err = || VerifyError::BaseFold(crate::pcs::basefold::VerifyError::InvalidProofShape);
    if proof.ring_switches.len() != n_rs
        || proof.ring_switches.iter().any(|rs| rs.s_hat_v.len() != 1 << LOG_PACKING)
    {
        return Err(shape_err());
    }
    challenger.observe_label(b"flock-pcs-open-batch-v0");

    let mut rs_outputs = Vec::with_capacity(n_rs);
    for i in 0..n_rs {
        rs_outputs.push(
            ring_switch::verify_succinct(claims[i], z_skips[i], x_outers[i], &proof.ring_switches[i], challenger)
                .map_err(VerifyError::RingSwitch)?,
        );
    }
    let gammas_rs: Vec<F128> = (0..n_rs).map(|_| challenger.sample_f128()).collect();
    let mut target_combined = F128::ZERO;
    for (out, g) in rs_outputs.iter().zip(gammas_rs.iter()) {
        target_combined += *g * out.sumcheck_claim;
    }

    for claim in stack_pd {
        challenger.observe_label(b"flock-pcs-packed-direct-v0");
        challenger.observe_f128(claim.value());
    }
    let gammas_pd: Vec<F128> = (0..stack_pd.len()).map(|_| challenger.sample_f128()).collect();
    for (claim, g) in stack_pd.iter().zip(gammas_pd.iter()) {
        target_combined += *g * claim.value();
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
                for (claim, g) in stack_pd.iter().zip(gammas_pd.iter()) {
                    acc += *g * stack_claim_eq_at(claim, &x);
                }
                acc
            })
            .collect()
    };

    let ok = ligerito::recursive_verifier_with_basis_succinct(
        lig_config,
        &proof.ligerito,
        log_n,
        target_combined,
        &stack_commitment.root,
        eval_b_residual,
        challenger,
    );
    if !ok {
        return Err(VerifyError::BaseFold(crate::pcs::basefold::VerifyError::InvalidProofShape));
    }
    Ok(())
}

/// Ligerito-backend counterpart to [`open_batch_mixed_with_precomputed_s_hat_v`].
/// Shares the ring_switch + b_combined computation, then routes to
/// [`ligerito::recursive_prover_with_basis`] using the existing `prover_data`'s
/// codeword + tree as Ligerito's L0 commit (no L0 re-commit).
///
/// `lig_config.initial_k` must equal `commitment.params.log_batch_size` so that
/// `prover_data`'s codeword/tree shape matches what Ligerito expects for L0.
#[allow(clippy::too_many_arguments)]
pub fn open_batch_mixed_ligerito_with_precomputed_s_hat_v<Ch: Challenger>(
    packed_witness: Vec<F128>,
    prover_data: &ProverData,
    commitment: &Commitment,
    x_outers: &[&[F128]],
    precomputed_s_hat_v: &[Option<&[F128]>],
    packed_direct: &[PackedDirectClaim],
    padding: &PaddingSpec,
    lig_config: &ligerito::ProverConfig,
    challenger: &mut Ch,
) -> BatchOpeningProofLigerito {
    let trace = std::env::var("PCS_TRACE").is_ok();
    let t_total = std::time::Instant::now();

    assert_eq!(
        lig_config.initial_k, commitment.params.log_batch_size,
        "ligerito initial_k ({}) must match PcsParams.log_batch_size ({}) for L0 reuse",
        lig_config.initial_k, commitment.params.log_batch_size,
    );
    assert_eq!(
        lig_config.log_inv_rates[0], commitment.params.log_inv_rate,
        "ligerito log_inv_rates[0] ({}) must match PcsParams.log_inv_rate ({}) for L0 reuse",
        lig_config.log_inv_rates[0], commitment.params.log_inv_rate,
    );

    let combined = compute_combined_basis_and_target(
        &packed_witness,
        x_outers,
        precomputed_s_hat_v,
        packed_direct,
        padding,
        challenger,
        trace,
    );

    let t = std::time::Instant::now();
    let ligerito_proof = ligerito::recursive_prover_with_basis_precomputed_round0(
        lig_config,
        packed_witness,
        combined.b_combined,
        combined.target_combined,
        &prover_data.codeword,
        &prover_data.merkle_tree,
        combined.round0_prime,
        challenger,
    );
    if trace {
        eprintln!(
            "  [open_batch] ligerito::recursive_prover_with_basis: {:6.2} ms",
            t.elapsed().as_secs_f64() * 1e3
        );
        eprintln!(
            "  [open_batch] TOTAL: {:6.2} ms",
            t_total.elapsed().as_secs_f64() * 1e3
        );
    }

    BatchOpeningProofLigerito {
        ring_switches: combined.ring_switches,
        ligerito: ligerito_proof,
    }
}

/// What ring_switch + claim-combination produces, fed to either BaseFold or Ligerito.
struct CombinedClaim {
    ring_switches: Vec<RingSwitchProof>,
    b_combined: Vec<F128>,
    target_combined: F128,
    /// BaseFold's round-0 sumcheck `(u_0, u_2)` prime. Ligerito ignores it.
    round0_prime: (F128, F128),
}

/// Shared by both backends: runs ring_switch over RS claims, observes packed-
/// direct claim values + samples their gammas, then builds `b_combined` (the
/// γ-weighted linear combination of all `rs_eq_ind`s and `eq_ind`s) and
/// `target_combined`. Also computes the BaseFold round-0 prime as a side
/// effect (cheap since it shares the b_combined pass).
#[allow(clippy::too_many_arguments)]
fn compute_combined_basis_and_target<Ch: Challenger>(
    packed_witness: &[F128],
    x_outers: &[&[F128]],
    precomputed_s_hat_v: &[Option<&[F128]>],
    packed_direct: &[PackedDirectClaim],
    padding: &PaddingSpec,
    challenger: &mut Ch,
    trace: bool,
) -> CombinedClaim {
    let n_rs = x_outers.len();
    let n_pd = packed_direct.len();
    assert!(n_rs + n_pd > 0, "open_batch_mixed: need at least one claim");
    assert!(
        precomputed_s_hat_v.is_empty() || precomputed_s_hat_v.len() == n_rs,
        "precomputed_s_hat_v: must be empty or length {n_rs}, got {}",
        precomputed_s_hat_v.len(),
    );

    challenger.observe_label(b"flock-pcs-open-batch-v0");

    // 1. Ring-switching for all x_outers.
    let t = std::time::Instant::now();
    let (rs_results, gammas_rs): (
        Vec<(RingSwitchProof, ring_switch::RingSwitchBatchOutput)>,
        Vec<F128>,
    ) = if n_rs > 0 {
        ring_switch::prove_batched_padded_with_precomputed(
            packed_witness,
            x_outers,
            precomputed_s_hat_v,
            padding,
            challenger,
        )
    } else {
        (Vec::new(), Vec::new())
    };
    if trace {
        eprintln!(
            "  [open_batch] ring_switch::prove_batched ×{}: {:6.2} ms",
            n_rs,
            t.elapsed().as_secs_f64() * 1e3
        );
    }

    // 2. Observe packed-direct claim values + sample γ_pd.
    for pd in packed_direct {
        challenger.observe_label(b"flock-pcs-packed-direct-v0");
        challenger.observe_f128(pd.value);
    }
    let gammas_pd: Vec<F128> = (0..n_pd).map(|_| challenger.sample_f128()).collect();

    let t = std::time::Instant::now();
    use rayon::prelude::*;

    let l = if let Some((_, out)) = rs_results.first() {
        out.rs_eq_ind.len()
    } else {
        1usize << packed_direct[0].point.len()
    };
    debug_assert!(rs_results.iter().all(|(_, o)| o.rs_eq_ind.len() == l));
    debug_assert!(
        packed_direct.iter().all(|pd| 1usize << pd.point.len() == l),
        "all packed-direct claims must share L (= packed witness length)"
    );

    let mut target_combined = F128::ZERO;
    for ((_, output), g) in rs_results.iter().zip(gammas_rs.iter()) {
        target_combined += *g * output.sumcheck_claim;
    }
    for (pd, g) in packed_direct.iter().zip(gammas_pd.iter()) {
        target_combined += *g * pd.value;
    }

    let rs_baked: Vec<&[F128]> = rs_results
        .iter()
        .filter_map(|(_, o)| match &o.rs_eq_ind {
            ring_switch::RsEqInd::Dense(v) => Some(v.as_slice()),
            _ => None,
        })
        .collect();
    // Deferred-dense claims (fused fast path): the per-claim `γ_k·B_k` buffer
    // was never materialized — fold each slot on the fly below and accumulate
    // straight into `b_combined`, saving a 2^(m-7) materialize + readback per
    // claim. Carries (eq_lo, eq_hi, γ-baked table, log₂ B).
    let rs_deferred: Vec<(&[F128], &[F128], &[F128], usize)> = rs_results
        .iter()
        .filter_map(|(_, o)| match &o.rs_eq_ind {
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
    let pd_dense: Vec<(&[F128], F128)> = packed_direct
        .iter()
        .zip(gammas_pd.iter())
        .filter_map(|(pd, g)| match &pd.eq_ind {
            DirectEqInd::Dense(v) => Some((v.as_slice(), *g)),
            _ => None,
        })
        .collect();

    // ---- Build b_combined (γ-weighted sum of all rs_eq_ind + eq_ind) and the
    //      BaseFold round-0 prime (u_0, u_2 over packed_witness · b_combined).
    let mut b_combined: Vec<F128> = crate::scratch::take_f128(l);

    // Fast path (compression-proof open: claims ab, c): every RS claim is a
    // fused DeferredDense fold and there are no packed-direct claims. Fold all
    // claims block-by-block straight into b_combined — each claim's `e_hi`
    // hoisted once per block, exactly as in `fold_b128_elems_split` — and fuse
    // the round-0 prime in the same pass. Neither the per-claim `γ_k·B_k` buffer
    // nor a combine readback is ever materialized (saves ~2·L writes + 2·L reads
    // of the 2^(m-7) basis).
    let use_fast = packed_direct.is_empty()
        && !rs_deferred.is_empty()
        && rs_deferred.len() == rs_results.len();

    let (mut round0_u0, mut round0_u2) = if use_fast {
        let b = rs_deferred[0].0.len(); // eq_lo.len(); shared across claims (same split)
        debug_assert!(b >= 2 && b.is_multiple_of(2));
        debug_assert!(rs_deferred.iter().all(|d| d.0.len() == b));
        b_combined
            .par_chunks_mut(b)
            .enumerate()
            .map(|(hi, out_block)| {
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
                // Round-0 prime over this block's pairs (b is even, base is even).
                let base = hi * b;
                let mut u0 = F128::ZERO;
                let mut u2 = F128::ZERO;
                for t in 0..(b / 2) {
                    let s0 = out_block[2 * t];
                    let s1 = out_block[2 * t + 1];
                    let a0 = packed_witness[base + 2 * t];
                    let a1 = packed_witness[base + 2 * t + 1];
                    u0 += a0 * s0;
                    u2 += (a0 + a1) * (s0 + s1);
                }
                (u0, u2)
            })
            .reduce(
                || (F128::ZERO, F128::ZERO),
                |(x0, x2), (y0, y2)| (x0 + y0, x2 + y2),
            )
    } else {
        // General path (mixed / sparse / packed-direct): materialize any
        // deferred-dense claims (parallel block fold), then the per-element
        // combine over all dense buffers + packed-direct, matching the
        // original behavior.
        let materialized: Vec<Vec<F128>> = rs_results
            .iter()
            .filter_map(|(_, o)| match &o.rs_eq_ind {
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
        let prime = b_combined
            .par_chunks_mut(2)
            .enumerate()
            .map(|(i, chunk)| {
                let mut b0 = F128::ZERO;
                let mut b1 = F128::ZERO;
                for v in rs_dense_all.iter() {
                    b0 += v[2 * i];
                    b1 += v[2 * i + 1];
                }
                for (v, g) in pd_dense.iter() {
                    b0 += *g * v[2 * i];
                    b1 += *g * v[2 * i + 1];
                }
                chunk[0] = b0;
                chunk[1] = b1;
                let a0 = packed_witness[2 * i];
                let a1 = packed_witness[2 * i + 1];
                (a0 * b0, (a0 + a1) * (b0 + b1))
            })
            .reduce(
                || (F128::ZERO, F128::ZERO),
                |(x0, x2), (y0, y2)| (x0 + y0, x2 + y2),
            );
        for v in materialized {
            crate::scratch::give_f128(v);
        }
        prime
    };
    let mut adjust_prime_for_delta = |idx: usize, delta: F128| {
        let pair = idx / 2;
        let a0 = packed_witness[2 * pair];
        let a1 = packed_witness[2 * pair + 1];
        if idx & 1 == 0 {
            round0_u0 += a0 * delta;
        }
        round0_u2 += (a0 + a1) * delta;
    };
    for (_, output) in rs_results.iter() {
        if let ring_switch::RsEqInd::Sparse { entries, .. } = &output.rs_eq_ind {
            for &(idx, val) in entries {
                b_combined[idx] += val;
                adjust_prime_for_delta(idx, val);
            }
        }
    }
    for (pd, g) in packed_direct.iter().zip(gammas_pd.iter()) {
        if let DirectEqInd::Sparse(eq) = &pd.eq_ind {
            sparse_scatter_add_parallel(&mut b_combined, eq, *g);
            let (u0_fix, u2_fix) = b_combined
                .par_chunks(2)
                .enumerate()
                .map(|(i, chunk)| {
                    let a0 = packed_witness[2 * i];
                    let a1 = packed_witness[2 * i + 1];
                    (a0 * chunk[0], (a0 + a1) * (chunk[0] + chunk[1]))
                })
                .reduce(
                    || (F128::ZERO, F128::ZERO),
                    |(x0, x2), (y0, y2)| (x0 + y0, x2 + y2),
                );
            round0_u0 = u0_fix;
            round0_u2 = u2_fix;
        }
    }
    if trace {
        eprintln!(
            "  [open_batch] combine rs_eq_ind (L={}, rs×{}, pd×{}): {:6.2} ms",
            l,
            n_rs,
            n_pd,
            t.elapsed().as_secs_f64() * 1e3
        );
    }

    CombinedClaim {
        ring_switches: rs_results
            .into_iter()
            .map(|(p, o)| {
                // The per-claim rs_eq_ind (L F128s) dies here — recycle it.
                if let ring_switch::RsEqInd::Dense(v) = o.rs_eq_ind {
                    crate::scratch::give_f128(v);
                }
                p
            })
            .collect(),
        b_combined,
        target_combined,
        round0_prime: (round0_u0, round0_u2),
    }
}

/// Parallel sparse scatter-add: `b_combined[scatter_idx(c)] += gamma * eq.live_tensor[c]`
/// for every `c`. Partitions `c`-space across rayon threads; since
/// [`SparseEqTensor::scatter_idx`] is monotonic in `c` (live_positions sorted
/// ascending), each thread's scattered indices fall in a contiguous, disjoint
/// range of `b_combined`. Splits `b_combined` at the chunk boundaries via
/// `split_at_mut`, then writes scatter-adds into the disjoint mutable slices —
/// safe rust, no atomics.
fn sparse_scatter_add_parallel(b_combined: &mut [F128], eq: &SparseEqTensor, gamma: F128) {
    use rayon::prelude::*;

    let c_total = eq.live_tensor.len();
    if c_total == 0 {
        return;
    }
    let n_threads = rayon::current_num_threads().max(1);
    let c_per_chunk = c_total.div_ceil(n_threads).max(1);
    let actual_n_chunks = c_total.div_ceil(c_per_chunk);

    // Boundaries in `b_combined` index space. `b_boundaries[i]` is where chunk
    // `i` starts. `b_boundaries[i+1] − b_boundaries[i]` is chunk `i`'s slice
    // length. The last chunk extends to `b_combined.len()` to absorb any tail
    // positions beyond the maximum scatter idx (those contain only dense
    // contributions from the parallel pass).
    let b_boundaries: Vec<usize> = (0..=actual_n_chunks)
        .map(|i| {
            if i == 0 {
                0
            } else if i == actual_n_chunks {
                b_combined.len()
            } else {
                eq.scatter_idx(i * c_per_chunk)
            }
        })
        .collect();
    debug_assert!(b_boundaries.windows(2).all(|w| w[0] <= w[1]));

    // Disjoint mutable slices via repeated split_at_mut.
    let mut remaining: &mut [F128] = b_combined;
    let mut slices: Vec<&mut [F128]> = Vec::with_capacity(actual_n_chunks);
    for i in 1..actual_n_chunks {
        let split_at = b_boundaries[i] - b_boundaries[i - 1];
        let (left, right) = remaining.split_at_mut(split_at);
        slices.push(left);
        remaining = right;
    }
    slices.push(remaining);
    debug_assert_eq!(slices.len(), actual_n_chunks);

    slices.into_par_iter().enumerate().for_each(|(t, slice)| {
        let c_lo = t * c_per_chunk;
        let c_hi = ((t + 1) * c_per_chunk).min(c_total);
        let b_lo = b_boundaries[t];
        for c in c_lo..c_hi {
            let val = eq.live_tensor[c];
            let idx = eq.scatter_idx(c);
            slice[idx - b_lo] += gamma * val;
        }
    });
}

/// Verify a batched opening produced by [`open_batch`]. Each `(claim, z_skip,
/// x_outer)` triple is checked via its own ring-switching message; then the
/// random-linear-combination of their `rs_eq_ind`s is verified against the
/// single BaseFold proof.
pub fn verify_opening_batch<Ch: Challenger>(
    commitment: &Commitment,
    claims: &[F128],
    z_skips: &[F128],
    x_outers: &[&[F128]],
    proof: &BatchOpeningProof,
    challenger: &mut Ch,
) -> Result<(), VerifyError> {
    verify_opening_batch_mixed(
        commitment,
        claims,
        z_skips,
        x_outers,
        &[],
        proof,
        challenger,
    )
}

/// Verifier reference to a packed-direct claim: the multilinear point at
/// which `ẑ_packed` was claimed equal to `value`. The verifier owns the data
/// (it appears in the public statement of whatever produced the claim, e.g.
/// the chain shift sumcheck output).
#[derive(Clone, Copy, Debug)]
pub struct PackedDirectClaimRef<'a> {
    pub point: &'a [F128],
    pub value: F128,
}

/// Verify a mixed-claim batched opening. Mirror of [`open_batch_mixed`].
#[allow(clippy::too_many_arguments)]
pub fn verify_opening_batch_mixed<Ch: Challenger>(
    commitment: &Commitment,
    claims: &[F128],
    z_skips: &[F128],
    x_outers: &[&[F128]],
    packed_direct: &[PackedDirectClaimRef<'_>],
    proof: &BatchOpeningProof,
    challenger: &mut Ch,
) -> Result<(), VerifyError> {
    let n_rs = claims.len();
    let n_pd = packed_direct.len();
    assert_eq!(z_skips.len(), n_rs);
    assert_eq!(x_outers.len(), n_rs);
    assert_eq!(proof.ring_switches.len(), n_rs);
    assert!(
        n_rs + n_pd > 0,
        "verify_opening_batch_mixed: need at least one claim"
    );

    challenger.observe_label(b"flock-pcs-open-batch-v0");

    let trace = std::env::var("VERIFY_TRACE").is_ok();
    let fmt = |s: f64| -> String {
        let ms = s * 1000.0;
        if ms < 1.0 {
            format!("{:>8.2} µs", s * 1e6)
        } else {
            format!("{:>8.2} ms", ms)
        }
    };

    // 1. Ring-switch verify per ring-switched claim (succinct: skip dense
    //    rs_eq_ind alloc). After all RS claims are observed, sample γ_rs —
    //    matches the prover's `prove_batched_padded_with_precomputed` which
    //    samples γ_rs at the same transcript point and bakes it into the fold.
    let t = std::time::Instant::now();
    let mut rs_outputs = Vec::with_capacity(n_rs);
    for i in 0..n_rs {
        let out = ring_switch::verify_succinct(
            claims[i],
            z_skips[i],
            x_outers[i],
            &proof.ring_switches[i],
            challenger,
        )
        .map_err(VerifyError::RingSwitch)?;
        rs_outputs.push(out);
    }
    let gammas_rs: Vec<F128> = (0..n_rs).map(|_| challenger.sample_f128()).collect();
    if trace {
        eprintln!(
            "      [pcsv] ring_switch::verify_succinct ×{}: {}",
            n_rs,
            fmt(t.elapsed().as_secs_f64())
        );
    }

    // 2. Observe packed-direct claim values, then sample γ_pd (Schwartz-
    //    Zippel-sound: γ_pd[k] is sampled after pd.value[k] is observed).
    for pd in packed_direct {
        challenger.observe_label(b"flock-pcs-packed-direct-v0");
        challenger.observe_f128(pd.value);
    }
    let gammas_pd: Vec<F128> = (0..n_pd).map(|_| challenger.sample_f128()).collect();

    // 4. Combined target: γ_rs · sumcheck_claim_rs + γ_pd · value_pd.
    let mut target_combined = F128::ZERO;
    for (out, g) in rs_outputs.iter().zip(gammas_rs.iter()) {
        target_combined += *g * out.sumcheck_claim;
    }
    for (pd, g) in packed_direct.iter().zip(gammas_pd.iter()) {
        target_combined += *g * pd.value;
    }

    // 5. BaseFold verify against combined target.
    let t = std::time::Instant::now();
    let ntt = crate::ntt::AdditiveNttF128::standard(commitment.params.k_code());
    if trace {
        eprintln!(
            "      [pcsv] AdditiveNttF128::standard: {}",
            fmt(t.elapsed().as_secs_f64())
        );
    }
    let t = std::time::Instant::now();
    let challenges = basefold::verify(
        target_combined,
        &proof.basefold,
        &commitment.root,
        &ntt,
        commitment.params.log_inv_rate,
        commitment.params.log_batch_size,
        challenger,
    )
    .map_err(VerifyError::BaseFold)?;
    if trace {
        eprintln!(
            "      [pcsv] basefold::verify: {}",
            fmt(t.elapsed().as_secs_f64())
        );
    }

    // 6. `final_b` must equal Σ_rs γ_rs · MLE(rs_eq_ind, challenges) + Σ_pd γ_pd ·
    //    eq_eval(point, challenges). Ring-switched uses the DP24 succinct
    //    recurrence; packed-direct uses the standard multilinear eq evaluation.
    let t = std::time::Instant::now();
    let mut expected_final_b = F128::ZERO;
    for (out, (g, x_outer)) in rs_outputs.iter().zip(gammas_rs.iter().zip(x_outers.iter())) {
        expected_final_b +=
            *g * ring_switch::eval_rs_eq(&x_outer[1..], &challenges, &out.eq_r_dprime);
    }
    // Packed-direct: γ_pd · eq_eval(point, basefold_challenges). The basefold
    // challenges have length L = m − 7, matching the packed-direct point.
    for (pd, g) in packed_direct.iter().zip(gammas_pd.iter()) {
        expected_final_b += *g * crate::zerocheck::multilinear::eq_eval(pd.point, &challenges);
    }
    if trace {
        eprintln!(
            "      [pcsv] eval_rs_eq ×{} + eq_eval pd×{}: {}",
            n_rs,
            n_pd,
            fmt(t.elapsed().as_secs_f64())
        );
    }
    if expected_final_b != proof.basefold.final_b {
        return Err(VerifyError::FinalBMismatch);
    }
    Ok(())
}

/// Ligerito-backend mirror of [`verify_opening_batch_mixed`]. Uses
/// `ring_switch::verify` (non-succinct, so it returns the dense `rs_eq_ind`)
/// to reconstruct `b_combined`, then delegates to
/// [`ligerito::recursive_verifier_with_basis`].
///
/// NOTE: this is the simple (non-succinct) verifier path; it materializes
/// the full `2^(m-7)` rs_eq_ind, costing ~16 MB at m=29. A succinct variant
/// (DP24-style polylog reconstruction at the residual point only) is a
/// natural follow-up — would bring verifier cost in line with the basefold
/// succinct path.
#[allow(clippy::too_many_arguments)]
pub fn verify_opening_batch_ligerito_mixed<Ch: Challenger>(
    commitment: &Commitment,
    claims: &[F128],
    z_skips: &[F128],
    x_outers: &[&[F128]],
    packed_direct: &[PackedDirectClaimRef<'_>],
    proof: &BatchOpeningProofLigerito,
    lig_config: &ligerito::VerifierConfig,
    challenger: &mut Ch,
) -> Result<(), VerifyError> {
    let n_rs = claims.len();
    let n_pd = packed_direct.len();
    assert_eq!(z_skips.len(), n_rs);
    assert_eq!(x_outers.len(), n_rs);
    assert_eq!(proof.ring_switches.len(), n_rs);
    assert!(n_rs + n_pd > 0);

    challenger.observe_label(b"flock-pcs-open-batch-v0");

    // 1. Ring-switch SUCCINCT verify per claim — gets sumcheck_claim and a
    //    length-128 `eq_r_dprime` instead of the dense `rs_eq_ind`. Saves
    //    ~16 MB allocation at m=29.
    let mut rs_outputs = Vec::with_capacity(n_rs);
    for i in 0..n_rs {
        let out = ring_switch::verify_succinct(
            claims[i],
            z_skips[i],
            x_outers[i],
            &proof.ring_switches[i],
            challenger,
        )
        .map_err(VerifyError::RingSwitch)?;
        rs_outputs.push(out);
    }
    let gammas_rs: Vec<F128> = (0..n_rs).map(|_| challenger.sample_f128()).collect();

    // 2. PD claim values + γ_pd.
    for pd in packed_direct {
        challenger.observe_label(b"flock-pcs-packed-direct-v0");
        challenger.observe_f128(pd.value);
    }
    let gammas_pd: Vec<F128> = (0..n_pd).map(|_| challenger.sample_f128()).collect();

    // 3. target_combined from succinct rs claims + PD values.
    let mut target_combined = F128::ZERO;
    for (out, g) in rs_outputs.iter().zip(gammas_rs.iter()) {
        target_combined += *g * out.sumcheck_claim;
    }
    for (pd, g) in packed_direct.iter().zip(gammas_pd.iter()) {
        target_combined += *g * pd.value;
    }

    // 4. Batch evaluator: returns b_combined at all yr positions in one call.
    //    For RS claims, precompute the ring_switch tensor PREFIX once (over
    //    the ris part) and only re-do the yr_log_n-step suffix per y.
    //    For PD claims, precompute eq prefix factors over ris and finish per y.
    //    For BLAKE3 m=30: ris is 19 dims, yr is 4 dims → 19× prefix reuse.
    let log_n = commitment.params.m - LOG_PACKING;
    let eval_b_residual = |ris: &[F128], yr_log_n: usize| -> Vec<F128> {
        use crate::zerocheck::multilinear::eq_eval;
        let yr_len = 1usize << yr_log_n;
        let prefix_len = ris.len();

        // ---- RS claim prefixes ----
        let rs_prefixes: Vec<crate::pcs::tensor_algebra::TensorAlgebra> = rs_outputs
            .iter()
            .zip(x_outers.iter())
            .map(|(_out, x_outer)| {
                // x_outer[1..] has length log_n; we feed only the ris prefix.
                ring_switch::eval_rs_eq_prefix(&x_outer[1..1 + prefix_len], ris)
            })
            .collect();

        // ---- PD claim prefix scalars ----
        // eq(pd.point, point) factors over coordinates; precompute the prefix product.
        let pd_prefix_scalars: Vec<F128> = packed_direct
            .iter()
            .map(|pd| eq_eval(&pd.point[..prefix_len], ris))
            .collect();

        // ---- Per-y assembly (parallel over yr positions; each y is independent).
        //      y_suffix is binary (bits of y), so we use the binary-query
        //      specializations of eval_rs_eq_finish / eq_eval — each suffix
        //      step collapses to a single scale_vertical / scalar product.
        use rayon::prelude::*;
        debug_assert!(yr_log_n <= 32, "yr_log_n > 32 not supported by binary path");
        (0..yr_len)
            .into_par_iter()
            .map(|y| {
                let y_bits = y as u32;
                let mut sum = F128::ZERO;
                for (((out, g), x_outer), prefix) in rs_outputs
                    .iter()
                    .zip(gammas_rs.iter())
                    .zip(x_outers.iter())
                    .zip(rs_prefixes.iter())
                {
                    sum += *g
                        * ring_switch::eval_rs_eq_finish_from_prefix_binary_q(
                            prefix,
                            &x_outer[1 + prefix_len..],
                            y_bits,
                            &out.eq_r_dprime,
                        );
                }
                for ((pd, g), prefix_scalar) in packed_direct
                    .iter()
                    .zip(gammas_pd.iter())
                    .zip(pd_prefix_scalars.iter())
                {
                    sum += *g
                        * *prefix_scalar
                        * crate::zerocheck::multilinear::eq_eval_binary_x(
                            &pd.point[prefix_len..],
                            y_bits,
                        );
                }
                sum
            })
            .collect()
    };

    // 5. Drive ligerito SUCCINCT verifier — eval_b_residual is called ONCE
    //    at the residual check (returns all yr_len values in one batch).
    let ok = ligerito::recursive_verifier_with_basis_succinct(
        lig_config,
        &proof.ligerito,
        log_n,
        target_combined,
        &commitment.root,
        eval_b_residual,
        challenger,
    );
    if !ok {
        return Err(VerifyError::BaseFold(
            crate::pcs::basefold::VerifyError::InvalidProofShape,
        ));
    }
    Ok(())
}

/// Verify an opening proof against the commitment. Returns `Ok(())` iff valid.
pub fn verify_opening<Ch: Challenger>(
    commitment: &Commitment,
    claim: F128,
    z_skip: F128,
    x_outer: &[F128],
    proof: &OpeningProof,
    challenger: &mut Ch,
) -> Result<(), VerifyError> {
    challenger.observe_label(b"flock-pcs-open-v0");

    // Ring-switching (succinct): claim → sumcheck_claim + eq_r_dprime. The
    // dense rs_eq_ind is never materialized on the verifier side.
    let rs_output =
        ring_switch::verify_succinct(claim, z_skip, x_outer, &proof.ring_switch, challenger)
            .map_err(VerifyError::RingSwitch)?;

    // BaseFold sumcheck + FRI: sumcheck_claim → verified final_a · final_b.
    let ntt = crate::ntt::AdditiveNttF128::standard(commitment.params.k_code());
    let challenges = basefold::verify(
        rs_output.sumcheck_claim,
        &proof.basefold,
        &commitment.root,
        &ntt,
        commitment.params.log_inv_rate,
        commitment.params.log_batch_size,
        challenger,
    )
    .map_err(VerifyError::BaseFold)?;

    // Independent check: final_b should equal MLE(rs_eq_ind)(challenges).
    // Computed succinctly via the DP24 tensor-algebra recurrence (polylog in
    // witness size), instead of materializing rs_eq_ind densely.
    let expected_final_b =
        ring_switch::eval_rs_eq(&x_outer[1..], &challenges, &rs_output.eq_r_dprime);
    if expected_final_b != proof.basefold.final_b {
        return Err(VerifyError::FinalBMismatch);
    }

    Ok(())
}
