import SphincsSecurity.Proof.JointSigningCollisionCoverage
import SphincsSecurity.Proof.DoubleSharedParentRefundStep

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
set_option backward.isDefEq.respectTransparency false

noncomputable def jointCollisionCoverageFailureOverlap
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (state : CoverLogState) : ENNReal :=
  ∑' result, Pr[= result | stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
    input frame state.1 false false] *
      (if result.2 then jointCollisionCoverageStepEnvelope parameter root otsTable ftsTable cap budget input state result.1.2 else 0)

theorem jointCollisionCoverageStepFailureCharge_add_overlap
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (state : CoverLogState) :
    jointCollisionCoverageStepFailureCharge parameter root otsTable ftsTable cap budget input frame state +
      jointCollisionCoverageFailureOverlap parameter root otsTable ftsTable cap budget input frame state =
        Pr[fun result => result.2 = true | stepWithFailure (parentException parameter otsTable ftsTable)
          parameter root otsTable ftsTable input frame state.1 false false] := by
  rw [jointCollisionCoverageStepFailureCharge, jointCollisionCoverageFailureOverlap, probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
  apply tsum_congr
  intro result
  rw [← mul_add]
  cases result.2 <;> simp only [Bool.false_eq_true, if_false, if_true, add_zero, mul_zero]
  rw [tsub_add_cancel_of_le (show jointCollisionCoverageStepEnvelope parameter root otsTable ftsTable cap budget input state result.1.2 ≤ 1 from
    boundedUnionPotential_le_one _ _), mul_one]

theorem twice_survivingFtsParentReserve_scaled_le_one
    (key : SecretKey) (cache : QueryCache HashSpec) (hit : Bool)
    (hfinite : Finite cache) (hcap : QueryCache.enncard cache ≤ (2 ^ 127 : Nat)) :
    survivingFtsParentReserve key cache hit * (2 * (Fintype.card Digest : ENNReal)⁻¹) ≤ 1 := by
  cases hh : hit with
  | true => simp [survivingFtsParentReserve]
  | false =>
      have hparent := (Nat.cast_le (α := ENNReal).mpr (parentReserve_le_answerPotential key.parameter key.otsSecret key.ftsSecret
        (fun position => ¬ OtsProbeSimulation.IsOtsPosition position) cache)).trans
        (Nat.cast_le.mpr (answerPotential_le_cachedInputs key.parameter key.otsSecret key.ftsSecret hfinite))
      rw [hfinite.cachedInputs_ncard_toENNReal_eq_enncard] at hparent
      simp only [survivingFtsParentReserve, Bool.false_eq_true, if_false]
      apply (mul_le_mul' (hparent.trans hcap) le_rfl).trans_eq
      norm_num [Digest, digestBits, ← mul_assoc, ENNReal.mul_inv_cancel]

theorem twice_survivingFtsParentReserve_scaled_le_jointEnvelope
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : (OracleWorld + SigningSpec).Domain) (state : CoverLogState)
    (result : ((OracleWorld + SigningSpec).Range input × QueryCache HashSpec) × Bool)
    (hfinite : Finite result.1.2) (hcap : QueryCache.enncard result.1.2 ≤ (2 ^ 127 : Nat)) :
    survivingFtsParentReserve (secretKey parameter root otsTable ftsTable) result.1.2 result.2 *
      (2 * (Fintype.card Digest : ENNReal)⁻¹) ≤ jointCollisionCoverageStepEnvelope parameter root otsTable ftsTable cap budget input state result := by
  let key := secretKey parameter root otsTable ftsTable
  have hcard : ((2 ^ 127 : Nat) : ENNReal) ≤ (Fintype.card Digest : ENNReal) := by norm_num [Digest, digestBits]
  have hleft := twice_survivingFtsParentReserve_scaled_le_collisionEnvelope parameter root otsTable ftsTable state.1 result hfinite (hcap.trans hcard)
  have hsmall := twice_survivingFtsParentReserve_scaled_le_one key result.1.2 result.2 hfinite hcap
  rw [jointCollisionCoverageStepEnvelope, boundedUnionPotential_comm, boundedUnionPotential]
  exact (le_min hsmall hleft).trans le_self_add

theorem sharedParentDiscard_scaled_le_jointFailureOverlap
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (state : CoverLogState)
    (hfinite : Finite state.1)
    (hcap : ∀ result ∈ support (stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      input frame state.1 false false), QueryCache.enncard result.1.2.1.2 ≤ (2 ^ 127 : Nat)) :
    sharedFailureDiscardStep (parentException parameter otsTable ftsTable) (survivingFtsParentReserve (secretKey parameter root otsTable ftsTable))
      parameter root otsTable ftsTable input frame state.1 false false * (2 * (Fintype.card Digest : ENNReal)⁻¹) ≤
        jointCollisionCoverageFailureOverlap parameter root otsTable ftsTable cap budget input frame state := by
  rw [sharedFailureDiscardStep, if_neg Bool.false_ne_true, jointCollisionCoverageFailureOverlap, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro result
  rw [mul_assoc]
  by_cases hr : result ∈ support (stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable input frame state.1 false false)
  · cases hf : result.2 with
    | false => simp only [Bool.false_eq_true, if_false, zero_mul, le_refl]
    | true =>
        simp only [if_true]
        have ha := stepWithFailure_original_support (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
          input frame state.1 false false result hr
        have hfin := finite_cache_of_mem_support _ state.1 result.1.2.1.1 result.1.2.1.2
          (runExceptionMonitor_support_project _ _ state.1 false ha) hfinite
        exact mul_le_mul' le_rfl (twice_survivingFtsParentReserve_scaled_le_jointEnvelope parameter root otsTable ftsTable
          cap budget input state result.1.2 hfin (hcap result hr))
  · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]

theorem jointCollisionCoverageStepFailureCharge_add_parentRefund_le
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (state : CoverLogState)
    (hfinite : Finite state.1)
    (hcap : ∀ result ∈ support (stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      input frame state.1 false false), QueryCache.enncard result.1.2.1.2 ≤ (2 ^ 127 : Nat)) :
    jointCollisionCoverageStepFailureCharge parameter root otsTable ftsTable cap budget input frame state +
      sharedFailureDiscardStep (parentException parameter otsTable ftsTable) (survivingFtsParentReserve (secretKey parameter root otsTable ftsTable))
        parameter root otsTable ftsTable input frame state.1 false false * (2 * (Fintype.card Digest : ENNReal)⁻¹) ≤
          Pr[fun result => result.2 = true | stepWithFailure (parentException parameter otsTable ftsTable)
            parameter root otsTable ftsTable input frame state.1 false false] :=
  (add_le_add le_rfl (sharedParentDiscard_scaled_le_jointFailureOverlap parameter root otsTable ftsTable cap budget input frame state hfinite hcap)).trans_eq
    (jointCollisionCoverageStepFailureCharge_add_overlap parameter root otsTable ftsTable cap budget input frame state)

noncomputable def jointCollisionCoverageParentRemainder
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : (OracleWorld + SigningSpec).Domain) (state : CoverLogState)
    (result : ((OracleWorld + SigningSpec).Range input × QueryCache HashSpec) × Bool) : ENNReal :=
  (1 - survivingFtsParentReserve (secretKey parameter root otsTable ftsTable) result.1.2 result.2 *
    (2 * (Fintype.card Digest : ENNReal)⁻¹)) *
      boundedRemainingCoveragePotential (secretKey parameter root otsTable ftsTable) cap budget
        (result.1.2, state.2 ++ signingLogFragment input result.1.1)

theorem parentRefund_add_coverageRemainder_le_jointEnvelope
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : (OracleWorld + SigningSpec).Domain) (state : CoverLogState)
    (result : ((OracleWorld + SigningSpec).Range input × QueryCache HashSpec) × Bool)
    (hfinite : Finite result.1.2) (hcap : QueryCache.enncard result.1.2 ≤ (2 ^ 127 : Nat)) :
    survivingFtsParentReserve (secretKey parameter root otsTable ftsTable) result.1.2 result.2 * (2 * (Fintype.card Digest : ENNReal)⁻¹) +
      jointCollisionCoverageParentRemainder parameter root otsTable ftsTable cap budget input state result ≤
        jointCollisionCoverageStepEnvelope parameter root otsTable ftsTable cap budget input state result := by
  have hcard : ((2 ^ 127 : Nat) : ENNReal) ≤ (Fintype.card Digest : ENNReal) := by norm_num [Digest, digestBits]
  have hl := twice_survivingFtsParentReserve_scaled_le_collisionEnvelope parameter root otsTable ftsTable state.1 result hfinite (hcap.trans hcard)
  have hs := twice_survivingFtsParentReserve_scaled_le_one (secretKey parameter root otsTable ftsTable) result.1.2 result.2 hfinite hcap
  have h := boundedUnionPotential_mono_left hl
    (remainingCoveragePotential (secretKey parameter root otsTable ftsTable) cap budget
      (result.1.2, state.2 ++ signingLogFragment input result.1.1) ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹)
  conv_lhs at h => rw [boundedUnionPotential_comm, boundedUnionPotential, min_eq_right hs]
  exact h

noncomputable def jointFailureCoverageAfterParentRefund
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (state : CoverLogState) : ENNReal :=
  ∑' result, Pr[= result | stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
    input frame state.1 false false] *
      (if result.2 then jointCollisionCoverageParentRemainder parameter root otsTable ftsTable cap budget input state result.1.2 else 0)

theorem sharedParentDiscard_add_coverageRemainder_le_jointFailureOverlap
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (state : CoverLogState)
    (hfinite : Finite state.1)
    (hcap : ∀ result ∈ support (stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      input frame state.1 false false), QueryCache.enncard result.1.2.1.2 ≤ (2 ^ 127 : Nat)) :
    sharedFailureDiscardStep (parentException parameter otsTable ftsTable) (survivingFtsParentReserve (secretKey parameter root otsTable ftsTable))
      parameter root otsTable ftsTable input frame state.1 false false * (2 * (Fintype.card Digest : ENNReal)⁻¹) +
        jointFailureCoverageAfterParentRefund parameter root otsTable ftsTable cap budget input frame state ≤
          jointCollisionCoverageFailureOverlap parameter root otsTable ftsTable cap budget input frame state := by
  rw [sharedFailureDiscardStep, if_neg Bool.false_ne_true, jointFailureCoverageAfterParentRefund,
    jointCollisionCoverageFailureOverlap, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  rw [mul_assoc, ← mul_add]
  by_cases hr : result ∈ support (stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable input frame state.1 false false)
  · cases hf : result.2 with
    | false => simp only [Bool.false_eq_true, if_false, zero_mul, add_zero, le_refl]
    | true =>
        simp only [if_true]
        have ha := stepWithFailure_original_support (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
          input frame state.1 false false result hr
        have hfin := finite_cache_of_mem_support _ state.1 result.1.2.1.1 result.1.2.1.2
          (runExceptionMonitor_support_project _ _ state.1 false ha) hfinite
        exact mul_le_mul' le_rfl (parentRefund_add_coverageRemainder_le_jointEnvelope parameter root otsTable ftsTable
          cap budget input state result.1.2 hfin (hcap result hr))
  · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]

theorem jointCollisionCoverageStepFailureCharge_add_parent_and_coverage_le
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (state : CoverLogState)
    (hfinite : Finite state.1)
    (hcap : ∀ result ∈ support (stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      input frame state.1 false false), QueryCache.enncard result.1.2.1.2 ≤ (2 ^ 127 : Nat)) :
    jointCollisionCoverageStepFailureCharge parameter root otsTable ftsTable cap budget input frame state +
      (sharedFailureDiscardStep (parentException parameter otsTable ftsTable) (survivingFtsParentReserve (secretKey parameter root otsTable ftsTable))
        parameter root otsTable ftsTable input frame state.1 false false * (2 * (Fintype.card Digest : ENNReal)⁻¹) +
          jointFailureCoverageAfterParentRefund parameter root otsTable ftsTable cap budget input frame state) ≤
            Pr[fun result => result.2 = true | stepWithFailure (parentException parameter otsTable ftsTable)
              parameter root otsTable ftsTable input frame state.1 false false] :=
  (add_le_add le_rfl (sharedParentDiscard_add_coverageRemainder_le_jointFailureOverlap parameter root otsTable ftsTable
    cap budget input frame state hfinite hcap)).trans_eq
      (jointCollisionCoverageStepFailureCharge_add_overlap parameter root otsTable ftsTable cap budget input frame state)

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
