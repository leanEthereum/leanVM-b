import SphincsSecurity.Proof.JointProbeCollisionStructuralStep
import SphincsSecurity.Proof.JointParentReserveConservation
import SphincsSecurity.Proof.CollisionTerminalReserve

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] parentReserve answerPotential
set_option backward.isDefEq.respectTransparency false

theorem twice_parentReserve_scaled_le_collisionRecordPotential
    (key : SecretKey) (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (hcap : QueryCache.enncard cache ≤ (Fintype.card Digest : ENNReal)) :
    (parentReserve key.parameter key.otsSecret key.ftsSecret
      (fun position => ¬ OtsProbeSimulation.IsOtsPosition position) cache : ENNReal) *
      (2 * (Fintype.card Digest : ENNReal)⁻¹) ≤ collisionStructuralRecordPotential key cache none := by
  have hanswer : (answerPotential key.parameter key.otsSecret key.ftsSecret cache : ENNReal) ≤
      (Fintype.card Digest : ENNReal) := by
    have h := Nat.cast_le (α := ENNReal).mpr (answerPotential_le_cachedInputs key.parameter key.otsSecret key.ftsSecret hfinite)
    rw [hfinite.cachedInputs_ncard_toENNReal_eq_enncard] at h
    exact h.trans hcap
  have hsmall : (answerPotential key.parameter key.otsSecret key.ftsSecret cache : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ ≤ 1 :=
    (mul_le_mul' hanswer le_rfl).trans_eq (ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (by finiteness))
  have h := answer_parent_reserves_le_collisionRecordPotential key cache hfinite
  rw [min_eq_right hsmall] at h
  apply le_trans ?_ h
  rw [mul_left_comm, two_mul]
  exact add_le_add (mul_le_mul' (Nat.cast_le.mpr (parentReserve_le_answerPotential key.parameter _ _ _ _)) le_rfl) le_rfl

theorem twice_survivingFtsParentReserve_scaled_le_collisionEnvelope
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cache : QueryCache HashSpec) (result : (α × QueryCache HashSpec) × Bool)
    (hfinite : Finite result.1.2) (hcap : QueryCache.enncard result.1.2 ≤ (Fintype.card Digest : ENNReal)) :
    survivingFtsParentReserve (secretKey parameter root otsTable ftsTable) result.1.2 result.2 * (2 * (Fintype.card Digest : ENNReal)⁻¹) ≤
      collisionStructuralEnvelope parameter root otsTable ftsTable cache result := by
  cases hh : result.2 with
  | true => simp only [survivingFtsParentReserve, if_true, zero_mul, zero_le]
  | false =>
      simp only [survivingFtsParentReserve, collisionStructuralEnvelope, hh, Bool.false_eq_true, if_false]
      exact twice_parentReserve_scaled_le_collisionRecordPotential (secretKey parameter root otsTable ftsTable) result.1.2 hfinite hcap

theorem expected_collisionPotential_add_twice_sharedParentDiscard_step_le
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Frame) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (henabled : frame.Enabled parameter otsTable ftsTable input cache false)
    (hcomputed : OtsProbeSimulation.DeferredComputationsClosed frame.context)
    (hcap : ∀ result ∈ support (stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      input (some frame) cache false false), QueryCache.enncard result.1.2.1.2 ≤ (Fintype.card Digest : ENNReal)) :
    (∑' result, Pr[= result | stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      input (some frame) cache false false] *
      collisionSurvivingStructuralPotential (secretKey parameter root otsTable ftsTable) result.1.2.1.2 result.1.2.2 result.2) +
      sharedFailureDiscardStep (parentException parameter otsTable ftsTable) (survivingFtsParentReserve (secretKey parameter root otsTable ftsTable))
        parameter root otsTable ftsTable input (some frame) cache false false * (2 * (Fintype.card Digest : ENNReal)⁻¹) ≤
      collisionStructuralRecordPotential (secretKey parameter root otsTable ftsTable) cache none +
        expectedPreExceptionCharge (parentException parameter otsTable ftsTable) (collisionSigningStructuralCharge (secretKey parameter root otsTable ftsTable))
          (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache false * (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [sharedFailureDiscardStep]
  simp only [Bool.false_eq_true, if_false]
  rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
  apply le_trans _ (expected_collisionStructuralEnvelope_step_le parameter root otsTable ftsTable input (some frame) cache hfinite)
  apply ENNReal.tsum_le_tsum
  intro result
  rw [mul_assoc, ← mul_add]
  by_cases hr : result ∈ support (stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      input (some frame) cache false false)
  · apply mul_le_mul' le_rfl
    cases hf : result.2 with
    | true =>
        simp only [collisionSurvivingStructuralPotential, if_true, zero_add]
        have ha := stepWithFailure_original_support (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
          input (some frame) cache false false result hr
        have hfin := finite_cache_of_mem_support _ cache result.1.2.1.1 result.1.2.1.2
          (runExceptionMonitor_support_project (parentException parameter otsTable ftsTable) _ cache false ha) hfinite
        exact twice_survivingFtsParentReserve_scaled_le_collisionEnvelope parameter root otsTable ftsTable cache result.1.2 hfin (hcap result hr)
    | false =>
        simp only [Bool.false_eq_true, if_false, zero_mul, add_zero]
        have he : ¬ EarlyOtsParentTransition parameter otsTable ftsTable cache result.1.2.1.2 := by
          intro he
          have h := stepWithFailure_earlyOtsParent_imp_failed (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
            input frame cache henabled hcomputed result hr he
          simp [hf] at h
        cases hh : result.1.2.2 <;> simp [collisionSurvivingStructuralPotential, collisionStructuralEnvelope, he, hh]
  · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
