import SphincsSecurity.Proof.JointProbeCollisionStructuralStep
import SphincsSecurity.Proof.JointParentReserveConservation

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] parentReserve
set_option backward.isDefEq.respectTransparency false

theorem survivingFtsParentReserve_scaled_le_collisionEnvelope
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cache : QueryCache HashSpec) (result : (α × QueryCache HashSpec) × Bool) :
    survivingFtsParentReserve (secretKey parameter root otsTable ftsTable) result.1.2 result.2 * (Fintype.card Digest : ENNReal)⁻¹ ≤
      collisionStructuralEnvelope parameter root otsTable ftsTable cache result := by
  cases hh : result.2 with
  | true => simp only [survivingFtsParentReserve, if_true, zero_mul, zero_le]
  | false =>
      simp only [survivingFtsParentReserve, collisionStructuralEnvelope, hh, Bool.false_eq_true, if_false,
        collisionStructuralRecordPotential, ftsParentSelectionPotential, firstExceptionSelectionPotential]
      exact le_add_self

theorem expected_collisionPotential_add_sharedParentDiscard_step_le
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Frame) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (henabled : frame.Enabled parameter otsTable ftsTable input cache false)
    (hcomputed : OtsProbeSimulation.DeferredComputationsClosed frame.context) :
    (∑' result, Pr[= result | stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      input (some frame) cache false false] *
      collisionSurvivingStructuralPotential (secretKey parameter root otsTable ftsTable) result.1.2.1.2 result.1.2.2 result.2) +
      sharedFailureDiscardStep (parentException parameter otsTable ftsTable) (survivingFtsParentReserve (secretKey parameter root otsTable ftsTable))
        parameter root otsTable ftsTable input (some frame) cache false false * (Fintype.card Digest : ENNReal)⁻¹ ≤
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
        exact survivingFtsParentReserve_scaled_le_collisionEnvelope parameter root otsTable ftsTable cache result.1.2
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
