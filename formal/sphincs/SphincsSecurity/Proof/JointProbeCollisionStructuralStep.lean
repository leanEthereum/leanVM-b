import SphincsSecurity.Proof.CollisionStructuralPotential
import SphincsSecurity.Proof.JointProbeOriginalStructuralStep

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex IsOtsPosition)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def collisionSurvivingStructuralPotential (key : SecretKey) (cache : QueryCache HashSpec) (hit failed : Bool) : ENNReal :=
  if failed then 0 else if hit then 1 else collisionStructuralRecordPotential key cache none

noncomputable def collisionStructuralEnvelope
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cache : QueryCache HashSpec) (result : (α × QueryCache HashSpec) × Bool) : ENNReal :=
  if result.2 then
    if EarlyOtsParentTransition parameter otsTable ftsTable cache result.1.2 then 0 else 1
  else collisionStructuralRecordPotential (secretKey parameter root otsTable ftsTable) result.1.2 none

theorem collisionStructuralEnvelope_le_recordPotential
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec)
    (result) (hr : result ∈ support (runFirstException (parentException parameter otsTable ftsTable)
      (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache none)) :
    collisionStructuralEnvelope parameter root otsTable ftsTable cache (result.1, result.2.isSome) ≤
      collisionStructuralRecordPotential (secretKey parameter root otsTable ftsTable) result.1.2 result.2 := by
  cases hs : result.2 with
  | none => simp only [collisionStructuralEnvelope, Option.isSome_none, Bool.false_eq_true, if_false, le_refl]
  | some record =>
      by_cases he : EarlyOtsParentTransition parameter otsTable ftsTable cache result.1.2
      · simp only [collisionStructuralEnvelope, Option.isSome_some, if_true, he, zero_le]
      · have hv := runFirstException_none_valid (parentException parameter otsTable ftsTable) _ cache hr record (by simp [hs])
        let key := secretKey parameter root otsTable ftsTable
        obtain ⟨child, parent, hat, hpar, _⟩ := hv.2.2.1.2.exists_full_parent_input key.parameter key.otsSecret key.ftsSecret hv.2.2.2
        have hp : ¬ IsOtsPosition parent := by
          intro hots
          exact he (firstOtsRecord_earlyTransition (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
            (fun _ _ _ h => h.2) input cache result.1 record (by simpa only [← hs] using hr)
            ⟨child, hat, hots.of_parent hpar⟩)
        have hselected : EligibleParentRecord (secretKey parameter root otsTable ftsTable).parameter (fun position => ¬ IsOtsPosition position) record :=
          ⟨child, parent, hat, hpar, hp⟩
        simp only [collisionStructuralEnvelope, Option.isSome_some, if_true, he, if_false, collisionStructuralRecordPotential,
          collisionAnswerEncodingMonitorPotential, ftsParentSelectionPotential, firstExceptionSelectionPotential, hselected, zero_add, le_refl]

theorem expected_collisionStructuralEnvelope_step_le
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    (∑' result, Pr[= result | stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      input frame cache false false] * collisionStructuralEnvelope parameter root otsTable ftsTable cache result.1.2) ≤
      collisionStructuralRecordPotential (secretKey parameter root otsTable ftsTable) cache none +
        expectedPreExceptionCharge (parentException parameter otsTable ftsTable) (collisionSigningStructuralCharge (secretKey parameter root otsTable ftsTable))
          (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache false * (Fintype.card Digest : ENNReal)⁻¹ := by
  let exception := parentException parameter otsTable ftsTable
  let cost := collisionStructuralEnvelope parameter root otsTable ftsTable cache (α := (OracleWorld + SigningSpec).Range input)
  calc
    _ = ∑' result, Pr[= result | runFirstException exception (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache none] *
        cost (result.1, result.2.isSome) := by
      have hm := tsum_probOutput_map_mul
        (stepWithFailure exception parameter root otsTable ftsTable input frame cache false false) Prod.fst (fun result => cost result.2)
      rw [stepWithFailure_project, step_expect_original] at hm
      have hflag := runFirstException_flag_projection exception (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache none
      simp only [Option.isSome_none] at hflag
      rw [← hm, ← hflag, tsum_probOutput_map_mul]
    _ ≤ ∑' result, Pr[= result | runFirstException exception (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache none] *
        collisionStructuralRecordPotential (secretKey parameter root otsTable ftsTable) result.1.2 result.2 := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support (runFirstException exception (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache none)
      · exact mul_le_mul' le_rfl (collisionStructuralEnvelope_le_recordPotential parameter root otsTable ftsTable input cache result hr)
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ ≤ _ := expected_collisionStructuralRecordPotential_le_preCharge (secretKey parameter root otsTable ftsTable) _ cache hfinite none

theorem expected_collisionSurvivingStructuralPotential_step_le
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Frame) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (henabled : frame.Enabled parameter otsTable ftsTable input cache false)
    (hcomputed : OtsProbeSimulation.DeferredComputationsClosed frame.context) :
    (∑' result, Pr[= result | stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      input (some frame) cache false false] *
      collisionSurvivingStructuralPotential (secretKey parameter root otsTable ftsTable) result.1.2.1.2 result.1.2.2 result.2) ≤
    collisionStructuralRecordPotential (secretKey parameter root otsTable ftsTable) cache none +
      expectedPreExceptionCharge (parentException parameter otsTable ftsTable) (collisionSigningStructuralCharge (secretKey parameter root otsTable ftsTable))
        (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache false * (Fintype.card Digest : ENNReal)⁻¹ := by
  let exception := parentException parameter otsTable ftsTable
  let cost := collisionStructuralEnvelope parameter root otsTable ftsTable cache (α := (OracleWorld + SigningSpec).Range input)
  calc
    _ ≤ ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input (some frame) cache false false] * cost result.1.2 := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input (some frame) cache false false)
      · apply mul_le_mul' le_rfl
        cases hf : result.2 with
        | true => simp only [collisionSurvivingStructuralPotential, if_true, zero_le]
        | false =>
            have he : ¬ EarlyOtsParentTransition parameter otsTable ftsTable cache result.1.2.1.2 := by
              intro he
              have h := stepWithFailure_earlyOtsParent_imp_failed exception parameter root otsTable ftsTable input frame cache henabled hcomputed result hr he
              simp [hf] at h
            cases ho : result.1.2.2 <;> simp [collisionSurvivingStructuralPotential, cost, collisionStructuralEnvelope, he, ho]
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ ≤ _ := expected_collisionStructuralEnvelope_step_le parameter root otsTable ftsTable input (some frame) cache hfinite

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
