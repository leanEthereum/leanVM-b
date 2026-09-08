import SphincsSecurity.Proof.DeficitStructuralPotential
import SphincsSecurity.Proof.DeficitOtsParentRecord
import SphincsSecurity.Proof.DeficitRecordCost
import SphincsSecurity.Proof.JointProbeCollisionStructuralStep

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable

theorem collisionStructuralEnvelope_le_deficit_recordPotential
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec)
    (hclean : ¬ MessageDeficitExceptional (secretKey parameter root otsTable ftsTable) cache)
    (result) (hr : result ∈ support (runFirstException
      (deficitStoppingException (secretKey parameter root otsTable ftsTable) (parentException parameter otsTable ftsTable))
      (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache none)) :
    collisionStructuralEnvelope parameter root otsTable ftsTable cache (result.1, result.2.isSome) ≤
      collisionStructuralRecordPotential (secretKey parameter root otsTable ftsTable) result.1.2 result.2 +
        if (∃ record ∈ result.2, MessageHashInput parameter record.input) then 1 else 0 := by
  cases hs : result.2 with
  | none => simp only [collisionStructuralEnvelope, Option.isSome_none, Bool.false_eq_true, if_false,
      Option.not_mem_none, false_and, exists_false, add_zero, le_refl]
  | some record =>
      by_cases hm : MessageHashInput parameter record.input
      · have hevent : ∃ current ∈ some record, MessageHashInput parameter current.input := ⟨record, by simp, hm⟩
        rw [if_pos hevent]
        apply le_trans (b := (1 : ENNReal)) _ le_add_self
        simp only [collisionStructuralEnvelope, Option.isSome_some, if_true]
        split_ifs <;> simp only [zero_le, le_refl]
      · have hevent : ¬ ∃ current ∈ some record, MessageHashInput parameter current.input := by simpa using hm
        rw [if_neg hevent, add_zero]
        have hbase := firstDeficitExceptionRecord_support_nonmessage (secretKey parameter root otsTable ftsTable)
          (parentException parameter otsTable ftsTable) _ cache hclean result.1 record (by simpa only [← hs] using hr) hm
        exact collisionStructuralEnvelope_le_recordPotential parameter root otsTable ftsTable input cache (result.1, some record) hbase

theorem expected_deficitCollisionStructuralEnvelope_step_le
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (hclean : ¬ MessageDeficitExceptional (secretKey parameter root otsTable ftsTable) cache) :
    (∑' result, Pr[= result | stepWithFailure
        (deficitStoppingException (secretKey parameter root otsTable ftsTable) (parentException parameter otsTable ftsTable))
        parameter root otsTable ftsTable input frame cache false false] *
      collisionStructuralEnvelope parameter root otsTable ftsTable cache result.1.2) ≤
      collisionStructuralRecordPotential (secretKey parameter root otsTable ftsTable) cache none +
        expectedPreExceptionCharge
          (deficitStoppingException (secretKey parameter root otsTable ftsTable) (parentException parameter otsTable ftsTable))
          (collisionSigningStructuralCharge (secretKey parameter root otsTable ftsTable))
          (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache false * (Fintype.card Digest : ENNReal)⁻¹ +
        Pr[fun result => ∃ record ∈ result.2, MessageHashInput parameter record.input |
          runFirstException
            (deficitStoppingException (secretKey parameter root otsTable ftsTable) (parentException parameter otsTable ftsTable))
            (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache none] := by
  let key := secretKey parameter root otsTable ftsTable
  let exception := deficitStoppingException key (parentException parameter otsTable ftsTable)
  let cost := collisionStructuralEnvelope parameter root otsTable ftsTable cache (α := (OracleWorld + SigningSpec).Range input)
  calc
    _ = ∑' result, Pr[= result | runFirstException exception (expandedAdversaryImpl key input) cache none] *
        cost (result.1, result.2.isSome) := by
      have hm := tsum_probOutput_map_mul
        (stepWithFailure exception parameter root otsTable ftsTable input frame cache false false) Prod.fst (fun result => cost result.2)
      rw [stepWithFailure_project, step_expect_original] at hm
      have hflag := runFirstException_flag_projection exception (expandedAdversaryImpl key input) cache none
      simp only [Option.isSome_none] at hflag
      rw [← hm, ← hflag, tsum_probOutput_map_mul]
    _ ≤ (∑' result, Pr[= result | runFirstException exception (expandedAdversaryImpl key input) cache none] *
        collisionStructuralRecordPotential key result.1.2 result.2) +
        Pr[fun result => ∃ record ∈ result.2, MessageHashInput parameter record.input |
          runFirstException exception (expandedAdversaryImpl key input) cache none] := by
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support (runFirstException exception (expandedAdversaryImpl key input) cache none)
      · have h := mul_le_mul' (le_refl (Pr[= result | runFirstException exception (expandedAdversaryImpl key input) cache none]))
          (collisionStructuralEnvelope_le_deficit_recordPotential parameter root otsTable ftsTable input cache hclean result hr)
        simpa only [mul_add, mul_ite, mul_one, mul_zero] using h
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
        split_ifs <;> exact zero_le
    _ ≤ _ := add_le_add (expected_deficitStructuralRecordPotential_le_preCharge key
      (expandedAdversaryImpl key input) cache hfinite none (fun _ => hclean)) le_rfl

theorem expected_deficitCollisionSurvivingStructuralPotential_step_le
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (frame : Frame) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (hclean : ¬ MessageDeficitExceptional (secretKey parameter root otsTable ftsTable) cache)
    (henabled : frame.Enabled parameter otsTable ftsTable input cache false)
    (hcomputed : OtsProbeSimulation.DeferredComputationsClosed frame.context) :
    (∑' result, Pr[= result | stepWithFailure
        (deficitStoppingException (secretKey parameter root otsTable ftsTable) (parentException parameter otsTable ftsTable))
        parameter root otsTable ftsTable input (some frame) cache false false] *
      collisionSurvivingStructuralPotential (secretKey parameter root otsTable ftsTable) result.1.2.1.2 result.1.2.2 result.2) ≤
      collisionStructuralRecordPotential (secretKey parameter root otsTable ftsTable) cache none +
        expectedPreExceptionCharge
          (deficitStoppingException (secretKey parameter root otsTable ftsTable) (parentException parameter otsTable ftsTable))
          (collisionSigningStructuralCharge (secretKey parameter root otsTable ftsTable))
          (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache false * (Fintype.card Digest : ENNReal)⁻¹ +
        Pr[fun result => ∃ record ∈ result.2, MessageHashInput parameter record.input |
          runFirstException
            (deficitStoppingException (secretKey parameter root otsTable ftsTable) (parentException parameter otsTable ftsTable))
            (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable) input) cache none] := by
  let exception := deficitStoppingException (secretKey parameter root otsTable ftsTable) (parentException parameter otsTable ftsTable)
  apply le_trans _ (expected_deficitCollisionStructuralEnvelope_step_le parameter root otsTable ftsTable input (some frame) cache hfinite hclean)
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
        cases ho : result.1.2.2 <;> simp [collisionSurvivingStructuralPotential, collisionStructuralEnvelope, he, ho]
  · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
