import SphincsSecurity.Proof.AnswerEncodingStoppedBound
import SphincsSecurity.Proof.ParentReserveStoppedBound
import SphincsSecurity.Proof.SigningStoppedStructuralBudget

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] instFintypePosition
set_option backward.isDefEq.respectTransparency false

noncomputable def ftsParentSelectionPotential (key : SecretKey) (cache : QueryCache HashSpec) (saved : Option ExceptionRecord) : ENNReal :=
  firstExceptionSelectionPotential (EligibleParentRecord key.parameter (fun position => ¬ OtsProbeSimulation.IsOtsPosition position))
    (fun cache => (parentReserve key.parameter key.otsSecret key.ftsSecret
      (fun position => ¬ OtsProbeSimulation.IsOtsPosition position) cache : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹) cache saved

theorem expected_ftsParentSelectionPotential_le_preCharge
    (key : SecretKey) (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (saved : Option ExceptionRecord) :
    (∑' result, Pr[= result | runFirstException (CleanParentSettlement key.parameter key.otsSecret key.ftsSecret) computation cache saved] *
      ftsParentSelectionPotential key result.1.2 result.2) ≤
      ftsParentSelectionPotential key cache saved +
        expectedPreExceptionCharge (CleanParentSettlement key.parameter key.otsSecret key.ftsSecret) (ftsParentQueryCharge key)
          computation cache saved.isSome * (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [← expectedPreExceptionCharge_mul]
  apply expected_runFirstException_potential_le_preExceptionCharge (hfinite := hfinite)
  intro query cache hfinite saved
  cases saved with
  | some record =>
      simp only [retainFirstException, ftsParentSelectionPotential, firstExceptionSelectionPotential,
        Option.isSome_some, if_true, add_zero]
      rw [ENNReal.tsum_mul_right, romImpl_query_mass, one_mul]
  | none =>
      apply (ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl
        (firstParentSelectionPotential_query_le_reserve key.parameter key.otsSecret key.ftsSecret
          (fun position => ¬ OtsProbeSimulation.IsOtsPosition position) query cache result (Fintype.card Digest : ENNReal)⁻¹)).trans
      simpa only [ftsParentSelectionPotential, firstExceptionSelectionPotential, ftsParentQueryCharge,
        exceptionReservePotential, Bool.false_eq_true, if_false, zero_add, Bool.false_or, Option.isSome_none] using
        expected_exceptionReserve_query_le
          (EligibleParentSettlement key.parameter key.otsSecret key.ftsSecret (fun position => ¬ OtsProbeSimulation.IsOtsPosition position))
          (parentReserve key.parameter key.otsSecret key.ftsSecret (fun position => ¬ OtsProbeSimulation.IsOtsPosition position))
          (parentReserveCharge key.parameter key.otsSecret key.ftsSecret (fun position => ¬ OtsProbeSimulation.IsOtsPosition position))
          (Fintype.card Digest : ENNReal)⁻¹
          (fun target => by
            rw [← probOutput_map]
            simpa only [show Fintype.card Digest = 2 ^ digestBits from card_bitVec digestBits] using probOutput_truncateHash_le target)
          (fun _ hfinite input hfresh => parentReserve_step key.parameter key.otsSecret key.ftsSecret
            (fun position => ¬ OtsProbeSimulation.IsOtsPosition position) hfinite input hfresh)
          query cache hfinite false

noncomputable def structuralRecordPotential (key : SecretKey) (cache : QueryCache HashSpec) (saved : Option ExceptionRecord) : ENNReal :=
  answerEncodingMonitorPotential key cache saved.isSome + ftsParentSelectionPotential key cache saved

theorem expected_structuralRecordPotential_le_preCharge
    (key : SecretKey) (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (saved : Option ExceptionRecord) :
    (∑' result, Pr[= result | runFirstException (CleanParentSettlement key.parameter key.otsSecret key.ftsSecret) computation cache saved] *
      structuralRecordPotential key result.1.2 result.2) ≤
      structuralRecordPotential key cache saved +
        expectedPreExceptionCharge (CleanParentSettlement key.parameter key.otsSecret key.ftsSecret) (signingStructuralCharge key)
          computation cache saved.isSome * (Fintype.card Digest : ENNReal)⁻¹ := by
  have ha := expected_answerEncodingMonitorPotential_le_preExceptionCharge key computation cache hfinite saved.isSome
  rw [← runFirstException_flag_projection, tsum_probOutput_map_mul] at ha
  have hp := expected_ftsParentSelectionPotential_le_preCharge key computation cache hfinite saved
  simp only [structuralRecordPotential, mul_add, ENNReal.tsum_add]
  apply (add_le_add ha hp).trans_eq
  rw [show signingStructuralCharge key = (fun cache input => parentStoppedEncodingQueryCharge key cache input +
    ftsParentQueryCharge key cache input) from rfl, expectedPreExceptionCharge_add, add_mul]
  ac_rfl

theorem structuralRecordPotential_none_ge_bad
    (key : SecretKey) (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (hbad : Bad key.parameter key.otsSecret key.ftsSecret cache ∨ EncodingBad cache key) :
    1 ≤ structuralRecordPotential key cache none := by
  simp only [structuralRecordPotential, answerEncodingMonitorPotential, Option.isSome_none, Bool.false_eq_true, if_false,
    answerEncodingAdaptivePotential_eq hfinite, answerEncodingTotalPotential_eq_one_of_bad_or_encodingBad hfinite hbad]
  exact le_self_add

end SphincsSecurity.Concrete
