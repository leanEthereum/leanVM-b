import SphincsSecurity.Proof.DeficitRetainedExecution
import SphincsSecurity.Proof.SecurityLiveNonSecretResidual

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex retainedRestVerdict)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable

theorem runRetainedWithDeficit_support_exception
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) (result) (hr : result ∈ support (runRetainedWithDeficit adversary parameter otsTable ftsTable q fuel)) :
    ∃ root, result ∈ support (runRetainedWithFailure
      (deficitStoppingException (secretKey parameter root otsTable ftsTable) (parentException parameter otsTable ftsTable))
      adversary parameter otsTable ftsTable q fuel) := by
  rw [runRetainedWithDeficit, mem_support_bind_iff] at hr
  obtain ⟨initial, hi, ht⟩ := hr
  refine ⟨initial.2.1, ?_⟩
  rw [runRetainedWithFailure, mem_support_bind_iff]
  exact ⟨initial, hi, ht⟩

theorem retained_deficit_win_cases
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (hots : otsTable ∈ support OtsProbeSimulation.sampleOtsHashTable)
    (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat)
    (result) (hr : result ∈ support (runRetainedWithDeficit adversary parameter otsTable ftsTable q fuel))
    (value : RetainedGameResult) (hv : result.1.2.1.1 = some value) (hwin : retainedRestVerdict value.2 = true) :
    result.2 = true ∨ SurvivingStructuralFailure parameter otsTable ftsTable result ∨
      LiveNonSecretResidual parameter otsTable ftsTable result := by
  cases hf : result.2 with
  | true => exact Or.inl rfl
  | false =>
      cases hh : result.1.2.2 with
      | true => exact Or.inr (Or.inl ⟨hf, Or.inl hh⟩)
      | false =>
          by_cases hb : Bad parameter (secretKey parameter default otsTable ftsTable).otsSecret
              (secretKey parameter default otsTable ftsTable).ftsSecret result.1.2.1.2 ∨
              EncodingBad result.1.2.1.2 (secretKey parameter default otsTable ftsTable)
          · exact Or.inr (Or.inl ⟨hf, Or.inr hb⟩)
          · have hn : ¬ SecretWitness parameter (OtsProbeSimulation.tableOtsSecret (OtsProbeSimulation.extendStartTable otsTable))
                (fun index tree leaf => ftsTable (index, tree, leaf)) (value, result.1.2.1.2) := by
              intro hw
              obtain ⟨root, hsupport⟩ := runRetainedWithDeficit_support_exception adversary parameter otsTable ftsTable q fuel result hr
              have h := clean_secretWitness_imp_failure
                (deficitStoppingException (secretKey parameter root otsTable ftsTable) (parentException parameter otsTable ftsTable))
                adversary q hq parameter hparameter otsTable hots ftsTable hfts fuel result hsupport hh value hv hw
              simp [hf] at h
            exact Or.inr (Or.inr ⟨hf, hh, value, hv, ⟨⟨⟨hwin, fun h => hb (Or.inl h), fun h => hn (Or.inl h)⟩,
              fun h => hb (Or.inr h)⟩, fun h => hn (Or.inr h)⟩⟩)

theorem probEvent_actual_win_le_deficit_failure_charge_residual
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (hots : otsTable ∈ support OtsProbeSimulation.sampleOtsHashTable)
    (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    Pr[fun result => retainedRestVerdict result.1.2 = true |
      OtsProbeSimulation.actualRetainedGameAfterTable adversary parameter
        (fun index tree leaf => ftsTable (index, tree, leaf)) (OtsProbeSimulation.extendStartTable otsTable)] ≤
      Pr[fun result => result.2 = true | runRetainedWithDeficit adversary parameter otsTable ftsTable q fuel] +
        initializedDeficitCollisionCharge adversary parameter otsTable ftsTable q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
        (q : ENNReal) / 2 ^ 223 +
        Pr[LiveNonSecretResidual parameter otsTable ftsTable |
          runRetainedWithDeficit adversary parameter otsTable ftsTable q fuel] := by
  have hm := congrArg
    (fun distribution => Pr[fun result => ∃ value, result.1 = some value ∧ retainedRestVerdict value.2 = true | distribution])
    (runRetainedWithDeficit_originalActual adversary q hq parameter hparameter otsTable ftsTable hfts fuel)
  rw [probEvent_map, probEvent_map] at hm
  simp only [Function.comp_def, Option.some.injEq, exists_eq_left'] at hm
  change Pr[fun result => ∃ value, result.1.2.1.1 = some value ∧ retainedRestVerdict value.2 = true |
    runRetainedWithDeficit adversary parameter otsTable ftsTable q fuel] =
    Pr[fun result => retainedRestVerdict result.1.2 = true |
      OtsProbeSimulation.actualRetainedGameAfterTable adversary parameter
        (fun index tree leaf => ftsTable (index, tree, leaf)) (OtsProbeSimulation.extendStartTable otsTable)] at hm
  rw [← hm]
  apply (probEvent_mono
    (q := fun result => result.2 = true ∨ SurvivingStructuralFailure parameter otsTable ftsTable result ∨
      LiveNonSecretResidual parameter otsTable ftsTable result)
    (fun result hr ⟨value, hv, hwin⟩ => retained_deficit_win_cases adversary q hq parameter hparameter otsTable hots ftsTable hfts
      fuel result hr value hv hwin)).trans
  apply (probEvent_or_le _ _ _).trans
  apply (add_le_add le_rfl (probEvent_or_le _ _ _)).trans
  rw [← add_assoc]
  apply add_le_add _ le_rfl
  rw [add_assoc]
  exact add_le_add le_rfl
    (probEvent_deficitSurvivingStructuralFailure_le adversary q hq hqMax parameter hparameter otsTable ftsTable hfts fuel)

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
