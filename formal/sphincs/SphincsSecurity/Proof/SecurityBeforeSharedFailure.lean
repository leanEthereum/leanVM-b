import SphincsSecurity.Proof.JointProbeOriginalStructuralInitialization
import SphincsSecurity.Proof.SecurityOriginalSharedFailureEndpoint

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex retainedRestVerdict)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

private theorem probEvent_evalDist_eq (computation : ProbComp α) (event : α → Prop) :
    Pr[event | evalDist computation] = Pr[event | computation] := rfl

theorem probEvent_originalRecords_eq_retained
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat)
    (event : RetainedGameResult × QueryCache HashSpec → Prop) :
    Pr[fun result => event result.1 | originalParentRecords adversary parameter otsTable ftsTable] =
    Pr[fun result => ∃ value, result.1.2.1.1 = some value ∧ event (value, result.1.2.1.2) |
      runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] := by
  have hm := congrArg (fun computation => Pr[fun result => ∃ value, result.1.1 = some value ∧ event (value, result.1.2) | computation])
    (runRetainedWithFailure_original (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel)
  rw [probEvent_map, probEvent_evalDist_eq, monitoredRetained_parent_eq adversary q hq parameter hparameter otsTable ftsTable hfts, probEvent_map] at hm
  have hf := runFirstException_flag_projection (parentException parameter otsTable ftsTable)
    (OtsProbeSimulation.retainedAfterSecretsComputation adversary parameter
      (OtsProbeSimulation.tableOtsSecret (OtsProbeSimulation.extendStartTable otsTable)) (fun index tree leaf => ftsTable (index, tree, leaf))) ∅ none
  change (fun result => (result.1, result.2.isSome)) <$> originalParentRecords adversary parameter otsTable ftsTable =
    originalParentMonitor adversary parameter otsTable ftsTable at hf
  rw [← hf, probEvent_map] at hm
  simpa only [Function.comp_def, Option.some.injEq, exists_eq_left'] using hm.symm

noncomputable def tableSecrets (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest) : SampledSecrets :=
  ⟨parameter, OtsProbeSimulation.tableOtsSecret (OtsProbeSimulation.extendStartTable otsTable), fun index tree leaf => ftsTable (index, tree, leaf)⟩

theorem retained_win_cases_before_failure
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (hots : otsTable ∈ support OtsProbeSimulation.sampleOtsHashTable)
    (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat)
    (result) (hr : result ∈ support (runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel))
    (value : RetainedGameResult) (hv : result.1.2.1.1 = some value) (hwin : retainedRestVerdict value.2 = true) :
    result.2 = true ∨ SurvivingStructuralFailure parameter otsTable ftsTable result ∨
      retainedNonSecretResidual (tableSecrets parameter otsTable ftsTable, ((value, result.1.2.1.2), none)) := by
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
              have h := clean_secretWitness_imp_failure (parentException parameter otsTable ftsTable) adversary q hq parameter hparameter
                otsTable hots ftsTable hfts fuel result hr hh value hv hw
              simp [hf] at h
            exact Or.inr (Or.inr ⟨⟨⟨hwin, fun h => hb (Or.inl h), fun h => hn (Or.inl h)⟩,
              fun h => hb (Or.inr h)⟩, fun h => hn (Or.inr h)⟩)

theorem probEvent_original_win_le_failure_add_beforeFailureCharge
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (hots : otsTable ∈ support OtsProbeSimulation.sampleOtsHashTable)
    (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    Pr[fun result => retainedRestVerdict result.1.1.2 = true | originalParentRecords adversary parameter otsTable ftsTable] ≤
    Pr[fun result => result.2 = true | runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] +
      initializedBeforeFailureStructuralCharge adversary parameter otsTable ftsTable q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
      Pr[fun result => retainedNonSecretResidual (tableSecrets parameter otsTable ftsTable, result) |
        originalParentRecords adversary parameter otsTable ftsTable] := by
  have hwin := probEvent_originalRecords_eq_retained adversary q hq parameter hparameter otsTable ftsTable hfts fuel
    (fun result => retainedRestVerdict result.1.2 = true)
  have hother := probEvent_originalRecords_eq_retained adversary q hq parameter hparameter otsTable ftsTable hfts fuel
    (fun result => retainedNonSecretResidual (tableSecrets parameter otsTable ftsTable, (result, none)))
  change Pr[fun result => retainedNonSecretResidual (tableSecrets parameter otsTable ftsTable, result) | _] = _ at hother
  rw [hwin, hother]
  apply (probEvent_mono
    (q := fun result => result.2 = true ∨ SurvivingStructuralFailure parameter otsTable ftsTable result ∨
      ∃ value, result.1.2.1.1 = some value ∧ retainedNonSecretResidual (tableSecrets parameter otsTable ftsTable, ((value, result.1.2.1.2), none)))
    (fun result hr ⟨value, hv, hwin⟩ => by
      rcases retained_win_cases_before_failure adversary q hq parameter hparameter otsTable hots ftsTable hfts fuel result hr value hv hwin with hf | hs | hn
      · exact Or.inl hf
      · exact Or.inr (Or.inl hs)
      · exact Or.inr (Or.inr ⟨value, hv, hn⟩))).trans
  apply (probEvent_or_le _ _ _).trans
  apply (add_le_add le_rfl (probEvent_or_le _ _ _)).trans
  rw [← add_assoc]
  exact add_le_add (add_le_add le_rfl (probEvent_survivingStructuralFailure_le_beforeFailureCharge adversary parameter otsTable ftsTable q fuel)) le_rfl

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
