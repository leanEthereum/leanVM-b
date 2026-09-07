import SphincsSecurity.Proof.SecuritySampledBeforeSharedFailure

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex retainedRestVerdict)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

def LiveNonSecretResidual (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (result : (Option Frame × ((Option RetainedGameResult × QueryCache HashSpec) × Bool)) × Bool) : Prop :=
  result.2 = false ∧ result.1.2.2 = false ∧ ∃ value, result.1.2.1.1 = some value ∧
    retainedNonSecretResidual (tableSecrets parameter otsTable ftsTable, ((value, result.1.2.1.2), none))

theorem retained_win_cases_live_residual
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (hots : otsTable ∈ support OtsProbeSimulation.sampleOtsHashTable)
    (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat)
    (result) (hr : result ∈ support (runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel))
    (value : RetainedGameResult) (hv : result.1.2.1.1 = some value) (hwin : retainedRestVerdict value.2 = true) :
    result.2 = true ∨ SurvivingStructuralFailure parameter otsTable ftsTable result ∨
      LiveNonSecretResidual parameter otsTable ftsTable result := by
  cases hf : result.2 with
  | true => exact Or.inl rfl
  | false =>
      cases hh : result.1.2.2 with
      | true => exact Or.inr (Or.inl ⟨hf, Or.inl hh⟩)
      | false =>
          rcases retained_win_cases_before_failure adversary q hq parameter hparameter otsTable hots ftsTable hfts fuel result hr value hv hwin with h | h | h
          · simp [hf] at h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr ⟨hf, hh, value, hv, h⟩)

theorem probEvent_original_win_le_failure_add_charge_add_live_residual
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (hots : otsTable ∈ support OtsProbeSimulation.sampleOtsHashTable)
    (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    Pr[fun result => retainedRestVerdict result.1.1.2 = true | originalParentRecords adversary parameter otsTable ftsTable] ≤
    Pr[fun result => result.2 = true | runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] +
      initializedBeforeFailureStructuralCharge adversary parameter otsTable ftsTable q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
      Pr[LiveNonSecretResidual parameter otsTable ftsTable |
        runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] := by
  rw [probEvent_originalRecords_eq_retained adversary q hq parameter hparameter otsTable ftsTable hfts fuel
    (fun result => retainedRestVerdict result.1.2 = true)]
  apply (probEvent_mono
    (q := fun result => result.2 = true ∨ SurvivingStructuralFailure parameter otsTable ftsTable result ∨
      LiveNonSecretResidual parameter otsTable ftsTable result)
    (fun result hr ⟨value, hv, hwin⟩ =>
      retained_win_cases_live_residual adversary q hq parameter hparameter otsTable hots ftsTable hfts fuel result hr value hv hwin)).trans
  apply (probEvent_or_le _ _ _).trans
  apply (add_le_add le_rfl (probEvent_or_le _ _ _)).trans
  rw [← add_assoc]
  exact add_le_add (add_le_add le_rfl (probEvent_survivingStructuralFailure_le_beforeFailureCharge adversary parameter otsTable ftsTable q fuel)) le_rfl

theorem probEvent_liveNonSecretResidual_le_original
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    Pr[LiveNonSecretResidual parameter otsTable ftsTable |
      runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] ≤
      Pr[fun result => retainedNonSecretResidual (tableSecrets parameter otsTable ftsTable, result) |
        originalParentRecords adversary parameter otsTable ftsTable] := by
  have hother := probEvent_originalRecords_eq_retained adversary q hq parameter hparameter otsTable ftsTable hfts fuel
    (fun result => retainedNonSecretResidual (tableSecrets parameter otsTable ftsTable, (result, none)))
  change Pr[fun result => retainedNonSecretResidual (tableSecrets parameter otsTable ftsTable, result) | _] = _ at hother
  rw [hother]
  exact probEvent_mono fun _ _ h => h.2.2

noncomputable def sampledLiveNonSecretResidual (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        Pr[LiveNonSecretResidual parameter table (curryFtsTableEquiv ftsSecret) |
          runRetainedWithFailure (parentException parameter table (curryFtsTableEquiv ftsSecret))
            adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel]

theorem forgeAdvantage_le_sharedFailure_add_structural_add_live_residual
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (fuel : Nat) :
    forgeAdvantage scheme adversary ≤ sampledParentSharedFailureRisk adversary q fuel +
      sampledBeforeFailureStructuralCharge adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
      sampledLiveNonSecretResidual adversary q fuel := by
  rw [forgeAdvantage_eq_sampledRetained_win, probEvent_sampledRetained_eq_recordRisk]
  unfold sampledOriginalRecordRisk sampledParentSharedFailureRisk sampledBeforeFailureStructuralCharge sampledLiveNonSecretResidual
  calc
    _ ≤ ∑' parameter, Pr[= parameter | sampleParameter] *
        ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
          ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
            (Pr[fun result => result.2 = true | runRetainedWithFailure (parentException parameter table (curryFtsTableEquiv ftsSecret))
              adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel] +
              initializedBeforeFailureStructuralCharge adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
              Pr[LiveNonSecretResidual parameter table (curryFtsTableEquiv ftsSecret) |
                runRetainedWithFailure (parentException parameter table (curryFtsTableEquiv ftsSecret))
                  adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel]) := by
      apply ENNReal.tsum_le_tsum
      intro parameter
      by_cases hp : parameter ∈ support sampleParameter
      · apply mul_le_mul' le_rfl
        apply ENNReal.tsum_le_tsum
        intro ftsSecret
        apply mul_le_mul' le_rfl
        apply ENNReal.tsum_le_tsum
        intro table
        by_cases ht : table ∈ support OtsProbeSimulation.sampleOtsHashTable
        · exact mul_le_mul' le_rfl (probEvent_original_win_le_failure_add_charge_add_live_residual adversary q hq parameter hp table ht
            (curryFtsTableEquiv ftsSecret) (mem_support_sampleFtsSecrets ftsSecret) fuel)
        · rw [probOutput_eq_zero_of_not_mem_support ht, zero_mul, zero_mul]
      · rw [probOutput_eq_zero_of_not_mem_support hp, zero_mul, zero_mul]
    _ = _ := by
      simp only [mul_add, ENNReal.tsum_add, ← mul_assoc, ENNReal.tsum_mul_right]

theorem sampledLiveNonSecretResidual_le_original
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (fuel : Nat) :
    sampledLiveNonSecretResidual adversary q fuel ≤
      Pr[retainedNonSecretResidual | OtsProbeSimulation.sampledFirstParentRetainedGame adversary] := by
  rw [probEvent_sampledRetained_eq_recordRisk]
  unfold sampledLiveNonSecretResidual sampledOriginalRecordRisk
  apply ENNReal.tsum_le_tsum
  intro parameter
  by_cases hp : parameter ∈ support sampleParameter
  · apply mul_le_mul' le_rfl
    apply ENNReal.tsum_le_tsum
    intro ftsSecret
    apply mul_le_mul' le_rfl
    apply ENNReal.tsum_le_tsum
    intro table
    exact mul_le_mul' le_rfl (probEvent_liveNonSecretResidual_le_original adversary q hq parameter hp table
      (curryFtsTableEquiv ftsSecret) (mem_support_sampleFtsSecrets ftsSecret) fuel)
  · rw [probOutput_eq_zero_of_not_mem_support hp, zero_mul, zero_mul]

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
