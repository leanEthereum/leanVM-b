import SphincsSecurity.Proof.JointProbeCollisionChargeBudget
import SphincsSecurity.Proof.SecurityLiveNonSecretResidual

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex retainedRestVerdict)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

noncomputable def sampledBeforeFailureCollisionCharge (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        initializedBeforeFailureCollisionCharge adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel

noncomputable def sampledBeforeFailureCollisionBaseCharge (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        initializedBeforeFailureCollisionBaseCharge adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel

noncomputable def sampledBeforeFailureEncodingPairCharge (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        initializedBeforeFailureEncodingPairCharge adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel

theorem probEvent_original_win_le_failure_add_collisionCharge_add_live_residual
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (hots : otsTable ∈ support OtsProbeSimulation.sampleOtsHashTable)
    (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    Pr[fun result => retainedRestVerdict result.1.1.2 = true | originalParentRecords adversary parameter otsTable ftsTable] ≤
    Pr[fun result => result.2 = true | runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] +
      initializedBeforeFailureCollisionCharge adversary parameter otsTable ftsTable q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
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
  exact add_le_add (add_le_add le_rfl (probEvent_survivingStructuralFailure_le_beforeFailureCollisionCharge adversary parameter otsTable ftsTable q fuel)) le_rfl

theorem forgeAdvantage_le_sharedFailure_add_collisionCharge_add_live_residual
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (fuel : Nat) :
    forgeAdvantage scheme adversary ≤ sampledParentSharedFailureRisk adversary q fuel +
      sampledBeforeFailureCollisionCharge adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
      sampledLiveNonSecretResidual adversary q fuel := by
  rw [forgeAdvantage_eq_sampledRetained_win, probEvent_sampledRetained_eq_recordRisk]
  unfold sampledOriginalRecordRisk sampledParentSharedFailureRisk sampledBeforeFailureCollisionCharge sampledLiveNonSecretResidual
  calc
    _ ≤ ∑' parameter, Pr[= parameter | sampleParameter] *
        ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
          ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
            (Pr[fun result => result.2 = true | runRetainedWithFailure (parentException parameter table (curryFtsTableEquiv ftsSecret))
              adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel] +
              initializedBeforeFailureCollisionCharge adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
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
        · exact mul_le_mul' le_rfl (probEvent_original_win_le_failure_add_collisionCharge_add_live_residual adversary q hq parameter hp table ht
            (curryFtsTableEquiv ftsSecret) (mem_support_sampleFtsSecrets ftsSecret) fuel)
        · rw [probOutput_eq_zero_of_not_mem_support ht, zero_mul, zero_mul]
      · rw [probOutput_eq_zero_of_not_mem_support hp, zero_mul, zero_mul]
    _ = _ := by
      simp only [mul_add, ENNReal.tsum_add, ← mul_assoc, ENNReal.tsum_mul_right]


theorem sampledBeforeFailureCollisionCharge_eq_base_add_pairs (adversary : Adversary) (q fuel : Nat) :
    sampledBeforeFailureCollisionCharge adversary q fuel =
      sampledBeforeFailureCollisionBaseCharge adversary q fuel + sampledBeforeFailureEncodingPairCharge adversary q fuel := by
  simp only [sampledBeforeFailureCollisionCharge, sampledBeforeFailureCollisionBaseCharge, sampledBeforeFailureEncodingPairCharge,
    initializedBeforeFailureCollisionCharge_eq_base_add_pairs, mul_add, ENNReal.tsum_add]

theorem sampledBeforeFailureEncodingPairCharge_scaled_le_127
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledBeforeFailureEncodingPairCharge adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ ≤
      (q : ENNReal) * (1 / 64) * (Fintype.card Digest : ENNReal)⁻¹ := by
  calc
    _ = ∑' parameter, Pr[= parameter | sampleParameter] *
        ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
          ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
            (initializedBeforeFailureEncodingPairCharge adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel *
              (Fintype.card Digest : ENNReal)⁻¹) := by
      simp only [sampledBeforeFailureEncodingPairCharge, ← mul_assoc, ENNReal.tsum_mul_right]
    _ ≤ ∑' parameter, Pr[= parameter | sampleParameter] *
        ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
          ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
            ((q : ENNReal) * (1 / 64) * (Fintype.card Digest : ENNReal)⁻¹) := by
      apply ENNReal.tsum_le_tsum
      intro parameter
      by_cases hp : parameter ∈ support sampleParameter
      · apply mul_le_mul' le_rfl
        apply ENNReal.tsum_le_tsum
        intro ftsSecret
        apply mul_le_mul' le_rfl
        apply ENNReal.tsum_le_tsum
        intro table
        exact mul_le_mul' le_rfl (initializedBeforeFailureEncodingPairCharge_scaled_le_127 adversary q hq hqMax parameter hp table
          (curryFtsTableEquiv ftsSecret) (mem_support_sampleFtsSecrets ftsSecret) fuel)
      · rw [probOutput_eq_zero_of_not_mem_support hp, zero_mul, zero_mul]
    _ ≤ _ := by
      simp_rw [ENNReal.tsum_mul_right]
      exact (mul_le_mul' tsum_probOutput_le_one
        (mul_le_mul' tsum_probOutput_le_one (mul_le_mul' tsum_probOutput_le_one le_rfl))).trans_eq (by simp)

theorem sampledBeforeFailureCollisionCharge_le_base_add_127
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledBeforeFailureCollisionCharge adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ ≤
      sampledBeforeFailureCollisionBaseCharge adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
        (q : ENNReal) * (1 / 64) * (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [sampledBeforeFailureCollisionCharge_eq_base_add_pairs, add_mul]
  exact add_le_add le_rfl (sampledBeforeFailureEncodingPairCharge_scaled_le_127 adversary q hq hqMax fuel)

theorem forgeAdvantage_le_sharedFailure_add_beforeFailureCollisionBase127
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    forgeAdvantage scheme adversary ≤ sampledParentSharedFailureRisk adversary q fuel +
      sampledBeforeFailureCollisionBaseCharge adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
      (q : ENNReal) * (1 / 64) * (Fintype.card Digest : ENNReal)⁻¹ +
      sampledLiveNonSecretResidual adversary q fuel := by
  apply (forgeAdvantage_le_sharedFailure_add_collisionCharge_add_live_residual adversary q hq fuel).trans
  have h := add_le_add (add_le_add (le_refl (sampledParentSharedFailureRisk adversary q fuel))
    (sampledBeforeFailureCollisionCharge_le_base_add_127 adversary q hq hqMax fuel))
    (le_refl (sampledLiveNonSecretResidual adversary q fuel))
  simpa only [add_assoc] using h

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
