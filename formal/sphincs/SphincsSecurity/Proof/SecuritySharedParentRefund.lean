import SphincsSecurity.Proof.SecurityCollisionTerminalReserve
import SphincsSecurity.Proof.InitializedSharedParentRefund

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex retainedRestVerdict)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

noncomputable def initializedCollisionParentCredit
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) : ENNReal :=
  initializedCollisionTerminalReserve adversary parameter otsTable ftsTable q fuel +
    initializedSharedParentDiscard adversary parameter otsTable ftsTable q fuel * (Fintype.card Digest : ENNReal)⁻¹

theorem probEvent_structuralFailure_add_parentCredit_le_beforeFailureCollisionCharge
    (adversary : Adversary) (parameter : PublicParameter) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (q fuel : Nat) :
    Pr[SurvivingStructuralFailure parameter otsTable ftsTable |
      runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] +
      initializedCollisionParentCredit adversary parameter otsTable ftsTable q fuel ≤
      initializedBeforeFailureCollisionCharge adversary parameter otsTable ftsTable q fuel * (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [initializedCollisionParentCredit, ← add_assoc]
  apply le_trans _ (expected_collisionPotential_add_sharedParentDiscard_retained_le adversary parameter otsTable ftsTable q fuel)
  apply add_le_add _ le_rfl
  rw [probEvent_eq_tsum_ite, initializedCollisionTerminalReserve, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ support (runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel)
  · have h := mul_le_mul' (le_refl (Pr[= result | runRetainedWithFailure (parentException parameter otsTable ftsTable)
        adversary parameter otsTable ftsTable q fuel]))
      (structuralFailure_add_collisionTerminalReserve_le_potential parameter otsTable ftsTable result
        (runRetainedWithFailure_cache_finite _ adversary parameter otsTable ftsTable q fuel result hr))
    simpa only [mul_add, mul_ite, mul_one, mul_zero] using h
  · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    split_ifs <;> simp

theorem probEvent_original_win_add_collisionParentCredit_le_failure_add_charge_add_live_residual
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (hots : otsTable ∈ support OtsProbeSimulation.sampleOtsHashTable)
    (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    Pr[fun result => retainedRestVerdict result.1.1.2 = true | originalParentRecords adversary parameter otsTable ftsTable] +
      initializedCollisionParentCredit adversary parameter otsTable ftsTable q fuel ≤
    Pr[fun result => result.2 = true | runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] +
      initializedBeforeFailureCollisionCharge adversary parameter otsTable ftsTable q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
      Pr[LiveNonSecretResidual parameter otsTable ftsTable |
        runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] := by
  rw [probEvent_originalRecords_eq_retained adversary q hq parameter hparameter otsTable ftsTable hfts fuel
    (fun result => retainedRestVerdict result.1.2 = true)]
  apply (add_le_add (probEvent_mono
    (q := fun result => result.2 = true ∨ SurvivingStructuralFailure parameter otsTable ftsTable result ∨
      LiveNonSecretResidual parameter otsTable ftsTable result)
    (fun result hr ⟨value, hv, hwin⟩ =>
      retained_win_cases_live_residual adversary q hq parameter hparameter otsTable hots ftsTable hfts fuel result hr value hv hwin)) le_rfl).trans
  apply (add_le_add (probEvent_or_le _ _ _) le_rfl).trans
  apply (add_le_add (add_le_add le_rfl (probEvent_or_le _ _ _)) le_rfl).trans
  have hsum := add_le_add (add_le_add
    (le_refl (Pr[fun result => result.2 = true | runRetainedWithFailure (parentException parameter otsTable ftsTable)
      adversary parameter otsTable ftsTable q fuel]))
    (probEvent_structuralFailure_add_parentCredit_le_beforeFailureCollisionCharge adversary parameter otsTable ftsTable q fuel))
    (le_refl (Pr[LiveNonSecretResidual parameter otsTable ftsTable |
      runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel]))
  simpa only [add_assoc, add_comm, add_left_comm] using hsum

noncomputable def sampledCollisionParentCredit (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        initializedCollisionParentCredit adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel

theorem forgeAdvantage_add_collisionParentCredit_le_sharedFailure_add_charge_add_live_residual
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (fuel : Nat) :
    forgeAdvantage scheme adversary + sampledCollisionParentCredit adversary q fuel ≤ sampledParentSharedFailureRisk adversary q fuel +
      sampledBeforeFailureCollisionCharge adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
      sampledLiveNonSecretResidual adversary q fuel := by
  rw [forgeAdvantage_eq_sampledRetained_win, probEvent_sampledRetained_eq_recordRisk]
  unfold sampledCollisionParentCredit sampledOriginalRecordRisk sampledParentSharedFailureRisk sampledBeforeFailureCollisionCharge sampledLiveNonSecretResidual
  conv_lhs => simp only [← ENNReal.tsum_add, ← mul_add]
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
        · exact mul_le_mul' le_rfl (probEvent_original_win_add_collisionParentCredit_le_failure_add_charge_add_live_residual adversary q hq parameter hp table ht
            (curryFtsTableEquiv ftsSecret) (mem_support_sampleFtsSecrets ftsSecret) fuel)
        · rw [probOutput_eq_zero_of_not_mem_support ht, zero_mul, zero_mul]
      · rw [probOutput_eq_zero_of_not_mem_support hp, zero_mul, zero_mul]
    _ = _ := by
      simp only [mul_add, ENNReal.tsum_add, ← mul_assoc, ENNReal.tsum_mul_right]

noncomputable def sampledSharedParentDiscard (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        initializedSharedParentDiscard adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel

theorem sampledCollisionParentCredit_eq_terminal_add_shared (adversary : Adversary) (q fuel : Nat) :
    sampledCollisionParentCredit adversary q fuel = sampledCollisionTerminalReserve adversary q fuel +
      sampledSharedParentDiscard adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ := by
  unfold sampledCollisionParentCredit initializedCollisionParentCredit sampledCollisionTerminalReserve sampledSharedParentDiscard
  simp only [mul_add, ENNReal.tsum_add, ← mul_assoc, ENNReal.tsum_mul_right]

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
