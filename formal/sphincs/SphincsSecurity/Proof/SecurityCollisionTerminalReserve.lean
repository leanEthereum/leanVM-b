import SphincsSecurity.Proof.CollisionTerminalReserve
import SphincsSecurity.Proof.SecurityCollisionBeforeFailure

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex retainedRestVerdict)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

theorem probEvent_original_win_add_collisionTerminalReserve_le_failure_add_charge_add_live_residual
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (hots : otsTable ∈ support OtsProbeSimulation.sampleOtsHashTable)
    (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    Pr[fun result => retainedRestVerdict result.1.1.2 = true | originalParentRecords adversary parameter otsTable ftsTable] +
      initializedCollisionTerminalReserve adversary parameter otsTable ftsTable q fuel ≤
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
    (probEvent_structuralFailure_add_terminalReserve_le_beforeFailureCollisionCharge adversary parameter otsTable ftsTable q fuel))
    (le_refl (Pr[LiveNonSecretResidual parameter otsTable ftsTable |
      runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel]))
  simpa only [add_assoc, add_comm, add_left_comm] using hsum

noncomputable def sampledCollisionTerminalReserve (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        initializedCollisionTerminalReserve adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel

theorem forgeAdvantage_add_collisionTerminalReserve_le_sharedFailure_add_charge_add_live_residual
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (fuel : Nat) :
    forgeAdvantage scheme adversary + sampledCollisionTerminalReserve adversary q fuel ≤ sampledParentSharedFailureRisk adversary q fuel +
      sampledBeforeFailureCollisionCharge adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
      sampledLiveNonSecretResidual adversary q fuel := by
  rw [forgeAdvantage_eq_sampledRetained_win, probEvent_sampledRetained_eq_recordRisk]
  unfold sampledCollisionTerminalReserve sampledOriginalRecordRisk sampledParentSharedFailureRisk sampledBeforeFailureCollisionCharge sampledLiveNonSecretResidual
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
        · exact mul_le_mul' le_rfl (probEvent_original_win_add_collisionTerminalReserve_le_failure_add_charge_add_live_residual adversary q hq parameter hp table ht
            (curryFtsTableEquiv ftsSecret) (mem_support_sampleFtsSecrets ftsSecret) fuel)
        · rw [probOutput_eq_zero_of_not_mem_support ht, zero_mul, zero_mul]
      · rw [probOutput_eq_zero_of_not_mem_support hp, zero_mul, zero_mul]
    _ = _ := by
      simp only [mul_add, ENNReal.tsum_add, ← mul_assoc, ENNReal.tsum_mul_right]

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
