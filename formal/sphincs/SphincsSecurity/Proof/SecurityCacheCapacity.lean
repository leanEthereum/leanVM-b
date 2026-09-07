import SphincsSecurity.Proof.RetainedCacheCapacity
import SphincsSecurity.Proof.SecurityWorldCoverBudget

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

theorem probEvent_liveNonSecretResidual_le_capacityBudget_add_reuse
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127)
    (parameter : PublicParameter) (hp : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    Pr[LiveNonSecretResidual parameter otsTable ftsTable |
      runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] ≤
      worldCoverageBudget q + expectedRetainedCapacityReuseCharge adversary parameter (tableSecrets parameter otsTable ftsTable).otsSecret ftsTable q := by
  apply (probEvent_liveNonSecretResidual_le_original adversary q hq parameter hp otsTable ftsTable hfts fuel).trans
  apply (probEvent_original_residual_le_actual_validObservedCover adversary parameter otsTable ftsTable).trans
  simpa only [worldCoverageBudget_eq, mul_assoc] using
    probEvent_actualRetained_validObservedCover_le_capacity_of_hashQueryBound adversary parameter hp _
      (OtsProbeSimulation.mem_support_sampleOtsSecrets_all _) ftsTable hfts q hqMax hq

noncomputable def sampledRetainedCapacityReuseCharge (adversary : Adversary) (q : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        expectedRetainedCapacityReuseCharge adversary parameter
          (tableSecrets parameter table (curryFtsTableEquiv ftsSecret)).otsSecret (curryFtsTableEquiv ftsSecret) q

private theorem expected_le_const_add {α : Type} (computation : ProbComp α) (left right : α → ENNReal) (cost : ENNReal)
    (h : ∀ result ∈ support computation, left result ≤ cost + right result) :
    (∑' result, Pr[= result | computation] * left result) ≤ cost + ∑' result, Pr[= result | computation] * right result := by
  calc
    _ ≤ ∑' result, Pr[= result | computation] * (cost + right result) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hresult : result ∈ support computation
      · exact mul_le_mul' le_rfl (h result hresult)
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
    _ ≤ _ := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
      exact add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) le_rfl

theorem sampledLiveNonSecretResidual_le_capacityBudget_add_reuse
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledLiveNonSecretResidual adversary q fuel ≤ worldCoverageBudget q + sampledRetainedCapacityReuseCharge adversary q := by
  unfold sampledLiveNonSecretResidual sampledRetainedCapacityReuseCharge
  apply expected_le_const_add
  intro parameter hp
  apply expected_le_const_add
  intro ftsSecret hfts
  apply expected_le_const_add
  intro table _
  exact probEvent_liveNonSecretResidual_le_capacityBudget_add_reuse adversary q hq hqMax parameter hp table
    (curryFtsTableEquiv ftsSecret) hfts fuel

theorem forgeAdvantage_add_messageReserves_le_capacityBudget_add_reuse
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary +
      (sampledSelectedJointQueryCharge MessageHashInput adversary q + sampledBeforeFailureHashCharge messageHashCharge adversary q (q + 1)) *
        (Fintype.card Digest : ENNReal)⁻¹ ≤
      (sampledBeforeFailureRestHashCharge adversary q (q + 1) + (q : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ +
      (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) + worldCoverageBudget q + sampledRetainedCapacityReuseCharge adversary q := by
  apply (forgeAdvantage_add_messageReserves_le_joint_beforeFailureBudget_live adversary q hq hqMax).trans
  exact (add_le_add le_rfl (sampledLiveNonSecretResidual_le_capacityBudget_add_reuse adversary q hq hqMax (q + 1))).trans_eq
    (add_assoc _ _ _).symm

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
