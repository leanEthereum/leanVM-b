import SphincsSecurity.Proof.RetainedTargetCoverage127
import SphincsSecurity.Proof.SecurityWorldCoverBudget

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

theorem probEvent_liveNonSecretResidual_le_targetCoverage127
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127)
    (parameter : PublicParameter) (hp : parameter ∈ support sampleParameter)
    (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (hfts : (fun index tree leaf => ftsTable (index, tree, leaf)) ∈ support sampleFtsSecrets) (fuel : Nat) :
    Pr[LiveNonSecretResidual parameter otsTable ftsTable |
      runRetainedWithFailure (parentException parameter otsTable ftsTable) adversary parameter otsTable ftsTable q fuel] ≤
      (q : ENNReal) * ((29 / 64 : ENNReal) * ((2 ^ 127 : Nat) : ENNReal)⁻¹) := by
  apply (probEvent_liveNonSecretResidual_le_original adversary q hq parameter hp otsTable ftsTable hfts fuel).trans
  apply (probEvent_original_residual_le_actual_validObservedCover adversary parameter otsTable ftsTable).trans
  exact probEvent_actualRetained_validObservedCover_le_127_of_hashQueryBound adversary parameter hp _
    (OtsProbeSimulation.mem_support_sampleOtsSecrets_all _) ftsTable hfts q hqMax hq

private theorem expected_le_constant {α : Type} (computation : ProbComp α) (weight : α → ENNReal) (bound : ENNReal)
    (h : ∀ result ∈ support computation, weight result ≤ bound) :
    (∑' result, Pr[= result | computation] * weight result) ≤ bound := by
  calc
    _ ≤ ∑' result, Pr[= result | computation] * bound := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hresult : result ∈ support computation
      · exact mul_le_mul' le_rfl (h result hresult)
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one

theorem sampledLiveNonSecretResidual_le_targetCoverage127
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledLiveNonSecretResidual adversary q fuel ≤
      (q : ENNReal) * ((29 / 64 : ENNReal) * ((2 ^ 127 : Nat) : ENNReal)⁻¹) := by
  unfold sampledLiveNonSecretResidual
  apply expected_le_constant
  intro parameter hp
  apply expected_le_constant
  intro ftsSecret hfts
  apply expected_le_constant
  intro table _
  exact probEvent_liveNonSecretResidual_le_targetCoverage127 adversary q hq hqMax parameter hp table
    (curryFtsTableEquiv ftsSecret) hfts fuel

theorem forgeAdvantage_add_messageReserves_le_targetCoverage127
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary +
      (sampledSelectedJointQueryCharge MessageHashInput adversary q + sampledBeforeFailureHashCharge messageHashCharge adversary q (q + 1)) *
        (Fintype.card Digest : ENNReal)⁻¹ ≤
      (sampledBeforeFailureRestHashCharge adversary q (q + 1) + (q : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ +
      (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) +
      (q : ENNReal) * ((29 / 64 : ENNReal) * ((2 ^ 127 : Nat) : ENNReal)⁻¹) := by
  apply (forgeAdvantage_add_messageReserves_le_joint_beforeFailureBudget_live adversary q hq hqMax).trans
  exact add_le_add le_rfl (sampledLiveNonSecretResidual_le_targetCoverage127 adversary q hq hqMax (q + 1))

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
