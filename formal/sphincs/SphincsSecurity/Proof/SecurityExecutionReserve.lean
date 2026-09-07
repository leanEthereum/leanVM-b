import SphincsSecurity.Proof.InitializedExecutionReserve
import SphincsSecurity.Proof.SecurityStoppedTarget

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

noncomputable def sampledUnusedExecutionReserve (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        initializedUnusedExecutionReserve adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel

private theorem expected_add_le_constant {α : Type} (computation : ProbComp α)
    (left right : α → ENNReal) (bound : ENNReal)
    (h : ∀ result ∈ support computation, left result + right result ≤ bound) :
    (∑' result, Pr[= result | computation] * left result) +
      (∑' result, Pr[= result | computation] * right result) ≤ bound := by
  rw [← ENNReal.tsum_add]
  calc
    _ ≤ ∑' result, Pr[= result | computation] * bound := by
      apply ENNReal.tsum_le_tsum
      intro result
      rw [← mul_add]
      by_cases hresult : result ∈ support computation
      · exact mul_le_mul' le_rfl (h result hresult)
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one

theorem sampledStoppedTargetCharge_add_unused_execution_le_127
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledStoppedTargetCharge adversary q fuel + sampledUnusedExecutionReserve adversary q fuel ≤
      (q : ENNReal) * ((29 / 64 : ENNReal) * ((2 ^ 127 : Nat) : ENNReal)⁻¹) := by
  unfold sampledStoppedTargetCharge sampledUnusedExecutionReserve
  apply expected_add_le_constant
  intro parameter hp
  apply expected_add_le_constant
  intro ftsSecret hfts
  apply expected_add_le_constant
  intro table _
  exact initializedStoppedTargetCharge_add_unused_execution_le_127 adversary q hq hqMax parameter hp table
    (curryFtsTableEquiv ftsSecret) hfts fuel

theorem forgeAdvantage_add_message_signing_executionReserves_le_targetCoverage127
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary +
      (sampledSelectedJointQueryCharge MessageHashInput adversary q + sampledBeforeFailureHashCharge messageHashCharge adversary q (q + 1) +
        sampledSigningNonEncodingReserve adversary q (q + 1)) * (Fintype.card Digest : ENNReal)⁻¹ +
      sampledUnusedExecutionReserve adversary q (q + 1) ≤
      (sampledBeforeFailureRestHashCharge adversary q (q + 1) + (q : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ +
      (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) +
      (q : ENNReal) * ((29 / 64 : ENNReal) * ((2 ^ 127 : Nat) : ENNReal)⁻¹) := by
  apply (add_le_add (forgeAdvantage_add_message_and_signingReserves_le_stoppedTargetCharge adversary q hq hqMax) le_rfl).trans
  rw [add_assoc]
  exact add_le_add le_rfl (sampledStoppedTargetCharge_add_unused_execution_le_127 adversary q hq hqMax (q + 1))

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
