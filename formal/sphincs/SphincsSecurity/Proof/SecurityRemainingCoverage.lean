import SphincsSecurity.Proof.InitializedRemainingCoverage
import SphincsSecurity.Proof.SecurityDoubleSharedRefundAllocation

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

noncomputable def sampledRemainingUnusedCoverageCharge (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        initializedRemainingUnusedCoverageCharge adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel

private theorem expected_le_constant {α : Type} (computation : ProbComp α)
    (weight : α → ENNReal) (bound : ENNReal)
    (h : ∀ result ∈ support computation, weight result ≤ bound) :
    (∑' result, Pr[= result | computation] * weight result) ≤ bound := by
  calc
    _ ≤ ∑' result, Pr[= result | computation] * bound := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support computation
      · exact mul_le_mul' le_rfl (h result hr)
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one

theorem sampledLiveNonSecretResidual_add_remainingUnused_le_initial
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledLiveNonSecretResidual adversary q fuel + sampledRemainingUnusedCoverageCharge adversary q fuel ≤
      (q : ENNReal) * initialRawIndexRate q := by
  unfold sampledLiveNonSecretResidual sampledRemainingUnusedCoverageCharge
  simp only [← ENNReal.tsum_add, ← mul_add]
  apply expected_le_constant
  intro parameter hp
  apply expected_le_constant
  intro ftsSecret hfts
  apply expected_le_constant
  intro table _
  exact probEvent_liveNonSecretResidual_add_initialized_remainingUnused_le_initial adversary q hq hqMax parameter hp table
    (curryFtsTableEquiv ftsSecret) hfts fuel

theorem forgeAdvantage_add_doubleParentCredit_remainingCoverage_le_collisionEnvelope
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary + sampledCollisionDoubleParentCredit adversary q (q + 1) +
      (sampledSelectedJointQueryCharge MessageHashInput adversary q + sampledBeforeFailureHashCharge messageHashCharge adversary q (q + 1) +
        sampledSigningNonEncodingReserve adversary q (q + 1) + sampledOuterEncodingReserve adversary q (q + 1)) * (Fintype.card Digest : ENNReal)⁻¹ +
      sampledRemainingUnusedCoverageCharge adversary q (q + 1) ≤
      (sampledBeforeFailureRestHashCharge adversary q (q + 1) + (q : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ +
      (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) +
      sampledBeforeFailureEncodingPairCharge adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹ +
      (q : ENNReal) * initialRawIndexRate q := by
  have hbase := forgeAdvantage_add_collisionCredit_message_signing_encodingReserves_le_collision_live adversary q hqMax
    (sampledCollisionDoubleParentCredit adversary q (q + 1))
    (forgeAdvantage_add_collisionDoubleParentCredit_le_sharedFailure_add_charge_add_live_residual adversary q hq hqMax (q + 1))
  apply (add_le_add hbase le_rfl).trans
  rw [add_assoc]
  exact add_le_add le_rfl (sampledLiveNonSecretResidual_add_remainingUnused_le_initial adversary q hq hqMax (q + 1))

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
