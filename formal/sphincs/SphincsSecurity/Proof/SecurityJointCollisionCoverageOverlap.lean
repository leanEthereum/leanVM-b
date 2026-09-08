import SphincsSecurity.Proof.InitializedJointCollisionCoverageOverlap
import SphincsSecurity.Proof.SecurityJointCollisionCoverageCompletion
import SphincsSecurity.Proof.SecurityCollisionBeforeFailure
import SphincsSecurity.Proof.SecurityCollisionTerminalAllocation

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

noncomputable def sampledJointCollisionCoverageOverlap (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        initializedJointCollisionCoverageOverlap adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel

private theorem expected_add_le_add (computation : ProbComp α) (left overlap collision failure : α → ENNReal)
    (h : ∀ result ∈ support computation, left result + overlap result ≤ collision result + failure result) :
    (∑' result, Pr[= result | computation] * left result) + (∑' result, Pr[= result | computation] * overlap result) ≤
      (∑' result, Pr[= result | computation] * collision result) + (∑' result, Pr[= result | computation] * failure result) := by
  rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  rw [← mul_add, ← mul_add]
  by_cases hr : result ∈ support computation
  · exact mul_le_mul' le_rfl (h result hr)
  · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]

theorem sampledJointCollisionCoverageCharge_add_overlap_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (fuel : Nat) :
    sampledJointCollisionCoverageCharge adversary q fuel + sampledJointCollisionCoverageOverlap adversary q fuel ≤
      sampledBeforeFailureCollisionCharge adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
      sampledParentSharedFailureRisk adversary q fuel := by
  unfold sampledJointCollisionCoverageCharge sampledJointCollisionCoverageOverlap sampledBeforeFailureCollisionCharge sampledParentSharedFailureRisk
  simp only [← ENNReal.tsum_mul_right, mul_assoc]
  apply expected_add_le_add
  intro parameter hp
  apply expected_add_le_add
  intro ftsSecret hfts
  apply expected_add_le_add
  intro table _
  exact initializedJointCollisionCoverageCharge_add_overlap_le adversary q hq parameter hp table
    (curryFtsTableEquiv ftsSecret) hfts fuel

theorem forgeAdvantage_add_jointCredits_overlap_le_collisionEnvelope
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    forgeAdvantage scheme adversary + sampledJointCollisionCoverageCompletionCredit adversary q fuel +
      sampledJointCollisionCoverageCredit adversary q fuel + sampledJointCollisionCoverageOverlap adversary q fuel ≤
      min 1 ((q : ENNReal) * initialRawIndexRate q) + (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ +
        (sampledBeforeFailureCollisionCharge adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
          sampledParentSharedFailureRisk adversary q fuel) := by
  have h := add_le_add (forgeAdvantage_add_jointCollisionCoverage_completionCredits_le adversary q hq hqMax fuel)
    (le_refl (sampledJointCollisionCoverageOverlap adversary q fuel))
  rw [add_assoc _ (sampledJointCollisionCoverageCharge adversary q fuel)] at h
  exact h.trans (add_le_add le_rfl (sampledJointCollisionCoverageCharge_add_overlap_le adversary q hq fuel))

theorem forgeAdvantage_add_jointCredits_overlap_executionReserves_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary + sampledJointCollisionCoverageCompletionCredit adversary q (q + 1) +
      sampledJointCollisionCoverageCredit adversary q (q + 1) + sampledJointCollisionCoverageOverlap adversary q (q + 1) +
      (sampledSelectedJointQueryCharge MessageHashInput adversary q + sampledBeforeFailureHashCharge messageHashCharge adversary q (q + 1) +
        sampledSigningNonEncodingReserve adversary q (q + 1) + sampledOuterEncodingReserve adversary q (q + 1)) * (Fintype.card Digest : ENNReal)⁻¹ ≤
      (sampledBeforeFailureRestHashCharge adversary q (q + 1) + (q : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ +
        (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) +
        sampledBeforeFailureEncodingPairCharge adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹ +
        (min 1 ((q : ENNReal) * initialRawIndexRate q) + (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹) := by
  apply collisionFailureBound_add_message_signing_encodingReserves_le adversary q hqMax
  simpa only [add_assoc, add_comm, add_left_comm] using
    forgeAdvantage_add_jointCredits_overlap_le_collisionEnvelope adversary q hq hqMax (q + 1)

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
