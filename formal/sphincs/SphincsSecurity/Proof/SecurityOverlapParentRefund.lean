import SphincsSecurity.Proof.InitializedOverlapParentRefund
import SphincsSecurity.Proof.SecurityJointCollisionCoverageOverlap
import SphincsSecurity.Proof.SecuritySharedParentRefund

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

noncomputable def sampledJointCoverageAfterParentRefund (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        initializedJointCoverageAfterParentRefund adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel

private theorem expected_scaled_add_le (computation : ProbComp α) (parent remainder overlap : α → ENNReal) (rate : ENNReal)
    (h : ∀ result ∈ support computation, parent result * rate + remainder result ≤ overlap result) :
    (∑' result, Pr[= result | computation] * parent result) * rate + (∑' result, Pr[= result | computation] * remainder result) ≤
      ∑' result, Pr[= result | computation] * overlap result := by
  rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  rw [mul_assoc, ← mul_add]
  by_cases hr : result ∈ support computation
  · exact mul_le_mul' le_rfl (h result hr)
  · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]

theorem sampled_sharedParentDiscard_add_remainder_le_overlap
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledSharedParentDiscard adversary q fuel * (2 * (Fintype.card Digest : ENNReal)⁻¹) +
      sampledJointCoverageAfterParentRefund adversary q fuel ≤ sampledJointCollisionCoverageOverlap adversary q fuel := by
  unfold sampledSharedParentDiscard sampledJointCoverageAfterParentRefund sampledJointCollisionCoverageOverlap
  apply expected_scaled_add_le
  intro parameter hp
  apply expected_scaled_add_le
  intro ftsSecret hfts
  apply expected_scaled_add_le
  intro table _
  exact initialized_sharedParentDiscard_add_remainder_le_overlap adversary q hq hqMax parameter hp table
    (curryFtsTableEquiv ftsSecret) hfts fuel

theorem forgeAdvantage_add_jointCredits_sharedParentRefund_executionReserves_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary + sampledJointCollisionCoverageCompletionCredit adversary q (q + 1) +
      sampledJointCollisionCoverageCredit adversary q (q + 1) +
      (sampledSharedParentDiscard adversary q (q + 1) * (2 * (Fintype.card Digest : ENNReal)⁻¹) +
        sampledJointCoverageAfterParentRefund adversary q (q + 1)) +
      (sampledSelectedJointQueryCharge MessageHashInput adversary q + sampledBeforeFailureHashCharge messageHashCharge adversary q (q + 1) +
        sampledSigningNonEncodingReserve adversary q (q + 1) + sampledOuterEncodingReserve adversary q (q + 1)) * (Fintype.card Digest : ENNReal)⁻¹ ≤
      (sampledBeforeFailureRestHashCharge adversary q (q + 1) + (q : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ +
        (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) +
        sampledBeforeFailureEncodingPairCharge adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹ +
        (min 1 ((q : ENNReal) * initialRawIndexRate q) + (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹) :=
  (add_le_add (add_le_add le_rfl (sampled_sharedParentDiscard_add_remainder_le_overlap adversary q hq hqMax (q + 1))) le_rfl).trans
    (forgeAdvantage_add_jointCredits_overlap_executionReserves_le adversary q hq hqMax)

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
