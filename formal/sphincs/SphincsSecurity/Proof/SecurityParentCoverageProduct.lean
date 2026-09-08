import SphincsSecurity.Proof.InitializedParentCoverageProduct
import SphincsSecurity.Proof.SecurityJointParentFunding

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

private theorem expected_le_one (computation : SPMF α) (weight : α → ENNReal)
    (h : ∀ result ∈ support computation, weight result ≤ 1) :
    (∑' result, Pr[= result | computation] * weight result) ≤ 1 := by
  apply le_trans ?_ (tsum_probOutput_le_one (mx := computation))
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ support computation
  · exact mul_le_of_le_one_right' (h result hr)
  · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul]

private theorem expected_prob_le_one (computation : ProbComp α) (weight : α → ENNReal)
    (h : ∀ result ∈ support computation, weight result ≤ 1) :
    (∑' result, Pr[= result | computation] * weight result) ≤ 1 := by
  apply expected_le_one (evalDist computation) weight
  intro result hr
  exact h result ((mem_support_iff_evalDist_apply_ne_zero _ _).2 ((SPMF.mem_support_iff _ _).1 hr))

theorem sampledTerminalParentCoverageOverlap_le_one
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledTerminalParentCoverageOverlap adversary q fuel ≤ 1 := by
  unfold sampledTerminalParentCoverageOverlap
  apply expected_prob_le_one
  intro parameter hp
  apply expected_prob_le_one
  intro ftsSecret hfts
  apply expected_prob_le_one
  intro table _
  apply expected_le_one
  intro result hr
  have h := twice_terminalPendingParentCount_scaled_le_bounded_collision parameter default table (curryFtsTableEquiv ftsSecret) result
    (runRetainedWithFailure_cache_finite _ adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel result hr)
    ((runRetainedWithFailure_cache_le_queryBound _ adversary q hq parameter hp table (curryFtsTableEquiv ftsSecret) hfts fuel result hr).trans
      (Nat.cast_le.mpr hqMax))
  exact (le_add_self.trans_eq (terminalJointParentCredit_add_overlap parameter table (curryFtsTableEquiv ftsSecret) result)).trans
    (h.trans (min_le_left _ _))

noncomputable def sampledJointCoverageAfterTerminalRefund (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  sampledJointCoverageAfterParentRefund adversary q fuel - sampledTerminalParentCoverageOverlap adversary q fuel

theorem sampledJointCoverageAfterTerminalRefund_add_overlap
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    sampledJointCoverageAfterTerminalRefund adversary q fuel + sampledTerminalParentCoverageOverlap adversary q fuel =
      sampledJointCoverageAfterParentRefund adversary q fuel :=
  tsub_add_cancel_of_le (sampled_terminalParentOverlap_le_afterParentRefund adversary q hq hqMax fuel)

theorem forgeAdvantage_add_jointParentFunding_afterTerminalRefund_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary +
      (sampledJointCollisionCoverageCompletionCredit adversary q (q + 1) + sampledJointCollisionCoverageCredit adversary q (q + 1) +
        sampledJointCoverageAfterTerminalRefund adversary q (q + 1) +
        (sampledSelectedJointQueryCharge MessageHashInput adversary q + sampledBeforeFailureHashCharge messageHashCharge adversary q (q + 1) +
          sampledSigningNonEncodingReserve adversary q (q + 1) + sampledOuterEncodingReserve adversary q (q + 1)) * (Fintype.card Digest : ENNReal)⁻¹) +
      sampledFreshParentReserveCharge adversary q (q + 1) * (2 * (Fintype.card Digest : ENNReal)⁻¹) ≤
      (sampledBeforeFailureRestHashCharge adversary q (q + 1) + (q : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ +
        (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) + sampledBeforeFailureEncodingPairCharge adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹ +
        (min 1 ((q : ENNReal) * initialRawIndexRate q) + (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹) +
        (sampledTerminalParentDiscard adversary q (q + 1) + sampledLocalizedParentReleaseCharge adversary q (q + 1)) *
          (2 * (Fintype.card Digest : ENNReal)⁻¹) := by
  have h := forgeAdvantage_add_jointParentFunding_executionReserves_le adversary q hq hqMax
  rw [← sampledJointCoverageAfterTerminalRefund_add_overlap adversary q hq hqMax (q + 1)] at h
  apply ENNReal.le_of_add_le_add_right (ne_top_of_le_ne_top ENNReal.one_ne_top
    (sampledTerminalParentCoverageOverlap_le_one adversary q hq hqMax (q + 1)))
  convert h using 1 <;> first | rfl | ring

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
