import SphincsSecurity.Proof.SigningCoverageResidualRefund
import SphincsSecurity.Proof.AdaptivePaidCoverage

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation.JointOriginal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem remainingCoverageExecutionGap_arrivals_mono (key : SecretKey) (cap budget cost : Nat) (state : CoverLogState)
    {small large : Nat} (h : small ≤ large) :
    remainingCoverageExecutionGap key cap budget cost small state ∅ Finset.univ ≤
      remainingCoverageExecutionGap key cap budget cost large state ∅ Finset.univ := by
  unfold remainingCoverageExecutionGap
  exact add_le_add le_rfl (mul_le_mul' (mul_le_mul' le_rfl (Nat.cast_le.mpr (Nat.add_le_add_left h _))) le_rfl)

theorem signingCoverageExecutionRefund_le_twice_unused (key : SecretKey) (cap budget : Nat) (message : Message) (state : CoverLogState) :
    signingCoverageExecutionRefund key cap budget message state ≤
      2 * (remainingUnusedCoverageStepCharge key cap budget state (.inr message) ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹) := by
  have hcost : (signingExecutionHashCost (.inr message) : ENNReal) ≤
      2 * (unusedTargetExecutionCost key.parameter state.1 (.inr message) : ENNReal) := by
    norm_num [signingExecutionHashCost, unusedTargetExecutionCost, unusedTargetHashCost,
      signingMacroHashCost, targetArrivalHashCost, unusedSigningExecutionCost, digestAttemptLimit]
  have hgap := (remainingCoverageExecutionGap_arrivals_mono key cap budget (signingExecutionHashCost (.inr message)) state
    (Nat.zero_le (targetArrivalHashCost key.parameter state.1 (.inr message)))).trans
      (le_mul_of_one_le_left' (show (1 : ENNReal) ≤ 2 by norm_num))
  have h := mul_le_mul' (add_le_add
    (mul_le_mul' (mul_le_mul' (le_refl (cappedRemainingRawIndexEnvelope key cap budget state ∅ Finset.univ)) hcost)
      (le_refl (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹))) hgap)
    (le_refl (((2 ^ 140 : Nat) : ENNReal)⁻¹))
  simp only [signingCoverageExecutionRefund, coverageExecutionRefund, remainingUnusedCoverageStepCharge]
  convert h using 1 <;> first | rfl | ring

namespace FtsProbeSimulation.JointOriginal

theorem paidRemainingCoverageStepRefund_le_twice_unused
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsProbeSimulation.OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (input : (OracleWorld + SigningSpec).Domain) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) :
    paidRemainingCoverageStepRefund exception parameter root otsTable ftsTable cap budget input frame state hit failed ≤
      2 * (stoppedRemainingCoverageStepCharge exception parameter root otsTable ftsTable cap budget input frame state hit failed
        ∅ Finset.univ * ((2 ^ 140 : Nat) : ENNReal)⁻¹) := by
  cases input with
  | inl world => exact le_mul_of_one_le_left' (by norm_num)
  | inr message =>
      apply le_trans ?_ (mul_le_mul' (le_refl (2 : ENNReal)) (mul_le_mul' le_self_add le_rfl))
      simp only [paidRemainingCoverageStepRefund, survivingLogPotential]
      split_ifs
      · simp only [zero_mul, mul_zero, le_refl]
      · exact signingCoverageExecutionRefund_le_twice_unused _ cap budget message state

theorem expectedPaidCoverageRefund_le_twice_remainingUnused
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsProbeSimulation.OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) :
    expectedPaidCoverageRefund exception parameter root otsTable ftsTable cap computation budget frame state hit failed ≤
      2 * (expectedRemainingUnusedCoverageCharge exception parameter root otsTable ftsTable cap ∅ Finset.univ
        computation budget frame state hit failed * ((2 ^ 140 : Nat) : ENNReal)⁻¹) := by
  induction computation using OracleComp.inductionOn generalizing budget frame state hit failed with
  | pure value =>
      simp only [expectedPaidCoverageRefund, expectedBudgetedLogCharge_pure, expectedRemainingUnusedCoverageCharge_pure,
        survivingLogPotential_mul]
      exact le_mul_of_one_le_left' (by norm_num)
  | query_bind input next ih =>
      simp only [expectedPaidCoverageRefund, expectedBudgetedLogCharge_query_bind, expectedRemainingUnusedCoverageCharge_query_bind,
        add_mul, mul_add, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
      apply add_le_add (paidRemainingCoverageStepRefund_le_twice_unused exception parameter root otsTable ftsTable
        cap budget input frame state hit failed)
      apply ENNReal.tsum_le_tsum
      intro result
      have h := mul_le_mul' (le_refl (Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed]))
        (ih result.1.2.1.1 (budget - signingExecutionHashCost input) result.1.1 (stepSigningLogState input state.2 result) result.1.2.2 result.2)
      simpa only [expectedPaidCoverageRefund, mul_assoc, mul_comm, mul_left_comm] using h

theorem expectedPaidCoverageResidual_le_refund_fraction
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsProbeSimulation.OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (state : CoverLogState) (hit failed : Bool)
    (hsigned : SigningDigestsCached parameter state.1 root state.2) :
    expectedPaidCoverageResidual exception parameter root otsTable ftsTable cap computation budget frame state hit failed ≤
      expectedPaidCoverageRefund exception parameter root otsTable ftsTable cap computation budget frame state hit failed *
        ((2 ^ 22 : Nat) : ENNReal)⁻¹ := by
  induction computation using OracleComp.inductionOn generalizing budget frame state hit failed with
  | pure value => exact zero_le
  | query_bind input next ih =>
      simp only [expectedPaidCoverageRefund, expectedPaidCoverageResidual, expectedBudgetedLogCharge_query_bind,
        add_mul, ← ENNReal.tsum_mul_right]
      apply add_le_add (paidRemainingCoverageStepResidual_le_refund_fraction exception parameter root otsTable ftsTable
        cap budget input frame state hit failed hsigned)
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed)
      · have hlogged := stepWithFailure_logged_support exception parameter root otsTable ftsTable input frame state.1 state.2 hit failed result hr
        have h := ih result.1.2.1.1 (budget - signingExecutionHashCost input) result.1.1 (stepSigningLogState input state.2 result)
          result.1.2.2 result.2 (logTracedMappedAdversaryImpl_signingDigestsCached (secretKey parameter root otsTable ftsTable) input state hsigned _ hlogged)
        simpa only [mul_assoc] using mul_le_mul' (le_refl (Pr[= result |
          stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed])) h
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul, zero_mul]

end FtsProbeSimulation.JointOriginal
end SphincsSecurity.Concrete
