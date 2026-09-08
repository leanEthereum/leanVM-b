import SphincsSecurity.Proof.RemainingCoverageGap
import SphincsSecurity.Proof.StoppedTargetCharge

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
set_option backward.isDefEq.respectTransparency false

noncomputable def expectedRemainingUnusedCoverageCharge
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap : Nat) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (computation : OracleComp (OracleWorld + SigningSpec) α) : Nat → Option Frame → CoverLogState → Bool → Bool → ENNReal :=
  OracleComp.construct (fun _ budget _ state hit failed =>
    survivingLogPotential (fun current => remainingCoverageTerminalReserve
      (secretKey parameter root otsTable ftsTable) cap budget current groups remaining) state hit failed)
    (fun input _ next budget frame state hit failed =>
      survivingLogPotential (fun current => remainingUnusedCoverageStepCharge
        (secretKey parameter root otsTable ftsTable) cap budget current input groups remaining) state hit failed +
        ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
          next result.1.2.1.1 (budget - signingExecutionHashCost input) result.1.1
            (stepSigningLogState input state.2 result) result.1.2.2 result.2) computation

@[simp] theorem expectedRemainingUnusedCoverageCharge_pure
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap : Nat) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (value : α) (budget : Nat) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) :
    expectedRemainingUnusedCoverageCharge exception parameter root otsTable ftsTable cap groups remaining
      (pure value) budget frame state hit failed =
      survivingLogPotential (fun current => remainingCoverageTerminalReserve
        (secretKey parameter root otsTable ftsTable) cap budget current groups remaining) state hit failed := rfl

theorem expectedRemainingUnusedCoverageCharge_query_bind
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap : Nat) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (budget : Nat) (frame : Option Frame) (state : CoverLogState) (hit failed : Bool) :
    expectedRemainingUnusedCoverageCharge exception parameter root otsTable ftsTable cap groups remaining
        (OracleSpec.query input >>= next) budget frame state hit failed =
      survivingLogPotential (fun current => remainingUnusedCoverageStepCharge
        (secretKey parameter root otsTable ftsTable) cap budget current input groups remaining) state hit failed +
        ∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
          expectedRemainingUnusedCoverageCharge exception parameter root otsTable ftsTable cap groups remaining
            (next result.1.2.1.1) (budget - signingExecutionHashCost input) result.1.1
              (stepSigningLogState input state.2 result) result.1.2.2 result.2 := rfl

theorem stepWithFailure_remainingCoverage_add_unused_le
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (hcap : cap ≤ 2 ^ 127) (input : (OracleWorld + SigningSpec).Domain)
    (frame : Option Frame) (state : CoverLogState) (hit failed : Bool)
    (hsigned : SigningDigestsCached parameter state.1 root state.2) (hcache : QueryCache.enncard state.1 ≤ cap)
    (hcost : signingExecutionHashCost input ≤ budget)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] *
      survivingLogPotential (fun current => remainingCoveragePotential (secretKey parameter root otsTable ftsTable)
        cap (budget - signingExecutionHashCost input) current groups remaining)
          (stepSigningLogState input state.2 result) result.1.2.2 result.2) +
      survivingLogPotential (fun current => remainingUnusedCoverageStepCharge
        (secretKey parameter root otsTable ftsTable) cap budget current input groups remaining) state hit failed ≤
      survivingLogPotential (fun current => remainingCoveragePotential (secretKey parameter root otsTable ftsTable)
        cap budget current groups remaining) state hit failed := by
  have hstep := stepWithFailure_expect_surviving_le exception parameter root otsTable ftsTable input frame state hit failed
    (fun current => remainingCoveragePotential (secretKey parameter root otsTable ftsTable)
      cap (budget - signingExecutionHashCost input) current groups remaining) _ le_rfl
  apply (add_le_add hstep le_rfl).trans
  unfold survivingLogPotential
  split_ifs
  · simp only [zero_add, le_refl]
  · exact expected_logTraced_remainingCoverage_add_stepCharge_le (secretKey parameter root otsTable ftsTable)
      cap budget hcap state hsigned hcache input hcost groups remaining hvalid

theorem expected_runWithFailure_remainingTarget_add_unused_le
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (hcap : cap ≤ 2 ^ 127) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (state : CoverLogState) (hit failed : Bool)
    (hbound : (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).IsQueryBoundP (· matches Sum.inr _) budget)
    (hsigned : SigningDigestsCached parameter state.1 root state.2)
    (hcache : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).run state),
      QueryCache.enncard result.2.1 ≤ cap)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | runWithFailure exception parameter root otsTable ftsTable
        (withSigningLog computation state.2) frame state.1 hit failed] *
      survivingLogPotential (fun current => cappedRemainingCachedTargetEnvelope (secretKey parameter root otsTable ftsTable)
        cap 0 current groups remaining) (result.1.2.1.2, result.1.2.1.1.2) result.1.2.2 result.2) +
      expectedRemainingUnusedCoverageCharge exception parameter root otsTable ftsTable cap groups remaining
        computation budget frame state hit failed ≤
      survivingLogPotential (fun current => remainingCoveragePotential (secretKey parameter root otsTable ftsTable)
        cap budget current groups remaining) state hit failed := by
  let key := secretKey parameter root otsTable ftsTable
  induction computation using OracleComp.inductionOn generalizing budget frame state hit failed with
  | pure value =>
      simp only [withSigningLog_pure, runWithFailure_pure, tsum_probOutput_pure_mul,
        expectedRemainingUnusedCoverageCharge_pure, Prod.mk.eta]
      unfold survivingLogPotential
      split_ifs
      · simp only [zero_add, le_refl]
      · exact le_of_eq (remainingTarget_add_terminalReserve key cap budget state groups remaining hvalid)
  | query_bind input next ih =>
      have htail := simulateQ_logTraced_tail_cache_bound key cap input next state hcache
      have hbefore := simulateQ_logTraced_initial_cache_bound key cap (OracleSpec.query input >>= next) state hcache
      have hcost : signingExecutionHashCost input ≤ budget := by
        obtain ⟨result, hr⟩ := simulateQ_logTraced_support_nonempty key (OracleSpec.query input) state
        rw [simulateQ_spec_query] at hr
        exact (expanded_query_bound_signing_execution key input next budget hbound state result hr).1
      have hstep := stepWithFailure_remainingCoverage_add_unused_le exception parameter root otsTable ftsTable cap budget hcap
        input frame state hit failed hsigned hbefore hcost groups remaining hvalid
      rw [withSigningLog_query_bind, runWithFailure_query_bind, tsum_probOutput_bind_mul,
        expectedRemainingUnusedCoverageCharge_query_bind, add_left_comm]
      rw [← ENNReal.tsum_add]
      simp_rw [← mul_add]
      rw [add_comm] at hstep
      apply le_trans ?_ hstep
      apply add_le_add le_rfl
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support (stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed)
      · have hlogged := stepWithFailure_logged_support exception parameter root otsTable ftsTable input frame state.1 state.2 hit failed result hr
        exact mul_le_mul' le_rfl (ih result.1.2.1.1 (budget - signingExecutionHashCost input) result.1.1
          (stepSigningLogState input state.2 result) result.1.2.2 result.2
          (expanded_query_bound_signing_execution key input next budget hbound state _ hlogged).2
          (logTracedMappedAdversaryImpl_signingDigestsCached key input state hsigned _ hlogged) (htail _ hlogged))
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
