import SphincsSecurity.Proof.JointCollisionCoverageStep

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
set_option backward.isDefEq.respectTransparency false

noncomputable def expectedJointCollisionCoverageCharge
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α) : Nat → Option Frame → CoverLogState → Bool → Bool → ENNReal :=
  OracleComp.construct (fun _ _ _ _ _ _ => 0)
    (fun input _ next budget frame state hit failed =>
      jointCollisionCoverageBudgetStepCharge parameter root otsTable ftsTable cap budget input frame state hit failed +
        ∑' result, Pr[= result | stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
          input frame state.1 hit failed] * next result.1.2.1.1 (budget - signingExecutionHashCost input) result.1.1
            (stepSigningLogState input state.2 result) result.1.2.2 result.2) computation

noncomputable def expectedJointCollisionCoverageCredit
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α) : Nat → Option Frame → CoverLogState → Bool → Bool → ENNReal :=
  OracleComp.construct (fun _ budget _ state hit failed =>
    jointCollisionCoverageTerminalCredit (secretKey parameter root otsTable ftsTable) cap budget state hit failed)
    (fun input _ next budget frame state hit failed =>
      jointCollisionCoverageBudgetStepCredit (secretKey parameter root otsTable ftsTable) cap budget input state hit failed +
        ∑' result, Pr[= result | stepWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
          input frame state.1 hit failed] * next result.1.2.1.1 (budget - signingExecutionHashCost input) result.1.1
            (stepSigningLogState input state.2 result) result.1.2.2 result.2) computation

private theorem expected_add_credit_le (computation : SPMF α) (value credit risk after : α → ENNReal)
    (currentCredit before currentRisk : ENNReal)
    (htail : ∀ result ∈ support computation, value result + credit result ≤ after result + risk result)
    (hstep : (∑' result, Pr[= result | computation] * after result) + currentCredit ≤ before + currentRisk) :
    (∑' result, Pr[= result | computation] * value result) +
        (currentCredit + ∑' result, Pr[= result | computation] * credit result) ≤
      before + (currentRisk + ∑' result, Pr[= result | computation] * risk result) := by
  calc
    _ = (∑' result, Pr[= result | computation] * (value result + credit result)) + currentCredit := by
      simp only [mul_add, ENNReal.tsum_add]
      ring
    _ ≤ (∑' result, Pr[= result | computation] * (after result + risk result)) + currentCredit := by
      apply add_le_add _ le_rfl
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support computation
      · exact mul_le_mul' le_rfl (htail result hr)
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ = ((∑' result, Pr[= result | computation] * after result) + currentCredit) +
        ∑' result, Pr[= result | computation] * risk result := by
      simp only [mul_add, ENNReal.tsum_add]
      ring
    _ ≤ _ := (add_le_add hstep le_rfl).trans_eq (add_assoc _ _ _)

theorem expected_runWithFailure_jointCollisionCoverage_add_credit_le
    (parameter : PublicParameter) (root : Digest) (otsTable : OtsSecretIndex → HashOutput) (ftsTable : Coordinate → Digest)
    (cap budget : Nat) (hcap : cap ≤ 2 ^ 127) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (frame : Option Frame) (state : CoverLogState) (hit failed : Bool)
    (hfinite : Finite state.1)
    (hvalid : ∀ live, frame = some live → live.Valid parameter otsTable ftsTable state.1)
    (hfuel : ∀ live, frame = some live → budget ≤ live.ftsFuel)
    (hcomputed : ∀ live, frame = some live → OtsProbeSimulation.DeferredComputationsClosed live.context)
    (hstate : frame.isNone = (hit || failed))
    (hbudget : (simulateQ (expandedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).IsQueryBoundP
      (· matches Sum.inr _) budget)
    (hsigned : SigningDigestsCached parameter state.1 root state.2)
    (hcache : ∀ result ∈ support ((simulateQ (logTracedMappedAdversaryImpl (secretKey parameter root otsTable ftsTable)) computation).run state),
      QueryCache.enncard result.2.1 ≤ cap) :
    (∑' result, Pr[= result | runWithFailure (parentException parameter otsTable ftsTable) parameter root otsTable ftsTable
      (withSigningLog computation state.2) frame state.1 hit failed] *
        jointCollisionCoveragePotential (secretKey parameter root otsTable ftsTable) cap 0
          (result.1.2.1.2, result.1.2.1.1.2) result.1.2.2 result.2) +
      expectedJointCollisionCoverageCredit parameter root otsTable ftsTable cap computation budget frame state hit failed ≤
        jointCollisionCoverageBudgetPotential (secretKey parameter root otsTable ftsTable) cap budget state hit failed +
          expectedJointCollisionCoverageCharge parameter root otsTable ftsTable cap computation budget frame state hit failed := by
  let key := secretKey parameter root otsTable ftsTable
  let exception := parentException parameter otsTable ftsTable
  induction computation using OracleComp.inductionOn generalizing budget frame state hit failed with
  | pure value =>
      simp only [withSigningLog_pure, runWithFailure_pure, tsum_probOutput_pure_mul, Prod.mk.eta,
        expectedJointCollisionCoverageCredit, expectedJointCollisionCoverageCharge, construct_pure, add_zero]
      exact (jointCollisionCoverage_add_terminalCredit key cap budget state hit failed).le
  | query_bind input next ih =>
      have htail := simulateQ_logTraced_tail_cache_bound key cap input next state hcache
      have hbefore := simulateQ_logTraced_initial_cache_bound key cap (OracleSpec.query input >>= next) state hcache
      have hcost : signingExecutionHashCost input ≤ budget := by
        obtain ⟨result, hr⟩ := simulateQ_logTraced_support_nonempty key (OracleSpec.query input) state
        rw [simulateQ_spec_query] at hr
        exact (expanded_query_bound_signing_execution key input next budget hbudget state result hr).1
      have hhash : ∀ live, frame = some live → OtsProbeSimulation.IsOuterHash input → 0 < live.ftsFuel := by
        intro live hlive hi
        have hpositive : 0 < signingExecutionHashCost input := by
          cases input with
          | inl world =>
              cases world with
              | inl n => simp [OtsProbeSimulation.IsOuterHash] at hi
              | inr input => exact Nat.zero_lt_one
          | inr message => simp [OtsProbeSimulation.IsOuterHash] at hi
        exact (hpositive.trans_le hcost).trans_le (hfuel live hlive)
      have hstep := expected_jointCollisionCoverageBudget_step_add_credit_le parameter root otsTable ftsTable cap budget hcap
        input frame state hit failed hfinite hvalid hhash hcomputed hstate hsigned hbefore hcost
      rw [withSigningLog_query_bind, runWithFailure_query_bind, tsum_probOutput_bind_mul]
      change (∑' result, Pr[= result | stepWithFailure exception parameter root otsTable ftsTable input frame state.1 hit failed] * _) +
        (jointCollisionCoverageBudgetStepCredit key cap budget input state hit failed + _) ≤
          jointCollisionCoverageBudgetPotential key cap budget state hit failed +
            (jointCollisionCoverageBudgetStepCharge parameter root otsTable ftsTable cap budget input frame state hit failed + _)
      apply expected_add_credit_le _ _ _ _ _ _ _ _ _ hstep
      intro result hr
      have hp := stepWithFailure_support_project exception parameter root otsTable ftsTable input frame state.1 hit failed result hr
      have hv := stepWithFailure_invariant exception parameter root otsTable ftsTable input frame state.1 hit failed
        hvalid hhash hstate result hr
      have hlogged := stepWithFailure_logged_support exception parameter root otsTable ftsTable input frame state.1 state.2 hit failed result hr
      have ha := stepWithFailure_original_support exception parameter root otsTable ftsTable input frame state.1 hit failed result hr
      have hfin := finite_cache_of_mem_support _ state.1 result.1.2.1.1 result.1.2.1.2
        (runExceptionMonitor_support_project exception _ state.1 hit ha) hfinite
      have hnext : ∀ middle, result.1.1 = some middle →
          budget - signingExecutionHashCost input ≤ middle.ftsFuel ∧
            OtsProbeSimulation.DeferredComputationsClosed middle.context := by
        intro middle hm
        cases frame with
        | none =>
            rw [step, support_map] at hp
            obtain ⟨original, _, heq⟩ := hp
            have hn : result.1.1 = none := (congrArg Prod.fst heq).symm
            simp [hn] at hm
        | some frame =>
            exact ⟨step_ftsFuel_ge_execution_budget exception parameter root otsTable ftsTable input frame state.1 hit
                budget (hfuel frame rfl) result.1 hp middle hm,
              step_computed exception parameter root otsTable ftsTable input frame state.1 hit
                (hcomputed frame rfl) result.1 hp middle hm⟩
      exact ih result.1.2.1.1 (budget - signingExecutionHashCost input) result.1.1
        (stepSigningLogState input state.2 result) result.1.2.2 result.2 hfin hv.1
        (fun middle hm => (hnext middle hm).1) (fun middle hm => (hnext middle hm).2) hv.2
        (expanded_query_bound_signing_execution key input next budget hbudget state _ hlogged).2
        (logTracedMappedAdversaryImpl_signingDigestsCached key input state hsigned _ hlogged) (htail _ hlogged)

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
