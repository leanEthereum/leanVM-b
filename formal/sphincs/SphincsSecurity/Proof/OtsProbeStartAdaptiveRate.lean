import SphincsSecurity.Proof.OtsProbeStartHistoryRate
import SphincsSecurity.Proof.OtsProbeHistoryLiveRisk

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

theorem expected_completeHistoryResolvedPrefix_unresolvedStart_le_rate
    (entry : HistoryResolvedPrefix α) (candidate : DeferredContext → α → Option Probe)
    (budget : Nat) (hlength : entry.history.length ≤ budget) (hspace : budget < Fintype.card Digest) :
    (∑' result, Pr[= result | completeHistoryResolvedPrefix (some entry)] * historyUnresolvedStartAllowance candidate result) ≤
      (∑' result, Pr[= result | completeHistoryResolvedPrefix (some entry)] * historyUnresolvedStartCharge candidate result) *
        privateHistoryGuessRate budget := by
  unfold historyUnresolvedStartAllowance historyUnresolvedStartCharge
  rw [expected_completeHistoryResolvedPrefix_function entry (fun table context value =>
        unresolvedStartCandidateAllowance table context (candidate context value)),
      expected_completeHistoryResolvedPrefix_view_cost entry (fun context value =>
        unresolvedStartCandidateCharge context (candidate context value))]
  cases hcandidate : candidate entry.context entry.value with
  | none => simp [unresolvedStartCandidateAllowance, unresolvedStartCandidateCharge]
  | some probe =>
      rcases probe with ⟨coordinate, digest⟩
      cases coordinate with
      | position position => simp [unresolvedStartCandidateAllowance, unresolvedStartCandidateCharge]
      | chainStart lay tree leafIdx chainIdx =>
          by_cases hmissing : entry.context.state.values (.chainStart lay tree leafIdx chainIdx) = none
          · simp only [unresolvedStartCandidateAllowance, unresolvedStartCandidateCharge, if_pos hmissing]
            have hlocal := expected_history_guarded_chainStart_allowance_le_rate entry.context entry.history budget hlength hspace
              ⟨lay, tree, leafIdx, chainIdx⟩ digest hmissing
            simpa only [OtsSecretIndex.coordinate, ite_not, mul_assoc, mul_comm, mul_left_comm] using hlocal
          · simp [unresolvedStartCandidateAllowance, unresolvedStartCandidateCharge, hmissing]

theorem expected_live_historyCompletion_unresolvedStart_le_rate
    (entry : HistoryResolvedPrefix α) (candidate : DeferredContext → α → Option Probe)
    (hconsistent : entry.context.ValuesConsistent) (hcovered : PendingCoveredBy entry.history entry.context)
    (budget : Nat) (hlength : entry.history.length ≤ budget) (hspace : budget < Fintype.card Digest) :
    (∑' result, Pr[= result | completeHistoryResolvedPrefix (some entry)] * historyUnresolvedStartAllowance candidate (retainCompletableResult result)) ≤
      (∑' result, Pr[= result | completeHistoryResolvedPrefix (some entry)] * historyUnresolvedStartCharge candidate (retainCompletableResult result)) *
        privateHistoryGuessRate budget := by
  have hcard := (hcovered.card_le.trans hlength).trans_lt hspace
  rw [expected_live_historyCompletion_eq_context_guard entry (historyUnresolvedStartAllowance candidate) rfl hconsistent hcovered hcard,
    expected_live_historyCompletion_eq_context_guard entry (historyUnresolvedStartCharge candidate) rfl hconsistent hcovered hcard]
  split_ifs
  · exact expected_completeHistoryResolvedPrefix_unresolvedStart_le_rate entry candidate budget hlength hspace
  · simp

theorem expected_live_historyAdaptive_unresolvedStart_le_rate
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel bound budget : Nat) (history : List Probe)
    (candidate : DeferredContext → α → Option Probe)
    (hconsistent : context.ValuesConsistent) (hcovered : PendingCoveredBy history context)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe bound)
    (hbudget : history.length + bound ≤ budget) (hspace : budget < Fintype.card Digest) :
    (∑' result, Pr[= result | runResolvedHistoryAdaptive computation context fuel history] * historyUnresolvedStartAllowance candidate (retainCompletableResult result)) ≤
      (∑' result, Pr[= result | runResolvedHistoryAdaptive computation context fuel history] * historyUnresolvedStartCharge candidate (retainCompletableResult result)) *
        privateHistoryGuessRate budget := by
  simp only [runResolvedHistoryAdaptive_eq_prefix_complete, tsum_probOutput_bind_mul]
  rw [← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro option
  by_cases hsupport : option ∈ support (runResolvedHistoryPrefix computation context fuel history)
  · cases option with
    | none => simp [completeHistoryResolvedPrefix, retainCompletableResult, historyUnresolvedStartAllowance, historyUnresolvedStartCharge]
    | some entry =>
        have hinvariant := historyPrefix_invariant_of_mem computation context fuel bound history entry hcovered hbound hsupport
        have hvalues := valuesConsistent_of_mem_historyPrefix computation context fuel history entry hconsistent hsupport
        have hlocal := expected_live_historyCompletion_unresolvedStart_le_rate entry candidate hvalues hinvariant.1 budget (hinvariant.2.trans hbudget) hspace
        simpa only [mul_assoc] using mul_le_mul' le_rfl hlocal
  · simp [probOutput_eq_zero_of_not_mem_support hsupport]

theorem evalDist_live_sampledHistoryFilteredRun_eq_adaptive_rate
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel bound budget : Nat) (history : List Probe)
    (hconsistent : context.ValuesConsistent) (hcovered : PendingCoveredBy history context)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe bound)
    (hbudget : history.length + bound ≤ budget) (hspace : budget < Fintype.card Digest) :
    evalDist (sampledHistoryFilteredRun computation context fuel history >>= fun result => pure (retainCompletableResult result)) =
      evalDist (runResolvedHistoryAdaptive computation context fuel history >>= fun result => pure (retainCompletableResult result)) := by
  have heq := evalDist_history_filtered_runResolved_eq_adaptive_observe computation context fuel bound history
    (fun result => pure (retainCompletableResult result)) (by
      intro result _hvalues _hstarts hdoomed
      simp only [retainCompletableResult, if_neg hdoomed]) hconsistent hcovered (((Nat.add_le_add_right hcovered.card_le bound).trans hbudget).trans_lt hspace) hbound
  simpa only [sampledHistoryFilteredRun] using heq

theorem expected_live_sampledHistoryFilteredRun_eq_adaptive_rate
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel bound budget : Nat) (history : List Probe)
    (cost : Option (ResolvedRunResult α) → ℝ≥0∞)
    (hconsistent : context.ValuesConsistent) (hcovered : PendingCoveredBy history context)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe bound)
    (hbudget : history.length + bound ≤ budget) (hspace : budget < Fintype.card Digest) :
    (∑' result, Pr[= result | sampledHistoryFilteredRun computation context fuel history] * cost (retainCompletableResult result)) =
      ∑' result, Pr[= result | runResolvedHistoryAdaptive computation context fuel history] * cost (retainCompletableResult result) := by
  have hdist := evalDist_live_sampledHistoryFilteredRun_eq_adaptive_rate computation context fuel bound budget history
    hconsistent hcovered hbound hbudget hspace
  calc
    _ = ∑' result, Pr[= result | sampledHistoryFilteredRun computation context fuel history >>=
        fun result => pure (retainCompletableResult result)] * cost result := by
      simp only [tsum_probOutput_bind_mul, tsum_probOutput_pure_mul]
    _ = ∑' result, Pr[= result | runResolvedHistoryAdaptive computation context fuel history >>=
        fun result => pure (retainCompletableResult result)] * cost result := by
      apply tsum_congr
      intro result
      simp only [probOutput_def, hdist]
    _ = _ := by simp only [tsum_probOutput_bind_mul, tsum_probOutput_pure_mul]

theorem expected_live_sampledHistoryFilteredRun_unresolvedStart_le_rate
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel bound budget : Nat) (history : List Probe)
    (candidate : DeferredContext → α → Option Probe)
    (hconsistent : context.ValuesConsistent) (hcovered : PendingCoveredBy history context)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe bound)
    (hbudget : history.length + bound ≤ budget) (hspace : budget < Fintype.card Digest) :
    (∑' result, Pr[= result | sampledHistoryFilteredRun computation context fuel history] *
      historyUnresolvedStartAllowance candidate (retainCompletableResult result)) ≤
    (∑' result, Pr[= result | sampledHistoryFilteredRun computation context fuel history] *
      historyUnresolvedStartCharge candidate (retainCompletableResult result)) *
      privateHistoryGuessRate budget := by
  rw [expected_live_sampledHistoryFilteredRun_eq_adaptive_rate computation context fuel bound budget history
      (historyUnresolvedStartAllowance candidate) hconsistent hcovered hbound hbudget hspace,
    expected_live_sampledHistoryFilteredRun_eq_adaptive_rate computation context fuel bound budget history
      (historyUnresolvedStartCharge candidate) hconsistent hcovered hbound hbudget hspace]
  exact expected_live_historyAdaptive_unresolvedStart_le_rate computation context fuel bound budget history candidate
    hconsistent hcovered hbound hbudget hspace

theorem probEvent_live_unresolvedStart_hit_le_native_charge_rate
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel bound budget : Nat) (history : List Probe)
    (candidate : DeferredContext → α → Option Probe)
    (hconsistent : context.ValuesConsistent) (hcovered : PendingCoveredBy history context)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe bound)
    (hbudget : history.length + bound ≤ budget) (hspace : budget < Fintype.card Digest) :
    Pr[LiveUnresolvedStartHit candidate | sampledHistoryFilteredRun computation context fuel history] ≤
      (∑' result, Pr[= result | sampledHistoryFilteredRun computation context fuel history] *
        historyUnresolvedStartCharge candidate (retainCompletableResult result)) *
        privateHistoryGuessRate budget := by
  rw [probEvent_liveUnresolvedStartHit_eq_expected]
  exact expected_live_sampledHistoryFilteredRun_unresolvedStart_le_rate computation context fuel bound budget history candidate
    hconsistent hcovered hbound hbudget hspace

end SphincsSecurity.Concrete.OtsProbeSimulation
