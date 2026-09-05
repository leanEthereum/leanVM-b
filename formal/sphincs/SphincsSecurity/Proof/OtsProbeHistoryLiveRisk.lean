import SphincsSecurity.Proof.OtsProbeHistoryPrefixRisk

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

theorem valuesConsistent_of_mem_historyPrefix
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (history : List Probe) (result : HistoryResolvedPrefix α)
    (hconsistent : context.ValuesConsistent)
    (hresult : some result ∈ support (runResolvedHistoryPrefix computation context fuel history)) :
    result.context.ValuesConsistent := by
  induction computation using OracleComp.inductionOn generalizing context fuel history with
  | pure value =>
      simp only [runResolvedHistoryPrefix, OracleComp.construct_pure, mem_support_pure_iff, Option.some.injEq] at hresult
      subst result
      exact hconsistent
  | query_bind input next ih =>
      rw [runResolvedHistoryPrefix_query_bind] at hresult
      cases input with
      | uniform n =>
          simp only [historyAdaptiveQueryStep, historyCompletionQueryStep, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, htail⟩ := hresult
          exact ih output context fuel history hconsistent htail
      | hashOutput =>
          simp only [historyAdaptiveQueryStep, historyCompletionQueryStep, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, htail⟩ := hresult
          exact ih output context fuel history hconsistent htail
      | ensure coordinate =>
          exact ih () { context with state := context.state.ensure coordinate } fuel history hconsistent hresult
      | peek coordinate =>
          exact ih (context.state.values coordinate) context fuel history hconsistent hresult
      | publish coordinate =>
          exact ih () { context with state := context.state.publish coordinate } fuel history hconsistent hresult
      | probe coordinate digest =>
          cases fuel with
          | zero => simp [historyAdaptiveQueryStep] at hresult
          | succ remaining =>
              simp only [historyAdaptiveQueryStep] at hresult
              split_ifs at hresult with hrevealed
              · exact ih () context remaining history hconsistent hresult
              · exact ih () { context with state := context.state.addPending coordinate digest }
                  remaining (history ++ [⟨coordinate, digest⟩]) (hconsistent.addPending coordinate digest) hresult
      | reveal coordinate =>
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              simp only [historyAdaptiveQueryStep, historyCompletionQueryStep, OtsSecretIndex.coordinate] at hresult
              cases hknown : context.state.values (.chainStart lay tree leafIdx chainIdx) with
              | some output =>
                  rw [hknown] at hresult
                  dsimp only at hresult
                  split_ifs at hresult with hhit
                  · simp at hresult
                  · exact ih output
                      { context with state := context.state.materialize (.chainStart lay tree leafIdx chainIdx) output }
                      fuel history (valuesConsistent_materialize_chainStart context ⟨lay, tree, leafIdx, chainIdx⟩ output hconsistent) hresult
              | none =>
                  rw [hknown] at hresult
                  dsimp only at hresult
                  rw [mem_support_bind_iff] at hresult
                  obtain ⟨output, _houtput, htail⟩ := hresult
                  split_ifs at htail with hhit
                  · simp at htail
                  · exact ih output
                      { context with state := context.state.materialize (.chainStart lay tree leafIdx chainIdx) output }
                      fuel history (valuesConsistent_materialize_chainStart context ⟨lay, tree, leafIdx, chainIdx⟩ output hconsistent) htail
          | position position =>
              simp only [historyAdaptiveQueryStep, historyCompletionQueryStep, mem_support_bind_iff] at hresult
              obtain ⟨option, hoption, htail⟩ := hresult
              cases option with
              | none => simp at htail
              | some resolved =>
                  exact ih resolved.output
                    { state := context.state.materialize (.position position) resolved.output, values := resolved.values }
                    fuel history
                    (hconsistent.materializeResolvedPosition_of (startTableAvoidingPending context) position resolved hoption) htail

theorem deferredCompletable_history_clean_iff
    (context : DeferredContext) (history : List Probe) (base : OtsSecretIndex → HashOutput)
    (hconsistent : context.ValuesConsistent) (hcovered : PendingCoveredBy history context)
    (hcard : context.state.pending.card < Fintype.card Digest)
    (hclean : ¬ChainStartHistoryHit context history base) :
    DeferredCompletable (completedStartTable context.state base) context ↔
      context.Valid ∧ ¬PrivateStructuralHit context := by
  constructor
  · intro hcomplete
    exact ⟨valid_of_resolvedCore_completable _ context hconsistent
      (startTableAgrees_completedStartTable context.state base) hcomplete,
      not_privateStructuralHit_of_deferredCompletable hcomplete⟩
  · rintro ⟨hvalid, hprivate⟩
    exact deferredCompletable_of_valid_of_no_boundary_hit _ context hvalid
      (startTableAgrees_completedStartTable context.state base) hprivate
      (no_missingChainStartHit_of_history_clean context history base hcovered hclean) hcard

noncomputable def retainCompletableResult : Option (ResolvedRunResult α) → Option (ResolvedRunResult α)
  | none => none
  | some result => if DeferredCompletable result.table result.context then some result else none

theorem expected_live_historyCompletion_eq_context_guard
    (entry : HistoryResolvedPrefix α) (cost : Option (ResolvedRunResult α) → ℝ≥0∞)
    (hzero : cost none = 0) (hconsistent : entry.context.ValuesConsistent)
    (hcovered : PendingCoveredBy entry.history entry.context)
    (hcard : entry.context.state.pending.card < Fintype.card Digest) :
    (∑' result, Pr[= result | completeHistoryResolvedPrefix (some entry)] * cost (retainCompletableResult result)) =
      if entry.context.Valid ∧ ¬PrivateStructuralHit entry.context then
        ∑' result, Pr[= result | completeHistoryResolvedPrefix (some entry)] * cost result
      else 0 := by
  by_cases hgood : entry.context.Valid ∧ ¬PrivateStructuralHit entry.context
  · simp only [if_pos hgood, completeHistoryResolvedPrefix, completeResolvedHistory, tsum_probOutput_bind_mul]
    apply tsum_congr
    intro base
    by_cases hhit : ChainStartHistoryHit entry.context entry.history base
    · simp [hhit, retainCompletableResult, hzero]
    · have hcomplete := (deferredCompletable_history_clean_iff entry.context entry.history base hconsistent hcovered hcard hhit).mpr hgood
      simp [hhit, retainCompletableResult, hcomplete]
  · simp only [if_neg hgood, completeHistoryResolvedPrefix, completeResolvedHistory, tsum_probOutput_bind_mul]
    apply ENNReal.tsum_eq_zero.mpr
    intro base
    by_cases hhit : ChainStartHistoryHit entry.context entry.history base
    · simp [hhit, retainCompletableResult, hzero]
    · have hcomplete : ¬DeferredCompletable (completedStartTable entry.context.state base) entry.context :=
        fun h => hgood ((deferredCompletable_history_clean_iff entry.context entry.history base hconsistent hcovered hcard hhit).mp h)
      simp [hhit, retainCompletableResult, hcomplete, hzero]

theorem expected_live_historyCompletion_unresolvedStart_le
    (entry : HistoryResolvedPrefix α) (candidate : DeferredContext → α → Option Probe)
    (hconsistent : entry.context.ValuesConsistent) (hcovered : PendingCoveredBy entry.history entry.context)
    (hlength : entry.history.length ≤ 2 ^ 126) :
    (∑' result, Pr[= result | completeHistoryResolvedPrefix (some entry)] * historyUnresolvedStartAllowance candidate (retainCompletableResult result)) ≤
      (∑' result, Pr[= result | completeHistoryResolvedPrefix (some entry)] * historyUnresolvedStartCharge candidate (retainCompletableResult result)) *
        ((4 / 3 : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) := by
  have hspace : 2 ^ 126 < Fintype.card Digest := by norm_num [digestBits]
  have hcard := (hcovered.card_le.trans hlength).trans_lt hspace
  rw [expected_live_historyCompletion_eq_context_guard entry (historyUnresolvedStartAllowance candidate) rfl hconsistent hcovered hcard,
    expected_live_historyCompletion_eq_context_guard entry (historyUnresolvedStartCharge candidate) rfl hconsistent hcovered hcard]
  split_ifs
  · exact expected_completeHistoryResolvedPrefix_unresolvedStart_le entry candidate hlength
  · simp

theorem expected_live_historyAdaptive_unresolvedStart_le
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel bound : Nat) (history : List Probe)
    (candidate : DeferredContext → α → Option Probe)
    (hconsistent : context.ValuesConsistent) (hcovered : PendingCoveredBy history context)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe bound)
    (hbudget : history.length + bound ≤ 2 ^ 126) :
    (∑' result, Pr[= result | runResolvedHistoryAdaptive computation context fuel history] * historyUnresolvedStartAllowance candidate (retainCompletableResult result)) ≤
      (∑' result, Pr[= result | runResolvedHistoryAdaptive computation context fuel history] * historyUnresolvedStartCharge candidate (retainCompletableResult result)) *
        ((4 / 3 : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) := by
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
        have hlocal := expected_live_historyCompletion_unresolvedStart_le entry candidate hvalues hinvariant.1 (hinvariant.2.trans hbudget)
        simpa only [mul_assoc] using mul_le_mul' le_rfl hlocal
  · simp [probOutput_eq_zero_of_not_mem_support hsupport]

noncomputable def sampledHistoryFilteredRun
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (history : List Probe) : ProbComp (Option (ResolvedRunResult α)) := do
  let base ← sampleOtsHashTable
  if ChainStartHistoryHit context history base then pure none
  else runResolvedFromTable context fuel (completedStartTable context.state base) computation

theorem evalDist_live_sampledHistoryFilteredRun_eq_adaptive
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel bound : Nat) (history : List Probe)
    (hconsistent : context.ValuesConsistent) (hcovered : PendingCoveredBy history context)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe bound)
    (hbudget : history.length + bound ≤ 2 ^ 126) :
    evalDist (sampledHistoryFilteredRun computation context fuel history >>= fun result => pure (retainCompletableResult result)) =
      evalDist (runResolvedHistoryAdaptive computation context fuel history >>= fun result => pure (retainCompletableResult result)) := by
  have heq := evalDist_history_filtered_runResolved_eq_prefix_observe computation context fuel bound history
    (fun result => pure (retainCompletableResult result)) (by
      intro result _hvalues _hstarts hdoomed
      simp only [retainCompletableResult, if_neg hdoomed]) hconsistent hcovered hbound hbudget
  simpa only [sampledHistoryFilteredRun, runResolvedHistoryAdaptive_eq_prefix_complete] using heq

theorem expected_live_sampledHistoryFilteredRun_eq_adaptive
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel bound : Nat) (history : List Probe)
    (cost : Option (ResolvedRunResult α) → ℝ≥0∞)
    (hconsistent : context.ValuesConsistent) (hcovered : PendingCoveredBy history context)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe bound)
    (hbudget : history.length + bound ≤ 2 ^ 126) :
    (∑' result, Pr[= result | sampledHistoryFilteredRun computation context fuel history] * cost (retainCompletableResult result)) =
      ∑' result, Pr[= result | runResolvedHistoryAdaptive computation context fuel history] * cost (retainCompletableResult result) := by
  have hdist := evalDist_live_sampledHistoryFilteredRun_eq_adaptive computation context fuel bound history
    hconsistent hcovered hbound hbudget
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

theorem expected_live_sampledHistoryFilteredRun_unresolvedStart_le
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel bound : Nat) (history : List Probe)
    (candidate : DeferredContext → α → Option Probe)
    (hconsistent : context.ValuesConsistent) (hcovered : PendingCoveredBy history context)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe bound)
    (hbudget : history.length + bound ≤ 2 ^ 126) :
    (∑' result, Pr[= result | sampledHistoryFilteredRun computation context fuel history] *
      historyUnresolvedStartAllowance candidate (retainCompletableResult result)) ≤
    (∑' result, Pr[= result | sampledHistoryFilteredRun computation context fuel history] *
      historyUnresolvedStartCharge candidate (retainCompletableResult result)) *
      ((4 / 3 : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) := by
  rw [expected_live_sampledHistoryFilteredRun_eq_adaptive computation context fuel bound history
      (historyUnresolvedStartAllowance candidate) hconsistent hcovered hbound hbudget,
    expected_live_sampledHistoryFilteredRun_eq_adaptive computation context fuel bound history
      (historyUnresolvedStartCharge candidate) hconsistent hcovered hbound hbudget]
  exact expected_live_historyAdaptive_unresolvedStart_le computation context fuel bound history candidate
    hconsistent hcovered hbound hbudget

theorem expected_live_sampled_runResolved_empty_unresolvedStart_le
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (fuel bound : Nat)
    (candidate : DeferredContext → α → Option Probe)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe bound) (hbudget : bound ≤ 2 ^ 126) :
    (∑' result, Pr[= result | do
        let table ← sampleOtsHashTable
        runResolvedFromTable { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
          fuel table computation] * historyUnresolvedStartAllowance candidate (retainCompletableResult result)) ≤
    (∑' result, Pr[= result | do
        let table ← sampleOtsHashTable
        runResolvedFromTable { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
          fuel table computation] * historyUnresolvedStartCharge candidate (retainCompletableResult result)) *
      ((4 / 3 : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) := by
  have hnative := expected_live_sampledHistoryFilteredRun_unresolvedStart_le computation
    { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
    fuel bound [] candidate DeferredContext.valid_empty.valuesConsistent pendingCoveredBy_empty hbound
    (by simpa only [List.length_nil, Nat.zero_add] using hbudget)
  have htable : ∀ base, completedStartTable LazyRevealProbe.State.empty base = base := by
    intro base
    funext index
    rfl
  simpa only [sampledHistoryFilteredRun, ChainStartHistoryHit, List.not_mem_nil, false_and, exists_false, ↓reduceIte,
    htable] using hnative

def UnresolvedStartProbeHit (table : OtsSecretIndex → HashOutput) (context : DeferredContext) : Option Probe → Prop
  | some ⟨.chainStart lay tree leafIdx chainIdx, digest⟩ =>
      context.state.values (.chainStart lay tree leafIdx chainIdx) = none ∧
      ¬(.chainStart lay tree leafIdx chainIdx ∈ context.state.revealed ∨
        (.chainStart lay tree leafIdx chainIdx, digest) ∈ context.state.pending) ∧
      truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩) = digest
  | _ => False

theorem unresolvedStartCandidateAllowance_eq_indicator
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext) (candidate : Option Probe) :
    unresolvedStartCandidateAllowance table context candidate = if UnresolvedStartProbeHit table context candidate then 1 else 0 := by
  cases candidate with
  | none => simp [unresolvedStartCandidateAllowance, UnresolvedStartProbeHit]
  | some candidate =>
      rcases candidate with ⟨coordinate, digest⟩
      cases coordinate with
      | position position => simp [unresolvedStartCandidateAllowance, UnresolvedStartProbeHit]
      | chainStart lay tree leafIdx chainIdx =>
          by_cases hmissing : context.state.values (.chainStart lay tree leafIdx chainIdx) = none
          · by_cases hseen : .chainStart lay tree leafIdx chainIdx ∈ context.state.revealed ∨
                (.chainStart lay tree leafIdx chainIdx, digest) ∈ context.state.pending
            · simp [unresolvedStartCandidateAllowance, UnresolvedStartProbeHit, candidateFailureAllowance, hmissing, hseen]
            · simp [unresolvedStartCandidateAllowance, UnresolvedStartProbeHit, candidateFailureAllowance,
                resolvedCompletionValue, hmissing, hseen]
          · simp [unresolvedStartCandidateAllowance, UnresolvedStartProbeHit, hmissing]

def LiveUnresolvedStartHit (candidate : DeferredContext → α → Option Probe) : Option (ResolvedRunResult α) → Prop
  | none => False
  | some result => DeferredCompletable result.table result.context ∧
      UnresolvedStartProbeHit result.table result.context (candidate result.context result.value)

theorem historyUnresolvedStartAllowance_live_eq_indicator
    (candidate : DeferredContext → α → Option Probe) (result : Option (ResolvedRunResult α)) :
    historyUnresolvedStartAllowance candidate (retainCompletableResult result) =
      if LiveUnresolvedStartHit candidate result then 1 else 0 := by
  cases result with
  | none => simp [retainCompletableResult, historyUnresolvedStartAllowance, LiveUnresolvedStartHit]
  | some result =>
      by_cases hcomplete : DeferredCompletable result.table result.context
      · simp [retainCompletableResult, historyUnresolvedStartAllowance, LiveUnresolvedStartHit, hcomplete,
          unresolvedStartCandidateAllowance_eq_indicator]
      · simp [retainCompletableResult, historyUnresolvedStartAllowance, LiveUnresolvedStartHit, hcomplete]

theorem probEvent_liveUnresolvedStartHit_eq_expected
    (run : ProbComp (Option (ResolvedRunResult α))) (candidate : DeferredContext → α → Option Probe) :
    Pr[LiveUnresolvedStartHit candidate | run] =
      ∑' result, Pr[= result | run] * historyUnresolvedStartAllowance candidate (retainCompletableResult result) := by
  rw [probEvent_eq_tsum_ite]
  apply tsum_congr
  intro result
  rw [historyUnresolvedStartAllowance_live_eq_indicator]
  split_ifs <;> simp

theorem probEvent_live_unresolvedStart_hit_le_native_charge
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel bound : Nat) (history : List Probe)
    (candidate : DeferredContext → α → Option Probe)
    (hconsistent : context.ValuesConsistent) (hcovered : PendingCoveredBy history context)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe bound)
    (hbudget : history.length + bound ≤ 2 ^ 126) :
    Pr[LiveUnresolvedStartHit candidate | sampledHistoryFilteredRun computation context fuel history] ≤
      (∑' result, Pr[= result | sampledHistoryFilteredRun computation context fuel history] *
        historyUnresolvedStartCharge candidate (retainCompletableResult result)) *
        ((4 / 3 : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) := by
  rw [probEvent_liveUnresolvedStartHit_eq_expected]
  exact expected_live_sampledHistoryFilteredRun_unresolvedStart_le computation context fuel bound history candidate
    hconsistent hcovered hbound hbudget

end SphincsSecurity.Concrete.OtsProbeSimulation
