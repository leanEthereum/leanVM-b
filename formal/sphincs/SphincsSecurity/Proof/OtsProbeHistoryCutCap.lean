import SphincsSecurity.Proof.OtsProbeErasedHistorySampling

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem runResolvedHistoryPrefix_bind
    (left : OracleComp (LazyRevealProbe.World Coordinate) α)
    (next : α → OracleComp (LazyRevealProbe.World Coordinate) β)
    (context : DeferredContext) (fuel : Nat) (history : List Probe) :
    runResolvedHistoryPrefix (left >>= next) context fuel history =
      runResolvedHistoryPrefix left context fuel history >>= fun entry =>
        match entry with
        | none => pure none
        | some entry => runResolvedHistoryPrefix (next entry.value) entry.context entry.remaining entry.history := by
  induction left using OracleComp.inductionOn generalizing context fuel history with
  | pure value => rfl
  | query_bind input continuation ih =>
      rw [bind_assoc, runResolvedHistoryPrefix_query_bind, runResolvedHistoryPrefix_query_bind,
        historyAdaptiveQueryStep_bind input (fun output => runResolvedHistoryPrefix (continuation output)) context fuel history
          (fun entry => match entry with
            | none => pure none
            | some entry => runResolvedHistoryPrefix (next entry.value) entry.context entry.remaining entry.history) rfl]
      apply congrArg (fun next => historyAdaptiveQueryStep input next context fuel history)
      funext reply context fuel history
      exact ih reply context fuel history

theorem runResolvedHistoryPrefix_map
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (f : α → β)
    (context : DeferredContext) (fuel : Nat) (history : List Probe) :
    runResolvedHistoryPrefix (f <$> computation) context fuel history =
      (Option.map (fun entry => (⟨entry.context, entry.remaining, f entry.value, entry.history⟩ : HistoryResolvedPrefix β))) <$>
        runResolvedHistoryPrefix computation context fuel history := by
  rw [map_eq_bind_pure_comp, runResolvedHistoryPrefix_bind, map_eq_bind_pure_comp]
  apply bind_congr
  intro entry
  cases entry <;> rfl

theorem eraseProbeQueries_bind
    (left : OracleComp (LazyRevealProbe.World Coordinate) α)
    (next : α → OracleComp (LazyRevealProbe.World Coordinate) β) :
    eraseProbeQueries (left >>= next) = eraseProbeQueries left >>= fun value => eraseProbeQueries (next value) := by
  induction left using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input continuation ih =>
      rw [bind_assoc, eraseProbeQueries_query_bind, eraseProbeQueries_query_bind, bind_assoc]
      exact bind_congr ih

theorem eraseProbeQueries_map
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (f : α → β) :
    eraseProbeQueries (f <$> computation) = f <$> eraseProbeQueries computation := by
  rw [map_eq_bind_pure_comp, eraseProbeQueries_bind, map_eq_bind_pure_comp]
  rfl

theorem nativeProbeCutAt_start_test_cap
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (q ordinal : Nat) (hordinal : ordinal < q) :
    (fun cut => decide (IsChainStartCut cut)) <$> nativeProbeCutAt computation ordinal =
      (fun cut => decide (IsChainStartCut cut)) <$> nativeProbeCutAt (capProbeQueries computation q) ordinal := by
  induction computation using OracleComp.inductionOn generalizing q ordinal with
  | pure value => rfl
  | query_bind input next ih =>
      rw [capProbeQueries_query_bind_of_positive input next q (by intro _; omega)]
      simp only [nativeProbeCutAt_query_bind]
      by_cases hprobe : LazyRevealProbe.IsProbe input
      · simp only [if_pos hprobe]
        cases ordinal with
        | zero =>
            cases input <;> try rfl
            case probe coordinate digest => cases coordinate <;> rfl
        | succ ordinal =>
            rw [map_bind, map_bind]
            apply bind_congr
            intro reply
            exact ih reply (q - 1) ordinal (by omega)
      · simp only [if_neg hprobe]
        rw [map_bind, map_bind]
        exact bind_congr fun reply => ih reply q ordinal hordinal

theorem erasedHistoryStartCutCharge_eq_test
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (context : DeferredContext) (ordinal : Nat) :
    erasedHistoryStartCutCharge computation context ordinal =
      Pr[fun value => value = some true | historyPrefixValue <$>
        runResolvedHistoryPrefix (eraseProbeQueries ((fun cut => decide (IsChainStartCut cut)) <$>
          nativeProbeCutAt computation ordinal)) context 0 []] := by
  rw [eraseProbeQueries_map, runResolvedHistoryPrefix_map, Functor.map_map, probEvent_map]
  unfold erasedHistoryStartCutCharge
  apply probEvent_congr' _ rfl
  intro entry _
  cases entry <;> simp [Function.comp_def, historyPrefixValue, HistoryChainStartCutReached]

theorem erasedHistoryStartCutCharge_cap
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (context : DeferredContext)
    (q ordinal : Nat) (hordinal : ordinal < q) :
    erasedHistoryStartCutCharge computation context ordinal =
      erasedHistoryStartCutCharge (capProbeQueries computation q) context ordinal := by
  rw [erasedHistoryStartCutCharge_eq_test, erasedHistoryStartCutCharge_eq_test,
    nativeProbeCutAt_start_test_cap computation q ordinal hordinal]

end SphincsSecurity.Concrete.OtsProbeSimulation
