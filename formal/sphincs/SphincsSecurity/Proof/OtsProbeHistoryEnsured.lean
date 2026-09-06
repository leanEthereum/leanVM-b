import SphincsSecurity.Proof.OtsProbeErasedHistoryCostBound
import SphincsSecurity.Proof.OtsProbeEnsuredExecution

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def HistoryResolvedPrefix.enlargeEnsured (entry : HistoryResolvedPrefix α) (extra : Finset Coordinate) : HistoryResolvedPrefix α :=
  { entry with context := entry.context.enlargeEnsured extra }

theorem runResolvedHistoryPrefix_enlargeEnsured
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (history : List Probe) (extra : Finset Coordinate) :
    runResolvedHistoryPrefix computation (context.enlargeEnsured extra) fuel history =
      Option.map (fun entry => entry.enlargeEnsured extra) <$> runResolvedHistoryPrefix computation context fuel history := by
  induction computation using OracleComp.inductionOn generalizing context fuel history with
  | pure value => simp [runResolvedHistoryPrefix, HistoryResolvedPrefix.enlargeEnsured]
  | query_bind input next ih =>
      rw [runResolvedHistoryPrefix_query_bind, runResolvedHistoryPrefix_query_bind]
      cases input with
      | uniform n =>
          simp only [historyAdaptiveQueryStep, historyCompletionQueryStep, map_bind]
          exact bind_congr fun output => ih output context fuel history
      | hashOutput =>
          simp only [historyAdaptiveQueryStep, historyCompletionQueryStep, map_bind]
          exact bind_congr fun output => ih output context fuel history
      | ensure coordinate =>
          simpa only [historyAdaptiveQueryStep, historyCompletionQueryStep, DeferredContext.enlargeEnsured,
            LazyRevealProbe.State.ensure, Finset.insert_union] using
            ih () { context with state := context.state.ensure coordinate } fuel history
      | publish coordinate =>
          exact ih () { context with state := context.state.publish coordinate } fuel history
      | peek coordinate => exact ih (context.state.values coordinate) context fuel history
      | probe coordinate candidate =>
          cases fuel with
          | zero => simp [historyAdaptiveQueryStep]
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · simpa only [historyAdaptiveQueryStep, DeferredContext.enlargeEnsured, hrevealed, if_true] using
                  ih () context remaining history
              · simpa only [historyAdaptiveQueryStep, DeferredContext.enlargeEnsured, hrevealed, if_false,
                  LazyRevealProbe.State.addPending] using
                  ih () { context with state := context.state.addPending coordinate candidate } remaining
                    (history ++ [⟨coordinate, candidate⟩])
      | reveal coordinate =>
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              simp only [historyAdaptiveQueryStep, historyCompletionQueryStep, DeferredContext.enlargeEnsured,
                OtsSecretIndex.coordinate]
              cases hknown : context.state.values (.chainStart lay tree leafIdx chainIdx) with
              | some output =>
                  by_cases hhit : context.state.hitAt (.chainStart lay tree leafIdx chainIdx) output
                  · simp only [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt] at hhit ⊢
                    simp [hhit]
                  · simp only [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt] at hhit ⊢
                    simp only [hhit, if_false]
                    simpa only [DeferredContext.enlargeEnsured, LazyRevealProbe.State.materialize, LazyRevealProbe.State.pendingAway,
                      Finset.insert_union] using
                      ih output { context with state := context.state.materialize (.chainStart lay tree leafIdx chainIdx) output } fuel history
              | none =>
                  simp only [map_bind]
                  apply bind_congr
                  intro output
                  by_cases hhit : ChainStartHistoryOutputHit history ⟨lay, tree, leafIdx, chainIdx⟩ output
                  · simp [hhit]
                  · simpa only [hhit, if_false, DeferredContext.enlargeEnsured, LazyRevealProbe.State.materialize, LazyRevealProbe.State.pendingAway,
                      Finset.insert_union] using
                      ih output { context with state := context.state.materialize (.chainStart lay tree leafIdx chainIdx) output } fuel history
          | position position =>
              simp only [historyAdaptiveQueryStep, historyCompletionQueryStep]
              rw [show startTableAvoidingPending (context.enlargeEnsured extra) = startTableAvoidingPending context from rfl,
                resolveDeferredReveal_enlargeEnsured, bind_map_left, map_bind]
              apply bind_congr
              intro result
              cases result with
              | none => simp
              | some result =>
                  simpa only [Option.map, DeferredResolution.enlargeEnsured, DeferredContext.enlargeEnsured,
                    LazyRevealProbe.State.materialize, LazyRevealProbe.State.pendingAway, Finset.insert_union] using
                    ih result.output { state := context.state.materialize (.position position) result.output, values := result.values } fuel history

end SphincsSecurity.Concrete.OtsProbeSimulation
