import SphincsSecurity.Proof.JointProbeFtsInterpreter

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
open OtsProbeSimulation (HistoryResolvedPrefix)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def cleanJointHistory : AdaptiveRevealProbe.DetailedResult Coordinate (Option (HistoryResolvedPrefix α)) →
    Option (HistoryResolvedPrefix α)
  | .stopped _ => none
  | .done true _ _ => none
  | .done false _ result => result

def flattenOptionalHistory : Option (HistoryResolvedPrefix (Option α)) → Option (HistoryResolvedPrefix α)
  | none => none
  | some entry => entry.value.map (fun value => ⟨entry.context, entry.remaining, value, entry.history⟩)

theorem runJointFts_erasedHistory_commute
    (table : Coordinate → Digest) (computation : OracleComp JointProbeWorld α)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe) :
    cleanJointHistory <$>
      AdaptiveRevealProbe.runDetailed table state ftsFuel (runJointErasedHistory computation context fuel history) =
      flattenOptionalHistory <$>
        OtsProbeSimulation.runResolvedHistoryPrefix
          (OtsProbeSimulation.eraseProbeQueries (runJointFts table computation state ftsFuel)) context fuel history := by
  induction computation using OracleComp.inductionOn generalizing state ftsFuel context fuel history with
  | pure value =>
      simp only [runJointErasedHistory_pure, AdaptiveRevealProbe.runDetailed, runJointFts_pure]
      cases hhit : AdaptiveRevealProbe.tableHits state table <;>
        simp [cleanJointHistory, flattenOptionalHistory, OtsProbeSimulation.eraseProbeQueries, OtsProbeSimulation.runResolvedHistoryPrefix, hhit]
  | query_bind input next ih =>
      rw [runJointErasedHistory_query_bind, runJointFts_query_bind]
      cases input with
      | inl input =>
          rw [AdaptiveRevealProbe.runDetailed_liftProbComp_bind, map_bind,
            OtsProbeSimulation.eraseProbeQueries_query_bind, OtsProbeSimulation.runResolvedHistoryPrefix_bind, map_bind]
          apply bind_congr
          intro result
          cases result with
          | none =>
              cases hhit : AdaptiveRevealProbe.tableHits state table <;>
                simp [AdaptiveRevealProbe.runDetailed, cleanJointHistory, flattenOptionalHistory, hhit]
          | some entry => exact ih entry.value state ftsFuel entry.context entry.remaining entry.history
      | inr input =>
          cases input with
          | uniform n =>
              rw [AdaptiveRevealProbe.runDetailed_uniform_query_bind, map_bind]
              simp only [OtsProbeSimulation.eraseProbeQueries, OtsProbeSimulation.runResolvedHistoryPrefix]
              exact bind_congr (fun output => ih output state ftsFuel context fuel history)
          | hashOutput =>
              rw [AdaptiveRevealProbe.runDetailed_hashOutput_query_bind, map_bind]
              simp only [OtsProbeSimulation.eraseProbeQueries, OtsProbeSimulation.runResolvedHistoryPrefix]
              exact bind_congr (fun output => ih output state ftsFuel context fuel history)
          | probe coordinate candidate =>
              rw [AdaptiveRevealProbe.runDetailed_probe_query_bind]
              dsimp only
              cases ftsFuel with
              | zero =>
                  simp [cleanJointHistory, flattenOptionalHistory, OtsProbeSimulation.eraseProbeQueries, OtsProbeSimulation.runResolvedHistoryPrefix]
              | succ remaining =>
                  cases state.revealed coordinate with
                  | none => exact ih () (state.addPending coordinate candidate) remaining context fuel history
                  | some value => exact ih () state remaining context fuel history
          | reveal coordinate =>
              rw [AdaptiveRevealProbe.runDetailed_reveal_query_bind]
              dsimp only
              cases state.revealed coordinate with
              | some value => exact ih value state ftsFuel context fuel history
              | none =>
                  split_ifs
                  · simp [cleanJointHistory, flattenOptionalHistory, OtsProbeSimulation.eraseProbeQueries, OtsProbeSimulation.runResolvedHistoryPrefix]
                  · exact ih (table coordinate) (state.install coordinate (table coordinate)) ftsFuel context fuel history

end SphincsSecurity.Concrete.FtsProbeSimulation
