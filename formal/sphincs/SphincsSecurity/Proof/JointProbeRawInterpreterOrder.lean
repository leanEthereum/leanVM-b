import SphincsSecurity.Proof.JointProbeFtsRaw

namespace SphincsSecurity.AdaptiveRevealProbe

open _root_.OracleComp OracleSpec
variable {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]

theorem runRaw_liftProbComp_bind
    (table : Coordinate → Digest) (state : State Coordinate) (fuel : Nat)
    (computation : ProbComp α) (next : α → OracleComp (World Coordinate) β) :
    runRaw table state fuel (liftProbComp computation >>= next) =
      computation >>= fun value => runRaw table state fuel (next value) := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input continuation ih =>
      rw [liftProbComp, simulateQ_query_bind, bind_assoc]
      change runRaw table state fuel (uniformQuery input >>= _) = _
      rw [uniformQuery, runRaw_uniform_query_bind, bind_assoc]
      exact bind_congr ih

end SphincsSecurity.AdaptiveRevealProbe

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
open OtsProbeSimulation (HistoryResolvedPrefix)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def rawJointHistory : AdaptiveRevealProbe.RawResult Coordinate (Option (HistoryResolvedPrefix α)) →
    Option (HistoryResolvedPrefix (AdaptiveRevealProbe.State Coordinate × Nat × α))
  | .stopped _ => none
  | .done state remaining result => result.map
      (fun entry => ⟨entry.context, entry.remaining, (state, remaining, entry.value), entry.history⟩)

def flattenRawHistory : Option (HistoryResolvedPrefix (AdaptiveRevealProbe.RawResult Coordinate α)) →
    Option (HistoryResolvedPrefix (AdaptiveRevealProbe.State Coordinate × Nat × α))
  | none => none
  | some entry => match entry.value with
    | .stopped _ => none
    | .done state remaining value => some ⟨entry.context, entry.remaining, (state, remaining, value), entry.history⟩

theorem runJointFtsRaw_erasedHistory_commute
    (table : Coordinate → Digest) (computation : OracleComp JointProbeWorld α)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe) :
    rawJointHistory <$>
      AdaptiveRevealProbe.runRaw table state ftsFuel (runJointErasedHistory computation context fuel history) =
      flattenRawHistory <$>
        OtsProbeSimulation.runResolvedHistoryPrefix
          (OtsProbeSimulation.eraseProbeQueries (runJointFtsRaw table computation state ftsFuel)) context fuel history := by
  induction computation using OracleComp.inductionOn generalizing state ftsFuel context fuel history with
  | pure value => rfl
  | query_bind input next ih =>
      rw [runJointErasedHistory_query_bind, runJointFtsRaw_query_bind]
      cases input with
      | inl input =>
          rw [AdaptiveRevealProbe.runRaw_liftProbComp_bind, map_bind,
            OtsProbeSimulation.eraseProbeQueries_query_bind, OtsProbeSimulation.runResolvedHistoryPrefix_bind, map_bind]
          apply bind_congr
          intro result
          cases result with
          | none => rfl
          | some entry => exact ih entry.value state ftsFuel entry.context entry.remaining entry.history
      | inr input =>
          cases input with
          | uniform n =>
              rw [AdaptiveRevealProbe.runRaw_uniform_query_bind, map_bind]
              simp only [OtsProbeSimulation.eraseProbeQueries, OtsProbeSimulation.runResolvedHistoryPrefix]
              exact bind_congr (fun output => ih output state ftsFuel context fuel history)
          | hashOutput =>
              rw [AdaptiveRevealProbe.runRaw_hashOutput_query_bind, map_bind]
              simp only [OtsProbeSimulation.eraseProbeQueries, OtsProbeSimulation.runResolvedHistoryPrefix]
              exact bind_congr (fun output => ih output state ftsFuel context fuel history)
          | probe coordinate candidate =>
              rw [AdaptiveRevealProbe.runRaw_probe_query_bind]
              dsimp only
              cases ftsFuel with
              | zero => rfl
              | succ remaining =>
                  cases state.revealed coordinate with
                  | none => exact ih () (state.addPending coordinate candidate) remaining context fuel history
                  | some value => exact ih () state remaining context fuel history
          | reveal coordinate =>
              rw [AdaptiveRevealProbe.runRaw_reveal_query_bind]
              dsimp only
              cases state.revealed coordinate with
              | some value => exact ih value state ftsFuel context fuel history
              | none =>
                  split_ifs
                  · rfl
                  · exact ih (table coordinate) (state.install coordinate (table coordinate)) ftsFuel context fuel history

end SphincsSecurity.Concrete.FtsProbeSimulation
