import SphincsSecurity.Proof.JointProbeResolvedSource

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def rawJointResolved : AdaptiveRevealProbe.RawResult Coordinate (Option (ResolvedRunResult α)) →
    Option (ResolvedRunResult (AdaptiveRevealProbe.State Coordinate × Nat × α))
  | .stopped _ => none
  | .done state remaining result => result.map
      (fun entry => ⟨entry.context, entry.remaining, (state, remaining, entry.value), entry.table⟩)

def flattenRawResolved : Option (ResolvedRunResult (AdaptiveRevealProbe.RawResult Coordinate α)) →
    Option (ResolvedRunResult (AdaptiveRevealProbe.State Coordinate × Nat × α))
  | none => none
  | some entry => match entry.value with
    | .stopped _ => none
    | .done state remaining value => some ⟨entry.context, entry.remaining, (state, remaining, value), entry.table⟩

theorem runJointFtsRaw_resolved_commute
    (table : Coordinate → Digest) (computation : OracleComp JointProbeWorld α)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) :
    rawJointResolved <$>
      AdaptiveRevealProbe.runRaw table state ftsFuel (runJointResolved computation context fuel otsTable) =
      flattenRawResolved <$>
        OtsProbeSimulation.runResolvedFromTable context fuel otsTable (runJointFtsRaw table computation state ftsFuel) := by
  induction computation using OracleComp.inductionOn generalizing state ftsFuel context fuel otsTable with
  | pure value => rfl
  | query_bind input next ih =>
      rw [runJointResolved_query_bind, runJointFtsRaw_query_bind]
      cases input with
      | inl input =>
          rw [AdaptiveRevealProbe.runRaw_liftProbComp_bind, map_bind,
            OtsProbeSimulation.runResolvedFromTable_bind, map_bind]
          apply bind_congr
          intro result
          cases result with
          | none => rfl
          | some entry => exact ih entry.value state ftsFuel entry.context entry.remaining entry.table
      | inr input =>
          cases input with
          | uniform n =>
              rw [AdaptiveRevealProbe.runRaw_uniform_query_bind, map_bind]
              simp only [OtsProbeSimulation.runResolvedFromTable]
              exact bind_congr (fun output => ih output state ftsFuel context fuel otsTable)
          | hashOutput =>
              rw [AdaptiveRevealProbe.runRaw_hashOutput_query_bind, map_bind]
              simp only [OtsProbeSimulation.runResolvedFromTable]
              exact bind_congr (fun output => ih output state ftsFuel context fuel otsTable)
          | probe coordinate candidate =>
              rw [AdaptiveRevealProbe.runRaw_probe_query_bind]
              dsimp only
              cases ftsFuel with
              | zero => rfl
              | succ remaining =>
                  cases state.revealed coordinate with
                  | none => exact ih () (state.addPending coordinate candidate) remaining context fuel otsTable
                  | some value => exact ih () state remaining context fuel otsTable
          | reveal coordinate =>
              rw [AdaptiveRevealProbe.runRaw_reveal_query_bind]
              dsimp only
              cases state.revealed coordinate with
              | some value => exact ih value state ftsFuel context fuel otsTable
              | none =>
                  split_ifs
                  · rfl
                  · exact ih (table coordinate) (state.install coordinate (table coordinate)) ftsFuel context fuel otsTable

end SphincsSecurity.Concrete.FtsProbeSimulation
