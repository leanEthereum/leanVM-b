import SphincsSecurity.Proof.AdaptiveRevealProbeBind

namespace SphincsSecurity.AdaptiveRevealProbe

open _root_.OracleComp OracleSpec
variable {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]

def RawResult.mapValue (f : α → β) : RawResult Coordinate α → RawResult Coordinate β
  | .stopped hit => .stopped hit
  | .done state remaining value => .done state remaining (f value)

theorem runRaw_mapValue (table : Coordinate → Digest) (state : State Coordinate) (fuel : Nat)
    (computation : OracleComp (World Coordinate) α) (f : α → β) :
    runRaw table state fuel (f <$> computation) = RawResult.mapValue f <$> runRaw table state fuel computation := by
  rw [map_eq_bind_pure_comp, runRaw_bind, map_eq_bind_pure_comp]
  apply bind_congr
  intro result
  cases result <;> rfl

def rawResultWithRemaining (remaining : Nat) : DetailedResult Coordinate α → RawResult Coordinate α
  | .stopped hit => .stopped hit
  | .done _ state value => .done state remaining value

theorem runRaw_eq_detailed_of_probeFree (table : Coordinate → Digest) (state : State Coordinate) (fuel : Nat)
    (computation : OracleComp (World Coordinate) α) (hbound : computation.IsQueryBoundP IsProbe 0) :
    runRaw table state fuel computation = rawResultWithRemaining fuel <$> runDetailed table state fuel computation := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      cases input with
      | uniform n =>
          rw [runRaw_uniform_query_bind, runDetailed_uniform_query_bind, map_bind]
          exact bind_congr (fun output => ih output state (by simpa [IsProbe] using hbound.2 output))
      | hashOutput =>
          rw [runRaw_hashOutput_query_bind, runDetailed_hashOutput_query_bind, map_bind]
          exact bind_congr (fun output => ih output state (by simpa [IsProbe] using hbound.2 output))
      | probe coordinate candidate => simp [IsProbe] at hbound
      | reveal coordinate =>
          rw [runRaw_reveal_query_bind, runDetailed_reveal_query_bind]
          cases state.revealed coordinate with
          | some value => exact ih value state (by simpa [IsProbe] using hbound.2 value)
          | none =>
              dsimp only
              split_ifs
              · rfl
              · exact ih (table coordinate) (state.install coordinate (table coordinate))
                  (by simpa [IsProbe] using hbound.2 (table coordinate))

theorem runRaw_eq_detailed_of_probePrefix (table : Coordinate → Digest) (state : State Coordinate) (remaining : Nat)
    (coordinate : Coordinate) (candidate : Digest) (computation : OracleComp (World Coordinate) α)
    (hbound : computation.IsQueryBoundP IsProbe 0) :
    runRaw table state (remaining + 1) (probeQuery coordinate candidate >>= fun _ => computation) =
      rawResultWithRemaining remaining <$>
        runDetailed table state (remaining + 1) (probeQuery coordinate candidate >>= fun _ => computation) := by
  rw [probeQuery, runRaw_probe_query_bind, runDetailed_probe_query_bind]
  cases state.revealed coordinate with
  | none => exact runRaw_eq_detailed_of_probeFree table (state.addPending coordinate candidate) remaining computation hbound
  | some value => exact runRaw_eq_detailed_of_probeFree table state remaining computation hbound

end SphincsSecurity.AdaptiveRevealProbe
