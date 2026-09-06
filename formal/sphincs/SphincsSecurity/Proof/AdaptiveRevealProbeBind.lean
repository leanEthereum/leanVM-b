import SphincsSecurity.Proof.AdaptiveRevealProbe

namespace SphincsSecurity.AdaptiveRevealProbe

open OracleComp OracleSpec ENNReal

variable {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]

theorem runDetailed_bind_probePrefix
    (table : Coordinate → Digest) (state : State Coordinate) (remaining : Nat)
    (coordinate : Coordinate) (candidate : Digest)
    (left : OracleComp (World Coordinate) α) (next : α → OracleComp (World Coordinate) β)
    (hfree : left.IsQueryBoundP IsProbe 0) :
    runDetailed table state (remaining + 1) ((probeQuery coordinate candidate >>= fun _ => left) >>= next) =
      runDetailed table state (remaining + 1) (probeQuery coordinate candidate >>= fun _ => left) >>= fun result =>
        match result with
        | .stopped hit => pure (.stopped hit)
        | .done _ finalState value => runDetailed table finalState remaining (next value) := by
  rw [bind_assoc, probeQuery, runDetailed_probe_query_bind, runDetailed_probe_query_bind]
  cases state.revealed coordinate <;> exact runDetailed_bind_probeFree table _ remaining left next hfree

end SphincsSecurity.AdaptiveRevealProbe
