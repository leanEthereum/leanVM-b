import SphincsSecurity.Proof.AdaptiveRevealProbe

namespace SphincsSecurity.AdaptiveRevealProbe

open _root_.OracleComp OracleSpec ENNReal

variable {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]

theorem runDetailed_liftProbComp_bind
    (table : Coordinate → Digest) (state : State Coordinate) (fuel : Nat)
    (computation : ProbComp α) (next : α → OracleComp (World Coordinate) β) :
    runDetailed table state fuel (liftProbComp computation >>= next) =
      computation >>= fun value => runDetailed table state fuel (next value) := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input continuation ih =>
      rw [liftProbComp, simulateQ_query_bind, bind_assoc]
      change runDetailed table state fuel (uniformQuery input >>= _) = _
      rw [uniformQuery, runDetailed_uniform_query_bind, bind_assoc]
      exact bind_congr ih

end SphincsSecurity.AdaptiveRevealProbe
