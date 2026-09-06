import SphincsSecurity.Proof.AdaptiveRevealProbeCostBind

namespace SphincsSecurity.AdaptiveRevealProbe

open _root_.OracleComp OracleSpec ENNReal
variable {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]

def unrevealedProbeCharge (state : State Coordinate) (coordinate : Coordinate) (candidate : Digest) : Nat :=
  if state.revealed coordinate = none then pendingProbeCharge state coordinate candidate else 0

omit [Fintype Coordinate] [DecidableEq Coordinate] in
theorem unrevealedProbeCharge_le_one (state : State Coordinate) (coordinate : Coordinate) (candidate : Digest) :
    unrevealedProbeCharge state coordinate candidate ≤ 1 := by
  unfold unrevealedProbeCharge
  split_ifs
  · exact pendingProbeCharge_le_one state coordinate candidate
  · omega

theorem runCharged_probeFree
    (table : Coordinate → Digest) (state : State Coordinate) (fuel : Nat)
    (computation : OracleComp (World Coordinate) α) (hbound : computation.IsQueryBoundP IsProbe 0) :
    runCharged table state fuel computation = (fun result => (result, 0)) <$> runDetailed table state fuel computation := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [runCharged, runDetailed, construct_pure, map_pure]
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      rw [runCharged, runDetailed, construct_query_bind, construct_query_bind]
      cases input with
      | uniform n =>
          rw [map_bind]
          exact bind_congr fun output => ih output state (by simpa [IsProbe] using hbound.2 output)
      | hashOutput =>
          rw [map_bind]
          exact bind_congr fun output => ih output state (by simpa [IsProbe] using hbound.2 output)
      | probe coordinate candidate => simp [IsProbe] at hbound
      | reveal coordinate =>
          cases hrevealed : state.revealed coordinate with
          | some value => simpa only [hrevealed, runCharged, runDetailed] using ih value state (by simpa [IsProbe] using hbound.2 value)
          | none =>
              simp only [hrevealed]
              by_cases hhit : table coordinate ∈ state.pending coordinate
              · simp only [hhit, ↓reduceIte, map_pure]
              · simp only [hhit, ↓reduceIte]
                exact ih (table coordinate) (state.install coordinate (table coordinate)) (by simpa [IsProbe] using hbound.2 (table coordinate))

theorem runCharged_bind_probeFree
    (table : Coordinate → Digest) (state : State Coordinate) (fuel : Nat)
    (left : OracleComp (World Coordinate) α) (next : α → OracleComp (World Coordinate) β)
    (hbound : left.IsQueryBoundP IsProbe 0) :
    runCharged table state fuel (left >>= next) =
      runDetailed table state fuel left >>= fun result =>
        match result with
        | .stopped hit => pure (.stopped hit, 0)
        | .done _ finalState value => runCharged table finalState fuel (next value) := by
  induction left using OracleComp.inductionOn generalizing state with
  | pure value => simp only [pure_bind, runDetailed, construct_pure]
  | query_bind input continuation ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      rw [bind_assoc, runCharged, construct_query_bind, runDetailed, construct_query_bind]
      cases input with
      | uniform n =>
          rw [bind_assoc]
          exact bind_congr fun output => ih output state (by simpa [IsProbe] using hbound.2 output)
      | hashOutput =>
          rw [bind_assoc]
          exact bind_congr fun output => ih output state (by simpa [IsProbe] using hbound.2 output)
      | probe coordinate candidate => simp [IsProbe] at hbound
      | reveal coordinate =>
          cases hrevealed : state.revealed coordinate with
          | some value => simpa only [hrevealed, runCharged, runDetailed] using ih value state (by simpa [IsProbe] using hbound.2 value)
          | none =>
              simp only [hrevealed]
              by_cases hhit : table coordinate ∈ state.pending coordinate
              · simp only [hhit, ↓reduceIte, pure_bind]
              · simp only [hhit, ↓reduceIte]
                exact ih (table coordinate) (state.install coordinate (table coordinate)) (by simpa [IsProbe] using hbound.2 (table coordinate))

theorem runCharged_bind_probePrefix
    (table : Coordinate → Digest) (state : State Coordinate) (remaining : Nat)
    (coordinate : Coordinate) (candidate : Digest)
    (left : OracleComp (World Coordinate) α) (next : α → OracleComp (World Coordinate) β)
    (hbound : left.IsQueryBoundP IsProbe 0) :
    runCharged table state (remaining + 1) ((probeQuery coordinate candidate >>= fun _ => left) >>= next) =
      runDetailed table state (remaining + 1) (probeQuery coordinate candidate >>= fun _ => left) >>= fun result =>
        match result with
        | .stopped hit => pure (.stopped hit, unrevealedProbeCharge state coordinate candidate)
        | .done _ finalState value =>
            (fun result => (result.1, result.2 + unrevealedProbeCharge state coordinate candidate)) <$>
              runCharged table finalState remaining (next value) := by
  rw [bind_assoc]
  unfold probeQuery
  rw [runCharged, construct_query_bind, runDetailed_probe_query_bind]
  cases hrevealed : state.revealed coordinate with
  | some value =>
      simp only [hrevealed]
      change runCharged table state remaining (left >>= next) = _
      rw [runCharged_bind_probeFree table state remaining left next hbound]
      have hz : unrevealedProbeCharge state coordinate candidate = 0 := by simp [unrevealedProbeCharge, hrevealed]
      rw [hz]
      apply bind_congr
      intro result
      cases result <;> simp
  | none =>
      simp only [hrevealed]
      change (fun result : DetailedResult Coordinate β × Nat => (result.1, result.2 + pendingProbeCharge state coordinate candidate)) <$>
        runCharged table (state.addPending coordinate candidate) remaining (left >>= next) = _
      rw [runCharged_bind_probeFree table (state.addPending coordinate candidate) remaining left next hbound, map_bind]
      simp only [unrevealedProbeCharge, hrevealed, if_true]
      apply bind_congr
      intro result
      cases result <;> simp

end SphincsSecurity.AdaptiveRevealProbe
