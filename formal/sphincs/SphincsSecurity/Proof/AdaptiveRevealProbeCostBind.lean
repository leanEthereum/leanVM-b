import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.AdaptiveRevealProbeCost

namespace SphincsSecurity.AdaptiveRevealProbe

open OracleComp OracleSpec ENNReal

variable {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]

set_option maxRecDepth 10000 in
theorem runCharged_bind_done_support {α β : Type}
    (table : Coordinate → Digest) (left : OracleComp (World Coordinate) α)
    (next : α → OracleComp (World Coordinate) β) (state : State Coordinate) (fuel : Nat)
    (hit : Bool) (finalState : State Coordinate) (value : β) (cost : Nat)
    (hresult : (.done hit finalState value, cost) ∈ support (runCharged table state fuel (left >>= next))) :
    ∃ middleState middleValue middleFuel leftCost rightCost,
      middleFuel ≤ fuel ∧
      (.done (tableHits middleState table) middleState middleValue, leftCost) ∈
        support (runCharged table state fuel left) ∧
      (.done hit finalState value, rightCost) ∈
        support (runCharged table middleState middleFuel (next middleValue)) ∧
      cost = leftCost + rightCost := by
  induction left using OracleComp.inductionOn generalizing state fuel cost with
  | pure middleValue =>
      rw [pure_bind] at hresult
      refine ⟨state, middleValue, fuel, 0, cost, le_rfl, ?_, hresult, by omega⟩
      simp only [runCharged, OracleComp.construct_pure, support_pure, Set.mem_singleton_iff]
  | query_bind input continuation ih =>
      rw [bind_assoc, runCharged, OracleComp.construct_query_bind] at hresult
      cases input with
      | uniform n =>
          rw [mem_support_bind_iff] at hresult
          obtain ⟨output, houtput, hrest⟩ := hresult
          obtain ⟨middleState, middleValue, middleFuel, leftCost, rightCost, hbudget, hleft, hright, hcost⟩ :=
            ih output state fuel cost hrest
          refine ⟨middleState, middleValue, middleFuel, leftCost, rightCost, hbudget, ?_, hright, hcost⟩
          rw [runCharged, OracleComp.construct_query_bind, mem_support_bind_iff]
          exact ⟨output, houtput, hleft⟩
      | hashOutput =>
          rw [mem_support_bind_iff] at hresult
          obtain ⟨output, houtput, hrest⟩ := hresult
          obtain ⟨middleState, middleValue, middleFuel, leftCost, rightCost, hbudget, hleft, hright, hcost⟩ :=
            ih output state fuel cost hrest
          refine ⟨middleState, middleValue, middleFuel, leftCost, rightCost, hbudget, ?_, hright, hcost⟩
          rw [runCharged, OracleComp.construct_query_bind, mem_support_bind_iff]
          exact ⟨output, houtput, hleft⟩
      | probe coordinate candidate =>
          cases fuel with
          | zero =>
              simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at hresult
          | succ remaining =>
              cases hrevealed : state.revealed coordinate with
              | some revealed =>
                  simp only [hrevealed] at hresult
                  obtain ⟨middleState, middleValue, middleFuel, leftCost, rightCost, hbudget, hleft, hright, hcost⟩ :=
                    ih () state remaining cost hresult
                  refine ⟨middleState, middleValue, middleFuel, leftCost, rightCost,
                    hbudget.trans (Nat.le_succ _), ?_, hright, hcost⟩
                  rw [runCharged, OracleComp.construct_query_bind]
                  simpa only [hrevealed, runCharged] using hleft
              | none =>
                  simp only [hrevealed, support_map, Set.mem_image] at hresult
                  obtain ⟨⟨previousResult, previousCost⟩, hrest, heq⟩ := hresult
                  have hresultEq : previousResult = .done hit finalState value := congrArg Prod.fst heq
                  have hcostEq : previousCost + pendingProbeCharge state coordinate candidate = cost := congrArg Prod.snd heq
                  rw [hresultEq] at hrest
                  obtain ⟨middleState, middleValue, middleFuel, leftCost, rightCost, hbudget, hleft, hright, hcost⟩ :=
                    ih () (state.addPending coordinate candidate) remaining previousCost hrest
                  refine ⟨middleState, middleValue, middleFuel,
                    leftCost + pendingProbeCharge state coordinate candidate, rightCost,
                    hbudget.trans (Nat.le_succ _), ?_, hright, by omega⟩
                  rw [runCharged, OracleComp.construct_query_bind]
                  simp only [hrevealed, support_map, Set.mem_image]
                  exact ⟨(.done (tableHits middleState table) middleState middleValue, leftCost), hleft, rfl⟩
      | reveal coordinate =>
          cases hrevealed : state.revealed coordinate with
          | some revealed =>
              simp only [hrevealed] at hresult
              obtain ⟨middleState, middleValue, middleFuel, leftCost, rightCost, hbudget, hleft, hright, hcost⟩ :=
                ih revealed state fuel cost hresult
              refine ⟨middleState, middleValue, middleFuel, leftCost, rightCost, hbudget, ?_, hright, hcost⟩
              rw [runCharged, OracleComp.construct_query_bind]
              simpa only [hrevealed, runCharged] using hleft
          | none =>
              simp only [hrevealed] at hresult
              split_ifs at hresult with hhit
              · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at hresult
              · obtain ⟨middleState, middleValue, middleFuel, leftCost, rightCost, hbudget, hleft, hright, hcost⟩ :=
                  ih (table coordinate) (state.install coordinate (table coordinate)) fuel cost hresult
                refine ⟨middleState, middleValue, middleFuel, leftCost, rightCost, hbudget, ?_, hright, hcost⟩
                rw [runCharged, OracleComp.construct_query_bind]
                simpa only [hrevealed, hhit, ↓reduceIte, runCharged] using hleft

theorem runCharged_done_mem_support {α : Type}
    (table : Coordinate → Digest) (state finalState : State Coordinate) (fuel : Nat)
    (computation : OracleComp (World Coordinate) α) (hit : Bool) (value : α) (cost : Nat)
    (hresult : (.done hit finalState value, cost) ∈ support (runCharged table state fuel computation)) :
    value ∈ support computation := by
  apply mem_support_of_mem_runDetailed_done table state finalState fuel computation hit value
  rw [← runCharged_result_eq_runDetailed, support_map]
  exact ⟨(.done hit finalState value, cost), hresult, rfl⟩

theorem runCharged_done_stateFree {α : Type}
    (table : Coordinate → Digest) (state finalState : State Coordinate) (fuel : Nat)
    (computation : OracleComp (World Coordinate) α)
    (hbound : computation.IsQueryBoundP IsStateful 0) (hit : Bool) (value : α) (cost : Nat)
    (hresult : (.done hit finalState value, cost) ∈ support (runCharged table state fuel computation)) :
    finalState = state ∧ cost = 0 := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure result =>
      simp only [runCharged, OracleComp.construct_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, DetailedResult.done.injEq] at hresult
      exact ⟨hresult.1.2.1, hresult.2⟩
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      rw [runCharged, OracleComp.construct_query_bind] at hresult
      cases input with
      | uniform n =>
          rw [mem_support_bind_iff] at hresult
          obtain ⟨output, _, hrest⟩ := hresult
          exact ih output state fuel (by simpa [IsStateful] using hbound.2 output) hrest
      | hashOutput =>
          rw [mem_support_bind_iff] at hresult
          obtain ⟨output, _, hrest⟩ := hresult
          exact ih output state fuel (by simpa [IsStateful] using hbound.2 output) hrest
      | probe coordinate candidate => simp [IsStateful] at hbound
      | reveal coordinate => simp [IsStateful] at hbound

end SphincsSecurity.AdaptiveRevealProbe
