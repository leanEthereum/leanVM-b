import SphincsSecurity.Proof.LazyRevealProbeCost

namespace SphincsSecurity.LazyRevealProbe

open OracleComp OracleSpec ENNReal

variable {Coordinate : Type} [DecidableEq Coordinate]

set_option maxRecDepth 10000 in
theorem runCharged_bind_done_support {α β : Type}
    (left : OracleComp (World Coordinate) α) (next : α → OracleComp (World Coordinate) β)
    (state : State Coordinate) (fuel : Nat) (finalState : State Coordinate) (remaining : Nat)
    (value : β) (cost : Nat)
    (hresult : (.done finalState remaining value, cost) ∈ support (runCharged state fuel (left >>= next))) :
    ∃ middleState middleValue middleFuel leftCost rightCost,
      middleFuel ≤ fuel ∧
      (.done middleState middleFuel middleValue, leftCost) ∈ support (runCharged state fuel left) ∧
      (.done finalState remaining value, rightCost) ∈ support (runCharged middleState middleFuel (next middleValue)) ∧
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
      | ensure coordinate =>
          simpa only [runCharged, OracleComp.construct_query_bind] using
            ih () (state.ensure coordinate) fuel cost hresult
      | peek coordinate =>
          simpa only [runCharged, OracleComp.construct_query_bind] using
            ih (state.values coordinate) state fuel cost hresult
      | publish coordinate =>
          simpa only [runCharged, OracleComp.construct_query_bind] using
            ih () (state.publish coordinate) fuel cost hresult
      | probe coordinate candidate =>
          cases fuel with
          | zero =>
              simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at hresult
          | succ restFuel =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · simp only [hrevealed, ↓reduceIte] at hresult
                obtain ⟨middleState, middleValue, middleFuel, leftCost, rightCost, hbudget, hleft, hright, hcost⟩ :=
                  ih () state restFuel cost hresult
                refine ⟨middleState, middleValue, middleFuel, leftCost, rightCost,
                  hbudget.trans (Nat.le_succ _), ?_, hright, hcost⟩
                rw [runCharged, OracleComp.construct_query_bind]
                simpa only [hrevealed, ↓reduceIte, runCharged] using hleft
              · simp only [hrevealed, ↓reduceIte, support_map, Set.mem_image] at hresult
                obtain ⟨⟨previousResult, previousCost⟩, hrest, heq⟩ := hresult
                have hresultEq : previousResult = .done finalState remaining value := congrArg Prod.fst heq
                have hcostEq : previousCost + pendingProbeCharge state coordinate candidate = cost := congrArg Prod.snd heq
                rw [hresultEq] at hrest
                obtain ⟨middleState, middleValue, middleFuel, leftCost, rightCost, hbudget, hleft, hright, hcost⟩ :=
                  ih () (state.addPending coordinate candidate) restFuel previousCost hrest
                refine ⟨middleState, middleValue, middleFuel, leftCost + pendingProbeCharge state coordinate candidate,
                  rightCost, hbudget.trans (Nat.le_succ _), ?_, hright, by omega⟩
                rw [runCharged, OracleComp.construct_query_bind]
                simp only [hrevealed, ↓reduceIte, support_map, Set.mem_image]
                exact ⟨(.done middleState middleFuel middleValue, leftCost), hleft, rfl⟩
      | reveal coordinate =>
          dsimp only at hresult
          cases hvalue : state.values coordinate with
          | some output =>
              simp only [hvalue] at hresult
              obtain ⟨middleState, middleValue, middleFuel, leftCost, rightCost, hbudget, hleft, hright, hcost⟩ :=
                ih output state fuel cost hresult
              refine ⟨middleState, middleValue, middleFuel, leftCost, rightCost, hbudget, ?_, hright, hcost⟩
              rw [runCharged, OracleComp.construct_query_bind]
              simpa only [hvalue, runCharged] using hleft
          | none =>
              simp only [hvalue, mem_support_bind_iff] at hresult
              obtain ⟨output, houtput, hrest⟩ := hresult
              split_ifs at hrest with hhit
              · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at hrest
              · obtain ⟨middleState, middleValue, middleFuel, leftCost, rightCost, hbudget, hleft, hright, hcost⟩ :=
                  ih output (state.materialize coordinate output) fuel cost hrest
                refine ⟨middleState, middleValue, middleFuel, leftCost, rightCost, hbudget, ?_, hright, hcost⟩
                rw [runCharged, OracleComp.construct_query_bind]
                simp only [hvalue, mem_support_bind_iff]
                exact ⟨output, houtput, by simpa only [hhit, ↓reduceIte, runCharged] using hleft⟩

theorem expectedProbeCharge_eq_zero_of_probeFree {α : Type}
    (computation : OracleComp (World Coordinate) α) (state : State Coordinate) (fuel : Nat)
    (hbound : computation.IsQueryBoundP IsProbe 0) : expectedProbeCharge computation state fuel = 0 := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure value => rfl
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [expectedProbeCharge_query_bind]
      cases input with
      | uniform n =>
          apply ENNReal.tsum_eq_zero.mpr
          intro output
          rw [ih output state fuel (by simpa [IsProbe] using hbound.2 output), mul_zero]
      | hashOutput =>
          apply ENNReal.tsum_eq_zero.mpr
          intro output
          rw [ih output state fuel (by simpa [IsProbe] using hbound.2 output), mul_zero]
      | ensure coordinate => exact ih () (state.ensure coordinate) fuel (by simpa [IsProbe] using hbound.2 ())
      | peek coordinate => exact ih (state.values coordinate) state fuel (by simpa [IsProbe] using hbound.2 _)
      | publish coordinate => exact ih () (state.publish coordinate) fuel (by simpa [IsProbe] using hbound.2 ())
      | probe coordinate candidate => simpa [IsProbe] using hbound.1
      | reveal coordinate =>
          dsimp only
          cases hvalue : state.values coordinate with
          | some output => exact ih output state fuel (by simpa [IsProbe] using hbound.2 output)
          | none =>
              apply ENNReal.tsum_eq_zero.mpr
              intro output
              rw [ih output (state.materialize coordinate output) fuel (by simpa [IsProbe] using hbound.2 output)]
              simp only [ite_self, mul_zero]

theorem runCharged_cost_eq_zero_of_probeFree {α : Type}
    (computation : OracleComp (World Coordinate) α) (state : State Coordinate) (fuel : Nat)
    (hbound : computation.IsQueryBoundP IsProbe 0) (result : RawResult Coordinate α × Nat)
    (hresult : result ∈ support (runCharged state fuel computation)) : result.2 = 0 := by
  have hexpectation := runCharged_expectedCost_eq computation state fuel
  rw [expectedProbeCharge_eq_zero_of_probeFree computation state fuel hbound, ENNReal.tsum_eq_zero] at hexpectation
  have hterm := hexpectation result
  have hmass : Pr[= result | runCharged state fuel computation] ≠ 0 := by
    rwa [mem_support_iff_evalDist_apply_ne_zero] at hresult
  exact_mod_cast (mul_eq_zero.mp hterm).resolve_left hmass

end SphincsSecurity.LazyRevealProbe
