import SphincsSecurity.Proof.LazyRevealProbeCharge

namespace SphincsSecurity.LazyRevealProbe

open OracleComp OracleSpec ENNReal

variable {Coordinate : Type} [DecidableEq Coordinate]

noncomputable def runCharged {α : Type} (state : State Coordinate) (fuel : Nat)
    (computation : OracleComp (World Coordinate) α) : ProbComp (RawResult Coordinate α × Nat) :=
  OracleComp.construct
    (C := fun _ => State Coordinate → Nat → ProbComp (RawResult Coordinate α × Nat))
    (fun value state remaining => pure (.done state remaining value, 0))
    (fun input _ next state fuel =>
      match input with
      | .uniform n => do
          let output ← liftM (unifSpec.query n)
          next output state fuel
      | .hashOutput => do
          let output ← sampleHashOutput
          next output state fuel
      | .ensure coordinate => next () (state.ensure coordinate) fuel
      | .probe coordinate candidate =>
          match fuel with
          | 0 => pure (.stopped false, 0)
          | remaining + 1 =>
              if coordinate ∈ state.revealed then next () state remaining
              else (fun result => (result.1, result.2 + pendingProbeCharge state coordinate candidate)) <$>
                next () (state.addPending coordinate candidate) remaining
      | .peek coordinate => next (state.values coordinate) state fuel
      | .publish coordinate => next () (state.publish coordinate) fuel
      | .reveal coordinate =>
          match state.values coordinate with
          | some output => next output state fuel
          | none => do
              let output ← sampleHashOutput
              if state.hitAt coordinate output then pure (.stopped true, 0)
              else next output (state.materialize coordinate output) fuel)
    computation state fuel

theorem runCharged_result_eq_runRaw {α : Type} (state : State Coordinate) (fuel : Nat)
    (computation : OracleComp (World Coordinate) α) :
    Prod.fst <$> runCharged state fuel computation = runRaw state fuel computation := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure value => simp only [runCharged, runRaw, OracleComp.construct_pure, map_pure]
  | query_bind input next ih =>
      rw [runCharged, runRaw, OracleComp.construct_query_bind, OracleComp.construct_query_bind]
      cases input with
      | uniform n =>
          simp only [map_bind]
          exact bind_congr fun output => ih output state fuel
      | hashOutput =>
          simp only [map_bind]
          exact bind_congr fun output => ih output state fuel
      | ensure coordinate => exact ih () (state.ensure coordinate) fuel
      | peek coordinate => exact ih (state.values coordinate) state fuel
      | publish coordinate => exact ih () (state.publish coordinate) fuel
      | probe coordinate candidate =>
          cases fuel with
          | zero => simp only [map_pure]
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · simpa only [runCharged, runRaw, hrevealed, ↓reduceIte] using ih () state remaining
              · simpa only [runCharged, runRaw, hrevealed, ↓reduceIte, Functor.map_map] using
                  ih () (state.addPending coordinate candidate) remaining
      | reveal coordinate =>
          dsimp only
          cases hvalue : state.values coordinate with
          | some output => exact ih output state fuel
          | none =>
              rw [map_bind]
              apply bind_congr
              intro output
              split_ifs with hhit
              · simp only [map_pure]
              · exact ih output (state.materialize coordinate output) fuel

theorem runCharged_cost_le_fuel {α : Type} (state : State Coordinate) (fuel : Nat)
    (computation : OracleComp (World Coordinate) α) :
    ∀ result ∈ support (runCharged state fuel computation), result.2 ≤ fuel := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure value =>
      intro result hresult
      simp only [runCharged, OracleComp.construct_pure, support_pure, Set.mem_singleton_iff] at hresult
      rw [hresult]
      exact Nat.zero_le _
  | query_bind input next ih =>
      intro result hresult
      rw [runCharged, OracleComp.construct_query_bind] at hresult
      cases input with
      | uniform n =>
          rw [mem_support_bind_iff] at hresult
          obtain ⟨output, _, hrest⟩ := hresult
          exact ih output state fuel result hrest
      | hashOutput =>
          rw [mem_support_bind_iff] at hresult
          obtain ⟨output, _, hrest⟩ := hresult
          exact ih output state fuel result hrest
      | ensure coordinate => exact ih () (state.ensure coordinate) fuel result hresult
      | peek coordinate => exact ih (state.values coordinate) state fuel result hresult
      | publish coordinate => exact ih () (state.publish coordinate) fuel result hresult
      | probe coordinate candidate =>
          cases fuel with
          | zero =>
              simp only [support_pure, Set.mem_singleton_iff] at hresult
              rw [hresult]
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · simp only [hrevealed, ↓reduceIte] at hresult
                exact (ih () state remaining result hresult).trans (Nat.le_succ remaining)
              · simp only [hrevealed, ↓reduceIte, support_map, Set.mem_image] at hresult
                obtain ⟨previous, hprevious, heq⟩ := hresult
                rw [← heq]
                exact Nat.add_le_add (ih () (state.addPending coordinate candidate) remaining previous hprevious)
                  (pendingProbeCharge_le_one state coordinate candidate)
      | reveal coordinate =>
          dsimp only at hresult
          cases hvalue : state.values coordinate with
          | some output =>
              simp only [hvalue] at hresult
              exact ih output state fuel result hresult
          | none =>
              simp only [hvalue, mem_support_bind_iff] at hresult
              obtain ⟨output, _, hrest⟩ := hresult
              split_ifs at hrest with hhit
              · simp only [support_pure, Set.mem_singleton_iff] at hrest
                rw [hrest]
                exact Nat.zero_le _
              · exact ih output (state.materialize coordinate output) fuel result hrest

theorem runCharged_expectedCost_eq {α : Type}
    (computation : OracleComp (World Coordinate) α) (state : State Coordinate) (fuel : Nat) :
    (∑' result, Pr[= result | runCharged state fuel computation] * (result.2 : ℝ≥0∞)) =
      expectedProbeCharge computation state fuel := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure value => simp only [runCharged, expectedProbeCharge, OracleComp.construct_pure,
      tsum_probOutput_pure_mul, Nat.cast_zero]
  | query_bind input next ih =>
      rw [expectedProbeCharge_query_bind, runCharged, OracleComp.construct_query_bind]
      cases input with
      | uniform n =>
          rw [tsum_probOutput_bind_mul]
          exact tsum_congr fun output => congrArg (fun cost => Pr[= output | (liftM (unifSpec.query n) : ProbComp _)] * cost)
            (ih output state fuel)
      | hashOutput =>
          rw [tsum_probOutput_bind_mul]
          exact tsum_congr fun output => congrArg (fun cost => Pr[= output | sampleHashOutput] * cost)
            (ih output state fuel)
      | ensure coordinate => exact ih () (state.ensure coordinate) fuel
      | peek coordinate => exact ih (state.values coordinate) state fuel
      | publish coordinate => exact ih () (state.publish coordinate) fuel
      | probe coordinate candidate =>
          cases fuel with
          | zero => simp only [tsum_probOutput_pure_mul, Nat.cast_zero]
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · simp only [hrevealed, ↓reduceIte]
                exact ih () state remaining
              · simp only [hrevealed, ↓reduceIte, tsum_probOutput_map_mul, Nat.cast_add, mul_add]
                rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
                change (∑' result, Pr[= result | runCharged (state.addPending coordinate candidate) remaining
                  (next ())] * (result.2 : ℝ≥0∞)) + _ = _
                rw [ih, add_comm]
      | reveal coordinate =>
          dsimp only
          cases hvalue : state.values coordinate with
          | some output => exact ih output state fuel
          | none =>
              rw [tsum_probOutput_bind_mul]
              apply tsum_congr
              intro output
              split_ifs with hhit
              · simp only [tsum_probOutput_pure_mul, Nat.cast_zero]
              · exact congrArg (fun cost => Pr[= output | sampleHashOutput] * cost)
                  (ih output (state.materialize coordinate output) fuel)

end SphincsSecurity.LazyRevealProbe
