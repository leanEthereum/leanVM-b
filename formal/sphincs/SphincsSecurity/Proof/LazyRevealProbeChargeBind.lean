import SphincsSecurity.Proof.LazyRevealProbeCostBind

namespace SphincsSecurity.LazyRevealProbe

open OracleComp OracleSpec ENNReal

variable {Coordinate : Type} [DecidableEq Coordinate]

noncomputable def RawResult.continuationCharge {α β : Type}
    (next : α → OracleComp (World Coordinate) β) : RawResult Coordinate α → ℝ≥0∞
  | .stopped _ => 0
  | .done state remaining value => expectedProbeCharge (next value) state remaining

theorem expectedProbeCharge_bind {α β : Type}
    (left : OracleComp (World Coordinate) α) (next : α → OracleComp (World Coordinate) β)
    (state : State Coordinate) (fuel : Nat) :
    expectedProbeCharge (left >>= next) state fuel = expectedProbeCharge left state fuel +
      ∑' result, Pr[= result | runRaw state fuel left] * result.continuationCharge next := by
  induction left using OracleComp.inductionOn generalizing state fuel with
  | pure value =>
      simp only [pure_bind, expectedProbeCharge, OracleComp.construct_pure, runRaw,
        tsum_probOutput_pure_mul, RawResult.continuationCharge, zero_add]
  | query_bind input continuation ih =>
      rw [bind_assoc, expectedProbeCharge_query_bind, expectedProbeCharge_query_bind]
      cases input with
      | uniform n =>
          rw [runRaw_uniform_query_bind, tsum_probOutput_bind_mul]
          simp_rw [ih, mul_add, ENNReal.tsum_add]
      | hashOutput =>
          rw [runRaw_hashOutput_query_bind, tsum_probOutput_bind_mul]
          simp_rw [ih, mul_add, ENNReal.tsum_add]
      | ensure coordinate =>
          rw [runRaw_ensure_query_bind]
          exact ih () (state.ensure coordinate) fuel
      | peek coordinate =>
          rw [runRaw_peek_query_bind]
          exact ih (state.values coordinate) state fuel
      | publish coordinate =>
          rw [runRaw_publish_query_bind]
          exact ih () (state.publish coordinate) fuel
      | probe coordinate candidate =>
          rw [runRaw_probe_query_bind]
          cases fuel with
          | zero => simp only [tsum_probOutput_pure_mul, RawResult.continuationCharge, add_zero]
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · simp only [hrevealed, ↓reduceIte]
                exact ih () state remaining
              · simp only [hrevealed, ↓reduceIte]
                rw [ih, add_assoc]
      | reveal coordinate =>
          rw [runRaw_reveal_query_bind]
          dsimp only
          cases hvalue : state.values coordinate with
          | some output => exact ih output state fuel
          | none =>
              rw [tsum_probOutput_bind_mul, ← ENNReal.tsum_add]
              apply tsum_congr
              intro output
              by_cases hhit : state.hitAt coordinate output
              · simp only [hhit, ↓reduceIte, tsum_probOutput_pure_mul,
                  RawResult.continuationCharge, mul_zero, add_zero]
              · simp only [hhit, ↓reduceIte, ih, mul_add]

theorem expectedProbeCharge_bind_of_probeFree {α β : Type}
    (left : OracleComp (World Coordinate) α) (next : α → OracleComp (World Coordinate) β)
    (state : State Coordinate) (fuel : Nat) (hleft : left.IsQueryBoundP IsProbe 0) :
    expectedProbeCharge (left >>= next) state fuel =
      ∑' result, Pr[= result | runRaw state fuel left] * result.continuationCharge next := by
  rw [expectedProbeCharge_bind, expectedProbeCharge_eq_zero_of_probeFree left state fuel hleft, zero_add]

theorem expectedProbeCharge_bind_pure {α β : Type}
    (computation : OracleComp (World Coordinate) α) (f : α → β)
    (state : State Coordinate) (fuel : Nat) :
    expectedProbeCharge (computation >>= fun value => pure (f value)) state fuel =
      expectedProbeCharge computation state fuel := by
  rw [expectedProbeCharge_bind]
  suffices hzero : (∑' result, Pr[= result | runRaw state fuel computation] *
      result.continuationCharge (fun value => pure (f value))) = 0 by rw [hzero, add_zero]
  apply ENNReal.tsum_eq_zero.mpr
  intro result
  cases result <;> simp only [RawResult.continuationCharge, expectedProbeCharge,
    OracleComp.construct_pure, mul_zero]

theorem expectedProbeCharge_bind_of_tail_probeFree {α β : Type}
    (left : OracleComp (World Coordinate) α) (next : α → OracleComp (World Coordinate) β)
    (state : State Coordinate) (fuel : Nat) (hnext : ∀ value, (next value).IsQueryBoundP IsProbe 0) :
    expectedProbeCharge (left >>= next) state fuel = expectedProbeCharge left state fuel := by
  rw [expectedProbeCharge_bind]
  suffices hzero : (∑' result, Pr[= result | runRaw state fuel left] * result.continuationCharge next) = 0 by
    rw [hzero, add_zero]
  apply ENNReal.tsum_eq_zero.mpr
  intro result
  cases result with
  | stopped hit => simp only [RawResult.continuationCharge, mul_zero]
  | done nextState remaining value =>
      simp only [RawResult.continuationCharge,
        expectedProbeCharge_eq_zero_of_probeFree _ nextState remaining (hnext value), mul_zero]

end SphincsSecurity.LazyRevealProbe
