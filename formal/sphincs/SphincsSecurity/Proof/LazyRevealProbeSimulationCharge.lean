import SphincsSecurity.Proof.LazyRevealProbeChargeBind

namespace SphincsSecurity.LazyRevealProbe

open OracleComp OracleSpec ENNReal

variable {Coordinate Cache ι : Type} [DecidableEq Coordinate] {spec : OracleSpec ι}

noncomputable def expectedSimulationCharge {α : Type}
    (impl : QueryImpl spec (StateT Cache (OracleComp (World Coordinate))))
    (charge : spec.Domain → Cache → State Coordinate → Nat → ℝ≥0∞)
    (computation : OracleComp spec α) : Cache → State Coordinate → Nat → ℝ≥0∞ :=
  OracleComp.construct (fun _ _ _ _ => 0)
    (fun input _ next cache state fuel =>
      charge input cache state fuel +
        ∑' result, Pr[= result | runRaw state fuel ((impl input).run cache)] *
          match result with
          | .stopped _ => 0
          | .done nextState remaining value => next value.1 value.2 nextState remaining)
    computation

theorem expectedSimulationCharge_query_bind {α : Type}
    (impl : QueryImpl spec (StateT Cache (OracleComp (World Coordinate))))
    (charge : spec.Domain → Cache → State Coordinate → Nat → ℝ≥0∞)
    (input : spec.Domain) (next : spec.Range input → OracleComp spec α)
    (cache : Cache) (state : State Coordinate) (fuel : Nat) :
    expectedSimulationCharge impl charge (OracleSpec.query input >>= next) cache state fuel =
      charge input cache state fuel +
        ∑' result, Pr[= result | runRaw state fuel ((impl input).run cache)] *
          match result with
          | .stopped _ => 0
          | .done nextState remaining value =>
              expectedSimulationCharge impl charge (next value.1) value.2 nextState remaining := rfl

theorem expectedProbeCharge_simulateQ_le {α : Type}
    (impl : QueryImpl spec (StateT Cache (OracleComp (World Coordinate))))
    (charge : spec.Domain → Cache → State Coordinate → Nat → ℝ≥0∞)
    (hcharge : ∀ input cache state fuel,
      expectedProbeCharge ((impl input).run cache) state fuel ≤ charge input cache state fuel)
    (computation : OracleComp spec α) (cache : Cache) (state : State Coordinate) (fuel : Nat) :
    expectedProbeCharge ((simulateQ impl computation).run cache) state fuel ≤
      expectedSimulationCharge impl charge computation cache state fuel := by
  induction computation using OracleComp.inductionOn generalizing cache state fuel with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, expectedProbeCharge, expectedSimulationCharge,
        OracleComp.construct_pure, le_refl]
  | query_bind input next ih =>
      rw [simulateQ_query_bind, StateT.run_bind, expectedProbeCharge_bind,
        expectedSimulationCharge_query_bind]
      apply add_le_add (hcharge input cache state fuel)
      apply ENNReal.tsum_le_tsum
      intro result
      apply mul_le_mul' le_rfl
      cases result with
      | stopped hit => exact le_rfl
      | done nextState remaining value => exact ih value.1 value.2 nextState remaining

end SphincsSecurity.LazyRevealProbe
