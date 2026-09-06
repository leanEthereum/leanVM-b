import SphincsSecurity.Proof.AdaptiveRevealProbeCostProbeFree

namespace SphincsSecurity.AdaptiveRevealProbe

open _root_.OracleComp OracleSpec ENNReal
variable {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]

noncomputable def expectedRunChargedCost (table : Coordinate → Digest) (state : State Coordinate) (fuel : Nat)
    (computation : OracleComp (World Coordinate) α) : ENNReal :=
  ∑' result, Pr[= result | runCharged table state fuel computation] * (result.2 : ENNReal)

theorem expectedRunChargedCost_pure (table : Coordinate → Digest) (state : State Coordinate) (fuel : Nat) (value : α) :
    expectedRunChargedCost table state fuel (pure value) = 0 := by
  simp only [expectedRunChargedCost, runCharged, construct_pure, tsum_probOutput_pure_mul, Nat.cast_zero]

theorem expectedRunChargedCost_probeFree
    (table : Coordinate → Digest) (state : State Coordinate) (fuel : Nat)
    (computation : OracleComp (World Coordinate) α) (hfree : computation.IsQueryBoundP IsProbe 0) :
    expectedRunChargedCost table state fuel computation = 0 := by
  rw [expectedRunChargedCost, runCharged_probeFree table state fuel computation hfree, tsum_probOutput_map_mul]
  simp only [Nat.cast_zero, mul_zero, tsum_zero]

theorem expectedRunChargedCost_bind_of_resume
    (table : Coordinate → Digest) (state : State Coordinate) (fuel remaining charge : Nat)
    (left : OracleComp (World Coordinate) α) (next : α → OracleComp (World Coordinate) β)
    (hresume : runCharged table state fuel (left >>= next) =
      runDetailed table state fuel left >>= fun result =>
        match result with
        | .stopped hit => pure ((DetailedResult.stopped hit : DetailedResult Coordinate β), charge)
        | .done _ finalState value => (fun result => (result.1, result.2 + charge)) <$>
            runCharged table finalState remaining (next value)) :
    expectedRunChargedCost table state fuel (left >>= next) = (charge : ENNReal) +
      ∑' result, Pr[= result | runDetailed table state fuel left] *
        match result with
        | .stopped _ => 0
        | .done _ finalState value => expectedRunChargedCost table finalState remaining (next value) := by
  unfold expectedRunChargedCost
  rw [hresume, tsum_probOutput_bind_mul]
  have hcost (result : DetailedResult Coordinate α) :
      (∑' final, Pr[= final | (match result with
        | .stopped hit => pure ((DetailedResult.stopped hit : DetailedResult Coordinate β), charge)
        | .done _ finalState value => (fun result : DetailedResult Coordinate β × Nat => (result.1, result.2 + charge)) <$>
            runCharged table finalState remaining (next value))] * (final.2 : ENNReal)) =
        (charge : ENNReal) + match result with
        | .stopped _ => 0
        | .done _ finalState value => ∑' final, Pr[= final | runCharged table finalState remaining (next value)] * (final.2 : ENNReal) := by
    cases result with
    | stopped hit => simp only [tsum_probOutput_pure_mul, add_zero]
    | done hit finalState value =>
        rw [tsum_probOutput_map_mul]
        simp only [Nat.cast_add, mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul, add_comm]
  calc
    _ = ∑' result, Pr[= result | runDetailed table state fuel left] *
        ((charge : ENNReal) + match result with
        | .stopped _ => 0
        | .done _ finalState value => ∑' final, Pr[= final | runCharged table finalState remaining (next value)] * (final.2 : ENNReal)) := by
      apply tsum_congr
      intro result
      congr 1
      cases result with
      | stopped hit => exact hcost (.stopped hit)
      | done hit finalState value => exact hcost (.done hit finalState value)
    _ = _ := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]

end SphincsSecurity.AdaptiveRevealProbe
