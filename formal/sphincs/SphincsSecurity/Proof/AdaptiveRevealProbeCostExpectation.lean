import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.AdaptiveRevealProbeCost

namespace SphincsSecurity.AdaptiveRevealProbe

open OracleComp OracleSpec ENNReal

variable {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]

theorem expectedCost_congr {β : Type} (left right : ProbComp β) (cost : β → ℝ≥0∞)
    (hdist : evalDist left = evalDist right) :
    (∑' result, Pr[= result | left] * cost result) =
      ∑' result, Pr[= result | right] * cost result := by
  apply tsum_congr
  intro result
  rw [OracleComp.probOutput_congr (x := result) (y := result) rfl hdist]

set_option maxRecDepth 100000 in
theorem chargedExperiment_expectedCost_eq {α : Type}
    (computation : OracleComp (World Coordinate) α) (state : State Coordinate) (fuel : Nat) :
    (∑' result, Pr[= result | chargedExperiment state fuel computation] * (result.2 : ℝ≥0∞)) =
      expectedProbeCharge computation state fuel := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure result =>
      rw [chargedExperiment, tsum_probOutput_bind_mul]
      simp only [runCharged, OracleComp.construct_pure, tsum_probOutput_pure_mul,
        Nat.cast_zero, mul_zero, tsum_zero, expectedProbeCharge]
  | query_bind input next ih =>
      rw [expectedProbeCharge_query_bind]
      cases input with
      | uniform n =>
          have hdist : evalDist (chargedExperiment state fuel
              ((liftM (OracleSpec.query (spec := World Coordinate) (.uniform n)) :
                OracleComp (World Coordinate) _) >>= next)) =
              evalDist ((liftM (unifSpec.query n) : ProbComp _) >>= fun output =>
                chargedExperiment state fuel (next output)) := by
            unfold chargedExperiment
            change evalDist (sampleTable >>= fun base =>
              (liftM (unifSpec.query n) : ProbComp _) >>= fun output =>
                runCharged (extendTable state base) state fuel (next output)) = _
            exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
          rw [expectedCost_congr _ _ _ hdist, tsum_probOutput_bind_mul]
          simp_rw [ih]
      | hashOutput =>
          have hdist : evalDist (chargedExperiment state fuel
              ((liftM (OracleSpec.query (spec := World Coordinate) .hashOutput) :
                OracleComp (World Coordinate) HashOutput) >>= next)) =
              evalDist (sampleHashOutput >>= fun output =>
                chargedExperiment state fuel (next output)) := by
            unfold chargedExperiment
            change evalDist (sampleTable >>= fun base => sampleHashOutput >>= fun output =>
              runCharged (extendTable state base) state fuel (next output)) = _
            exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
          rw [expectedCost_congr _ _ _ hdist, tsum_probOutput_bind_mul]
          simp_rw [ih]
      | probe coordinate candidate =>
          cases fuel with
          | zero =>
              rw [chargedExperiment, tsum_probOutput_bind_mul]
              simp only [runCharged, OracleComp.construct_query_bind, tsum_probOutput_pure_mul,
                Nat.cast_zero, mul_zero, tsum_zero]
          | succ remaining =>
              cases hrevealed : state.revealed coordinate with
              | some value =>
                  simp only [hrevealed]
                  have heq : chargedExperiment state (remaining + 1)
                      ((liftM (OracleSpec.query (spec := World Coordinate) (.probe coordinate candidate)) :
                        OracleComp (World Coordinate) Unit) >>= next) =
                      chargedExperiment state remaining (next ()) := by
                    unfold chargedExperiment
                    apply bind_congr
                    intro base
                    rw [runCharged, OracleComp.construct_query_bind]
                    simp only [hrevealed]
                    rfl
                  rw [heq]
                  exact ih () state remaining
              | none =>
                  simp only [hrevealed]
                  have heq : chargedExperiment state (remaining + 1)
                      ((liftM (OracleSpec.query (spec := World Coordinate) (.probe coordinate candidate)) :
                        OracleComp (World Coordinate) Unit) >>= next) =
                      (fun result : DetailedResult Coordinate α × Nat => (result.1, result.2 + pendingProbeCharge state coordinate candidate)) <$>
                        chargedExperiment (state.addPending coordinate candidate) remaining (next ()) := by
                    unfold chargedExperiment
                    rw [map_bind]
                    apply bind_congr
                    intro base
                    rw [runCharged, OracleComp.construct_query_bind]
                    simp only [hrevealed]
                    rfl
                  rw [heq, tsum_probOutput_map_mul]
                  simp only [Nat.cast_add, mul_add]
                  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right,
                    tsum_probOutput_of_liftM_PMF, one_mul, ih, add_comm]
      | reveal coordinate =>
          cases hrevealed : state.revealed coordinate with
          | some value =>
              simp only [hrevealed]
              have heq : chargedExperiment state fuel
                  ((liftM (OracleSpec.query (spec := World Coordinate) (.reveal coordinate)) :
                    OracleComp (World Coordinate) Digest) >>= next) =
                  chargedExperiment state fuel (next value) := by
                unfold chargedExperiment
                apply bind_congr
                intro base
                rw [runCharged, OracleComp.construct_query_bind]
                simp only [hrevealed]
                rfl
              rw [heq]
              exact ih value state fuel
          | none =>
              simp only [hrevealed]
              let resume : Digest → ProbComp (DetailedResult Coordinate α × Nat) := fun value =>
                if value ∈ state.pending coordinate then pure (.stopped true, 0)
                else chargedExperiment (state.install coordinate value) fuel (next value)
              have hdist : evalDist (chargedExperiment state fuel
                  ((liftM (OracleSpec.query (spec := World Coordinate) (.reveal coordinate)) :
                    OracleComp (World Coordinate) Digest) >>= next)) =
                  evalDist (($ᵗ Digest : ProbComp Digest) >>= resume) := by
                unfold chargedExperiment
                change evalDist (sampleTable >>= fun base =>
                  match state.revealed coordinate with
                  | some value => runCharged (extendTable state base) state fuel (next value)
                  | none =>
                      if extendTable state base coordinate ∈ state.pending coordinate then pure (.stopped true, 0)
                      else runCharged (extendTable state base)
                        (state.install coordinate (extendTable state base coordinate)) fuel
                        (next (extendTable state base coordinate))) = _
                simp only [hrevealed]
                exact evalDist_sample_applyReveal_result (.stopped true, 0) state coordinate hrevealed
                  (fun table value nextState => runCharged table nextState fuel (next value))
              rw [expectedCost_congr _ _ _ hdist, tsum_probOutput_bind_mul]
              apply tsum_congr
              intro value
              dsimp only [resume]
              by_cases hhit : value ∈ state.pending coordinate
              · simp only [hhit, ↓reduceIte, tsum_probOutput_pure_mul, Nat.cast_zero, mul_zero]
              · simp only [hhit, ↓reduceIte, ih]

theorem chargedExperiment_probability_le_expectedCost {α : Type} [Nonempty Coordinate]
    (fuel : Nat) (computation : OracleComp (World Coordinate) α) :
    Pr[fun result => result.1.hit = true | chargedExperiment State.empty fuel computation] ≤
      (∑' result, Pr[= result | chargedExperiment State.empty fuel computation] * (result.2 : ℝ≥0∞)) *
        (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  rw [chargedExperiment_expectedCost_eq]
  have heq : Pr[fun result => result.1.hit = true | chargedExperiment State.empty fuel computation] =
      Pr[fun hit : Bool => hit = true | experiment State.empty fuel computation] := by
    rw [← chargedExperiment_hit_eq, probEvent_map]
    rfl
  rw [heq]
  exact experiment_empty_probability_le_expectedProbeCharge fuel computation

end SphincsSecurity.AdaptiveRevealProbe
