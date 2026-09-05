import SphincsSecurity.Proof.OtsProbePreloadCharge

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

noncomputable def runPermissiveJointChargedFromTable
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    ProbComp (Option (CleanRunResult α) × Nat) :=
  OracleComp.construct
    (C := fun _ => LazyRevealProbe.State Coordinate → Nat → ProbComp (Option (CleanRunResult α) × Nat))
    (fun value state remaining => pure (some ⟨state, remaining, value, table⟩, 0))
    (fun input _ next state fuel =>
      match input with
      | .uniform n => do
          let output ← liftM (unifSpec.query n)
          next output state fuel
      | .hashOutput => do
          let output ← LazyRevealProbe.sampleHashOutput
          next output state fuel
      | .ensure coordinate => next () (state.ensure coordinate) fuel
      | .probe coordinate candidate =>
          match fuel with
          | 0 => pure (none, 0)
          | remaining + 1 =>
              if coordinate ∈ state.revealed then next () state remaining
              else (fun result => (result.1, result.2 +
                (unmaterializedCandidateCharge state (some ⟨coordinate, candidate⟩) +
                  materializedCandidateCharge state (some ⟨coordinate, candidate⟩)))) <$>
                next () (state.addPending coordinate candidate) remaining
      | .peek coordinate => next (state.values coordinate) state fuel
      | .publish coordinate => next () (state.publish coordinate) fuel
      | .reveal coordinate =>
          match state.values coordinate with
          | some output => next output state fuel
          | none =>
              match coordinate with
              | .chainStart lay tree leafIdx chainIdx =>
                  let output := table ⟨lay, tree, leafIdx, chainIdx⟩
                  next output (state.materialize coordinate output) fuel
              | .position _ => do
                  let output ← LazyRevealProbe.sampleHashOutput
                  next output (state.materialize coordinate output) fuel)
    computation state fuel

theorem runPermissiveJointChargedFromTable_project
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    Prod.fst <$> runPermissiveJointChargedFromTable state fuel table computation =
      runPermissiveFromTable state fuel table computation := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure value => simp only [runPermissiveJointChargedFromTable, runPermissiveFromTable,
      OracleComp.construct_pure, map_pure]
  | query_bind input next ih =>
      rw [runPermissiveJointChargedFromTable, runPermissiveFromTable,
        OracleComp.construct_query_bind, OracleComp.construct_query_bind]
      cases input with
      | uniform n =>
          rw [map_bind]
          exact bind_congr fun output => ih output state fuel
      | hashOutput =>
          rw [map_bind]
          exact bind_congr fun output => ih output state fuel
      | ensure coordinate => exact ih () (state.ensure coordinate) fuel
      | peek coordinate => exact ih (state.values coordinate) state fuel
      | publish coordinate => exact ih () (state.publish coordinate) fuel
      | probe coordinate candidate =>
          cases fuel with
          | zero => simp only [map_pure]
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · simpa only [runPermissiveJointChargedFromTable, runPermissiveFromTable, hrevealed, ↓reduceIte] using ih () state remaining
              · simpa only [runPermissiveJointChargedFromTable, runPermissiveFromTable, hrevealed, ↓reduceIte, Functor.map_map] using
                  ih () (state.addPending coordinate candidate) remaining
      | reveal coordinate =>
          dsimp only
          cases hvalue : state.values coordinate with
          | some output => exact ih output state fuel
          | none =>
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx => exact ih _ _ fuel
              | position position =>
                  rw [map_bind]
                  exact bind_congr fun output => ih output (state.materialize (.position position) output) fuel

noncomputable def finishPermissiveJointCharged
    (table : OtsSecretIndex → HashOutput) (next : α → OracleComp (LazyRevealProbe.World Coordinate) β)
    (result : Option (CleanRunResult α) × Nat) : ProbComp (Option (CleanRunResult β) × Nat) :=
  match result.1 with
  | none => pure (none, result.2)
  | some before => (fun after => (after.1, result.2 + after.2)) <$>
      runPermissiveJointChargedFromTable before.state before.remaining table (next before.value)

theorem runPermissiveJointChargedFromTable_bind
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (left : OracleComp (LazyRevealProbe.World Coordinate) α)
    (next : α → OracleComp (LazyRevealProbe.World Coordinate) β) :
    runPermissiveJointChargedFromTable state fuel table (left >>= next) =
      runPermissiveJointChargedFromTable state fuel table left >>= finishPermissiveJointCharged table next := by
  induction left using OracleComp.inductionOn generalizing state fuel with
  | pure value =>
      simp [runPermissiveJointChargedFromTable, finishPermissiveJointCharged]
  | query_bind input continuation ih =>
      rw [bind_assoc, runPermissiveJointChargedFromTable, runPermissiveJointChargedFromTable,
        OracleComp.construct_query_bind, OracleComp.construct_query_bind]
      cases input with
      | uniform n =>
          rw [bind_assoc]
          exact bind_congr fun output => ih output state fuel
      | hashOutput =>
          rw [bind_assoc]
          exact bind_congr fun output => ih output state fuel
      | ensure coordinate => exact ih () (state.ensure coordinate) fuel
      | peek coordinate => exact ih (state.values coordinate) state fuel
      | publish coordinate => exact ih () (state.publish coordinate) fuel
      | probe coordinate candidate =>
          cases fuel with
          | zero => simp [finishPermissiveJointCharged]
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · simpa only [runPermissiveJointChargedFromTable, hrevealed, ↓reduceIte] using ih () state remaining
              · simp only [hrevealed, ↓reduceIte]
                simp only [runPermissiveJointChargedFromTable] at ih
                rw [ih () (state.addPending coordinate candidate) remaining, map_bind, bind_map_left]
                apply bind_congr
                intro result
                cases result with
                | mk before cost =>
                    cases before with
                    | none => simp [finishPermissiveJointCharged]
                    | some before =>
                        simp [finishPermissiveJointCharged, Functor.map_map, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      | reveal coordinate =>
          dsimp only
          cases hvalue : state.values coordinate with
          | some output => exact ih output state fuel
          | none =>
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx => exact ih _ _ fuel
              | position position =>
                  rw [bind_assoc]
                  exact bind_congr fun output => ih output (state.materialize (.position position) output) fuel

theorem runPermissiveJointChargedFromTable_cost_le_probeBound
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (q : Nat)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe q) :
    ∀ result ∈ support (runPermissiveJointChargedFromTable state fuel table computation), result.2 ≤ q := by
  induction computation using OracleComp.inductionOn generalizing state fuel q with
  | pure value =>
      intro result hresult
      simp only [runPermissiveJointChargedFromTable, OracleComp.construct_pure,
        mem_support_pure_iff] at hresult
      rw [hresult]
      exact Nat.zero_le q
  | query_bind input next ih =>
      intro result hresult
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [runPermissiveJointChargedFromTable, OracleComp.construct_query_bind] at hresult
      cases input with
      | uniform n =>
          rw [mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output state fuel q (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output) result hrest
      | hashOutput =>
          rw [mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output state fuel q (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output) result hrest
      | ensure coordinate =>
          exact ih () (state.ensure coordinate) fuel q
            (by simpa [LazyRevealProbe.IsProbe] using hbound.2 ()) result hresult
      | peek coordinate =>
          exact ih (state.values coordinate) state fuel q
            (by simpa [LazyRevealProbe.IsProbe] using hbound.2 (state.values coordinate)) result hresult
      | publish coordinate =>
          exact ih () (state.publish coordinate) fuel q
            (by simpa [LazyRevealProbe.IsProbe] using hbound.2 ()) result hresult
      | probe coordinate candidate =>
          have hpositive : 0 < q := by simpa [LazyRevealProbe.IsProbe] using hbound.1
          have hnext : (next ()).IsQueryBoundP LazyRevealProbe.IsProbe (q - 1) := by
            simpa [LazyRevealProbe.IsProbe] using hbound.2 ()
          cases fuel with
          | zero =>
              simp only [mem_support_pure_iff] at hresult
              rw [hresult]
              exact Nat.zero_le q
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · simp only [hrevealed, ↓reduceIte] at hresult
                exact (ih () state remaining (q - 1) hnext result hresult).trans (Nat.sub_le q 1)
              · simp only [hrevealed, ↓reduceIte, support_map, Set.mem_image] at hresult
                obtain ⟨previous, hprevious, heq⟩ := hresult
                rw [← heq]
                have htail := ih () (state.addPending coordinate candidate) remaining (q - 1) hnext previous hprevious
                have hcharge := candidateCharge_sum_le_one state (some ⟨coordinate, candidate⟩)
                dsimp only
                omega
      | reveal coordinate =>
          dsimp only at hresult
          cases hvalue : state.values coordinate with
          | some output =>
              simp only [hvalue] at hresult
              exact ih output state fuel q
                (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output) result hresult
          | none =>
              simp only [hvalue] at hresult
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  exact ih _ _ fuel q (by simpa [LazyRevealProbe.IsProbe] using hbound.2 _) result hresult
              | position position =>
                  rw [mem_support_bind_iff] at hresult
                  obtain ⟨output, _houtput, hrest⟩ := hresult
                  exact ih output (state.materialize (.position position) output) fuel q
                    (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output) result hrest

theorem runPermissiveJointChargedFromTable_expectedCost_le_probeBound
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (q : Nat)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe q) :
    (∑' result, Pr[= result | runPermissiveJointChargedFromTable state fuel table computation] *
      (result.2 : ℝ≥0∞)) ≤ q := by
  calc
    _ ≤ ∑' result, Pr[= result | runPermissiveJointChargedFromTable state fuel table computation] * (q : ℝ≥0∞) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hresult : result ∈ support (runPermissiveJointChargedFromTable state fuel table computation)
      · exact mul_le_mul' le_rfl (Nat.cast_le.mpr
          (runPermissiveJointChargedFromTable_cost_le_probeBound state fuel table computation q hbound result hresult))
      · simp [probOutput_eq_zero_of_not_mem_support hresult]
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left (by positivity) tsum_probOutput_le_one

end SphincsSecurity.Concrete.OtsProbeSimulation
