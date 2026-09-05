import SphincsSecurity.Proof.OtsProbeJointCostCoupling

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

def PreloadedJointChargedRunRel (target : Position)
    (left right : Option (CleanRunResult α) × Nat) : Prop :=
  left.2 ≤ right.2 ∧ PreloadedPermissiveCleanRel target left.1 right.1

theorem jointChargedRunRel_to_preloadedJointChargedRunRel
    (target : Position) {left right : Option (CleanRunResult α) × Nat}
    (hrel : JointChargedRunRel left right) : PreloadedJointChargedRunRel target left right := by
  refine ⟨hrel.1, permissiveCleanRel_to_preloadedPermissiveCleanRel target ?_⟩
  obtain ⟨left, leftCost⟩ := left
  obtain ⟨right, rightCost⟩ := right
  have hoption := hrel.2
  cases left <;> cases right
  · trivial
  · exact False.elim hoption
  · exact False.elim hoption
  · exact ⟨⟨hoption.1.values, hoption.1.revealed⟩, hoption.2⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem relTriple_sample_preload_runPermissiveJointChargedFromTable
    (target : Position)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hvalue : state.values (.position target) = none)
    (hnoPeek : computation.IsQueryBoundP (IsTargetPeek target) 0) :
    RelTriple
      (LazyRevealProbe.sampleHashOutput >>= fun output =>
        runPermissiveJointChargedFromTable (preloadPositionValue target output state) fuel table computation)
      (runPermissiveJointChargedFromTable state fuel table computation)
      (PreloadedJointChargedRunRel target) := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure value =>
      simp only [runPermissiveJointChargedFromTable, OracleComp.construct_pure]
      apply relTriple_of_evalDist_eq_right
        (OracleComp.DeferredSampling.evalDist_bind_const_neverFails
          LazyRevealProbe.sampleHashOutput (by simp [LazyRevealProbe.sampleHashOutput]) _)
      apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
      intro output other heq
      subst other
      exact relTriple_pure_pure ⟨le_refl 0, rfl, rfl, rfl,
        Or.inr (preloadedPositionStateRel_preload target output state hvalue)⟩
  | query_bind query next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hnoPeek
      have hnext : ∀ output, (next output).IsQueryBoundP (IsTargetPeek target) 0 := by
        intro output
        simpa using hnoPeek.2 output
      cases query with
      | uniform n =>
          simp only [runPermissiveJointChargedFromTable, OracleComp.construct_query_bind]
          have hleft : evalDist
              (LazyRevealProbe.sampleHashOutput >>= fun targetOutput =>
                (liftM (unifSpec.query n) >>= fun output =>
                  runPermissiveJointChargedFromTable (preloadPositionValue target targetOutput state) fuel
                    table (next output))) =
              evalDist
                (liftM (unifSpec.query n) >>= fun output =>
                  LazyRevealProbe.sampleHashOutput >>= fun targetOutput =>
                    runPermissiveJointChargedFromTable (preloadPositionValue target targetOutput state) fuel
                      table (next output)) :=
            OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
          apply relTriple_of_evalDist_eq_left hleft
          apply relTriple_bind (relTriple_refl (liftM (unifSpec.query n)))
          intro leftOutput rightOutput heq
          subst rightOutput
          exact ih leftOutput state fuel hvalue (hnext leftOutput)
      | hashOutput =>
          simp only [runPermissiveJointChargedFromTable, OracleComp.construct_query_bind]
          have hleft : evalDist
              (LazyRevealProbe.sampleHashOutput >>= fun targetOutput =>
                (LazyRevealProbe.sampleHashOutput >>= fun output =>
                  runPermissiveJointChargedFromTable (preloadPositionValue target targetOutput state) fuel
                    table (next output))) =
              evalDist
                (LazyRevealProbe.sampleHashOutput >>= fun output =>
                  LazyRevealProbe.sampleHashOutput >>= fun targetOutput =>
                    runPermissiveJointChargedFromTable (preloadPositionValue target targetOutput state) fuel
                      table (next output)) :=
            OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
          apply relTriple_of_evalDist_eq_left hleft
          apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
          intro leftOutput rightOutput heq
          subst rightOutput
          exact ih leftOutput state fuel hvalue (hnext leftOutput)
      | ensure coordinate =>
          simp only [runPermissiveJointChargedFromTable, OracleComp.construct_query_bind]
          change RelTriple
            (LazyRevealProbe.sampleHashOutput >>= fun output =>
              runPermissiveJointChargedFromTable
                ((preloadPositionValue target output state).ensure coordinate)
                fuel table (next ()))
            (runPermissiveJointChargedFromTable (state.ensure coordinate) fuel table (next ()))
            (PreloadedJointChargedRunRel target)
          simp_rw [← preloadPositionValue_ensure]
          exact ih () (state.ensure coordinate) fuel hvalue (hnext ())
      | probe coordinate candidate =>
          simp only [runPermissiveJointChargedFromTable, OracleComp.construct_query_bind]
          cases fuel with
          | zero =>
              apply relTriple_of_evalDist_eq_left
                (OracleComp.DeferredSampling.evalDist_bind_const_neverFails
                  LazyRevealProbe.sampleHashOutput (by simp [LazyRevealProbe.sampleHashOutput]) (pure (none, 0)))
              exact relTriple_pure_pure ⟨le_refl 0, trivial⟩
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · simp only [preloadPositionValue_revealed, hrevealed, ↓reduceIte]
                exact ih () state remaining hvalue (hnext ())
              · simp only [preloadPositionValue_revealed, hrevealed, ↓reduceIte]
                simp_rw [candidateCharge_sum_preload_eq]
                rw [← map_bind]
                apply relTriple_map
                apply relTriple_post_mono
                  (ih () (state.addPending coordinate candidate) remaining hvalue (hnext ()))
                intro left right hrel
                exact ⟨Nat.add_le_add_right hrel.1 _, hrel.2⟩
      | peek coordinate =>
          simp only [runPermissiveJointChargedFromTable, OracleComp.construct_query_bind]
          have hne : coordinate ≠ .position target := by
            intro heq
            subst coordinate
            have hnot : ¬IsTargetPeek target
                (LazyRevealProbe.Query.peek (.position target)) := by
              simpa using hnoPeek.1
            exact hnot (by simp [IsTargetPeek])
          change RelTriple
            (LazyRevealProbe.sampleHashOutput >>= fun output =>
              runPermissiveJointChargedFromTable (preloadPositionValue target output state) fuel table
                (next ((preloadPositionValue target output state).values coordinate)))
            (runPermissiveJointChargedFromTable state fuel table (next (state.values coordinate)))
            (PreloadedJointChargedRunRel target)
          simp_rw [preloadPositionValue_values_of_ne target _ state coordinate hne]
          exact ih (state.values coordinate) state fuel hvalue
            (hnext (state.values coordinate))
      | publish coordinate =>
          simp only [runPermissiveJointChargedFromTable, OracleComp.construct_query_bind]
          change RelTriple
            (LazyRevealProbe.sampleHashOutput >>= fun output =>
              runPermissiveJointChargedFromTable
                ((preloadPositionValue target output state).publish coordinate)
                fuel table (next ()))
            (runPermissiveJointChargedFromTable (state.publish coordinate) fuel table (next ()))
            (PreloadedJointChargedRunRel target)
          simp_rw [← preloadPositionValue_publish]
          exact ih () (state.publish coordinate) fuel hvalue (hnext ())
      | reveal coordinate =>
          simp only [runPermissiveJointChargedFromTable, OracleComp.construct_query_bind]
          by_cases htarget : coordinate = .position target
          · subst coordinate
            simp only [preloadPositionValue_values_target, hvalue]
            apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
            intro leftOutput rightOutput heq
            subst rightOutput
            have hstate : JointChargeStateRel
                (preloadPositionValue target leftOutput state)
                (state.materialize (.position target) leftOutput) :=
              jointChargeStateRel_preload_materialize target leftOutput state
            apply relTriple_post_mono
              (relTriple_runPermissiveJointChargedFromTable_of_stateRel (next leftOutput)
                (preloadPositionValue target leftOutput state)
                (state.materialize (.position target) leftOutput) fuel table hstate)
            intro left right hrel
            exact jointChargedRunRel_to_preloadedJointChargedRunRel target hrel
          · simp_rw [preloadPositionValue_values_of_ne target _ state coordinate htarget]
            cases hcoordinateValue : state.values coordinate with
            | some output =>
                simp only
                exact ih output state fuel hvalue (hnext output)
            | none =>
                simp only
                cases coordinate with
                | chainStart lay tree leafIdx chainIdx =>
                    simp only
                    let coordinate : Coordinate := .chainStart lay tree leafIdx chainIdx
                    let output := table ⟨lay, tree, leafIdx, chainIdx⟩
                    have hvalue' : (state.materialize coordinate output).values
                        (.position target) = none := by
                      simp [coordinate, LazyRevealProbe.State.materialize,
                        hvalue]
                    have hcoupling :=
                      ih output (state.materialize coordinate output) fuel hvalue'
                        (hnext output)
                    simp_rw [preloadPositionValue_materialize_of_ne target _ state coordinate
                      output htarget] at hcoupling
                    exact hcoupling
                | position position =>
                    simp only
                    have hposition : Coordinate.position position ≠ .position target := htarget
                    have hvalue' (output : HashOutput) :
                        (state.materialize (.position position) output).values
                          (.position target) = none := by
                      simp [LazyRevealProbe.State.materialize,
                        Function.update_of_ne (Ne.symm hposition), hvalue]
                    have hleft : evalDist
                        (LazyRevealProbe.sampleHashOutput >>= fun targetOutput =>
                          LazyRevealProbe.sampleHashOutput >>= fun output =>
                            runPermissiveJointChargedFromTable
                              (preloadPositionValue target targetOutput
                                (state.materialize (.position position) output))
                              fuel table (next output)) =
                        evalDist
                          (LazyRevealProbe.sampleHashOutput >>= fun output =>
                            LazyRevealProbe.sampleHashOutput >>= fun targetOutput =>
                              runPermissiveJointChargedFromTable
                                (preloadPositionValue target targetOutput
                                  (state.materialize (.position position) output))
                                fuel table (next output)) :=
                      OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
                    simp only [preloadPositionValue_materialize_of_ne target _ state
                      (.position position) _ hposition] at hleft
                    apply relTriple_of_evalDist_eq_left hleft
                    apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
                    intro leftOutput rightOutput heq
                    subst rightOutput
                    have hcoupling :=
                      ih leftOutput (state.materialize (.position position) leftOutput) fuel
                        (hvalue' leftOutput) (hnext leftOutput)
                    simp_rw [preloadPositionValue_materialize_of_ne target _ state
                      (.position position) leftOutput hposition] at hcoupling
                    change RelTriple _
                      (runPermissiveJointChargedFromTable
                        (state.materialize (.position position) leftOutput) fuel table
                        (next leftOutput))
                      (PreloadedJointChargedRunRel target)
                    exact hcoupling


theorem sample_preload_runPermissiveJointChargedFromTable_expectedCost_le
    (target : Position)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hvalue : state.values (.position target) = none)
    (hnoPeek : computation.IsQueryBoundP (IsTargetPeek target) 0) :
    (∑' result, Pr[= result | LazyRevealProbe.sampleHashOutput >>= fun output =>
      runPermissiveJointChargedFromTable (preloadPositionValue target output state)
        fuel table computation] * (result.2 : ℝ≥0∞)) ≤
    ∑' result, Pr[= result | runPermissiveJointChargedFromTable state fuel table computation] *
      (result.2 : ℝ≥0∞) := by
  simpa using SphincsSecurity.expected_cost_le_of_relTriple
    (relTriple_sample_preload_runPermissiveJointChargedFromTable target computation state fuel table hvalue hnoPeek)
    (fun result => (result.2 : ℝ≥0∞)) (fun result => (result.2 : ℝ≥0∞)) (fun _ => 0)
    (fun _ _ hresult => by simpa using (Nat.cast_le.mpr hresult.1 : (_ : ℝ≥0∞) ≤ _))

end SphincsSecurity.Concrete.OtsProbeSimulation
