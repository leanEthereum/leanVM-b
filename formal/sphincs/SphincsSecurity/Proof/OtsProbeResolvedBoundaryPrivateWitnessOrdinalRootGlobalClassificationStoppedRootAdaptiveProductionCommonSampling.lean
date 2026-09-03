import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveProductionCommonCacheLift

/-!
# Continuation-aware one-cell factorization

The distinguished uniform sample remains outside a target-peek-free computation until that
computation reveals the target. This form composes with a recursive outer selector without
conditioning away the sample's independence.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem relTriple_sample_preload_runPermissiveFromTable_then
    (target : Position)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (leftFinish : Option (CleanRunResult α) → ProbComp β)
    (rightFinish : Option (CleanRunResult α) → ProbComp γ)
    (relation : β → γ → Prop)
    (hvalue : state.values (.position target) = none)
    (hnoPeek : computation.IsQueryBoundP (IsTargetPeek target) 0)
    (hpreloaded : ∀ nextState remaining value nextTable,
      nextState.values (.position target) = none →
      RelTriple
        (LazyRevealProbe.sampleHashOutput >>= fun output =>
          leftFinish (some ⟨preloadPositionValue target output nextState,
            remaining, value, nextTable⟩))
        (rightFinish (some ⟨nextState, remaining, value, nextTable⟩)) relation)
    (hsynchronized : ∀ left right,
      PermissiveCleanRel left right →
      RelTriple (leftFinish left) (rightFinish right) relation) :
    RelTriple
      (LazyRevealProbe.sampleHashOutput >>= fun output =>
        runPermissiveFromTable (preloadPositionValue target output state) fuel table computation >>=
          leftFinish)
      (runPermissiveFromTable state fuel table computation >>= rightFinish)
      relation := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure value =>
      simp only [runPermissiveFromTable, OracleComp.construct_pure, pure_bind]
      exact hpreloaded state fuel value table hvalue
  | query_bind query next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hnoPeek
      have hnext : ∀ output, (next output).IsQueryBoundP (IsTargetPeek target) 0 := by
        intro output
        simpa using hnoPeek.2 output
      cases query with
      | uniform n =>
          simp only [runPermissiveFromTable, OracleComp.construct_query_bind, bind_assoc]
          have hleft : evalDist
              (LazyRevealProbe.sampleHashOutput >>= fun targetOutput =>
                (liftM (unifSpec.query n) >>= fun output =>
                  runPermissiveFromTable (preloadPositionValue target targetOutput state) fuel
                    table (next output) >>= leftFinish)) =
              evalDist
                (liftM (unifSpec.query n) >>= fun output =>
                  LazyRevealProbe.sampleHashOutput >>= fun targetOutput =>
                    runPermissiveFromTable (preloadPositionValue target targetOutput state) fuel
                      table (next output) >>= leftFinish) :=
            OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
          apply relTriple_of_evalDist_eq_left hleft
          apply relTriple_bind (relTriple_refl (liftM (unifSpec.query n)))
          intro leftOutput rightOutput heq
          subst rightOutput
          exact ih leftOutput state fuel hvalue (hnext leftOutput)
      | hashOutput =>
          simp only [runPermissiveFromTable, OracleComp.construct_query_bind, bind_assoc]
          have hleft : evalDist
              (LazyRevealProbe.sampleHashOutput >>= fun targetOutput =>
                (LazyRevealProbe.sampleHashOutput >>= fun output =>
                  runPermissiveFromTable (preloadPositionValue target targetOutput state) fuel
                    table (next output) >>= leftFinish)) =
              evalDist
                (LazyRevealProbe.sampleHashOutput >>= fun output =>
                  LazyRevealProbe.sampleHashOutput >>= fun targetOutput =>
                    runPermissiveFromTable (preloadPositionValue target targetOutput state) fuel
                      table (next output) >>= leftFinish) :=
            OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
          apply relTriple_of_evalDist_eq_left hleft
          apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
          intro leftOutput rightOutput heq
          subst rightOutput
          exact ih leftOutput state fuel hvalue (hnext leftOutput)
      | ensure coordinate =>
          simp only [runPermissiveFromTable, OracleComp.construct_query_bind]
          simp_rw [← preloadPositionValue_ensure]
          exact ih () (state.ensure coordinate) fuel hvalue (hnext ())
      | probe coordinate candidate =>
          simp only [runPermissiveFromTable, OracleComp.construct_query_bind]
          cases fuel with
          | zero =>
              simp only [pure_bind]
              apply relTriple_of_evalDist_eq_left
                (OracleComp.DeferredSampling.evalDist_bind_const_neverFails
                  LazyRevealProbe.sampleHashOutput (by
                    simp [LazyRevealProbe.sampleHashOutput]) (leftFinish none))
              exact hsynchronized none none trivial
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · simp only [preloadPositionValue_revealed, hrevealed, ↓reduceIte]
                exact ih () state remaining hvalue (hnext ())
              · simp only [preloadPositionValue_revealed, hrevealed, ↓reduceIte]
                simp_rw [← preloadPositionValue_addPending]
                exact ih () (state.addPending coordinate candidate) remaining hvalue (hnext ())
      | peek coordinate =>
          simp only [runPermissiveFromTable, OracleComp.construct_query_bind]
          have hne : coordinate ≠ .position target := by
            intro heq
            subst coordinate
            have hnot : ¬IsTargetPeek target
                (LazyRevealProbe.Query.peek (.position target)) := by
              simpa using hnoPeek.1
            exact hnot (by simp [IsTargetPeek])
          simp_rw [preloadPositionValue_values_of_ne target _ state coordinate hne]
          exact ih (state.values coordinate) state fuel hvalue
            (hnext (state.values coordinate))
      | publish coordinate =>
          simp only [runPermissiveFromTable, OracleComp.construct_query_bind]
          simp_rw [← preloadPositionValue_publish]
          exact ih () (state.publish coordinate) fuel hvalue (hnext ())
      | reveal coordinate =>
          simp only [runPermissiveFromTable, OracleComp.construct_query_bind]
          by_cases htarget : coordinate = .position target
          · subst coordinate
            simp only [preloadPositionValue_values_target, hvalue, bind_assoc]
            apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
            intro leftOutput rightOutput heq
            subst rightOutput
            have hstate : PermissiveStateRel
                (preloadPositionValue target leftOutput state)
                (state.materialize (.position target) leftOutput) :=
              permissiveStateRel_preload_materialize target leftOutput state
            have hrun := relTriple_runPermissiveFromTable_of_stateRel (next leftOutput)
              (preloadPositionValue target leftOutput state)
              (state.materialize (.position target) leftOutput) fuel table hstate
            exact relTriple_bind hrun hsynchronized
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
                      simp [coordinate, LazyRevealProbe.State.materialize, hvalue]
                    have hcoupling := ih output (state.materialize coordinate output) fuel
                      hvalue' (hnext output)
                    simp_rw [preloadPositionValue_materialize_of_ne target _ state coordinate
                      output htarget] at hcoupling
                    exact hcoupling
                | position position =>
                    simp only [bind_assoc]
                    have hposition : Coordinate.position position ≠ .position target := htarget
                    have hvalue' (output : HashOutput) :
                        (state.materialize (.position position) output).values
                          (.position target) = none := by
                      simp [LazyRevealProbe.State.materialize,
                        Function.update_of_ne (Ne.symm hposition), hvalue]
                    have hleft : evalDist
                        (LazyRevealProbe.sampleHashOutput >>= fun targetOutput =>
                          LazyRevealProbe.sampleHashOutput >>= fun output =>
                            runPermissiveFromTable
                                (preloadPositionValue target targetOutput
                                  (state.materialize (.position position) output))
                                fuel table (next output) >>= leftFinish) =
                        evalDist
                          (LazyRevealProbe.sampleHashOutput >>= fun output =>
                            LazyRevealProbe.sampleHashOutput >>= fun targetOutput =>
                              runPermissiveFromTable
                                  (preloadPositionValue target targetOutput
                                    (state.materialize (.position position) output))
                                  fuel table (next output) >>= leftFinish) :=
                      OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
                    simp only [preloadPositionValue_materialize_of_ne target _ state
                      (.position position) _ hposition] at hleft
                    apply relTriple_of_evalDist_eq_left hleft
                    apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
                    intro leftOutput rightOutput heq
                    subst rightOutput
                    have hcoupling := ih leftOutput
                      (state.materialize (.position position) leftOutput) fuel
                      (hvalue' leftOutput) (hnext leftOutput)
                    simp_rw [preloadPositionValue_materialize_of_ne target _ state
                      (.position position) leftOutput hposition] at hcoupling
                    change RelTriple _
                      (runPermissiveFromTable
                          (state.materialize (.position position) leftOutput) fuel table
                          (next leftOutput) >>= rightFinish)
                      relation
                    exact hcoupling

end SphincsSecurity.Concrete.OtsProbeSimulation
