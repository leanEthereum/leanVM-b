import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootLazyEagerObservation
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootLazyEagerState

/-!
# Synchronized lazy and eager suffixes

Once both executions store the selected root, a safe pending difference at that root is preserved by every lazy-oracle computation. The eager observation log is the installed-root image of the lazy log.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def ObservedSafeTargetPendingRel
    (target : Position) (output : HashOutput) :
    Option (ObservedCleanRunResult α) → Option (ObservedCleanRunResult α) → Prop
  | none, none => True
  | some left, some right =>
      left.value = right.value ∧
        left.table = right.table ∧
        left.remaining = right.remaining ∧
        right.observations =
          left.observations.map (installPositionValueAtProbe target output) ∧
        SafeTargetPendingLE target output left.state right.state
  | _, _ => False

theorem ObservedSafeTargetPendingRel.pure
    (target : Position) (output : HashOutput)
    (leftObservations rightObservations : List CleanProbeObservation)
    (leftState rightState : LazyRevealProbe.State Coordinate)
    (fuel : Nat) (value : α) (table : OtsSecretIndex → HashOutput)
    (hobservations : rightObservations =
      leftObservations.map (installPositionValueAtProbe target output))
    (hstate : SafeTargetPendingLE target output leftState rightState) :
    ObservedSafeTargetPendingRel target output
      (some ⟨leftState, fuel, value, table, leftObservations⟩)
      (some ⟨rightState, fuel, value, table, rightObservations⟩) := by
  exact ⟨rfl, rfl, rfl, hobservations, hstate⟩

set_option maxRecDepth 100000 in
theorem relTriple_runObservedCleanFromTable_safeTargetPending
    (target : Position) (output : HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (leftObservations rightObservations : List CleanProbeObservation)
    (leftState rightState : LazyRevealProbe.State Coordinate)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hobservations : rightObservations =
      leftObservations.map (installPositionValueAtProbe target output))
    (hstate : SafeTargetPendingLE target output leftState rightState) :
    RelTriple
      (runObservedCleanFromTable leftObservations leftState fuel table computation)
      (runObservedCleanFromTable rightObservations rightState fuel table computation)
      (ObservedSafeTargetPendingRel target output) := by
  induction computation using OracleComp.inductionOn generalizing
      leftObservations rightObservations leftState rightState fuel with
  | pure value =>
      rw [runObservedCleanFromTable, OracleComp.construct_pure,
        runObservedCleanFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure
        (ObservedSafeTargetPendingRel.pure target output leftObservations rightObservations
          leftState rightState fuel value table hobservations hstate)
  | query_bind query next ih =>
      rw [runObservedCleanFromTable, OracleComp.construct_query_bind,
        runObservedCleanFromTable, OracleComp.construct_query_bind]
      cases query with
      | uniform n =>
          apply relTriple_bind (relTriple_refl (liftM (unifSpec.query n)))
          intro leftValue rightValue hvalue
          subst rightValue
          exact ih leftValue leftObservations rightObservations leftState rightState fuel
            hobservations hstate
      | hashOutput =>
          apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
          intro leftValue rightValue hvalue
          subst rightValue
          exact ih leftValue leftObservations rightObservations leftState rightState fuel
            hobservations hstate
      | ensure coordinate =>
          exact ih () leftObservations rightObservations
            (leftState.ensure coordinate) (rightState.ensure coordinate) fuel
            hobservations (hstate.ensure coordinate)
      | probe coordinate candidate =>
          cases fuel with
          | zero =>
              exact relTriple_pure_pure (by
                simp [ObservedSafeTargetPendingRel])
          | succ remaining =>
              let leftObservation := cleanProbeObservation leftState coordinate candidate
              let rightObservation := cleanProbeObservation rightState coordinate candidate
              have hrightObservation : rightObservation = leftObservation := by
                unfold leftObservation rightObservation cleanProbeObservation
                simp [hstate.values, hstate.revealed]
              have hnextObservations :
                  rightObservations ++ [rightObservation] =
                    (leftObservations ++ [leftObservation]).map
                      (installPositionValueAtProbe target output) := by
                rw [List.map_append, hobservations, hrightObservation]
                simp [leftObservation,
                  installPositionValueAtProbe_cleanProbeObservation_eq_self target output
                    leftState hstate.target_value]
              have hrevealed : coordinate ∈ leftState.revealed ↔
                  coordinate ∈ rightState.revealed := by
                rw [hstate.revealed]
              by_cases hleftRevealed : coordinate ∈ leftState.revealed
              · have hrightRevealed : coordinate ∈ rightState.revealed :=
                  hrevealed.mp hleftRevealed
                simp only [hleftRevealed, hrightRevealed, ↓reduceIte]
                exact ih () (leftObservations ++ [leftObservation])
                  (rightObservations ++ [rightObservation]) leftState rightState remaining
                  hnextObservations hstate
              · have hrightRevealed : coordinate ∉ rightState.revealed := by
                  simpa [hrevealed] using hleftRevealed
                simp only [hleftRevealed, hrightRevealed, ↓reduceIte]
                exact ih () (leftObservations ++ [leftObservation])
                  (rightObservations ++ [rightObservation])
                  (leftState.addPending coordinate candidate)
                  (rightState.addPending coordinate candidate) remaining
                  hnextObservations (hstate.addPending coordinate candidate)
      | peek coordinate =>
          simp only
          have hvalue : leftState.values coordinate = rightState.values coordinate := by
            rw [hstate.values]
          rw [hvalue]
          exact ih (rightState.values coordinate) leftObservations rightObservations
            leftState rightState fuel hobservations hstate
      | publish coordinate =>
          simp only
          exact ih () leftObservations rightObservations
            (leftState.publish coordinate) (rightState.publish coordinate) fuel
            hobservations (hstate.publish coordinate)
      | reveal coordinate =>
          simp only
          have hvalue : leftState.values coordinate = rightState.values coordinate := by
            rw [hstate.values]
          cases hrightValue : rightState.values coordinate with
          | some value =>
              have hleftValue : leftState.values coordinate = some value := by
                rw [hvalue, hrightValue]
              simp only [hleftValue]
              exact ih value leftObservations rightObservations leftState rightState fuel
                hobservations hstate
          | none =>
              have hleftValue : leftState.values coordinate = none := by
                rw [hvalue, hrightValue]
              simp only [hleftValue]
              have hne : coordinate ≠ .position target := by
                intro heq
                subst coordinate
                rw [hstate.right_target_value] at hrightValue
                simp at hrightValue
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let value := table ⟨lay, tree, leafIdx, chainIdx⟩
                  have hhit := hstate.hitAt_iff_of_ne
                    (.chainStart lay tree leafIdx chainIdx) value (by simp)
                  by_cases hleftHit : leftState.hitAt
                      (.chainStart lay tree leafIdx chainIdx) value
                  · have hrightHit := hhit.mp hleftHit
                    simp only [value, hleftHit, hrightHit, ↓reduceIte]
                    exact relTriple_pure_pure (by simp [ObservedSafeTargetPendingRel])
                  · have hrightHit : ¬rightState.hitAt
                        (.chainStart lay tree leafIdx chainIdx) value := by
                      simpa [hhit] using hleftHit
                    simp only [value, hleftHit, hrightHit, ↓reduceIte]
                    exact ih value leftObservations rightObservations
                      (leftState.materialize (.chainStart lay tree leafIdx chainIdx) value)
                      (rightState.materialize (.chainStart lay tree leafIdx chainIdx) value) fuel
                      hobservations
                      (hstate.materialize_of_ne (.chainStart lay tree leafIdx chainIdx) value
                        (by simp))
              | position position =>
                  have hposition : Coordinate.position position ≠ .position target := hne
                  apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
                  intro leftOutput rightOutput houtput
                  subst rightOutput
                  have hhit := hstate.hitAt_iff_of_ne (.position position) leftOutput hposition
                  by_cases hleftHit : leftState.hitAt (.position position) leftOutput
                  · have hrightHit := hhit.mp hleftHit
                    simp only [hleftHit, hrightHit, ↓reduceIte]
                    exact relTriple_pure_pure (by simp [ObservedSafeTargetPendingRel])
                  · have hrightHit : ¬rightState.hitAt (.position position) leftOutput := by
                      simpa [hhit] using hleftHit
                    simp only [hleftHit, hrightHit, ↓reduceIte]
                    exact ih leftOutput leftObservations rightObservations
                      (leftState.materialize (.position position) leftOutput)
                      (rightState.materialize (.position position) leftOutput) fuel
                      hobservations
                      (hstate.materialize_of_ne (.position position) leftOutput hposition)

end SphincsSecurity.Concrete.OtsProbeSimulation
