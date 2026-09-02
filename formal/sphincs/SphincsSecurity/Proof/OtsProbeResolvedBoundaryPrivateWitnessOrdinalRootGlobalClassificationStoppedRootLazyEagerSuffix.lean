import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootLazyEagerObservation
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootLazyEagerState
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalProbability

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

def FinalizedSafeTargetPendingRel
    (target : Position) (output : HashOutput) :
    Option (LazyRevealProbe.State Coordinate × (OtsSecretIndex → HashOutput)) →
      Option (LazyRevealProbe.State Coordinate × (OtsSecretIndex → HashOutput)) → Prop
  | none, none => True
  | some left, some right =>
      left.2 = right.2 ∧ SafeTargetPendingLE target output left.1 right.1
  | _, _ => False

set_option maxRecDepth 100000 in
theorem relTriple_finalizeCleanFromTable_safeTargetPending
    (target : Position) (output : HashOutput)
    (coordinates : List Coordinate)
    (left right : LazyRevealProbe.State Coordinate)
    (table : OtsSecretIndex → HashOutput)
    (hstate : SafeTargetPendingLE target output left right) :
    RelTriple
      (finalizeCleanFromTable coordinates left table)
      (finalizeCleanFromTable coordinates right table)
      (FinalizedSafeTargetPendingRel target output) := by
  induction coordinates generalizing left right with
  | nil =>
      exact relTriple_pure_pure ⟨rfl, hstate⟩
  | cons coordinate remaining ih =>
      rw [finalizeCleanFromTable.eq_def, finalizeCleanFromTable.eq_def]
      have hvalue : left.values coordinate = right.values coordinate := by
        rw [hstate.values]
      cases hrightValue : right.values coordinate with
      | some value =>
          have hleftValue : left.values coordinate = some value := by
            rw [hvalue, hrightValue]
          simp only [hleftValue, hrightValue]
          exact ih (left.clearPending coordinate) (right.clearPending coordinate)
            (hstate.clearPending coordinate)
      | none =>
          have hleftValue : left.values coordinate = none := by
            rw [hvalue, hrightValue]
          simp only [hleftValue, hrightValue]
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
              by_cases hleftHit : left.hitAt
                  (.chainStart lay tree leafIdx chainIdx) value
              · have hrightHit := hhit.mp hleftHit
                simp only [value, hleftHit, hrightHit, ↓reduceIte]
                exact relTriple_pure_pure (by trivial)
              · have hrightHit : ¬right.hitAt
                    (.chainStart lay tree leafIdx chainIdx) value := by
                  simpa [hhit] using hleftHit
                simp only [value, hleftHit, hrightHit, ↓reduceIte]
                exact ih
                  (left.complete (.chainStart lay tree leafIdx chainIdx) value)
                  (right.complete (.chainStart lay tree leafIdx chainIdx) value)
                  (hstate.complete_of_ne (.chainStart lay tree leafIdx chainIdx) value (by simp))
          | position position =>
              have hposition : Coordinate.position position ≠ .position target := hne
              apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
              intro leftOutput rightOutput houtput
              subst rightOutput
              have hhit := hstate.hitAt_iff_of_ne (.position position) leftOutput hposition
              by_cases hleftHit : left.hitAt (.position position) leftOutput
              · have hrightHit := hhit.mp hleftHit
                simp only [hleftHit, hrightHit, ↓reduceIte]
                exact relTriple_pure_pure (by trivial)
              · have hrightHit : ¬right.hitAt (.position position) leftOutput := by
                  simpa [hhit] using hleftHit
                simp only [hleftHit, hrightHit, ↓reduceIte]
                exact ih
                  (left.complete (.position position) leftOutput)
                  (right.complete (.position position) leftOutput)
                  (hstate.complete_of_ne (.position position) leftOutput hposition)

set_option maxRecDepth 100000 in
theorem relTriple_finalizeCleanFromTable_safeTargetPending_coordinates
    (target : Position) (output : HashOutput)
    (left right : LazyRevealProbe.State Coordinate)
    (table : OtsSecretIndex → HashOutput)
    (hstate : SafeTargetPendingLE target output left right) :
    RelTriple
      (finalizeCleanFromTable left.coordinates.toList left table)
      (finalizeCleanFromTable right.coordinates.toList right table)
      (FinalizedSafeTargetPendingRel target output) := by
  by_cases hleftTarget : Coordinate.position target ∈ left.coordinates
  · have hcoordinates := hstate.coordinates_eq_of_target_mem hleftTarget
    rw [← hcoordinates]
    exact relTriple_finalizeCleanFromTable_safeTargetPending target output
      left.coordinates.toList left right table hstate
  · have heval :
        evalDist (finalizeCleanFromTable right.coordinates.toList right table) =
          evalDist (finalizeCleanFromTable left.coordinates.toList left table) := by
      by_cases hrightTarget : Coordinate.position target ∈ right.coordinates
      · have herase := hstate.erase_target_coordinates_eq_of_not_mem_left hleftTarget
        have hperm : List.Perm
            (right.coordinates.toList.erase (.position target)) left.coordinates.toList := by
          apply List.perm_of_nodup_nodup_toFinset_eq
          · exact right.coordinates.nodup_toList.erase _
          · exact left.coordinates.nodup_toList
          · apply Finset.ext
            intro coordinate
            simp only [List.mem_toFinset, right.coordinates.nodup_toList.mem_erase_iff,
              Finset.mem_toList]
            rw [← Finset.mem_erase, herase]
        calc
          _ = evalDist (finalizeCleanFromTable
                (.position target :: right.coordinates.toList.erase (.position target))
                right table) :=
            evalDist_finalizeCleanFromTable_move_to_front (.position target)
              right.coordinates.toList right table (by simpa using hrightTarget)
          _ = evalDist (finalizeCleanFromTable
                (right.coordinates.toList.erase (.position target))
                (right.clearPending (.position target)) table) :=
            congrArg evalDist
              (finalizeCleanFromTable_cons_of_some (.position target)
                (right.coordinates.toList.erase (.position target)) right table output
                hstate.right_target_value)
          _ = evalDist (finalizeCleanFromTable
                (right.coordinates.toList.erase (.position target)) left table) := by
            rw [← hstate.clearPending_target_eq,
              clearPending_eq_self_of_not_mem_coordinates left (.position target) hleftTarget]
          _ = _ := evalDist_finalizeCleanFromTable_perm hperm left table
      · have heq := hstate.eq_of_target_not_mem_right_coordinates hrightTarget
        subst right
        rfl
    let run := finalizeCleanFromTable left.coordinates.toList left table
    have hbase :=
      SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support
        (relTriple_refl run) (fun result => result ∈ support run)
        (fun result hresult => hresult)
    have hpost : RelTriple run run (FinalizedSafeTargetPendingRel target output) := by
      apply relTriple_post_mono hbase
      intro leftFinal rightFinal hrelation
      obtain ⟨rfl, hleftFinal⟩ := hrelation
      cases leftFinal with
      | none => trivial
      | some final =>
          rcases final with ⟨finalState, finalTable⟩
          refine ⟨rfl, SafeTargetPendingLE.refl target output finalState ?_⟩
          exact values_eq_of_mem_finalizeCleanFromTable_of_not_mem
            (.position target) left.coordinates.toList left table output
            (by simpa using hleftTarget) hstate.target_value finalState finalTable hleftFinal
    exact relTriple_of_evalDist_eq_right heval.symm hpost

theorem relTriple_finishObservedCleanRunFromTable_safeTargetPending
    (target : Position) (output : HashOutput)
    (left right : ObservedCleanRunResult α)
    (hrel : ObservedSafeTargetPendingRel target output (some left) (some right))
    (htarget : Coordinate.position target ∈ left.state.coordinates) :
    RelTriple
      (finishObservedCleanRunFromTable (some left))
      (finishObservedCleanRunFromTable (some right))
      (ObservedSafeTargetPendingRel target output) := by
  rcases hrel with ⟨hvalue, htable, hremaining, hobservations, hstate⟩
  unfold finishObservedCleanRunFromTable
  simp only
  have hcoordinates := hstate.coordinates_eq_of_target_mem htarget
  rw [← hcoordinates, ← htable]
  apply relTriple_bind
    (relTriple_finalizeCleanFromTable_safeTargetPending target output
      left.state.coordinates.toList left.state right.state left.table hstate)
  intro leftFinal rightFinal hfinal
  cases leftFinal with
  | none =>
      cases rightFinal with
      | none => exact relTriple_pure_pure (by trivial)
      | some rightFinal => simp [FinalizedSafeTargetPendingRel] at hfinal
  | some leftFinal =>
      cases rightFinal with
      | none => simp [FinalizedSafeTargetPendingRel] at hfinal
      | some rightFinal =>
          rcases leftFinal with ⟨leftState, leftTable⟩
          rcases rightFinal with ⟨rightState, rightTable⟩
          rcases hfinal with ⟨hfinalTable, hfinalState⟩
          exact relTriple_pure_pure
            ⟨hvalue, hfinalTable, hremaining, hobservations, hfinalState⟩

theorem relTriple_finishObservedCleanRunFromTable_safeTargetPending_coordinates
    (target : Position) (output : HashOutput)
    (left right : ObservedCleanRunResult α)
    (hrel : ObservedSafeTargetPendingRel target output (some left) (some right)) :
    RelTriple
      (finishObservedCleanRunFromTable (some left))
      (finishObservedCleanRunFromTable (some right))
      (ObservedSafeTargetPendingRel target output) := by
  rcases hrel with ⟨hvalue, htable, hremaining, hobservations, hstate⟩
  unfold finishObservedCleanRunFromTable
  simp only
  rw [← htable]
  apply relTriple_bind
    (relTriple_finalizeCleanFromTable_safeTargetPending_coordinates target output
      left.state right.state left.table hstate)
  intro leftFinal rightFinal hfinal
  cases leftFinal with
  | none =>
      cases rightFinal with
      | none => exact relTriple_pure_pure (by trivial)
      | some rightFinal => simp [FinalizedSafeTargetPendingRel] at hfinal
  | some leftFinal =>
      cases rightFinal with
      | none => simp [FinalizedSafeTargetPendingRel] at hfinal
      | some rightFinal =>
          rcases leftFinal with ⟨leftState, leftTable⟩
          rcases rightFinal with ⟨rightState, rightTable⟩
          rcases hfinal with ⟨hfinalTable, hfinalState⟩
          exact relTriple_pure_pure
            ⟨hvalue, hfinalTable, hremaining, hobservations, hfinalState⟩

theorem ObservedSafeTargetPendingRel.successfulDoomedFirstRootGoodForComparisonAt
    (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (target : Position) (output : HashOutput) (rightRoot : Digest)
    (left right : ObservedCleanRunResult α)
    (hrel : ObservedSafeTargetPendingRel target output (some left) (some right))
    (hroot : IsLayerRoot target)
    (hselectedHit : ∀ selected : Fin left.observations.length,
      selected.val = ordinal →
        (left.observations.get selected).coordinate = .position target ∧
          (left.observations.get selected).revealedAtProbe = false ∧
          truncateHash output = (left.observations.get selected).candidate)
    (hactualAvoid : ∀ earlier : Fin left.observations.length,
      earlier.val < ordinal →
        (left.observations.get earlier).toProbe ≠
          ⟨.position target, truncateHash output⟩)
    (hgood : ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
      table ordinal target rightRoot (some left)) :
    ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
      table ordinal target rightRoot (some right) := by
  rcases hrel with ⟨_hvalue, _htable, _hremaining, hobservations, hstate⟩
  rcases hgood with ⟨⟨⟨hfinish, hdoomed, hfirstRoot⟩, hposition⟩, hcomparison⟩
  rcases hfinish with ⟨leftFinal, hleftFinal⟩
  have hfinishRel :=
    relTriple_finishObservedCleanRunFromTable_safeTargetPending_coordinates
      target output left right
      ⟨_hvalue, _htable, _hremaining, hobservations, hstate⟩
  obtain ⟨rightFinal?, hrightFinal, hfinalRel⟩ :=
    exists_right_mem_support_of_relTriple hfinishRel hleftFinal
  have hrightFinish : ∃ rightFinal, some rightFinal ∈ support
      (finishObservedCleanRunFromTable (some right)) := by
    cases rightFinal? with
    | none => simp [ObservedSafeTargetPendingRel] at hfinalRel
    | some rightFinal => exact ⟨rightFinal, hrightFinal⟩
  have hrightDoomed :
      ¬DeferredCompletable table (directDeferredContext right.state) := by
    intro hrightCompletable
    exact hdoomed (deferredCompletable_direct_of_probeStateLE table
      (hstate.toProbeStateLE hroot) hrightCompletable)
  rcases hfirstRoot with ⟨selected, hselected, hfirst, _hselectedRoot⟩
  have hfirstInstalled := firstExistingHiddenHitAt_map_installPositionValueAtProbe
    target output left ordinal hfirst hselectedHit hactualAvoid
  let installed : ObservedCleanRunResult α :=
    { left with observations :=
        left.observations.map (installPositionValueAtProbe target output) }
  have hfirstRight : FirstExistingHiddenHitAt right ordinal := by
    apply firstExistingHiddenHitAt_of_observations_eq installed right ordinal
    · exact hobservations.symm
    · exact hfirstInstalled
  have hpositionInstalled :
      observedFirstLayerRootPosition? ordinal (some installed) = some target := by
    exact (observedFirstLayerRootPosition?_map_installPositionValueAtProbe
      target output left ordinal).trans hposition
  have hpositionRight :
      observedFirstLayerRootPosition? ordinal (some right) = some target := by
    rw [← hpositionInstalled]
    exact (observedFirstLayerRootPosition?_eq_of_observations_eq ordinal installed right
      hobservations.symm).symm
  have hfirstRootRight := firstExistingHiddenRootHitAt_of_first_of_position
    right ordinal target hfirstRight hpositionRight
  have hcomparisonRight : CandidatesAvoidRoot target rightRoot
      (observedPrefixProbes ordinal (some right)) := by
    rw [← observedPrefixProbes_eq_of_observations_eq ordinal installed right
      hobservations.symm]
    simpa [installed] using hcomparison
  exact ⟨⟨⟨hrightFinish, hrightDoomed, hfirstRootRight⟩,
    hpositionRight⟩, hcomparisonRight⟩

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

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_observedMaterializedBoundary_safeTargetPending
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (output : HashOutput) (hroot : IsLayerRoot target)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (leftObservations rightObservations : List CleanProbeObservation)
    (leftState rightState : LazyRevealProbe.State Coordinate)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (cache : SplitHashCache)
    (hobservations : rightObservations =
      leftObservations.map (installPositionValueAtProbe target output))
    (hstate : SafeTargetPendingLE target output leftState rightState) :
    RelTriple
      (observedMaterializedBoundary parameter root ftsSecret computation leftObservations
        leftState fuel table cache)
      (observedMaterializedBoundary parameter root ftsSecret computation rightObservations
        rightState fuel table cache)
      (ObservedSafeTargetPendingRel target output) := by
  induction computation using OracleComp.inductionOn generalizing
      leftObservations rightObservations leftState rightState fuel cache with
  | pure value =>
      rw [observedMaterializedBoundary, OracleComp.construct_pure,
        observedMaterializedBoundary, OracleComp.construct_pure]
      exact relTriple_pure_pure
        (ObservedSafeTargetPendingRel.pure target output leftObservations rightObservations
          leftState rightState fuel (value, cache) table hobservations hstate)
  | query_bind query next ih =>
      rw [observedMaterializedBoundary, OracleComp.construct_query_bind,
        observedMaterializedBoundary, OracleComp.construct_query_bind]
      have continueAfter
          (leftRun rightRun : ProbComp (Option (ObservedCleanRunResult
            ((OracleWorld + SigningSpec).Range query × SplitHashCache))))
          (hrun : RelTriple leftRun rightRun
            (ObservedSafeTargetPendingRel target output)) :
          RelTriple
            (leftRun >>= fun result =>
              match result with
              | none => pure none
              | some result =>
                  observedMaterializedBoundary parameter root ftsSecret
                    (next result.value.1) result.observations result.state result.remaining table
                    result.value.2)
            (rightRun >>= fun result =>
              match result with
              | none => pure none
              | some result =>
                  observedMaterializedBoundary parameter root ftsSecret
                    (next result.value.1) result.observations result.state result.remaining table
                    result.value.2)
            (ObservedSafeTargetPendingRel target output) := by
        apply relTriple_bind hrun
        intro leftResult rightResult hresult
        cases leftResult with
        | none =>
            cases rightResult with
            | none => exact relTriple_pure_pure (by trivial)
            | some rightResult => simp [ObservedSafeTargetPendingRel] at hresult
        | some leftResult =>
            cases rightResult with
            | none => simp [ObservedSafeTargetPendingRel] at hresult
            | some rightResult =>
                simp only
                rcases hresult with
                  ⟨hvalue, _htable, hremaining, hnextObservations, hnextState⟩
                have houtput : leftResult.value.1 = rightResult.value.1 :=
                  congrArg Prod.fst hvalue
                have hnextCache : leftResult.value.2 = rightResult.value.2 :=
                  congrArg Prod.snd hvalue
                rw [← houtput, ← hnextCache, ← hremaining]
                exact ih leftResult.value.1 leftResult.observations rightResult.observations
                  leftResult.state rightResult.state leftResult.remaining leftResult.value.2
                  hnextObservations hnextState
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              change Fin (n + 1) → OracleComp (OracleWorld + SigningSpec) α at next
              simp only
              have hstep := relTriple_runObservedCleanFromTable_safeTargetPending target output
                ((splitUniformImpl n).run cache) leftObservations rightObservations leftState
                rightState fuel table hobservations hstate
              convert continueAfter _ _ hstep using 1 <;>
                apply bind_congr <;> intro result <;> cases result <;> rfl
          | inr input =>
              change HashOutput → OracleComp (OracleWorld + SigningSpec) α at next
              simp only
              let leftPublic := materializedCanonicalContext table leftState
              let rightPublic := materializedCanonicalContext table rightState
              have hpublicValues : leftPublic.state.values = rightPublic.state.values :=
                materializedCanonicalContext_values_eq_of_probeStateLE table
                  (hstate.toProbeStateLE hroot)
              have hplan : purePlanProbingHashQuery parameter input leftPublic.state =
                  purePlanProbingHashQuery parameter input rightPublic.state :=
                purePlanProbingHashQuery_eq_of_values_eq hpublicValues parameter input
              let plan := purePlanProbingHashQuery parameter input leftPublic.state
              have hexecutor :
                  probingHashQueryAfterRootAwarePublicPlan parameter input leftPublic.state plan =
                    probingHashQueryAfterRootAwarePublicPlan parameter input rightPublic.state
                      plan :=
                probingHashQueryAfterRootAwarePublicPlan_eq_of_values_eq parameter input
                  hpublicValues plan
              rw [← hplan, ← hexecutor]
              have hstep := relTriple_runObservedCleanFromTable_safeTargetPending target output
                ((probingHashQueryAfterRootAwarePublicPlan parameter input leftPublic.state
                  plan).run cache)
                leftObservations rightObservations leftState rightState fuel table hobservations
                hstate
              convert continueAfter _ _ hstep using 1 <;>
                simp only [leftPublic, plan, observedMaterializedBoundary] <;>
                apply bind_congr <;> intro result <;> cases result <;> rfl
      | inr message =>
          change Option Signature → OracleComp (OracleWorld + SigningSpec) α at next
          simp only
          have hstep := relTriple_runObservedCleanFromTable_safeTargetPending target output
            ((maskedSign parameter root ftsSecret message).run cache)
            leftObservations rightObservations leftState rightState fuel table hobservations hstate
          convert continueAfter _ _ hstep using 1 <;>
            simp only [observedMaterializedBoundary] <;>
                apply bind_congr <;> intro result <;> cases result <;> rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_observedMaterializedBoundary_after_target_resolution
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (output : HashOutput) (rightRoot : Digest)
    (ordinal : Nat) (hroot : IsLayerRoot target)
    (selection : PrivateOrdinalSelection)
    (hgood : selection.GoodForRoots target output rightRoot ordinal)
    (hcovered : PendingCoveredBy (selection.candidates.take ordinal) selection.context)
    (resolved : DeferredResolution)
    (hresolved : some resolved ∈ support
      (resolveDeferredPositionValue target selection.context))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (cache : SplitHashCache) :
    RelTriple
      (observedMaterializedBoundary parameter root ftsSecret computation observations
        (materializedDeferredState resolved.toDeferredContext) fuel table cache)
      (observedMaterializedBoundary parameter root ftsSecret computation
        (observations.map (installPositionValueAtProbe target output))
        (materializedDeferredState
          { selection.context with
            values := selection.context.values.install target output })
        fuel table cache)
      (ObservedSafeTargetPendingRel target output) := by
  apply relTriple_observedMaterializedBoundary_safeTargetPending parameter root ftsSecret target
    output hroot computation observations
    (observations.map (installPositionValueAtProbe target output))
    (materializedDeferredState resolved.toDeferredContext)
    (materializedDeferredState
      { selection.context with
        values := selection.context.values.install target output })
    fuel table cache rfl
  exact safeTargetPendingLE_of_resolveDeferredPositionValue hgood hcovered resolved hresolved

end SphincsSecurity.Concrete.OtsProbeSimulation
