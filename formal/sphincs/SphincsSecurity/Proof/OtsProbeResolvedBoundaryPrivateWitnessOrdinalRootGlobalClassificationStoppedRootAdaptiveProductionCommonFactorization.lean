import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveProductionCommonExperiment

/-!
# One-cell lazy factorization for common root production

An eager hidden root is represented by preloading only its value. Unlike materialization, this
does not erase probes accumulated at that coordinate. The preload therefore commutes through every
answer-independent step until the first reveal consumes the same uniform output on the lazy side.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def preloadPositionValue
    (target : Position) (output : HashOutput)
    (state : LazyRevealProbe.State Coordinate) : LazyRevealProbe.State Coordinate :=
  { state with
    values := Function.update state.values (.position target) (some output)
    ensured := insert (.position target) state.ensured }

@[simp] theorem preloadPositionValue_values_target
    (target : Position) (output : HashOutput)
    (state : LazyRevealProbe.State Coordinate) :
    (preloadPositionValue target output state).values (.position target) = some output := by
  simp [preloadPositionValue]

theorem preloadPositionValue_values_of_ne
    (target : Position) (output : HashOutput)
    (state : LazyRevealProbe.State Coordinate) (coordinate : Coordinate)
    (hne : coordinate ≠ .position target) :
    (preloadPositionValue target output state).values coordinate = state.values coordinate := by
  simp [preloadPositionValue, Function.update_of_ne hne]

@[simp] theorem preloadPositionValue_revealed
    (target : Position) (output : HashOutput)
    (state : LazyRevealProbe.State Coordinate) :
    (preloadPositionValue target output state).revealed = state.revealed :=
  rfl

@[simp] theorem preloadPositionValue_ensure
    (target : Position) (output : HashOutput)
    (state : LazyRevealProbe.State Coordinate) (coordinate : Coordinate) :
    preloadPositionValue target output (state.ensure coordinate) =
      (preloadPositionValue target output state).ensure coordinate := by
  cases state
  simp [preloadPositionValue, LazyRevealProbe.State.ensure, Finset.insert_comm]

@[simp] theorem preloadPositionValue_addPending
    (target : Position) (output : HashOutput)
    (state : LazyRevealProbe.State Coordinate) (coordinate : Coordinate) (candidate : Digest) :
    preloadPositionValue target output (state.addPending coordinate candidate) =
      (preloadPositionValue target output state).addPending coordinate candidate := by
  rfl

@[simp] theorem preloadPositionValue_publish
    (target : Position) (output : HashOutput)
    (state : LazyRevealProbe.State Coordinate) (coordinate : Coordinate) :
    preloadPositionValue target output (state.publish coordinate) =
      (preloadPositionValue target output state).publish coordinate := by
  rfl

theorem preloadPositionValue_materialize_of_ne
    (target : Position) (targetOutput : HashOutput)
    (state : LazyRevealProbe.State Coordinate) (coordinate : Coordinate)
    (output : HashOutput) (hne : coordinate ≠ .position target) :
    preloadPositionValue target targetOutput (state.materialize coordinate output) =
      (preloadPositionValue target targetOutput state).materialize coordinate output := by
  cases state
  simp [preloadPositionValue, LazyRevealProbe.State.materialize,
    LazyRevealProbe.State.pendingAway, Function.update_comm hne,
    Finset.insert_comm]

theorem preloadPositionValue_eq_materialize_of_pending_eq_empty
    (target : Position) (output : HashOutput)
    (state : LazyRevealProbe.State Coordinate)
    (hpending : state.pending = ∅) :
    preloadPositionValue target output state =
      state.materialize (.position target) output := by
  cases state with
  | mk pending values revealed ensured =>
      simp only at hpending
      subst pending
      simp [preloadPositionValue, LazyRevealProbe.State.materialize,
        LazyRevealProbe.State.pendingAway]

theorem permissiveStateRel_preload_materialize
    (target : Position) (output : HashOutput)
    (state : LazyRevealProbe.State Coordinate) :
    PermissiveStateRel (preloadPositionValue target output state)
      (state.materialize (.position target) output) := by
  exact ⟨rfl, rfl⟩

theorem materializedCanonicalContext_values_preload_hidden
    (table : OtsSecretIndex → HashOutput)
    (state : LazyRevealProbe.State Coordinate) (target : Position) (output : HashOutput)
    (hhidden : Coordinate.position target ∉ state.revealed) :
    (materializedCanonicalContext table
        (preloadPositionValue target output state)).state.values =
      (materializedCanonicalContext table state).state.values := by
  calc
    _ = (materializedCanonicalContext table
          (state.materialize (.position target) output)).state.values :=
      materializedCanonicalContext_values_eq_of_permissiveStateRel table
        (permissiveStateRel_preload_materialize target output state)
    _ = _ := materializedCanonicalContext_values_materialize_hidden table state target output
      hhidden

def IsTargetPeek (target : Position) : LazyRevealProbe.Query Coordinate → Prop
  | .peek (.position position) => position = target
  | _ => False

noncomputable instance (target : Position) : DecidablePred (IsTargetPeek target) :=
  fun _query => Classical.propDecidable _

def SplitCacheEqAway (target : Position) (left right : SplitHashCache) : Prop :=
  ∀ key, key ≠ .hidden (.position target) → left key = right key

theorem splitCacheEqAway_replaceHiddenRootCache
    (target : Position) (output : HashOutput) (cache : SplitHashCache) :
    SplitCacheEqAway target (replaceHiddenRootCache target output cache) cache := by
  intro key hne
  simp [replaceHiddenRootCache, Function.update_of_ne hne]

theorem SplitCacheEqAway.update
    {target : Position} {left right : SplitHashCache}
    (hrel : SplitCacheEqAway target left right)
    (key : SplitHashKey) (output : HashOutput) :
    SplitCacheEqAway target (Function.update left key (some output))
      (Function.update right key (some output)) := by
  intro other hother
  by_cases heq : other = key
  · subst other
    simp
  · simp [Function.update_of_ne heq, hrel other hother]

theorem SplitCacheEqAway.update_target_eq
    {target : Position} {left right : SplitHashCache}
    (hrel : SplitCacheEqAway target left right) (output : HashOutput) :
    Function.update left (.hidden (.position target)) (some output) =
      Function.update right (.hidden (.position target)) (some output) := by
  funext key
  by_cases heq : key = .hidden (.position target)
  · subst key
    simp
  · simp [Function.update_of_ne heq, hrel key heq]

def PreloadedPositionStateRel
    (target : Position) (left right : LazyRevealProbe.State Coordinate) : Prop :=
  right.values (.position target) = none ∧ left.revealed = right.revealed ∧
    ∃ output, left.values = Function.update right.values (.position target) (some output)

theorem preloadedPositionStateRel_preload
    (target : Position) (output : HashOutput)
    (state : LazyRevealProbe.State Coordinate)
    (hvalue : state.values (.position target) = none) :
    PreloadedPositionStateRel target (preloadPositionValue target output state) state := by
  exact ⟨hvalue, rfl, output, rfl⟩

def PreloadedPermissiveCleanRel
    (target : Position) :
    Option (CleanRunResult α) → Option (CleanRunResult α) → Prop
  | none, none => True
  | some left, some right =>
      left.remaining = right.remaining ∧ left.value = right.value ∧ left.table = right.table ∧
        (PermissiveStateRel left.state right.state ∨
          PreloadedPositionStateRel target left.state right.state)
  | _, _ => False

theorem permissiveCleanRel_to_preloadedPermissiveCleanRel
    (target : Position) {left right : Option (CleanRunResult α)}
    (hrel : PermissiveCleanRel left right) :
    PreloadedPermissiveCleanRel target left right := by
  cases left <;> cases right <;> simp_all [PermissiveCleanRel, PreloadedPermissiveCleanRel]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem relTriple_sample_preload_runPermissiveFromTable
    (target : Position)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hvalue : state.values (.position target) = none)
    (hnoPeek : computation.IsQueryBoundP (IsTargetPeek target) 0) :
    RelTriple
      (LazyRevealProbe.sampleHashOutput >>= fun output =>
        runPermissiveFromTable (preloadPositionValue target output state) fuel table computation)
      (runPermissiveFromTable state fuel table computation)
      (PreloadedPermissiveCleanRel target) := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure value =>
      simp only [runPermissiveFromTable, OracleComp.construct_pure]
      let rightResult : Option (CleanRunResult α) :=
        some ⟨state, fuel, value, table⟩
      let leftResult (output : HashOutput) : Option (CleanRunResult α) :=
        some ⟨preloadPositionValue target output state, fuel, value, table⟩
      change RelTriple
        (LazyRevealProbe.sampleHashOutput >>= fun output =>
          pure (leftResult output))
        (pure rightResult) (PreloadedPermissiveCleanRel target)
      rw [show (pure rightResult : ProbComp _) =
          (pure () >>= fun _ => pure rightResult) by simp]
      apply relTriple_bind
        (relTriple_true LazyRevealProbe.sampleHashOutput (pure ()))
      intro output _ _
      apply relTriple_pure_pure
      simp [leftResult, rightResult, PreloadedPermissiveCleanRel,
        preloadedPositionStateRel_preload target output state hvalue]
  | query_bind query next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hnoPeek
      have hnext : ∀ output, (next output).IsQueryBoundP (IsTargetPeek target) 0 := by
        intro output
        simpa using hnoPeek.2 output
      cases query with
      | uniform n =>
          simp only [runPermissiveFromTable, OracleComp.construct_query_bind]
          have hleft : evalDist
              (LazyRevealProbe.sampleHashOutput >>= fun targetOutput =>
                (liftM (unifSpec.query n) >>= fun output =>
                  runPermissiveFromTable (preloadPositionValue target targetOutput state) fuel
                    table (next output))) =
              evalDist
                (liftM (unifSpec.query n) >>= fun output =>
                  LazyRevealProbe.sampleHashOutput >>= fun targetOutput =>
                    runPermissiveFromTable (preloadPositionValue target targetOutput state) fuel
                      table (next output)) :=
            OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
          apply relTriple_of_evalDist_eq_left hleft
          apply relTriple_bind (relTriple_refl (liftM (unifSpec.query n)))
          intro leftOutput rightOutput heq
          subst rightOutput
          exact ih leftOutput state fuel hvalue (hnext leftOutput)
      | hashOutput =>
          simp only [runPermissiveFromTable, OracleComp.construct_query_bind]
          have hleft : evalDist
              (LazyRevealProbe.sampleHashOutput >>= fun targetOutput =>
                (LazyRevealProbe.sampleHashOutput >>= fun output =>
                  runPermissiveFromTable (preloadPositionValue target targetOutput state) fuel
                    table (next output))) =
              evalDist
                (LazyRevealProbe.sampleHashOutput >>= fun output =>
                  LazyRevealProbe.sampleHashOutput >>= fun targetOutput =>
                    runPermissiveFromTable (preloadPositionValue target targetOutput state) fuel
                      table (next output)) :=
            OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
          apply relTriple_of_evalDist_eq_left hleft
          apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
          intro leftOutput rightOutput heq
          subst rightOutput
          exact ih leftOutput state fuel hvalue (hnext leftOutput)
      | ensure coordinate =>
          simp only [runPermissiveFromTable, OracleComp.construct_query_bind]
          change RelTriple
            (LazyRevealProbe.sampleHashOutput >>= fun output =>
              runPermissiveFromTable
                ((preloadPositionValue target output state).ensure coordinate)
                fuel table (next ()))
            (runPermissiveFromTable (state.ensure coordinate) fuel table (next ()))
            (PreloadedPermissiveCleanRel target)
          simp_rw [← preloadPositionValue_ensure]
          exact ih () (state.ensure coordinate) fuel hvalue (hnext ())
      | probe coordinate candidate =>
          simp only [runPermissiveFromTable, OracleComp.construct_query_bind]
          cases fuel with
          | zero =>
              change RelTriple
                (LazyRevealProbe.sampleHashOutput >>= fun _ => pure none)
                (pure none) (PreloadedPermissiveCleanRel target)
              apply relTriple_of_evalDist_eq_left
                (OracleComp.DeferredSampling.evalDist_bind_const_neverFails
                  LazyRevealProbe.sampleHashOutput (by
                    simp [LazyRevealProbe.sampleHashOutput]) (pure none))
              exact relTriple_pure_pure (by simp [PreloadedPermissiveCleanRel])
          | succ remaining =>
              change RelTriple
                (LazyRevealProbe.sampleHashOutput >>= fun output =>
                  if coordinate ∈ (preloadPositionValue target output state).revealed then
                    runPermissiveFromTable (preloadPositionValue target output state) remaining
                      table (next ())
                  else
                    runPermissiveFromTable
                      ((preloadPositionValue target output state).addPending coordinate candidate)
                      remaining table (next ()))
                (if coordinate ∈ state.revealed then
                  runPermissiveFromTable state remaining table (next ())
                else runPermissiveFromTable (state.addPending coordinate candidate) remaining
                  table (next ()))
                (PreloadedPermissiveCleanRel target)
              by_cases hrevealed : coordinate ∈ state.revealed
              · simp only [preloadPositionValue_revealed, hrevealed, ↓reduceIte]
                exact ih () state remaining hvalue (hnext ())
              · simp only [preloadPositionValue_revealed, hrevealed, ↓reduceIte]
                exact ih () (state.addPending coordinate candidate) remaining hvalue
                  (hnext ())
      | peek coordinate =>
          simp only [runPermissiveFromTable, OracleComp.construct_query_bind]
          have hne : coordinate ≠ .position target := by
            intro heq
            subst coordinate
            have hnot : ¬IsTargetPeek target
                (LazyRevealProbe.Query.peek (.position target)) := by
              simpa using hnoPeek.1
            exact hnot (by simp [IsTargetPeek])
          change RelTriple
            (LazyRevealProbe.sampleHashOutput >>= fun output =>
              runPermissiveFromTable (preloadPositionValue target output state) fuel table
                (next ((preloadPositionValue target output state).values coordinate)))
            (runPermissiveFromTable state fuel table (next (state.values coordinate)))
            (PreloadedPermissiveCleanRel target)
          simp_rw [preloadPositionValue_values_of_ne target _ state coordinate hne]
          exact ih (state.values coordinate) state fuel hvalue
            (hnext (state.values coordinate))
      | publish coordinate =>
          simp only [runPermissiveFromTable, OracleComp.construct_query_bind]
          change RelTriple
            (LazyRevealProbe.sampleHashOutput >>= fun output =>
              runPermissiveFromTable
                ((preloadPositionValue target output state).publish coordinate)
                fuel table (next ()))
            (runPermissiveFromTable (state.publish coordinate) fuel table (next ()))
            (PreloadedPermissiveCleanRel target)
          simp_rw [← preloadPositionValue_publish]
          exact ih () (state.publish coordinate) fuel hvalue (hnext ())
      | reveal coordinate =>
          simp only [runPermissiveFromTable, OracleComp.construct_query_bind]
          by_cases htarget : coordinate = .position target
          · subst coordinate
            simp only [preloadPositionValue_values_target, hvalue]
            apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
            intro leftOutput rightOutput heq
            subst rightOutput
            have hstate : PermissiveStateRel
                (preloadPositionValue target leftOutput state)
                (state.materialize (.position target) leftOutput) :=
              permissiveStateRel_preload_materialize target leftOutput state
            apply relTriple_post_mono
              (relTriple_runPermissiveFromTable_of_stateRel (next leftOutput)
                (preloadPositionValue target leftOutput state)
                (state.materialize (.position target) leftOutput) fuel table hstate)
            intro left right hrel
            exact permissiveCleanRel_to_preloadedPermissiveCleanRel target hrel
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
                            runPermissiveFromTable
                              (preloadPositionValue target targetOutput
                                (state.materialize (.position position) output))
                              fuel table (next output)) =
                        evalDist
                          (LazyRevealProbe.sampleHashOutput >>= fun output =>
                            LazyRevealProbe.sampleHashOutput >>= fun targetOutput =>
                              runPermissiveFromTable
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
                      (runPermissiveFromTable
                        (state.materialize (.position position) leftOutput) fuel table
                        (next leftOutput))
                      (PreloadedPermissiveCleanRel target)
                    exact hcoupling

end SphincsSecurity.Concrete.OtsProbeSimulation
