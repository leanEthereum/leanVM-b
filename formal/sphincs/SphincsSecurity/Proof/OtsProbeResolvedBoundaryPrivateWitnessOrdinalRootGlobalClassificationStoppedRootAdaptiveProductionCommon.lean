import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveProductionNormalizeLift

/-!
# Common root production observer

The common selector keeps the selected structural position observable while a distinguished
position remains lazily sampled. Its split cache is completed at that position exactly when the
deferred context already contains the corresponding output.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable

noncomputable def installDeferredPositionCache
    (target : Position) (context : DeferredContext) (cache : SplitHashCache) : SplitHashCache :=
  match context.positionValue target with
  | none => cache
  | some output => replaceHiddenRootCache target output cache

theorem installDeferredPositionCache_eq_of_positionValue_eq
    (target : Position) (left right : DeferredContext) (cache : SplitHashCache)
    (hvalue : left.positionValue target = right.positionValue target) :
    installDeferredPositionCache target left cache =
      installDeferredPositionCache target right cache := by
  unfold installDeferredPositionCache
  rw [hvalue]

theorem permissiveStateRel_materializedDeferredState_of_finalizationContextEq
    (table : OtsSecretIndex → HashOutput) (left right : DeferredContext)
    (hcontext : FinalizationContextEq table (some left) (some right))
    (hvalues : left.state.values = right.state.values)
    (hrevealed : left.state.revealed = right.state.revealed) :
    PermissiveStateRel (materializedDeferredState left)
      (materializedDeferredState right) := by
  exact ⟨materializedDeferredState_values_eq_of_finalizationContextEq table left right
    hcontext hvalues, by simpa using hrevealed⟩

theorem positionValue_eq_of_finalizationContextEq
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (left right : DeferredContext)
    (hcontext : FinalizationContextEq table (some left) (some right)) :
    left.positionValue target = right.positionValue target := by
  have hvalue := congrFun hcontext.1.valueEq (Coordinate.position target)
  simpa [resolvedCompletionValue] using hvalue

structure PermissivePrivateOrdinalSelection where
  candidate : Probe
  state : LazyRevealProbe.State Coordinate
  candidates : List Probe

def erasePermissivePrivateOrdinalSelection :
    Option PermissivePrivateOrdinalSelection → Option Probe
  | none => none
  | some selection => some selection.candidate

noncomputable def permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? :
    Option PermissivePrivateOrdinalSelection → Option Position
  | none => none
  | some selection =>
      match candidateLayerRootPosition? selection.candidate with
      | none => none
      | some target =>
          if Coordinate.position target ∈ selection.state.revealed then none
          else some target

theorem permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition?_eq_some_iff
    (target : Position) (selection : Option PermissivePrivateOrdinalSelection) :
    permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target ↔
      ∃ selected, selection = some selected ∧
        candidateLayerRootPosition? selected.candidate = some target ∧
        Coordinate.position target ∉ selected.state.revealed := by
  cases selection with
  | none => simp [permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition?]
  | some selected =>
      simp only [permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition?]
      cases hposition : candidateLayerRootPosition? selected.candidate with
      | none => simp [hposition]
      | some position =>
          by_cases hrevealed : Coordinate.position position ∈ selected.state.revealed
          · simp only [hrevealed, ↓reduceIte]
            constructor
            · intro hnone
              contradiction
            · rintro ⟨other, heq, htarget, hunrevealed⟩
              cases heq
              have hpositionTarget : position = target := by
                rw [hposition] at htarget
                exact Option.some.inj htarget
              subst target
              exact False.elim (hunrevealed hrevealed)
          · simp only [hrevealed, ↓reduceIte, Option.some.injEq]
            constructor
            · intro heq
              subst position
              exact ⟨selected, rfl, hposition, hrevealed⟩
            · rintro ⟨other, heq, htarget, _hunrevealed⟩
              cases heq
              rw [hposition] at htarget
              exact Option.some.inj htarget

theorem permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition?_eq_some_of_candidate
    {target : Position} {selection : PermissivePrivateOrdinalSelection}
    (hcandidate : selection.candidate.coordinate = .position target)
    (hroot : IsLayerRoot target)
    (hunrevealed : Coordinate.position target ∉ selection.state.revealed) :
    permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? (some selection) =
      some target := by
  rw [permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition?_eq_some_iff]
  refine ⟨selection, rfl, ?_, hunrevealed⟩
  rw [candidateLayerRootPosition?_eq_some_iff]
  exact ⟨hcandidate, hroot⟩

noncomputable def finishPermissiveDetailedPrivateOrdinalSelection
    (observe : LazyRevealProbe.State Coordinate → Nat → α → SplitHashCache →
      List Probe → ProbComp (Option PermissivePrivateOrdinalSelection))
    (candidates : List Probe) : Option (CleanRunResult (α × SplitHashCache)) →
      ProbComp (Option PermissivePrivateOrdinalSelection)
  | none => pure none
  | some result =>
      observe result.state result.remaining result.value.1 result.value.2 candidates

noncomputable def permissiveDetailedRootAwareOrdinalSelection
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ProbComp (Option PermissivePrivateOrdinalSelection) := by
  classical
  exact OracleComp.construct
    (C := fun _ : OracleComp (OracleWorld + SigningSpec) α =>
      List Probe → LazyRevealProbe.State Coordinate → Nat →
        (OtsSecretIndex → HashOutput) → SplitHashCache →
          ProbComp (Option PermissivePrivateOrdinalSelection))
    (fun _value candidates state _fuel _table _cache =>
      if hselected : ordinal < candidates.length then
        pure (some ⟨candidates.get ⟨ordinal, hselected⟩, state, candidates⟩)
      else pure none)
    (fun query _next recursivelyRun candidates state fuel table cache =>
      if hselected : ordinal < candidates.length then
        pure (some ⟨candidates.get ⟨ordinal, hselected⟩, state, candidates⟩)
      else
        match query with
        | .inl (.inl n) =>
            runPermissiveFromTable state fuel table ((splitUniformImpl n).run cache) >>=
              finishPermissiveDetailedPrivateOrdinalSelection
                (fun nextState remaining value nextCache laterCandidates =>
                  recursivelyRun value laterCandidates nextState remaining table nextCache)
                candidates
        | .inl (.inr input) =>
            let nextCandidates := permissiveRootAwareCandidates parameter input table state
              candidates
            if hnextSelected : ordinal < nextCandidates.length then
              pure (some ⟨nextCandidates.get ⟨ordinal, hnextSelected⟩, state,
                nextCandidates⟩)
            else
              runPermissiveFromTable state fuel table
                  (permissiveRootAwarePublicAction parameter input table state cache) >>=
                finishPermissiveDetailedPrivateOrdinalSelection
                  (fun nextState remaining value nextCache laterCandidates =>
                    recursivelyRun value laterCandidates nextState remaining table nextCache)
                  nextCandidates
        | .inr message =>
            runPermissiveFromTable state fuel table
                ((maskedSign parameter root ftsSecret message).run cache) >>=
              finishPermissiveDetailedPrivateOrdinalSelection
                (fun nextState remaining value nextCache laterCandidates =>
                  recursivelyRun value laterCandidates nextState remaining table nextCache)
                candidates)
    computation candidates state fuel table cache

set_option maxRecDepth 100000 in
theorem map_erase_permissiveDetailedRootAwareOrdinalSelection
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    erasePermissivePrivateOrdinalSelection <$>
        permissiveDetailedRootAwareOrdinalSelection ordinal parameter root ftsSecret computation
          candidates state fuel table cache =
      permissiveRootAwareOrdinalSelection ordinal parameter root ftsSecret computation
        candidates state fuel table cache := by
  induction computation using OracleComp.inductionOn generalizing candidates state fuel cache with
  | pure value =>
      simp only [permissiveDetailedRootAwareOrdinalSelection, OracleComp.construct_pure,
        permissiveRootAwareOrdinalSelection]
      by_cases hselected : ordinal < candidates.length <;>
        simp [hselected, erasePermissivePrivateOrdinalSelection]
  | query_bind query next ih =>
      rw [permissiveDetailedRootAwareOrdinalSelection, OracleComp.construct_query_bind,
        permissiveRootAwareOrdinalSelection, OracleComp.construct_query_bind]
      by_cases hselected : ordinal < candidates.length
      · simp [hselected, erasePermissivePrivateOrdinalSelection]
      · simp only [hselected, ↓reduceDIte]
        cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                rw [map_bind]
                apply bind_congr
                intro result
                cases result with
                | none => rfl
                | some result =>
                    simp only [finishPermissiveDetailedPrivateOrdinalSelection,
                      finishPermissivePrivateOrdinalSelection]
                    exact ih result.value.1 candidates result.state result.remaining result.value.2
            | inr input =>
                simp only
                let nextCandidates :=
                  permissiveRootAwareCandidates parameter input table state candidates
                by_cases hnextSelected : ordinal < nextCandidates.length
                · simp [nextCandidates, hnextSelected, erasePermissivePrivateOrdinalSelection,
                    permissiveRootAwareHashStep, selectPermissiveOrdinal]
                · simp only [nextCandidates, hnextSelected, ↓reduceDIte,
                    permissiveRootAwareHashStep, selectPermissiveOrdinal,
                    permissiveRootAwareHashContinue]
                  rw [map_bind]
                  apply bind_congr
                  intro result
                  cases result with
                  | none => rfl
                  | some result =>
                      simp only [finishPermissiveDetailedPrivateOrdinalSelection,
                        finishPermissivePrivateOrdinalSelection]
                      exact ih result.value.1 nextCandidates result.state result.remaining
                        result.value.2
        | inr message =>
            rw [map_bind]
            apply bind_congr
            intro result
            cases result with
            | none => rfl
            | some result =>
                simp only [finishPermissiveDetailedPrivateOrdinalSelection,
                  finishPermissivePrivateOrdinalSelection]
                exact ih result.value.1 candidates result.state result.remaining result.value.2

def PermissiveDetailedSelectionRel :
    Option PermissivePrivateOrdinalSelection →
      Option PermissivePrivateOrdinalSelection → Prop
  | none, none => True
  | some left, some right =>
      left.candidate = right.candidate ∧ left.candidates = right.candidates ∧
        PermissiveStateRel left.state right.state
  | _, _ => False

def MaterializedPermissiveDetailedSelectionRel
    (target : Position) : Option Probe → Option PermissivePrivateOrdinalSelection → Prop :=
  fun materialized permissive =>
    materializedOrdinalSelectionAt target materialized →
      permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? permissive = some target

theorem relTriple_none_any_materializedPermissiveDetailedSelection
    (target : Position) (right : ProbComp (Option PermissivePrivateOrdinalSelection)) :
    RelTriple (pure none : ProbComp (Option Probe)) right
      (MaterializedPermissiveDetailedSelectionRel target) := by
  have hbase := relTriple_true (pure none : ProbComp (Option Probe)) right
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun value => value = none) (by
        intro value hvalue
        simpa using hvalue)
  apply relTriple_post_mono hsupported
  intro left right hrelation
  rw [hrelation.2]
  simp [MaterializedPermissiveDetailedSelectionRel, materializedOrdinalSelectionAt]

theorem relTriple_pure_selected_materializedPermissiveDetailedSelection
    (target : Position) (hroot : IsLayerRoot target)
    (candidate : Probe) (state : LazyRevealProbe.State Coordinate)
    (candidates : List Probe)
    (hunrevealed : Coordinate.position target ∉ state.revealed) :
    RelTriple
      (pure (some candidate) : ProbComp (Option Probe))
      (pure (some ⟨candidate, state, candidates⟩) :
        ProbComp (Option PermissivePrivateOrdinalSelection))
      (MaterializedPermissiveDetailedSelectionRel target) := by
  apply relTriple_pure_pure
  intro hselected
  exact permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition?_eq_some_of_candidate
    (by simpa [materializedOrdinalSelectionAt] using hselected) hroot hunrevealed

theorem relTriple_finishMaterializedPermissiveDetailedSelection
    (target : Position)
    (leftObserve : LazyRevealProbe.State Coordinate → Nat → α → SplitHashCache →
      List Probe → ProbComp (Option Probe))
    (rightObserve : LazyRevealProbe.State Coordinate → Nat → α → SplitHashCache →
      List Probe → ProbComp (Option PermissivePrivateOrdinalSelection))
    (candidates : List Probe)
    (left right : Option (CleanRunResult (α × SplitHashCache)))
    (hrelation : CleanPermissiveRel left right)
    (hrecursive : ∀ result : CleanRunResult (α × SplitHashCache),
      Coordinate.position target ∉ result.state.revealed →
      RelTriple
        (leftObserve result.state result.remaining result.value.1 result.value.2 candidates)
        (rightObserve result.state result.remaining result.value.1 result.value.2 candidates)
        (MaterializedPermissiveDetailedSelectionRel target)) :
    RelTriple
      (finishMaterializedPrivateOrdinalSelection
        (continueMaterializedPrivateOrdinalSelection target leftObserve) candidates left)
      (finishPermissiveDetailedPrivateOrdinalSelection rightObserve candidates right)
      (MaterializedPermissiveDetailedSelectionRel target) := by
  cases left with
  | none => exact relTriple_none_any_materializedPermissiveDetailedSelection target _
  | some left =>
      have hright : right = some left := hrelation
      subst right
      by_cases hrevealed : Coordinate.position target ∈ left.state.revealed
      · simp only [finishMaterializedPrivateOrdinalSelection,
          continueMaterializedPrivateOrdinalSelection,
          finishPermissiveDetailedPrivateOrdinalSelection, hrevealed, ↓reduceIte]
        exact relTriple_none_any_materializedPermissiveDetailedSelection target _
      · simp only [finishMaterializedPrivateOrdinalSelection,
          continueMaterializedPrivateOrdinalSelection,
          finishPermissiveDetailedPrivateOrdinalSelection, hrevealed, ↓reduceIte]
        exact hrecursive left hrevealed

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_materializedRootAware_permissiveDetailedRootAwareOrdinalSelection
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hunrevealed : Coordinate.position target ∉ state.revealed) :
    RelTriple
      (materializedActualRootAwareAvoidingOrdinalSelection ordinal parameter publicRoot target
        leftRoot rightRoot ftsSecret computation candidates state fuel table cache)
      (permissiveDetailedRootAwareOrdinalSelection ordinal parameter publicRoot ftsSecret
        computation candidates state fuel table cache)
      (MaterializedPermissiveDetailedSelectionRel target) := by
  induction computation using OracleComp.inductionOn generalizing candidates state fuel cache with
  | pure value =>
      simp only [materializedActualRootAwareAvoidingOrdinalSelection,
        materializedRootAwareAvoidingOrdinalSelection,
        permissiveDetailedRootAwareOrdinalSelection, OracleComp.construct_pure]
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte]
        exact relTriple_pure_selected_materializedPermissiveDetailedSelection target hroot
          (candidates.get ⟨ordinal, hselected⟩) state candidates hunrevealed
      · simp only [hselected, ↓reduceDIte]
        apply relTriple_pure_pure
        simp [MaterializedPermissiveDetailedSelectionRel, materializedOrdinalSelectionAt]
  | query_bind query next ih =>
      rw [materializedActualRootAwareAvoidingOrdinalSelection,
        materializedRootAwareAvoidingOrdinalSelection, OracleComp.construct_query_bind,
        permissiveDetailedRootAwareOrdinalSelection, OracleComp.construct_query_bind]
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte]
        exact relTriple_pure_selected_materializedPermissiveDetailedSelection target hroot
          (candidates.get ⟨ordinal, hselected⟩) state candidates hunrevealed
      · simp only [hselected, ↓reduceDIte]
        cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                let leftObserve : LazyRevealProbe.State Coordinate → Nat → Fin (n + 1) →
                    SplitHashCache → List Probe → ProbComp (Option Probe) :=
                  fun nextState remaining output nextCache laterCandidates =>
                    materializedActualRootAwareAvoidingOrdinalSelection ordinal parameter
                      publicRoot target leftRoot rightRoot ftsSecret (next output) laterCandidates
                      nextState remaining table nextCache
                let rightObserve : LazyRevealProbe.State Coordinate → Nat → Fin (n + 1) →
                    SplitHashCache → List Probe →
                      ProbComp (Option PermissivePrivateOrdinalSelection) :=
                  fun nextState remaining output nextCache laterCandidates =>
                    permissiveDetailedRootAwareOrdinalSelection ordinal parameter publicRoot
                      ftsSecret (next output) laterCandidates nextState remaining table nextCache
                apply relTriple_bind
                  (relTriple_runCleanFromTable_runPermissiveFromTable
                    ((splitUniformImpl n).run cache) state fuel table)
                intro leftResult rightResult hresult
                apply relTriple_finishMaterializedPermissiveDetailedSelection target leftObserve
                  rightObserve candidates leftResult rightResult hresult
                intro result hnextUnrevealed
                simpa [leftObserve, rightObserve] using
                  ih result.value.1 candidates result.state result.remaining result.value.2
                    hnextUnrevealed
            | inr input =>
                simp only
                let publicContext := materializedCanonicalContext table state
                let plan := purePlanProbingHashQuery parameter input publicContext.state
                let candidate? := rootAwareCandidateForPlan? parameter input plan
                let nextCandidates := appendPlannedCandidate candidates candidate?
                have hnextCandidates :
                    permissiveRootAwareCandidates parameter input table state candidates =
                      nextCandidates := by
                  rfl
                by_cases hnextSelected : ordinal < nextCandidates.length
                · have hleftSelected : ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state))).length := by
                    simpa [publicContext, plan, candidate?, nextCandidates] using hnextSelected
                  have hrightSelected : ordinal <
                      (permissiveRootAwareCandidates parameter input table state candidates).length :=
                    by simpa [hnextCandidates] using hnextSelected
                  simp only [hleftSelected, hrightSelected, ↓reduceDIte]
                  exact relTriple_pure_selected_materializedPermissiveDetailedSelection target
                    hroot (nextCandidates.get ⟨ordinal, hnextSelected⟩) state nextCandidates
                    hunrevealed
                · have hleftSelected : ¬ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state))).length := by
                    simpa [publicContext, plan, candidate?, nextCandidates] using hnextSelected
                  have hrightSelected : ¬ordinal <
                      (permissiveRootAwareCandidates parameter input table state candidates).length :=
                    by simpa [hnextCandidates] using hnextSelected
                  simp only [hleftSelected, hrightSelected, ↓reduceDIte]
                  by_cases hsafe : RootAwareCandidateAvoidsRoots target leftRoot rightRoot candidate?
                  · have hsafeActual : RootAwareCandidateAvoidsRoots target leftRoot rightRoot
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state)) := by
                      simpa [publicContext, plan, candidate?] using hsafe
                    simp only [hsafeActual, ↓reduceIte]
                    let leftObserve : LazyRevealProbe.State Coordinate → Nat → HashOutput →
                        SplitHashCache → List Probe → ProbComp (Option Probe) :=
                      fun nextState remaining output nextCache laterCandidates =>
                        materializedActualRootAwareAvoidingOrdinalSelection ordinal parameter
                          publicRoot target leftRoot rightRoot ftsSecret (next output)
                          laterCandidates nextState remaining table nextCache
                    let rightObserve : LazyRevealProbe.State Coordinate → Nat → HashOutput →
                        SplitHashCache → List Probe →
                          ProbComp (Option PermissivePrivateOrdinalSelection) :=
                      fun nextState remaining output nextCache laterCandidates =>
                        permissiveDetailedRootAwareOrdinalSelection ordinal parameter publicRoot
                          ftsSecret (next output) laterCandidates nextState remaining table nextCache
                    let inner :=
                      (probingHashQueryAfterRootAwarePublicPlan parameter input publicContext.state
                        plan).run cache
                    apply relTriple_bind
                      (relTriple_runCleanFromTable_runPermissiveFromTable inner state fuel table)
                    intro leftResult rightResult hresult
                    apply relTriple_finishMaterializedPermissiveDetailedSelection target
                      leftObserve rightObserve nextCandidates leftResult rightResult hresult
                    intro result hnextUnrevealed
                    simpa [leftObserve, rightObserve] using
                      ih result.value.1 nextCandidates result.state result.remaining result.value.2
                        hnextUnrevealed
                  · have hsafeActual : ¬RootAwareCandidateAvoidsRoots target leftRoot rightRoot
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state)) := by
                      simpa [publicContext, plan, candidate?] using hsafe
                    simp only [hsafeActual, ↓reduceIte]
                    exact relTriple_none_any_materializedPermissiveDetailedSelection target _
        | inr message =>
            let leftObserve : LazyRevealProbe.State Coordinate → Nat → Option Signature →
                SplitHashCache → List Probe → ProbComp (Option Probe) :=
              fun nextState remaining output nextCache laterCandidates =>
                materializedActualRootAwareAvoidingOrdinalSelection ordinal parameter publicRoot
                  target leftRoot rightRoot ftsSecret (next output) laterCandidates nextState
                  remaining table nextCache
            let rightObserve : LazyRevealProbe.State Coordinate → Nat → Option Signature →
                SplitHashCache → List Probe →
                  ProbComp (Option PermissivePrivateOrdinalSelection) :=
              fun nextState remaining output nextCache laterCandidates =>
                permissiveDetailedRootAwareOrdinalSelection ordinal parameter publicRoot ftsSecret
                  (next output) laterCandidates nextState remaining table nextCache
            apply relTriple_bind
              (relTriple_runCleanFromTable_runPermissiveFromTable
                ((maskedSign parameter publicRoot ftsSecret message).run cache) state fuel table)
            intro leftResult rightResult hresult
            apply relTriple_finishMaterializedPermissiveDetailedSelection target leftObserve
              rightObserve candidates leftResult rightResult hresult
            intro result hnextUnrevealed
            simpa [leftObserve, rightObserve] using
              ih result.value.1 candidates result.state result.remaining result.value.2
                hnextUnrevealed

theorem PermissiveDetailedSelectionRel.positionFiber_eq
    {left right : Option PermissivePrivateOrdinalSelection}
    (hrel : PermissiveDetailedSelectionRel left right) :
    permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? left =
      permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? right := by
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some right => exact False.elim hrel
  | some left =>
      cases right with
      | none => exact False.elim hrel
      | some right =>
          rcases hrel with ⟨hcandidate, _hcandidates, hstate⟩
          simp only [permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition?]
          rw [hcandidate, hstate.revealed]

theorem relTriple_finishPermissiveDetailedSelection
    (leftObserve rightObserve : LazyRevealProbe.State Coordinate → Nat → α →
      SplitHashCache → List Probe →
        ProbComp (Option PermissivePrivateOrdinalSelection))
    (leftCandidates rightCandidates : List Probe)
    (left right : Option (CleanRunResult (α × SplitHashCache)))
    (_hcandidates : leftCandidates = rightCandidates)
    (hresult : PermissiveCleanRel left right)
    (hrecursive : ∀ (leftResult rightResult : CleanRunResult (α × SplitHashCache)),
      PermissiveCleanRel (some leftResult) (some rightResult) →
      RelTriple
        (leftObserve leftResult.state leftResult.remaining leftResult.value.1
          leftResult.value.2 leftCandidates)
        (rightObserve rightResult.state rightResult.remaining rightResult.value.1
          rightResult.value.2 rightCandidates)
        PermissiveDetailedSelectionRel) :
    RelTriple
      (finishPermissiveDetailedPrivateOrdinalSelection leftObserve leftCandidates left)
      (finishPermissiveDetailedPrivateOrdinalSelection rightObserve rightCandidates right)
      PermissiveDetailedSelectionRel := by
  cases left with
  | none =>
      cases right with
      | none => exact relTriple_pure_pure trivial
      | some right => exact False.elim hresult
  | some left =>
      cases right with
      | none => exact False.elim hresult
      | some right => exact hrecursive left right hresult

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem relTriple_permissiveDetailedRootAwareOrdinalSelection_of_stateRel
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (leftCandidates rightCandidates : List Probe)
    (left right : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hcandidates : leftCandidates = rightCandidates)
    (hstate : PermissiveStateRel left right) :
    RelTriple
      (permissiveDetailedRootAwareOrdinalSelection ordinal parameter root ftsSecret computation
        leftCandidates left fuel table cache)
      (permissiveDetailedRootAwareOrdinalSelection ordinal parameter root ftsSecret computation
        rightCandidates right fuel table cache)
      PermissiveDetailedSelectionRel := by
  induction computation using OracleComp.inductionOn generalizing
      leftCandidates rightCandidates left right fuel cache with
  | pure value =>
      subst rightCandidates
      simp only [permissiveDetailedRootAwareOrdinalSelection, OracleComp.construct_pure]
      by_cases hselected : ordinal < leftCandidates.length
      · simp only [hselected, ↓reduceDIte]
        exact relTriple_pure_pure ⟨rfl, rfl, hstate⟩
      · simp only [hselected, ↓reduceDIte]
        exact relTriple_pure_pure trivial
  | query_bind query next ih =>
      subst rightCandidates
      rw [permissiveDetailedRootAwareOrdinalSelection, OracleComp.construct_query_bind,
        permissiveDetailedRootAwareOrdinalSelection, OracleComp.construct_query_bind]
      by_cases hselected : ordinal < leftCandidates.length
      · simp only [hselected, ↓reduceDIte]
        exact relTriple_pure_pure ⟨rfl, rfl, hstate⟩
      · simp only [hselected, ↓reduceDIte]
        cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                let leftObserve : LazyRevealProbe.State Coordinate → Nat → Fin (n + 1) →
                    SplitHashCache → List Probe →
                      ProbComp (Option PermissivePrivateOrdinalSelection) :=
                  fun nextState remaining output nextCache laterCandidates =>
                    permissiveDetailedRootAwareOrdinalSelection ordinal parameter root ftsSecret
                      (next output) laterCandidates nextState remaining table nextCache
                let rightObserve := leftObserve
                apply relTriple_bind
                  (relTriple_runPermissiveFromTable_of_stateRel
                    ((splitUniformImpl n).run cache) left right fuel table hstate)
                intro leftResult rightResult hresult
                apply relTriple_finishPermissiveDetailedSelection leftObserve rightObserve leftCandidates
                  leftCandidates leftResult rightResult rfl hresult
                intro nextLeft nextRight hnext
                rcases hnext with ⟨hnextState, hremaining, hvalue, htable⟩
                simpa only [leftObserve, rightObserve, hremaining, hvalue,
                  permissiveDetailedRootAwareOrdinalSelection] using
                  ih nextLeft.value.1 leftCandidates leftCandidates nextLeft.state nextRight.state
                    nextLeft.remaining nextLeft.value.2 rfl hnextState
            | inr input =>
                let leftNext :=
                  permissiveRootAwareCandidates parameter input table left leftCandidates
                let rightNext :=
                  permissiveRootAwareCandidates parameter input table right leftCandidates
                have hnext : leftNext = rightNext := by
                  exact permissiveRootAwareCandidates_eq_of_stateRel parameter input table
                    leftCandidates hstate
                by_cases hnextSelected : ordinal < leftNext.length
                · have hrightSelected : ordinal < rightNext.length := by rwa [← hnext]
                  simp only [leftNext, rightNext, hnextSelected, hrightSelected, ↓reduceDIte]
                  apply relTriple_pure_pure
                  change PermissiveDetailedSelectionRel
                    (some ⟨leftNext.get ⟨ordinal, hnextSelected⟩, left, leftNext⟩)
                    (some ⟨rightNext.get ⟨ordinal, hrightSelected⟩, right, rightNext⟩)
                  exact ⟨by
                    rw [List.get_eq_getElem, List.get_eq_getElem]
                    simpa only [hnext], hnext, hstate⟩
                · have hrightSelected : ¬ordinal < rightNext.length := by rwa [← hnext]
                  simp only [leftNext, rightNext, hnextSelected, hrightSelected, ↓reduceDIte]
                  have haction := permissiveRootAwarePublicAction_eq_of_stateRel parameter input
                    table cache hstate
                  let leftObserve : LazyRevealProbe.State Coordinate → Nat → HashOutput →
                      SplitHashCache → List Probe →
                        ProbComp (Option PermissivePrivateOrdinalSelection) :=
                    fun nextState remaining output nextCache laterCandidates =>
                      permissiveDetailedRootAwareOrdinalSelection ordinal parameter root ftsSecret
                        (next output) laterCandidates nextState remaining table nextCache
                  let rightObserve := leftObserve
                  apply relTriple_bind
                    (by
                      rw [haction]
                      exact relTriple_runPermissiveFromTable_of_stateRel _ left right fuel table
                        hstate)
                  intro leftResult rightResult hresult
                  apply relTriple_finishPermissiveDetailedSelection leftObserve rightObserve
                    leftNext rightNext
                    leftResult rightResult hnext hresult
                  intro nextLeft nextRight hnextResult
                  rcases hnextResult with ⟨hnextState, hremaining, hvalue, htable⟩
                  simpa only [leftObserve, rightObserve, hremaining, hvalue,
                    permissiveDetailedRootAwareOrdinalSelection] using
                    ih nextLeft.value.1 leftNext rightNext nextLeft.state nextRight.state
                      nextLeft.remaining nextLeft.value.2 hnext hnextState
        | inr message =>
            let leftObserve : LazyRevealProbe.State Coordinate → Nat → Option Signature →
                SplitHashCache → List Probe →
                  ProbComp (Option PermissivePrivateOrdinalSelection) :=
              fun nextState remaining output nextCache laterCandidates =>
                permissiveDetailedRootAwareOrdinalSelection ordinal parameter root ftsSecret
                  (next output) laterCandidates nextState remaining table nextCache
            let rightObserve := leftObserve
            apply relTriple_bind
              (relTriple_runPermissiveFromTable_of_stateRel
                ((maskedSign parameter root ftsSecret message).run cache)
                left right fuel table hstate)
            intro leftResult rightResult hresult
            apply relTriple_finishPermissiveDetailedSelection leftObserve rightObserve
              leftCandidates leftCandidates
              leftResult rightResult rfl hresult
            intro nextLeft nextRight hnext
            rcases hnext with ⟨hnextState, hremaining, hvalue, htable⟩
            simpa only [leftObserve, rightObserve, hremaining, hvalue,
              permissiveDetailedRootAwareOrdinalSelection] using
              ih nextLeft.value.1 leftCandidates leftCandidates nextLeft.state nextRight.state
                nextLeft.remaining nextLeft.value.2 rfl hnextState

noncomputable def permissiveDetailedRootAwarePositionFiberComplement
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (target : Position)
    (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) : ProbComp Bool := do
  let selection ← permissiveDetailedRootAwareOrdinalSelection ordinal parameter root ftsSecret
    computation candidates (materializedDeferredState context) fuel table
    (installDeferredPositionCache target context cache)
  pure (decide
    (permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection ≠ some target))

instance permissiveDetailedRootAwarePositionFiberComplement_observerSynchronized
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (target : Position)
    (table : OtsSecretIndex → HashOutput) :
    ObserverSynchronized table
      (permissiveDetailedRootAwarePositionFiberComplement ordinal parameter root ftsSecret
        computation candidates target table) where
  eq_of_synchronized left right fuel cache hcontext hvalues hrevealed := by
    have hstate :=
      permissiveStateRel_materializedDeferredState_of_finalizationContextEq table left right
        hcontext hvalues hrevealed
    have hcache := installDeferredPositionCache_eq_of_positionValue_eq target left right cache
      (positionValue_eq_of_finalizationContextEq table target left right hcontext)
    unfold permissiveDetailedRootAwarePositionFiberComplement
    rw [hcache]
    apply evalDist_eq_of_relTriple_eqRel
    apply relTriple_bind
      (relTriple_permissiveDetailedRootAwareOrdinalSelection_of_stateRel ordinal parameter root
        ftsSecret computation candidates candidates (materializedDeferredState left)
        (materializedDeferredState right) fuel table
        (installDeferredPositionCache target right cache) rfl hstate)
    intro leftSelection rightSelection hselection
    apply relTriple_pure_pure
    rw [hselection.positionFiber_eq]
    rfl

noncomputable def permissiveRootAwarePositionComplement
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (target : Position)
    (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) : ProbComp Bool := do
  let selection ← permissiveRootAwareOrdinalSelection ordinal parameter root ftsSecret
    computation candidates (materializedDeferredState context) fuel table
    (installDeferredPositionCache target context cache)
  pure (decide (¬materializedOrdinalSelectionAt target selection))

instance permissiveRootAwarePositionComplement_observerSynchronized
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (target : Position)
    (table : OtsSecretIndex → HashOutput) :
    ObserverSynchronized table
      (permissiveRootAwarePositionComplement ordinal parameter root ftsSecret computation
        candidates target table) where
  eq_of_synchronized left right fuel cache hcontext hvalues hrevealed := by
    have hstate :=
      permissiveStateRel_materializedDeferredState_of_finalizationContextEq table left right
        hcontext hvalues hrevealed
    have hcache := installDeferredPositionCache_eq_of_positionValue_eq target left right cache
      (positionValue_eq_of_finalizationContextEq table target left right hcontext)
    unfold permissiveRootAwarePositionComplement
    rw [hcache]
    apply evalDist_bind_eq_of_evalDist_eq
    exact evalDist_eq_of_relTriple_eqRel
      (relTriple_permissiveRootAwareOrdinalSelection_of_stateRel_aux ordinal parameter root
        ftsSecret computation candidates candidates (materializedDeferredState left)
        (materializedDeferredState right) fuel table
        (installDeferredPositionCache target right cache) rfl hstate)

end SphincsSecurity.Concrete.OtsProbeSimulation
