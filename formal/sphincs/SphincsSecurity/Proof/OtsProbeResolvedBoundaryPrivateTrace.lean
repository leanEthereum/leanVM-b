import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivatePlannedCommute

/-!
# Planned-probe hash trace

The proof-only hash handler returns the planned candidate beside the ordinary hash output. Projecting the first component recovers the concrete probing handler branch by branch.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

noncomputable def plannedProbingHashQuery (parameter : PublicParameter) (input : HashInput) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) (HashOutput × Option Probe) :=
  match decodeProbe? parameter input with
  | some candidate =>
      match decodePosition? parameter input with
      | some (.leaf lay tree leafIdx) => do
          let planned ← planLeafInputProbe input candidate lay tree leafIdx
          executeCandidate? planned
          let output ← resolveKnownInput parameter candidate.outputCoordinate input
          pure (output, planned)
      | _ => do
          probe candidate
          let output ← resolveKnownInput parameter candidate.outputCoordinate input
          pure (output, some candidate)
  | none =>
      match decodePosition? parameter input with
      | some position@(.chain _ _ _ _ _) => do
          let output ← resolveKnownInput parameter (.position position) input
          pure (output, none)
      | some position@(.leaf _ _ _) => do
          let output ← resolveKnownInput parameter (.position position) input
          pure (output, none)
      | some position@(.node _ _ _ _) => do
          let planned ← planFirstMissingInputCoordinate input 0
            (position.children.map Coordinate.position)
          executeCandidate? planned
          let output ← resolveKnownInput parameter (.position position) input
          pure (output, planned)
      | _ => do
          let output ← splitHashQuery (.ordinary input)
          pure (output, none)

set_option maxRecDepth 100000 in
theorem plannedProbingHashQuery_fst_leaf
    (parameter : PublicParameter) (input : HashInput) (candidate : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (hprobe : decodeProbe? parameter input = some candidate)
    (hposition : decodePosition? parameter input = some (.leaf lay tree leafIdx)) :
    Prod.fst <$> plannedProbingHashQuery parameter input = probingHashQuery parameter input := by
  unfold plannedProbingHashQuery probingHashQuery
  rw [hprobe, hposition]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  rw [← bind_assoc, planLeafInputProbe_execute]
  simp

set_option maxRecDepth 100000 in
theorem plannedProbingHashQuery_fst_node
    (parameter : PublicParameter) (input : HashInput)
    (lay : Layer) (tree : TreeIndex) (level : Fin maxLayerHeight)
    (nodeIdx : LeafIndex)
    (hprobe : decodeProbe? parameter input = none)
    (hposition : decodePosition? parameter input = some (.node lay tree level nodeIdx)) :
    Prod.fst <$> plannedProbingHashQuery parameter input = probingHashQuery parameter input := by
  unfold plannedProbingHashQuery probingHashQuery
  rw [hprobe, hposition]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  rw [← bind_assoc, planFirstMissingInputCoordinate_execute]
  simp

set_option maxRecDepth 100000 in
theorem plannedProbingHashQuery_fst_of_decodeProbe_some_nonleaf
    (parameter : PublicParameter) (input : HashInput) (candidate : Probe)
    (hprobe : decodeProbe? parameter input = some candidate)
    (hposition : ¬∃ lay tree leafIdx,
      decodePosition? parameter input = some (.leaf lay tree leafIdx)) :
    Prod.fst <$> plannedProbingHashQuery parameter input = probingHashQuery parameter input := by
  unfold plannedProbingHashQuery probingHashQuery
  rw [hprobe]
  cases hdecoded : decodePosition? parameter input with
  | none => simp
  | some position =>
      cases position with
      | leaf lay tree leafIdx => exact False.elim (hposition ⟨lay, tree, leafIdx, hdecoded⟩)
      | chain | node | ftsLeaf | ftsNode | ftsRoots => simp

set_option maxRecDepth 100000 in
theorem plannedProbingHashQuery_fst_of_decodeProbe_none_nonnode
    (parameter : PublicParameter) (input : HashInput)
    (hprobe : decodeProbe? parameter input = none)
    (hposition : ¬∃ lay tree level nodeIdx,
      decodePosition? parameter input = some (.node lay tree level nodeIdx)) :
    Prod.fst <$> plannedProbingHashQuery parameter input = probingHashQuery parameter input := by
  unfold plannedProbingHashQuery probingHashQuery
  rw [hprobe]
  cases hdecoded : decodePosition? parameter input with
  | none => simp
  | some position =>
      cases position with
      | node lay tree level nodeIdx =>
          exact False.elim (hposition ⟨lay, tree, level, nodeIdx, hdecoded⟩)
      | chain | leaf | ftsLeaf | ftsNode | ftsRoots => simp

noncomputable def plannedMaskedExpandedAdversaryImpl
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (query : (OracleWorld + SigningSpec).Domain) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate))
      ((OracleWorld + SigningSpec).Range query × Option Probe) := by
  cases query with
  | inl worldQuery =>
      cases worldQuery with
      | inl n =>
          exact do
            let output ← splitUniformImpl n
            pure (output, none)
      | inr input => exact plannedProbingHashQuery parameter input
  | inr message =>
      exact do
        let output ← maskedSign parameter root ftsSecret message
        pure (output, none)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem plannedMaskedExpandedAdversaryImpl_fst
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (query : (OracleWorld + SigningSpec).Domain) :
    Prod.fst <$> plannedMaskedExpandedAdversaryImpl parameter root ftsSecret query =
      maskedExpandedAdversaryImpl parameter root ftsSecret query := by
  cases query with
  | inl worldQuery =>
      cases worldQuery with
      | inl n =>
          simp [plannedMaskedExpandedAdversaryImpl, maskedExpandedAdversaryImpl,
            probingRomImpl]
      | inr input =>
          change Prod.fst <$> plannedProbingHashQuery parameter input =
            probingHashQuery parameter input
          cases hprobe : decodeProbe? parameter input with
          | some candidate =>
              cases hposition : decodePosition? parameter input with
              | none =>
                  exact plannedProbingHashQuery_fst_of_decodeProbe_some_nonleaf parameter input
                    candidate hprobe (by
                      rintro ⟨lay, tree, leafIdx, heq⟩
                      simp [hposition] at heq)
              | some position =>
                  cases position with
                  | leaf lay tree leafIdx =>
                      exact plannedProbingHashQuery_fst_leaf parameter input candidate lay tree
                        leafIdx hprobe hposition
                  | chain | node | ftsLeaf | ftsNode | ftsRoots =>
                      exact plannedProbingHashQuery_fst_of_decodeProbe_some_nonleaf parameter
                        input candidate hprobe (by
                          rintro ⟨lay, tree, leafIdx, heq⟩
                          simp [hposition] at heq)
          | none =>
              cases hposition : decodePosition? parameter input with
              | none =>
                  exact plannedProbingHashQuery_fst_of_decodeProbe_none_nonnode parameter input
                    hprobe (by
                      rintro ⟨lay, tree, level, nodeIdx, heq⟩
                      simp [hposition] at heq)
              | some position =>
                  cases position with
                  | node lay tree level nodeIdx =>
                      exact plannedProbingHashQuery_fst_node parameter input lay tree level
                        nodeIdx hprobe hposition
                  | chain | leaf | ftsLeaf | ftsNode | ftsRoots =>
                      exact plannedProbingHashQuery_fst_of_decodeProbe_none_nonnode parameter
                        input hprobe (by
                          rintro ⟨lay, tree, level, nodeIdx, heq⟩
                          simp [hposition] at heq)
  | inr message =>
      simp [plannedMaskedExpandedAdversaryImpl, maskedExpandedAdversaryImpl,
        maskedSigningImpl]

def appendPlannedCandidate (candidates : List Probe) : Option Probe → List Probe
  | none => candidates
  | some candidate => candidates ++ [candidate]

noncomputable def finishDirectDetailedPrivatePlanObserve
    (observe : DeferredContext → Nat → α → List Probe → ProbComp (Bool × List Probe))
    (candidates : List Probe) : DirectDetailedResult α → ProbComp (Bool × List Probe)
  | .stopped .privateStructuralHit => pure (true, candidates)
  | .stopped _ => pure (false, candidates)
  | .done result => observe result.context result.remaining result.value candidates

noncomputable def classifyDirectDetailedPrivatePlanObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List Probe → ProbComp (Bool × List Probe))
    (context : DeferredContext) (fuel : Nat) (value : α) (candidates : List Probe) :
    ProbComp (Bool × List Probe) := by
  classical
  exact if PrivateStructuralHit context then
      pure (true, candidates)
    else if DeferredCompletable table context then
      observe context fuel value candidates
    else
      pure (false, candidates)

noncomputable def canonicalizeDirectDetailedPrivatePlanObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List Probe → ProbComp (Bool × List Probe))
    (context : DeferredContext) (fuel : Nat) (value : α) (candidates : List Probe) :
    ProbComp (Bool × List Probe) := by
  classical
  exact if PrivateStructuralHit (canonicalizeMaterializedValues table context) then
      pure (true, candidates)
    else if PublishedValues context.state then
      classifyDirectDetailedPrivatePlanObserve table observe
        (canonicalizeMaterializedValues table context) fuel value candidates
    else
      pure (false, candidates)

noncomputable def runDirectDetailedPrivatePlanObserve
    (observe : DeferredContext → Nat → α → List Probe → ProbComp (Bool × List Probe))
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    ProbComp (Bool × List Probe) :=
  runDirectResolvedDetailedFromTable context fuel table computation >>=
    finishDirectDetailedPrivatePlanObserve observe candidates

noncomputable def directDetailedBoundaryPrivatePlanObserve
    (impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (planner : (query : spec.Domain) → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) (Option Probe))
    (computation : OracleComp spec α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) →
      List Probe → ProbComp (Bool × List Probe))
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ProbComp (Bool × List Probe) := by
  classical
  exact OracleComp.construct
    (C := fun _ : OracleComp spec α =>
      (DeferredContext → Nat → (α × SplitHashCache) →
        List Probe → ProbComp (Bool × List Probe)) →
      List Probe → DeferredContext → Nat → (OtsSecretIndex → HashOutput) →
        SplitHashCache → ProbComp (Bool × List Probe))
    (fun value observe candidates context fuel _table cache =>
      observe context fuel (value, cache) candidates)
    (fun query _next recursivelyRun observe candidates context fuel table cache =>
      runDirectResolvedDetailedFromTable context fuel table ((planner query).run cache) >>=
        fun plannedResult =>
          match plannedResult with
          | .stopped _ => pure (false, candidates)
          | .done plannedResult =>
              let nextCandidates := appendPlannedCandidate candidates plannedResult.value.1
              runDirectDetailedPrivatePlanObserve
                (canonicalizeDirectDetailedPrivatePlanObserve table
                  (fun nextContext remaining value nextCandidates =>
                    recursivelyRun value.1 observe nextCandidates nextContext remaining table
                      value.2))
                nextCandidates plannedResult.context plannedResult.remaining table
                ((impl query).run plannedResult.value.2))
    computation observe candidates context fuel table cache

noncomputable def maskedExpandedAdversaryPlanner
    (parameter : PublicParameter) (_root : Digest)
    (_ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (query : (OracleWorld + SigningSpec).Domain) :
    StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) (Option Probe) := by
  cases query with
  | inl worldQuery =>
      cases worldQuery with
      | inl _ => exact pure none
      | inr input =>
          exact match decodeProbe? parameter input with
          | some candidate =>
              match decodePosition? parameter input with
              | some (.leaf lay tree leafIdx) =>
                  planLeafInputProbe input candidate lay tree leafIdx
              | _ => pure (some candidate)
          | none =>
              match decodePosition? parameter input with
              | some position@(.node _ _ _ _) =>
                  planFirstMissingInputCoordinate input 0
                    (position.children.map Coordinate.position)
              | _ => pure none
  | inr _ => exact pure none

noncomputable def retainedResolvedFinalizationPrivatePlanObserve
    (table : OtsSecretIndex → HashOutput) (root : Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : RetainedRestResult × SplitHashCache) (candidates : List Probe) :
    ProbComp (Bool × List Probe) := do
  let hit ← retainedResolvedFinalizationPrivateObserve table root context fuel value
  pure (hit, candidates)

noncomputable def granularDetailedRetainedRestPrivatePlanObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (candidates : List Probe) :
    ProbComp (Bool × List Probe) :=
  directDetailedBoundaryPrivatePlanObserve
    (maskedExpandedAdversaryImpl parameter value.1 ftsSecret)
    (maskedExpandedAdversaryPlanner parameter value.1 ftsSecret)
    (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
    (retainedResolvedFinalizationPrivatePlanObserve table value.1)
    candidates context fuel table value.2

noncomputable def granularAllDirectBoundaryDetailedRetainedPrivatePlan
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp (Bool × List Probe) :=
  runDirectDetailedPrivatePlanObserve
    (granularDetailedRetainedRestPrivatePlanObserve adversary parameter table ftsSecret)
    []
    { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
      values := emptyDeferredStructuralValues }
    fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)

theorem evalDist_fst_finishDirectDetailedPrivatePlanObserve
    (observe : DeferredContext → Nat → α → List Probe → ProbComp (Bool × List Probe))
    (boolObserve : DeferredContext → Nat → α → ProbComp Bool)
    (candidates : List Probe) (result : DirectDetailedResult α)
    (hproject : ∀ context fuel value candidates,
      evalDist (Prod.fst <$> observe context fuel value candidates) =
        evalDist (boolObserve context fuel value)) :
    evalDist (Prod.fst <$>
        finishDirectDetailedPrivatePlanObserve observe candidates result) =
      evalDist (finishDirectDetailedPrivateObserve boolObserve result) := by
  cases result with
  | stopped reason => cases reason <;> rfl
  | done result => exact hproject result.context result.remaining result.value candidates

set_option maxRecDepth 100000 in
theorem evalDist_fst_runDirectDetailedPrivatePlanObserve
    (observe : DeferredContext → Nat → α → List Probe → ProbComp (Bool × List Probe))
    (boolObserve : DeferredContext → Nat → α → ProbComp Bool)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hproject : ∀ nextContext remaining value nextCandidates,
      evalDist (Prod.fst <$> observe nextContext remaining value nextCandidates) =
        evalDist (boolObserve nextContext remaining value)) :
    evalDist (Prod.fst <$>
        runDirectDetailedPrivatePlanObserve observe candidates context fuel table computation) =
      evalDist (runDirectDetailedPrivateObserve boolObserve context fuel table computation) := by
  unfold runDirectDetailedPrivatePlanObserve runDirectDetailedPrivateObserve
  rw [map_bind]
  apply evalDist_bind_congr
  intro result _hresult
  exact evalDist_fst_finishDirectDetailedPrivatePlanObserve observe boolObserve candidates result
    hproject

theorem evalDist_fst_classifyDirectDetailedPrivatePlanObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List Probe → ProbComp (Bool × List Probe))
    (boolObserve : DeferredContext → Nat → α → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (value : α) (candidates : List Probe)
    (hproject : ∀ nextContext remaining nextValue nextCandidates,
      evalDist (Prod.fst <$> observe nextContext remaining nextValue nextCandidates) =
        evalDist (boolObserve nextContext remaining nextValue)) :
    evalDist (Prod.fst <$>
        classifyDirectDetailedPrivatePlanObserve table observe context fuel value candidates) =
      evalDist (classifyDirectDetailedPrivateObserve table boolObserve context fuel value) := by
  unfold classifyDirectDetailedPrivatePlanObserve classifyDirectDetailedPrivateObserve
  by_cases hprivate : PrivateStructuralHit context
  · simp [hprivate]
  · simp only [hprivate, ↓reduceIte]
    by_cases hcompletable : DeferredCompletable table context
    · simpa [hcompletable] using hproject context fuel value candidates
    · simp [hcompletable]

theorem evalDist_fst_canonicalizeDirectDetailedPrivatePlanObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List Probe → ProbComp (Bool × List Probe))
    (boolObserve : DeferredContext → Nat → α → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (value : α) (candidates : List Probe)
    (hproject : ∀ nextContext remaining nextValue nextCandidates,
      evalDist (Prod.fst <$> observe nextContext remaining nextValue nextCandidates) =
        evalDist (boolObserve nextContext remaining nextValue)) :
    evalDist (Prod.fst <$> canonicalizeDirectDetailedPrivatePlanObserve table observe
        context fuel value candidates) =
      evalDist (canonicalizeDirectDetailedPrivateObserve table boolObserve
        context fuel value) := by
  unfold canonicalizeDirectDetailedPrivatePlanObserve
    canonicalizeDirectDetailedPrivateObserve
  by_cases hprivate : PrivateStructuralHit (canonicalizeMaterializedValues table context)
  · simp [hprivate]
  · simp only [hprivate, ↓reduceIte]
    by_cases hpublished : PublishedValues context.state
    · simp only [hpublished, ↓reduceIte]
      exact evalDist_fst_classifyDirectDetailedPrivatePlanObserve table observe boolObserve
        (canonicalizeMaterializedValues table context) fuel value candidates hproject
    · simp [hpublished]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem evalDist_fst_directDetailedBoundaryPrivatePlanObserve
    (impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (planner : (query : spec.Domain) → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) (Option Probe))
    (computation : OracleComp spec α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) →
      List Probe → ProbComp (Bool × List Probe))
    (boolObserve : DeferredContext → Nat → (α × SplitHashCache) → ProbComp Bool)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hplanner : ∀ query nextContext remaining nextCache,
      ∃ planned,
        runDirectResolvedDetailedFromTable nextContext remaining table
            ((planner query).run nextCache) =
          pure (.done ⟨nextContext, remaining, (planned, nextCache), table⟩))
    (hproject : ∀ nextContext remaining value nextCandidates,
      evalDist (Prod.fst <$> observe nextContext remaining value nextCandidates) =
        evalDist (boolObserve nextContext remaining value)) :
    evalDist (Prod.fst <$> directDetailedBoundaryPrivatePlanObserve impl planner computation
        observe candidates context fuel table cache) =
      evalDist (directDetailedBoundaryPrivateObserve impl computation boolObserve
        context fuel table cache) := by
  induction computation using OracleComp.inductionOn generalizing candidates context fuel cache with
  | pure value =>
      rw [directDetailedBoundaryPrivatePlanObserve, OracleComp.construct_pure,
        directDetailedBoundaryPrivateObserve, OracleComp.construct_pure]
      exact hproject context fuel (value, cache) candidates
  | query_bind query next ih =>
      rw [directDetailedBoundaryPrivatePlanObserve, OracleComp.construct_query_bind,
        directDetailedBoundaryPrivateObserve, OracleComp.construct_query_bind, map_bind]
      obtain ⟨planned, hplanned⟩ := hplanner query context fuel cache
      rw [hplanned, pure_bind]
      let nextCandidates := appendPlannedCandidate candidates planned
      apply evalDist_fst_runDirectDetailedPrivatePlanObserve
      intro nextContext remaining value finalCandidates
      apply evalDist_fst_canonicalizeDirectDetailedPrivatePlanObserve
      intro finalContext finalRemaining finalValue finalCandidates
      simpa [directDetailedBoundaryPrivatePlanObserve,
        directDetailedBoundaryPrivateObserve] using
        ih finalValue.1 finalCandidates finalContext finalRemaining finalValue.2

theorem evalDist_fst_retainedResolvedFinalizationPrivatePlanObserve
    (table : OtsSecretIndex → HashOutput) (root : Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : RetainedRestResult × SplitHashCache) (candidates : List Probe) :
    evalDist (Prod.fst <$>
        retainedResolvedFinalizationPrivatePlanObserve table root context fuel value candidates) =
      evalDist (retainedResolvedFinalizationPrivateObserve table root context fuel value) := by
  unfold retainedResolvedFinalizationPrivatePlanObserve
  simp

noncomputable def sampledGranularAllDirectBoundaryDetailedRetainedPrivatePlan
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp (Bool × List Probe) := do
  let table ← sampleOtsHashTable
  granularAllDirectBoundaryDetailedRetainedPrivatePlan adversary parameter table ftsSecret fuel

end SphincsSecurity.Concrete.OtsProbeSimulation
