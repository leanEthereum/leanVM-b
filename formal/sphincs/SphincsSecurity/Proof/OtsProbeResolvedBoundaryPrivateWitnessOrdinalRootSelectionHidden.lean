import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootSelectionHash

/-!
# Hidden-state materialized selection coupling

Canonical public views of two hidden-root-related states are equal. The materialized selection
prefix therefore chooses the same plan, while every safe public-plan execution and the complete
target-aware signer preserve the hidden-root quotient.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

theorem runCleanFromTable_publishOrdinaryInput
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (input : HashInput) (output : HashOutput)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat) (cache : SplitHashCache) :
    runCleanFromTable state fuel table
        ((publishOrdinaryInput coordinate input output).run cache) =
      pure (some
        { state := state.publish coordinate
          remaining := fuel
          value := (output, Function.update cache (.ordinary input) (some output))
          table := table }) := by
  unfold publishOrdinaryInput
  rw [StateT.run_bind, runCleanFromTable_bind, runCleanFromTable_publishCoordinate]
  simp [StateT.run_modify, runCleanFromTable]

theorem runCleanFromTable_revealPublishOrdinaryInput_of_value
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (input : HashInput) (state : LazyRevealProbe.State Coordinate)
    (fuel : Nat) (cache : SplitHashCache) (output : HashOutput)
    (hvalue : state.values coordinate = some output) :
    runCleanFromTable state fuel table
        ((revealPublishOrdinaryInput coordinate input).run cache) =
      pure (some
        { state := state.publish coordinate
          remaining := fuel
          value := (output, Function.update
            (Function.update cache (.hidden coordinate) (some output))
            (.ordinary input) (some output))
          table := table }) := by
  unfold revealPublishOrdinaryInput
  rw [StateT.run_bind, runCleanFromTable_bind, revealCoordinateOutput_run_eq,
    LazyRevealProbe.revealQuery, runCleanFromTable_reveal_query_bind, hvalue]
  simp only [runCleanFromTable, OracleComp.construct_pure, pure_bind]
  change runCleanFromTable state fuel table
      ((publishOrdinaryInput coordinate input output).run
        (Function.update cache (.hidden coordinate) (some output))) = _
  exact runCleanFromTable_publishOrdinaryInput table coordinate input output state fuel
    (Function.update cache (.hidden coordinate) (some output))

set_option maxRecDepth 100000 in
theorem evalDist_targetPublicResolve_then_finish_eq
    (parameter : PublicParameter) (target : Position)
    (leftOutput rightOutput : HashOutput)
    (publicState : LazyRevealProbe.State Coordinate) (input : HashInput)
    (leftState rightState : LazyRevealProbe.State Coordinate)
    (hstate : RootHiddenStateRel target leftOutput rightOutput leftState rightState)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (leftCache rightCache : SplitHashCache)
    (hcache : RootHiddenCacheRel target leftOutput rightOutput leftCache rightCache)
    (leftObserve rightObserve : LazyRevealProbe.State Coordinate → Nat → HashOutput →
      SplitHashCache → List Probe → ProbComp (Option Probe))
    (candidates : List Probe)
    (hrecursive : ∀ leftResult rightResult,
      RootHiddenCleanSameRel target leftOutput rightOutput
        (some leftResult) (some rightResult) →
      evalDist (continueMaterializedPrivateOrdinalSelection target leftObserve
          leftResult.state leftResult.remaining leftResult.value.1 leftResult.value.2 candidates) =
        evalDist (continueMaterializedPrivateOrdinalSelection target rightObserve
          rightResult.state rightResult.remaining rightResult.value.1 rightResult.value.2
          candidates)) :
    evalDist
        (runCleanFromTable leftState fuel table
            ((resolvePublicKnownInput parameter publicState (.position target) input).run
              leftCache) >>=
          finishMaterializedPrivateOrdinalSelection
            (continueMaterializedPrivateOrdinalSelection target leftObserve) candidates) =
      evalDist
        (runCleanFromTable rightState fuel table
            ((resolvePublicKnownInput parameter publicState (.position target) input).run
              rightCache) >>=
          finishMaterializedPrivateOrdinalSelection
            (continueMaterializedPrivateOrdinalSelection target rightObserve) candidates) := by
  unfold resolvePublicKnownInput
  cases hknown : purePeekTableInput parameter publicState (.position target) with
  | none =>
      apply evalDist_bind_eq_of_relTriple_next _ _ _ _ _
        (rootHiddenRelates_splitHashQuery_ordinary target leftOutput rightOutput input
          leftState rightState hstate fuel table leftCache rightCache hcache)
      intro leftResult rightResult hresult
      cases leftResult with
      | none =>
          cases rightResult with
          | none => rfl
          | some rightResult => simp [RootHiddenCleanSameRel] at hresult
      | some leftResult =>
          cases rightResult with
          | none => simp [RootHiddenCleanSameRel] at hresult
          | some rightResult => exact hrecursive leftResult rightResult hresult
  | some knownInput =>
      by_cases heq : knownInput = input
      · simp only [heq, ↓reduceIte]
        change evalDist
            (runCleanFromTable leftState fuel table
                ((revealPublishOrdinaryInput (.position target) input).run leftCache) >>=
              finishMaterializedPrivateOrdinalSelection
                (continueMaterializedPrivateOrdinalSelection target leftObserve) candidates) =
          evalDist
            (runCleanFromTable rightState fuel table
                ((revealPublishOrdinaryInput (.position target) input).run rightCache) >>=
              finishMaterializedPrivateOrdinalSelection
                (continueMaterializedPrivateOrdinalSelection target rightObserve) candidates)
        rw [runCleanFromTable_revealPublishOrdinaryInput_of_value table (.position target) input
            leftState fuel leftCache leftOutput hstate.left_target,
          runCleanFromTable_revealPublishOrdinaryInput_of_value table (.position target) input
            rightState fuel rightCache rightOutput hstate.right_target]
        simp [finishMaterializedPrivateOrdinalSelection,
          continueMaterializedPrivateOrdinalSelection, LazyRevealProbe.State.publish]
      · simp only [heq, ↓reduceIte]
        apply evalDist_bind_eq_of_relTriple_next _ _ _ _ _
          (rootHiddenRelates_splitHashQuery_ordinary target leftOutput rightOutput input
            leftState rightState hstate fuel table leftCache rightCache hcache)
        intro leftResult rightResult hresult
        cases leftResult with
        | none =>
            cases rightResult with
            | none => rfl
            | some rightResult => simp [RootHiddenCleanSameRel] at hresult
        | some leftResult =>
            cases rightResult with
            | none => simp [RootHiddenCleanSameRel] at hresult
            | some rightResult => exact hrecursive leftResult rightResult hresult

set_option maxRecDepth 100000 in
theorem evalDist_targetPublicPlan_then_finish_eq
    (parameter : PublicParameter) (target : Position)
    (leftOutput rightOutput : HashOutput)
    (publicState : LazyRevealProbe.State Coordinate) (input : HashInput)
    (plan : PlannedHashQuery) (haction : plan.action = .resolve (.position target))
    (leftState rightState : LazyRevealProbe.State Coordinate)
    (hstate : RootHiddenStateRel target leftOutput rightOutput leftState rightState)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (leftCache rightCache : SplitHashCache)
    (hcache : RootHiddenCacheRel target leftOutput rightOutput leftCache rightCache)
    (leftObserve rightObserve : LazyRevealProbe.State Coordinate → Nat → HashOutput →
      SplitHashCache → List Probe → ProbComp (Option Probe))
    (candidates : List Probe)
    (hrecursive : ∀ leftResult rightResult,
      RootHiddenCleanSameRel target leftOutput rightOutput
        (some leftResult) (some rightResult) →
      evalDist (continueMaterializedPrivateOrdinalSelection target leftObserve
          leftResult.state leftResult.remaining leftResult.value.1 leftResult.value.2 candidates) =
        evalDist (continueMaterializedPrivateOrdinalSelection target rightObserve
          rightResult.state rightResult.remaining rightResult.value.1 rightResult.value.2
          candidates)) :
    evalDist
        (runCleanFromTable leftState fuel table
            ((probingHashQueryAfterPublicPlan parameter input publicState plan).run leftCache) >>=
          finishMaterializedPrivateOrdinalSelection
            (continueMaterializedPrivateOrdinalSelection target leftObserve) candidates) =
      evalDist
        (runCleanFromTable rightState fuel table
            ((probingHashQueryAfterPublicPlan parameter input publicState plan).run rightCache) >>=
          finishMaterializedPrivateOrdinalSelection
            (continueMaterializedPrivateOrdinalSelection target rightObserve) candidates) := by
  unfold probingHashQueryAfterPublicPlan
  rw [haction, StateT.run_bind, StateT.run_bind,
    runCleanFromTable_bind, runCleanFromTable_bind]
  simp only [bind_assoc]
  apply evalDist_bind_eq_of_relTriple_next _ _ _ _ _
    (rootHiddenRelates_executeCandidate target leftOutput rightOutput plan.candidate?
      leftState rightState hstate fuel table leftCache rightCache hcache)
  intro leftResult rightResult hresult
  cases leftResult with
  | none =>
      cases rightResult with
      | none => rfl
      | some rightResult => simp [RootHiddenCleanSameRel] at hresult
  | some leftResult =>
      cases rightResult with
      | none => simp [RootHiddenCleanSameRel] at hresult
      | some rightResult =>
          rcases hresult with ⟨hnextState, hremaining, htable, hvalue, hnextCache⟩
          simp only
          rw [← hremaining, ← htable]
          exact evalDist_targetPublicResolve_then_finish_eq parameter target leftOutput
            rightOutput publicState input leftResult.state rightResult.state hnextState
            leftResult.remaining leftResult.table leftResult.value.2 rightResult.value.2
            hnextCache leftObserve rightObserve candidates hrecursive

theorem evalDist_finishMaterializedSelection_eq_of_rootHidden
    (target : Position) (leftOutput rightOutput : HashOutput)
    (observeLeft observeRight : LazyRevealProbe.State Coordinate → Nat → α →
      SplitHashCache → List Probe → ProbComp (Option Probe))
    (candidates : List Probe)
    (left right : Option (CleanRunResult (α × SplitHashCache)))
    (hrel : RootHiddenCleanSameRel target leftOutput rightOutput left right)
    (hnext : ∀ leftResult rightResult,
      RootHiddenCleanSameRel target leftOutput rightOutput
        (some leftResult) (some rightResult) →
      evalDist (observeLeft leftResult.state leftResult.remaining leftResult.value.1
          leftResult.value.2 candidates) =
        evalDist (observeRight rightResult.state rightResult.remaining rightResult.value.1
          rightResult.value.2 candidates)) :
    evalDist (finishMaterializedPrivateOrdinalSelection observeLeft candidates left) =
      evalDist (finishMaterializedPrivateOrdinalSelection observeRight candidates right) := by
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some rightResult => simp [RootHiddenCleanSameRel] at hrel
  | some leftResult =>
      cases right with
      | none => simp [RootHiddenCleanSameRel] at hrel
      | some rightResult => exact hnext leftResult rightResult hrel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem evalDist_materializedRootAvoidingOrdinalSelection_hidden
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (leftOutput rightOutput : HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe)
    (leftState rightState : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (leftCache rightCache : SplitHashCache)
    (hstate : RootHiddenStateRel target leftOutput rightOutput leftState rightState)
    (hcache : RootHiddenCacheRel target leftOutput rightOutput leftCache rightCache) :
    evalDist
        (materializedComparisonRootAvoidingOrdinalSelection ordinal parameter publicRoot target
          leftOutput rightOutput ftsSecret computation candidates leftState fuel table leftCache) =
      evalDist
        (materializedActualRootAvoidingOrdinalSelection ordinal parameter publicRoot target
          (truncateHash leftOutput) (truncateHash rightOutput) ftsSecret computation candidates
          rightState fuel table rightCache) := by
  classical
  induction computation using OracleComp.inductionOn generalizing
      candidates leftState rightState fuel leftCache rightCache with
  | pure value =>
      simp [materializedComparisonRootAvoidingOrdinalSelection,
        materializedActualRootAvoidingOrdinalSelection,
        materializedRootAvoidingOrdinalSelection]
  | query_bind query next ih =>
      unfold materializedComparisonRootAvoidingOrdinalSelection
        materializedActualRootAvoidingOrdinalSelection
      rw [materializedRootAvoidingOrdinalSelection, OracleComp.construct_query_bind,
        materializedRootAvoidingOrdinalSelection, OracleComp.construct_query_bind]
      by_cases hselected : ordinal < candidates.length
      · simp [hselected]
      · simp only [hselected, ↓reduceDIte]
        cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                apply evalDist_bind_eq_of_relTriple_next _ _ _ _ _
                  (rootHiddenRelates_splitUniformImpl target leftOutput rightOutput n
                    leftState rightState hstate fuel table leftCache rightCache hcache)
                intro leftResult rightResult hresult
                apply evalDist_finishMaterializedSelection_eq_of_rootHidden target leftOutput
                  rightOutput _ _ candidates _ _ hresult
                intro nextLeft nextRight hnextRel
                rcases hnextRel with ⟨hnextState, hremaining, htable, hvalue, hnextCache⟩
                rw [← hremaining, ← hvalue]
                unfold continueMaterializedPrivateOrdinalSelection
                have hreveal : nextLeft.state.revealed = nextRight.state.revealed :=
                  hnextState.revealed
                by_cases hrevealed : Coordinate.position target ∈ nextLeft.state.revealed
                · have hrightRevealed : Coordinate.position target ∈ nextRight.state.revealed := by
                    rwa [← hreveal]
                  simp [hrevealed, hrightRevealed]
                · have hrightRevealed : Coordinate.position target ∉ nextRight.state.revealed := by
                    intro hmem
                    exact hrevealed (by rwa [hreveal])
                  simp only [hrevealed, hrightRevealed, ↓reduceIte]
                  exact ih nextLeft.value.1 candidates nextLeft.state nextRight.state
                    nextLeft.remaining nextLeft.value.2 nextRight.value.2 hnextState hnextCache
            | inr input =>
                have hpublic := materializedCanonicalContext_state_eq_of_rootHidden hstate table
                rw [← hpublic]
                let publicContext := materializedCanonicalContext table leftState
                let plan := purePlanProbingHashQuery parameter input publicContext.state
                let candidate? := rootAwareCandidateForPlan? parameter input plan
                let nextCandidates := appendPlannedCandidate candidates candidate?
                by_cases hnextSelected : ordinal < nextCandidates.length
                · have hactual : ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table leftState).state))).length := by
                    simpa [publicContext, plan, candidate?, nextCandidates] using hnextSelected
                  simp [hactual]
                · have hactual : ¬ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table leftState).state))).length := by
                    simpa [publicContext, plan, candidate?, nextCandidates] using hnextSelected
                  simp only [hactual, ↓reduceDIte]
                  by_cases hsafe : RootAwareCandidateAvoidsRoots target
                      (truncateHash leftOutput) (truncateHash rightOutput) candidate?
                  · have hsafeActual : RootAwareCandidateAvoidsRoots target
                        (truncateHash leftOutput) (truncateHash rightOutput)
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table leftState).state)) := by
                      simpa [publicContext, plan, candidate?] using hsafe
                    simp only [hsafeActual, ↓reduceIte]
                    let leftObserve : LazyRevealProbe.State Coordinate → Nat → HashOutput →
                        SplitHashCache → List Probe → ProbComp (Option Probe) :=
                      fun nextState remaining value nextCache laterCandidates =>
                        materializedComparisonRootAvoidingOrdinalSelection ordinal parameter
                          publicRoot target leftOutput rightOutput ftsSecret (next value)
                          laterCandidates nextState remaining table nextCache
                    let rightObserve : LazyRevealProbe.State Coordinate → Nat → HashOutput →
                        SplitHashCache → List Probe → ProbComp (Option Probe) :=
                      fun nextState remaining value nextCache laterCandidates =>
                        materializedActualRootAvoidingOrdinalSelection ordinal parameter publicRoot
                          target (truncateHash leftOutput) (truncateHash rightOutput) ftsSecret
                          (next value) laterCandidates nextState remaining table nextCache
                    have hrecursive : ∀ nextLeft nextRight,
                        RootHiddenCleanSameRel target leftOutput rightOutput
                          (some nextLeft) (some nextRight) →
                        evalDist (continueMaterializedPrivateOrdinalSelection target leftObserve
                            nextLeft.state nextLeft.remaining nextLeft.value.1 nextLeft.value.2
                            nextCandidates) =
                          evalDist (continueMaterializedPrivateOrdinalSelection target rightObserve
                            nextRight.state nextRight.remaining nextRight.value.1 nextRight.value.2
                            nextCandidates) := by
                      intro nextLeft nextRight hnextRel
                      rcases hnextRel with
                        ⟨hnextState, hremaining, htable, hvalue, hnextCache⟩
                      rw [← hremaining, ← hvalue]
                      unfold continueMaterializedPrivateOrdinalSelection
                      have hreveal : nextLeft.state.revealed = nextRight.state.revealed :=
                        hnextState.revealed
                      by_cases hrevealed : Coordinate.position target ∈ nextLeft.state.revealed
                      · have hrightRevealed :
                            Coordinate.position target ∈ nextRight.state.revealed := by
                          rwa [← hreveal]
                        simp [hrevealed, hrightRevealed]
                      · have hrightRevealed :
                            Coordinate.position target ∉ nextRight.state.revealed := by
                          intro hmem
                          exact hrevealed (by rwa [hreveal])
                        simp only [hrevealed, hrightRevealed, ↓reduceIte]
                        exact ih nextLeft.value.1 nextCandidates nextLeft.state nextRight.state
                          nextLeft.remaining nextLeft.value.2 nextRight.value.2 hnextState hnextCache
                    letI : Decidable
                        (plan.action = PlannedHashAction.resolve (.position target)) :=
                      Classical.propDecidable _
                    by_cases haction : plan.action = .resolve (.position target)
                    · exact evalDist_targetPublicPlan_then_finish_eq parameter target leftOutput
                        rightOutput (materializedCanonicalContext table leftState).state input plan
                        haction leftState rightState hstate fuel table leftCache rightCache hcache
                        leftObserve rightObserve nextCandidates hrecursive
                    · apply evalDist_bind_eq_of_relTriple_next _ _ _ _ _
                        (rootHiddenRelates_probingHashQueryAfterPublicPlan parameter target
                          leftOutput rightOutput input
                          (materializedCanonicalContext table leftState).state plan haction
                          leftState rightState hstate fuel table leftCache rightCache hcache)
                      intro leftResult rightResult hresult
                      exact evalDist_finishMaterializedSelection_eq_of_rootHidden target leftOutput
                        rightOutput _ _ nextCandidates _ _ hresult hrecursive
                  · have hsafeActual : ¬RootAwareCandidateAvoidsRoots target
                        (truncateHash leftOutput) (truncateHash rightOutput)
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table leftState).state)) := by
                      simpa [publicContext, plan, candidate?] using hsafe
                    simp [hsafeActual]
        | inr message =>
            apply evalDist_bind_eq_of_relTriple_next _ _ _ _ _
              (rootHiddenRelates_maskedSignWithTargetComparison_actual parameter publicRoot
                ftsSecret target hroot leftOutput rightOutput message leftState rightState hstate
                fuel table leftCache rightCache hcache)
            intro leftResult rightResult hresult
            apply evalDist_finishMaterializedSelection_eq_of_rootHidden target leftOutput
              rightOutput _ _ candidates _ _ hresult
            intro nextLeft nextRight hnextRel
            rcases hnextRel with ⟨hnextState, hremaining, htable, hvalue, hnextCache⟩
            rw [← hremaining, ← hvalue]
            unfold continueMaterializedPrivateOrdinalSelection
            have hreveal : nextLeft.state.revealed = nextRight.state.revealed :=
              hnextState.revealed
            by_cases hrevealed : Coordinate.position target ∈ nextLeft.state.revealed
            · have hrightRevealed : Coordinate.position target ∈ nextRight.state.revealed := by
                rwa [← hreveal]
              simp [hrevealed, hrightRevealed]
            · have hrightRevealed : Coordinate.position target ∉ nextRight.state.revealed := by
                intro hmem
                exact hrevealed (by rwa [hreveal])
              simp only [hrevealed, hrightRevealed, ↓reduceIte]
              exact ih nextLeft.value.1 candidates nextLeft.state nextRight.state
                nextLeft.remaining nextLeft.value.2 nextRight.value.2 hnextState hnextCache

theorem evalDist_materializedRootAvoidingOrdinalSelection_deferred
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (leftOutput rightOutput : HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe)
    (leftContext rightContext : DeferredContext)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (leftCache rightCache : SplitHashCache)
    (hcontext : RootDeferredContextRel target leftOutput rightOutput
      leftContext rightContext)
    (hcache : RootDeferredCacheRel parameter target leftOutput rightOutput
      leftCache rightCache) :
    evalDist
        (materializedActualRootAvoidingOrdinalSelection ordinal parameter publicRoot target
          (truncateHash leftOutput) (truncateHash rightOutput) ftsSecret computation candidates
          (materializedDeferredState leftContext) fuel table leftCache) =
      evalDist
        (materializedActualRootAvoidingOrdinalSelection ordinal parameter publicRoot target
          (truncateHash rightOutput) (truncateHash leftOutput) ftsSecret computation candidates
          (materializedDeferredState rightContext) fuel table rightCache) := by
  obtain ⟨middleCache, hencoding, hhidden⟩ := hcache
  have hmaterialized := hcontext.materialized
  have hstored : StoredLayerRoot (materializedDeferredState leftContext) target
      (truncateHash leftOutput) :=
    ⟨leftOutput, hmaterialized.state.left_target, rfl⟩
  calc
    _ = evalDist
        (materializedComparisonRootAvoidingOrdinalSelection ordinal parameter publicRoot target
          leftOutput rightOutput ftsSecret computation candidates
          (materializedDeferredState leftContext) fuel table middleCache) :=
      evalDist_materializedRootAvoidingOrdinalSelection_encoding ordinal parameter publicRoot
        target hroot leftOutput rightOutput ftsSecret computation candidates
        (materializedDeferredState leftContext) fuel table leftCache middleCache hencoding hstored
    _ = evalDist
        (materializedActualRootAvoidingOrdinalSelection ordinal parameter publicRoot target
          (truncateHash leftOutput) (truncateHash rightOutput) ftsSecret computation candidates
          (materializedDeferredState rightContext) fuel table rightCache) :=
      evalDist_materializedRootAvoidingOrdinalSelection_hidden ordinal parameter publicRoot
        target hroot leftOutput rightOutput ftsSecret computation candidates
        (materializedDeferredState leftContext) (materializedDeferredState rightContext) fuel table
        middleCache rightCache hmaterialized.state hhidden
    _ = _ := congrArg evalDist
      (materializedRootAvoidingOrdinalSelection_swap_roots ordinal parameter target
        (truncateHash leftOutput) (truncateHash rightOutput)
        (maskedSign parameter publicRoot ftsSecret) computation candidates
        (materializedDeferredState rightContext) fuel table rightCache)

theorem evalDist_materializedRootAvoidingOrdinalSelection_fullSwap
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (leftOutput rightOutput : HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (context : DeferredContext)
    (hhidden : context.state.values (.position target) = none)
    (hprivate : Coordinate.position target ∉ context.state.revealed)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (cache : SplitHashCache)
    (hcache : cache (.hidden (.position target)) = some leftOutput) :
    let leftContext :=
      { context with values := context.values.install target leftOutput }
    let rightContext :=
      { context with values := context.values.install target rightOutput }
    evalDist
        (materializedActualRootAvoidingOrdinalSelection ordinal parameter publicRoot target
          (truncateHash leftOutput) (truncateHash rightOutput) ftsSecret computation candidates
          (materializedDeferredState leftContext) fuel table cache) =
      evalDist
        (materializedActualRootAvoidingOrdinalSelection ordinal parameter publicRoot target
          (truncateHash rightOutput) (truncateHash leftOutput) ftsSecret computation candidates
          (materializedDeferredState rightContext) fuel table
          (fullSwapRootCache parameter target (truncateHash leftOutput)
            (truncateHash rightOutput) rightOutput cache)) := by
  dsimp only
  exact evalDist_materializedRootAvoidingOrdinalSelection_deferred ordinal parameter publicRoot
    target hroot leftOutput rightOutput ftsSecret computation candidates _ _ fuel table cache _
    (rootDeferredContextRel_install target leftOutput rightOutput context hhidden hprivate)
    (rootDeferredCacheRel_fullSwapRootCache parameter target leftOutput rightOutput cache hcache)

end SphincsSecurity.Concrete.OtsProbeSimulation
