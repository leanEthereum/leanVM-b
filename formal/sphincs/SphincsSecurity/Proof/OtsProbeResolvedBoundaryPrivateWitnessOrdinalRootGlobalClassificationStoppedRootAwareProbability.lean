import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootSharedPrefix

/-!
# Root-aware selector probability

The shared-prefix outcome executes the proof-only encoding probe that the observed handler executes.
This module gives that outcome a clean optional projection and proves its root-swap bound without
discarding the production weight.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable

noncomputable def materializedRootAwareAvoidingOrdinalSelection
    (ordinal : Nat) (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest)
    (signer : Message → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) (Option Signature))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ProbComp (Option Probe) := by
  classical
  exact OracleComp.construct
    (C := fun _ : OracleComp (OracleWorld + SigningSpec) α =>
      List Probe → LazyRevealProbe.State Coordinate → Nat →
        (OtsSecretIndex → HashOutput) → SplitHashCache → ProbComp (Option Probe))
    (fun _value candidates _state _fuel _table _cache =>
      if hselected : ordinal < candidates.length then
        pure (some (candidates.get ⟨ordinal, hselected⟩))
      else pure none)
    (fun query next recursivelyRun candidates state fuel table cache =>
      if hselected : ordinal < candidates.length then
        pure (some (candidates.get ⟨ordinal, hselected⟩))
      else
        match query with
        | .inl (.inl n) =>
            runCleanFromTable state fuel table ((splitUniformImpl n).run cache) >>=
              finishMaterializedPrivateOrdinalSelection
                (continueMaterializedPrivateOrdinalSelection target
                  (fun nextState remaining value nextCache laterCandidates =>
                    recursivelyRun value laterCandidates nextState remaining table nextCache))
                candidates
        | .inl (.inr input) =>
            let publicContext := materializedCanonicalContext table state
            let plan := purePlanProbingHashQuery parameter input publicContext.state
            let candidate? := rootAwareCandidateForPlan? parameter input plan
            let nextCandidates := appendPlannedCandidate candidates candidate?
            if hnextSelected : ordinal < nextCandidates.length then
              pure (some (nextCandidates.get ⟨ordinal, hnextSelected⟩))
            else if RootAwareCandidateAvoidsRoots target leftRoot rightRoot candidate? then
              runCleanFromTable state fuel table
                  ((probingHashQueryAfterRootAwarePublicPlan parameter input publicContext.state
                    plan).run cache) >>=
                finishMaterializedPrivateOrdinalSelection
                  (continueMaterializedPrivateOrdinalSelection target
                    (fun nextState remaining value nextCache laterCandidates =>
                      recursivelyRun value laterCandidates nextState remaining table nextCache))
                  nextCandidates
            else pure none
        | .inr message =>
            runCleanFromTable state fuel table ((signer message).run cache) >>=
              finishMaterializedPrivateOrdinalSelection
                (continueMaterializedPrivateOrdinalSelection target
                  (fun nextState remaining value nextCache laterCandidates =>
                    recursivelyRun value laterCandidates nextState remaining table nextCache))
                candidates)
    computation candidates state fuel table cache

noncomputable def materializedActualRootAwareAvoidingOrdinalSelection
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ProbComp (Option Probe) :=
  materializedRootAwareAvoidingOrdinalSelection ordinal parameter target leftRoot rightRoot
    (maskedSign parameter publicRoot ftsSecret) computation candidates state fuel table cache

noncomputable def materializedComparisonRootAwareAvoidingOrdinalSelection
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (leftOutput rightOutput : HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ProbComp (Option Probe) :=
  materializedRootAwareAvoidingOrdinalSelection ordinal parameter target
    (truncateHash leftOutput) (truncateHash rightOutput)
    (maskedSignWithTargetComparison parameter publicRoot target (truncateHash rightOutput)
      ftsSecret)
    computation candidates state fuel table cache

set_option maxRecDepth 100000 in
theorem materializedRootAwareAvoidingOrdinalSelection_swap_roots
    (ordinal : Nat) (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest)
    (signer : Message → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) (Option Signature))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    materializedRootAwareAvoidingOrdinalSelection ordinal parameter target leftRoot rightRoot
        signer computation candidates state fuel table cache =
      materializedRootAwareAvoidingOrdinalSelection ordinal parameter target rightRoot leftRoot
        signer computation candidates state fuel table cache := by
  induction computation using OracleComp.inductionOn generalizing
      candidates state fuel cache with
  | pure value => simp [materializedRootAwareAvoidingOrdinalSelection]
  | query_bind query next ih =>
      rw [materializedRootAwareAvoidingOrdinalSelection, OracleComp.construct_query_bind,
        materializedRootAwareAvoidingOrdinalSelection, OracleComp.construct_query_bind]
      by_cases hselected : ordinal < candidates.length
      · simp [hselected]
      · simp only [hselected, ↓reduceDIte]
        cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                apply bind_congr
                intro result
                cases result with
                | none => rfl
                | some result =>
                    unfold finishMaterializedPrivateOrdinalSelection
                      continueMaterializedPrivateOrdinalSelection
                    by_cases hrevealed : Coordinate.position target ∈ result.state.revealed
                    · simp [hrevealed]
                    · simp only [hrevealed, ↓reduceIte]
                      exact ih result.value.1 candidates result.state result.remaining
                        result.value.2
            | inr input =>
                let publicContext := materializedCanonicalContext table state
                let plan := purePlanProbingHashQuery parameter input publicContext.state
                let candidate? := rootAwareCandidateForPlan? parameter input plan
                let nextCandidates := appendPlannedCandidate candidates candidate?
                by_cases hnextSelected : ordinal < nextCandidates.length
                · have hactual : ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state))).length := by
                    simpa [publicContext, plan, candidate?, nextCandidates] using hnextSelected
                  simp [hactual]
                · have hactual : ¬ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state))).length := by
                    simpa [publicContext, plan, candidate?, nextCandidates] using hnextSelected
                  simp only [hactual, ↓reduceDIte]
                  have hsafe := rootAwareCandidateAvoidsRoots_swap target leftRoot rightRoot
                    (rootAwareCandidateForPlan? parameter input
                      (purePlanProbingHashQuery parameter input
                        (materializedCanonicalContext table state).state))
                  rw [propext hsafe]
                  by_cases hholds : RootAwareCandidateAvoidsRoots target rightRoot leftRoot
                      (rootAwareCandidateForPlan? parameter input
                        (purePlanProbingHashQuery parameter input
                          (materializedCanonicalContext table state).state))
                  · simp only [hholds, ↓reduceIte]
                    apply bind_congr
                    intro result
                    cases result with
                    | none => rfl
                    | some result =>
                        unfold finishMaterializedPrivateOrdinalSelection
                          continueMaterializedPrivateOrdinalSelection
                        by_cases hrevealed : Coordinate.position target ∈ result.state.revealed
                        · simp [hrevealed]
                        · simp only [hrevealed, ↓reduceIte]
                          exact ih result.value.1 nextCandidates result.state result.remaining
                            result.value.2
                  · simp [hholds]
        | inr message =>
            apply bind_congr
            intro result
            cases result with
            | none => rfl
            | some result =>
                unfold finishMaterializedPrivateOrdinalSelection
                  continueMaterializedPrivateOrdinalSelection
                by_cases hrevealed : Coordinate.position target ∈ result.state.revealed
                · simp [hrevealed]
                · simp only [hrevealed, ↓reduceIte]
                  exact ih result.value.1 candidates result.state result.remaining result.value.2

theorem rootEncodingCacheCouples_probingHashQueryAfterRootAwarePublicPlan_avoids
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (input : HashInput)
    (publicState : LazyRevealProbe.State Coordinate) (plan : PlannedHashQuery)
    (havoid : RootInputAvoids parameter target leftRoot rightRoot input) :
    RootEncodingCacheCouples parameter target leftRoot rightRoot
      (probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan) := by
  unfold probingHashQueryAfterRootAwarePublicPlan
  apply (rootEncodingCacheCouples_executeCandidate parameter target leftRoot rightRoot
    (rootAwareCandidateForPlan? parameter input plan)).bind
  intro _
  cases plan.action with
  | ordinary =>
      exact rootEncodingCacheCouples_splitHashQuery_avoids parameter target leftRoot
        rightRoot input havoid
  | resolve coordinate =>
      exact rootEncodingCacheCouples_resolvePublicKnownInput_avoids parameter target leftRoot
        rightRoot publicState coordinate input havoid

theorem rootHiddenRelates_probingHashQueryAfterRootAwarePublicPlan
    (parameter : PublicParameter)
    (target : Position) (leftOutput rightOutput : HashOutput)
    (input : HashInput) (publicState : LazyRevealProbe.State Coordinate)
    (plan : PlannedHashQuery)
    (hsafe : plan.action ≠ .resolve (.position target)) :
    RootHiddenRelates target leftOutput rightOutput
      (probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan)
      (probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan) := by
  unfold probingHashQueryAfterRootAwarePublicPlan
  apply (rootHiddenRelates_executeCandidate target leftOutput rightOutput
    (rootAwareCandidateForPlan? parameter input plan)).bind
  intro _ _ _
  cases haction : plan.action with
  | ordinary =>
      exact rootHiddenRelates_splitHashQuery_ordinary target leftOutput rightOutput input
  | resolve coordinate =>
      have hne : coordinate ≠ .position target := by
        intro heq
        apply hsafe
        rw [haction, heq]
      exact rootHiddenRelates_resolvePublicKnownInput_of_ne parameter target leftOutput
        rightOutput publicState coordinate hne input

set_option maxRecDepth 100000 in
theorem evalDist_targetRootAwarePublicPlan_then_finish_eq
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
            ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run
              leftCache) >>=
          finishMaterializedPrivateOrdinalSelection
            (continueMaterializedPrivateOrdinalSelection target leftObserve) candidates) =
      evalDist
        (runCleanFromTable rightState fuel table
            ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run
              rightCache) >>=
          finishMaterializedPrivateOrdinalSelection
            (continueMaterializedPrivateOrdinalSelection target rightObserve) candidates) := by
  unfold probingHashQueryAfterRootAwarePublicPlan
  rw [haction, StateT.run_bind, StateT.run_bind,
    runCleanFromTable_bind, runCleanFromTable_bind]
  simp only [bind_assoc]
  apply evalDist_bind_eq_of_relTriple_next _ _ _ _ _
    (rootHiddenRelates_executeCandidate target leftOutput rightOutput
      (rootAwareCandidateForPlan? parameter input plan)
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

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem evalDist_materializedRootAwareAvoidingOrdinalSelection_encoding
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (leftOutput rightOutput : HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (leftCache rightCache : SplitHashCache)
    (hcache : RootEncodingCacheRel parameter target (truncateHash leftOutput)
      (truncateHash rightOutput) leftCache rightCache)
    (hstored : StoredLayerRoot state target (truncateHash leftOutput)) :
    evalDist
        (materializedActualRootAwareAvoidingOrdinalSelection ordinal parameter publicRoot target
          (truncateHash leftOutput) (truncateHash rightOutput) ftsSecret computation candidates
          state fuel table leftCache) =
      evalDist
        (materializedComparisonRootAwareAvoidingOrdinalSelection ordinal parameter publicRoot
          target leftOutput rightOutput ftsSecret computation candidates state fuel table
          rightCache) := by
  induction computation using OracleComp.inductionOn generalizing
      candidates state fuel leftCache rightCache with
  | pure value =>
      simp [materializedActualRootAwareAvoidingOrdinalSelection,
        materializedComparisonRootAwareAvoidingOrdinalSelection,
        materializedRootAwareAvoidingOrdinalSelection]
  | query_bind query next ih =>
      unfold materializedActualRootAwareAvoidingOrdinalSelection
        materializedComparisonRootAwareAvoidingOrdinalSelection
      rw [materializedRootAwareAvoidingOrdinalSelection, OracleComp.construct_query_bind,
        materializedRootAwareAvoidingOrdinalSelection, OracleComp.construct_query_bind]
      by_cases hselected : ordinal < candidates.length
      · simp [hselected]
      · simp only [hselected, ↓reduceDIte]
        cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                apply evalDist_bind_eq_of_relTriple_next _ _ _ _ _
                  (((rootEncodingCacheCouples_splitUniformImpl parameter target
                    (truncateHash leftOutput) (truncateHash rightOutput) n).relates.toStored)
                    leftCache rightCache hcache state fuel table hstored)
                intro leftResult rightResult hresult
                apply evalDist_finishMaterializedSelection_eq_of_rootEncoding _ _ candidates _ _
                  hresult
                intro nextLeft nextRight hnextRel
                rcases hnextRel with ⟨hclean, hnextStored⟩
                rcases hclean with ⟨hstate, hremaining, htable, hvalue, hnextCache⟩
                rw [← hstate, ← hremaining, ← hvalue]
                unfold continueMaterializedPrivateOrdinalSelection
                by_cases hrevealed : Coordinate.position target ∈ nextLeft.state.revealed
                · simp [hrevealed]
                · simp only [hrevealed, ↓reduceIte]
                  exact ih nextLeft.value.1 candidates nextLeft.state nextLeft.remaining
                    nextLeft.value.2 nextRight.value.2 hnextCache hnextStored
            | inr input =>
                let publicContext := materializedCanonicalContext table state
                let plan := purePlanProbingHashQuery parameter input publicContext.state
                let candidate? := rootAwareCandidateForPlan? parameter input plan
                let nextCandidates := appendPlannedCandidate candidates candidate?
                by_cases hnextSelected : ordinal < nextCandidates.length
                · have hactual : ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state))).length := by
                    simpa [publicContext, plan, candidate?, nextCandidates] using hnextSelected
                  simp [hactual]
                · have hactual : ¬ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state))).length := by
                    simpa [publicContext, plan, candidate?, nextCandidates] using hnextSelected
                  simp only [hactual, ↓reduceDIte]
                  by_cases hsafe : RootAwareCandidateAvoidsRoots target
                      (truncateHash leftOutput) (truncateHash rightOutput) candidate?
                  · have hsafeActual : RootAwareCandidateAvoidsRoots target
                        (truncateHash leftOutput) (truncateHash rightOutput)
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state)) := by
                      simpa [publicContext, plan, candidate?] using hsafe
                    simp only [hsafeActual, ↓reduceIte]
                    have hinput : RootInputAvoids parameter target
                        (truncateHash leftOutput) (truncateHash rightOutput) input := by
                      apply rootInputAvoids_of_rootAwareCandidateAvoidsRoots
                      simpa [rootAwareCandidateForPlan?_purePlan] using hsafeActual
                    apply evalDist_bind_eq_of_relTriple_next _ _ _ _ _
                      (((rootEncodingCacheCouples_probingHashQueryAfterRootAwarePublicPlan_avoids
                        parameter target (truncateHash leftOutput) (truncateHash rightOutput) input
                        (materializedCanonicalContext table state).state plan hinput).relates.toStored)
                        leftCache rightCache hcache state fuel table hstored)
                    intro leftResult rightResult hresult
                    apply evalDist_finishMaterializedSelection_eq_of_rootEncoding _ _
                      nextCandidates _ _ hresult
                    intro nextLeft nextRight hnextRel
                    rcases hnextRel with ⟨hclean, hnextStored⟩
                    rcases hclean with ⟨hstate, hremaining, htable, hvalue, hnextCache⟩
                    rw [← hstate, ← hremaining, ← hvalue]
                    unfold continueMaterializedPrivateOrdinalSelection
                    by_cases hrevealed : Coordinate.position target ∈ nextLeft.state.revealed
                    · simp [hrevealed]
                    · simp only [hrevealed, ↓reduceIte]
                      exact ih nextLeft.value.1 nextCandidates nextLeft.state nextLeft.remaining
                        nextLeft.value.2 nextRight.value.2 hnextCache hnextStored
                  · have hsafeActual : ¬RootAwareCandidateAvoidsRoots target
                        (truncateHash leftOutput) (truncateHash rightOutput)
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state)) := by
                      simpa [publicContext, plan, candidate?] using hsafe
                    simp [hsafeActual]
        | inr message =>
            apply evalDist_bind_eq_of_relTriple_next _ _ _ _ _
              (rootEncodingCacheRelatesStored_maskedSign_targetComparison parameter publicRoot
                target hroot (truncateHash leftOutput) (truncateHash rightOutput) ftsSecret message
                leftCache rightCache hcache state fuel table hstored)
            intro leftResult rightResult hresult
            apply evalDist_finishMaterializedSelection_eq_of_rootEncoding _ _ candidates _ _
              hresult
            intro nextLeft nextRight hnextRel
            rcases hnextRel with ⟨hclean, hnextStored⟩
            rcases hclean with ⟨hstate, hremaining, htable, hvalue, hnextCache⟩
            rw [← hstate, ← hremaining, ← hvalue]
            unfold continueMaterializedPrivateOrdinalSelection
            by_cases hrevealed : Coordinate.position target ∈ nextLeft.state.revealed
            · simp [hrevealed]
            · simp only [hrevealed, ↓reduceIte]
              exact ih nextLeft.value.1 candidates nextLeft.state nextLeft.remaining
                nextLeft.value.2 nextRight.value.2 hnextCache hnextStored

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem evalDist_materializedRootAwareAvoidingOrdinalSelection_hidden
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
        (materializedComparisonRootAwareAvoidingOrdinalSelection ordinal parameter publicRoot
          target leftOutput rightOutput ftsSecret computation candidates leftState fuel table
          leftCache) =
      evalDist
        (materializedActualRootAwareAvoidingOrdinalSelection ordinal parameter publicRoot target
          (truncateHash leftOutput) (truncateHash rightOutput) ftsSecret computation candidates
          rightState fuel table rightCache) := by
  classical
  induction computation using OracleComp.inductionOn generalizing
      candidates leftState rightState fuel leftCache rightCache with
  | pure value =>
      simp [materializedComparisonRootAwareAvoidingOrdinalSelection,
        materializedActualRootAwareAvoidingOrdinalSelection,
        materializedRootAwareAvoidingOrdinalSelection]
  | query_bind query next ih =>
      unfold materializedComparisonRootAwareAvoidingOrdinalSelection
        materializedActualRootAwareAvoidingOrdinalSelection
      rw [materializedRootAwareAvoidingOrdinalSelection, OracleComp.construct_query_bind,
        materializedRootAwareAvoidingOrdinalSelection, OracleComp.construct_query_bind]
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
                        materializedComparisonRootAwareAvoidingOrdinalSelection ordinal parameter
                          publicRoot target leftOutput rightOutput ftsSecret (next value)
                          laterCandidates nextState remaining table nextCache
                    let rightObserve : LazyRevealProbe.State Coordinate → Nat → HashOutput →
                        SplitHashCache → List Probe → ProbComp (Option Probe) :=
                      fun nextState remaining value nextCache laterCandidates =>
                        materializedActualRootAwareAvoidingOrdinalSelection ordinal parameter
                          publicRoot target (truncateHash leftOutput) (truncateHash rightOutput)
                          ftsSecret (next value) laterCandidates nextState remaining table nextCache
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
                      rcases hnextRel with ⟨hnextState, hremaining, htable, hvalue, hnextCache⟩
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
                    · exact evalDist_targetRootAwarePublicPlan_then_finish_eq parameter target
                        leftOutput rightOutput (materializedCanonicalContext table leftState).state
                        input plan haction leftState rightState hstate fuel table leftCache
                        rightCache hcache leftObserve rightObserve nextCandidates hrecursive
                    · apply evalDist_bind_eq_of_relTriple_next _ _ _ _ _
                        (rootHiddenRelates_probingHashQueryAfterRootAwarePublicPlan parameter target
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

theorem evalDist_materializedRootAwareAvoidingOrdinalSelection_deferred
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
        (materializedActualRootAwareAvoidingOrdinalSelection ordinal parameter publicRoot target
          (truncateHash leftOutput) (truncateHash rightOutput) ftsSecret computation candidates
          (materializedDeferredState leftContext) fuel table leftCache) =
      evalDist
        (materializedActualRootAwareAvoidingOrdinalSelection ordinal parameter publicRoot target
          (truncateHash rightOutput) (truncateHash leftOutput) ftsSecret computation candidates
          (materializedDeferredState rightContext) fuel table rightCache) := by
  obtain ⟨middleCache, hencoding, hhidden⟩ := hcache
  have hmaterialized := hcontext.materialized
  have hstored : StoredLayerRoot (materializedDeferredState leftContext) target
      (truncateHash leftOutput) :=
    ⟨leftOutput, hmaterialized.state.left_target, rfl⟩
  calc
    _ = evalDist
        (materializedComparisonRootAwareAvoidingOrdinalSelection ordinal parameter publicRoot
          target leftOutput rightOutput ftsSecret computation candidates
          (materializedDeferredState leftContext) fuel table middleCache) :=
      evalDist_materializedRootAwareAvoidingOrdinalSelection_encoding ordinal parameter publicRoot
        target hroot leftOutput rightOutput ftsSecret computation candidates
        (materializedDeferredState leftContext) fuel table leftCache middleCache hencoding hstored
    _ = evalDist
        (materializedActualRootAwareAvoidingOrdinalSelection ordinal parameter publicRoot target
          (truncateHash leftOutput) (truncateHash rightOutput) ftsSecret computation candidates
          (materializedDeferredState rightContext) fuel table rightCache) :=
      evalDist_materializedRootAwareAvoidingOrdinalSelection_hidden ordinal parameter publicRoot
        target hroot leftOutput rightOutput ftsSecret computation candidates
        (materializedDeferredState leftContext) (materializedDeferredState rightContext) fuel table
        middleCache rightCache hmaterialized.state hhidden
    _ = _ := congrArg evalDist
      (materializedRootAwareAvoidingOrdinalSelection_swap_roots ordinal parameter target
        (truncateHash leftOutput) (truncateHash rightOutput)
        (maskedSign parameter publicRoot ftsSecret) computation candidates
        (materializedDeferredState rightContext) fuel table rightCache)

theorem evalDist_materializedRootAwareAvoidingOrdinalSelection_fullSwap
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
        (materializedActualRootAwareAvoidingOrdinalSelection ordinal parameter publicRoot target
          (truncateHash leftOutput) (truncateHash rightOutput) ftsSecret computation candidates
          (materializedDeferredState leftContext) fuel table cache) =
      evalDist
        (materializedActualRootAwareAvoidingOrdinalSelection ordinal parameter publicRoot target
          (truncateHash rightOutput) (truncateHash leftOutput) ftsSecret computation candidates
          (materializedDeferredState rightContext) fuel table
          (fullSwapRootCache parameter target (truncateHash leftOutput)
            (truncateHash rightOutput) rightOutput cache)) := by
  dsimp only
  exact evalDist_materializedRootAwareAvoidingOrdinalSelection_deferred ordinal parameter
    publicRoot target hroot leftOutput rightOutput ftsSecret computation candidates _ _ fuel table
    cache _ (rootDeferredContextRel_install target leftOutput rightOutput context hhidden hprivate)
    (rootDeferredCacheRel_fullSwapRootCache parameter target leftOutput rightOutput cache hcache)

set_option maxRecDepth 100000 in
theorem evalDist_materializedActualRootAwareAvoidingOrdinalSelection_family_swap
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (output : Digest → HashOutput)
    (htruncate : ∀ root, truncateHash (output root) = root)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (context : DeferredContext)
    (hhidden : context.state.values (.position target) = none)
    (hprivate : Coordinate.position target ∉ context.state.revealed)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (cache : Digest → SplitHashCache)
    (htargetCache : ∀ root,
      cache root (.hidden (.position target)) = some (output root))
    (hcacheSwap : ∀ leftRoot rightRoot,
      fullSwapRootCache parameter target leftRoot rightRoot (output rightRoot)
        (cache leftRoot) = cache rightRoot)
    (leftRoot rightRoot : Digest) :
    let rootContext := fun root =>
      { context with values := context.values.install target (output root) }
    evalDist
        (materializedActualRootAwareAvoidingOrdinalSelection ordinal parameter publicRoot target
          leftRoot rightRoot ftsSecret computation candidates
          (materializedDeferredState (rootContext leftRoot)) fuel table (cache leftRoot)) =
      evalDist
        (materializedActualRootAwareAvoidingOrdinalSelection ordinal parameter publicRoot target
          rightRoot leftRoot ftsSecret computation candidates
          (materializedDeferredState (rootContext rightRoot)) fuel table (cache rightRoot)) := by
  dsimp only
  have hswap := evalDist_materializedRootAwareAvoidingOrdinalSelection_fullSwap ordinal parameter
    publicRoot target hroot (output leftRoot) (output rightRoot) ftsSecret computation candidates
    context hhidden hprivate fuel table (cache leftRoot) (htargetCache leftRoot)
  rw [htruncate leftRoot, htruncate rightRoot] at hswap
  simpa only [hcacheSwap leftRoot rightRoot] using hswap

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_materializedRootAwareAvoidingOrdinalSelection_weaken_comparison
    (ordinal : Nat) (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot matchRoot : Digest)
    (signer : Message → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) (Option Signature))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    RelTriple
      (materializedRootAwareAvoidingOrdinalSelection ordinal parameter target leftRoot rightRoot signer
        computation candidates state fuel table cache)
      (materializedRootAwareAvoidingOrdinalSelection ordinal parameter target leftRoot leftRoot signer
        computation candidates state fuel table cache)
      (MaterializedOptionMatchRel target matchRoot) := by
  induction computation using OracleComp.inductionOn generalizing candidates state fuel cache with
  | pure value =>
      simp only [materializedRootAwareAvoidingOrdinalSelection, OracleComp.construct_pure]
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte]
        exact relTriple_pure_pure (fun hmatch => hmatch)
      · simp only [hselected, ↓reduceDIte]
        exact relTriple_pure_pure (fun hmatch => hmatch)
  | query_bind query next ih =>
      rw [materializedRootAwareAvoidingOrdinalSelection, OracleComp.construct_query_bind,
        materializedRootAwareAvoidingOrdinalSelection, OracleComp.construct_query_bind]
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte]
        exact relTriple_pure_pure (fun hmatch => hmatch)
      · simp only [hselected, ↓reduceDIte]
        cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                let leftObserve : LazyRevealProbe.State Coordinate → Nat → Fin (n + 1) →
                    SplitHashCache → List Probe → ProbComp (Option Probe) :=
                  fun nextState remaining output nextCache laterCandidates =>
                    materializedRootAwareAvoidingOrdinalSelection ordinal parameter target leftRoot
                      rightRoot signer (next output) laterCandidates nextState remaining table
                      nextCache
                let rightObserve : LazyRevealProbe.State Coordinate → Nat → Fin (n + 1) →
                    SplitHashCache → List Probe → ProbComp (Option Probe) :=
                  fun nextState remaining output nextCache laterCandidates =>
                    materializedRootAwareAvoidingOrdinalSelection ordinal parameter target leftRoot
                      leftRoot signer (next output) laterCandidates nextState remaining table
                      nextCache
                apply relTriple_bind
                  (relTriple_refl
                    (runCleanFromTable state fuel table ((splitUniformImpl n).run cache)))
                intro leftResult rightResult hresult
                subst rightResult
                apply relTriple_finishMaterializedSelection_weaken target matchRoot
                  (continueMaterializedPrivateOrdinalSelection target leftObserve)
                  (continueMaterializedPrivateOrdinalSelection target rightObserve)
                  candidates leftResult
                intro resolved
                unfold continueMaterializedPrivateOrdinalSelection
                by_cases hrevealed : Coordinate.position target ∈ resolved.state.revealed
                · simp [hrevealed, MaterializedOptionMatchRel,
                    materializedOrdinalSelectionMatches]
                · simpa [hrevealed, leftObserve, rightObserve] using
                    ih resolved.value.1 candidates resolved.state resolved.remaining
                      resolved.value.2
            | inr input =>
                let publicContext := materializedCanonicalContext table state
                let plan := purePlanProbingHashQuery parameter input publicContext.state
                let candidate? := rootAwareCandidateForPlan? parameter input plan
                let nextCandidates := appendPlannedCandidate candidates candidate?
                by_cases hnextSelected : ordinal < nextCandidates.length
                · have hactual : ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state))).length := by
                    simpa [publicContext, plan, candidate?, nextCandidates] using hnextSelected
                  simp only [hactual, ↓reduceDIte]
                  exact relTriple_pure_pure (fun hmatch => hmatch)
                · have hactual : ¬ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state))).length := by
                    simpa [publicContext, plan, candidate?, nextCandidates] using hnextSelected
                  simp only [hactual, ↓reduceDIte]
                  by_cases hsafe : RootAwareCandidateAvoidsRoots target leftRoot rightRoot candidate?
                  · have hsafeActual : RootAwareCandidateAvoidsRoots target leftRoot rightRoot
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state)) := by
                      simpa [publicContext, plan, candidate?] using hsafe
                    have hleftSafe := rootAwareCandidateAvoidsRoots_actual target leftRoot rightRoot
                      candidate? hsafe
                    have hleftSafeActual : RootAwareCandidateAvoidsRoots target leftRoot leftRoot
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state)) := by
                      simpa [publicContext, plan, candidate?] using hleftSafe
                    simp only [hsafeActual, hleftSafeActual, ↓reduceIte]
                    let leftObserve : LazyRevealProbe.State Coordinate → Nat → HashOutput →
                        SplitHashCache → List Probe → ProbComp (Option Probe) :=
                      fun nextState remaining output nextCache laterCandidates =>
                        materializedRootAwareAvoidingOrdinalSelection ordinal parameter target leftRoot
                          rightRoot signer (next output) laterCandidates nextState remaining table
                          nextCache
                    let rightObserve : LazyRevealProbe.State Coordinate → Nat → HashOutput →
                        SplitHashCache → List Probe → ProbComp (Option Probe) :=
                      fun nextState remaining output nextCache laterCandidates =>
                        materializedRootAwareAvoidingOrdinalSelection ordinal parameter target leftRoot
                          leftRoot signer (next output) laterCandidates nextState remaining table
                          nextCache
                    apply relTriple_bind
                      (relTriple_refl
                        (runCleanFromTable state fuel table
                          ((probingHashQueryAfterRootAwarePublicPlan parameter input publicContext.state plan).run
                            cache)))
                    intro leftResult rightResult hresult
                    subst rightResult
                    apply relTriple_finishMaterializedSelection_weaken target matchRoot
                      (continueMaterializedPrivateOrdinalSelection target leftObserve)
                      (continueMaterializedPrivateOrdinalSelection target rightObserve)
                      nextCandidates leftResult
                    intro resolved
                    unfold continueMaterializedPrivateOrdinalSelection
                    by_cases hrevealed : Coordinate.position target ∈ resolved.state.revealed
                    · simp [hrevealed, MaterializedOptionMatchRel,
                        materializedOrdinalSelectionMatches]
                    · simpa [hrevealed, leftObserve, rightObserve] using
                        ih resolved.value.1 nextCandidates resolved.state resolved.remaining
                          resolved.value.2
                  · have hsafeActual : ¬RootAwareCandidateAvoidsRoots target leftRoot rightRoot
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state)) := by
                      simpa [publicContext, plan, candidate?] using hsafe
                    simp only [hsafeActual, ↓reduceIte]
                    exact relTriple_none_any_materializedOptionMatch target matchRoot _
        | inr message =>
            let leftObserve : LazyRevealProbe.State Coordinate → Nat → Option Signature →
                SplitHashCache → List Probe → ProbComp (Option Probe) :=
              fun nextState remaining output nextCache laterCandidates =>
                materializedRootAwareAvoidingOrdinalSelection ordinal parameter target leftRoot
                  rightRoot signer (next output) laterCandidates nextState remaining table nextCache
            let rightObserve : LazyRevealProbe.State Coordinate → Nat → Option Signature →
                SplitHashCache → List Probe → ProbComp (Option Probe) :=
              fun nextState remaining output nextCache laterCandidates =>
                materializedRootAwareAvoidingOrdinalSelection ordinal parameter target leftRoot leftRoot
                  signer (next output) laterCandidates nextState remaining table nextCache
            apply relTriple_bind
              (relTriple_refl (runCleanFromTable state fuel table ((signer message).run cache)))
            intro leftResult rightResult hresult
            subst rightResult
            apply relTriple_finishMaterializedSelection_weaken target matchRoot
              (continueMaterializedPrivateOrdinalSelection target leftObserve)
              (continueMaterializedPrivateOrdinalSelection target rightObserve)
              candidates leftResult
            intro resolved
            unfold continueMaterializedPrivateOrdinalSelection
            by_cases hrevealed : Coordinate.position target ∈ resolved.state.revealed
            · simp [hrevealed, MaterializedOptionMatchRel,
                materializedOrdinalSelectionMatches]
            · simpa [hrevealed, leftObserve, rightObserve] using
                ih resolved.value.1 candidates resolved.state resolved.remaining resolved.value.2

theorem probEvent_materializedRootAwareAvoidingOrdinalSelection_match_le_actual_guard
    (ordinal : Nat) (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot matchRoot : Digest)
    (signer : Message → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) (Option Signature))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    Pr[materializedOrdinalSelectionMatches target matchRoot |
        materializedRootAwareAvoidingOrdinalSelection ordinal parameter target leftRoot rightRoot
          signer computation candidates state fuel table cache] ≤
      Pr[materializedOrdinalSelectionMatches target matchRoot |
        materializedRootAwareAvoidingOrdinalSelection ordinal parameter target leftRoot leftRoot
          signer computation candidates state fuel table cache] :=
  probEvent_le_of_relTriple
    (relTriple_materializedRootAwareAvoidingOrdinalSelection_weaken_comparison ordinal parameter
      target leftRoot rightRoot matchRoot signer computation candidates state fuel table cache)
    (fun _ _ hrelation => hrelation)

set_option maxRecDepth 100000 in
theorem probEvent_sampledComparisonRoot_materializedRootAwareSelectionMatches_le_mul
    (ordinal : Nat) (parameter : PublicParameter) (target : Position)
    (leftRoot : Digest)
    (signer : Message → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) (Option Signature))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    Pr[fun result : Digest × Option Probe =>
        materializedOrdinalSelectionMatches target result.1 result.2 | do
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      let selection ← materializedRootAwareAvoidingOrdinalSelection ordinal parameter target
        leftRoot rightRoot signer computation candidates state fuel table cache
      pure (rightRoot, selection)] ≤
      Pr[materializedOrdinalSelectionAt target |
          materializedRootAwareAvoidingOrdinalSelection ordinal parameter target leftRoot leftRoot signer
            computation candidates state fuel table cache] *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  let reference := materializedRootAwareAvoidingOrdinalSelection ordinal parameter target leftRoot
    leftRoot signer computation candidates state fuel table cache
  calc
    _ ≤ Pr[fun result : Digest × Option Probe =>
          materializedOrdinalSelectionMatches target result.1 result.2 | do
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        let selection ← reference
        pure (rightRoot, selection)] := by
      apply probEvent_bind_le_bind_of_forall_le
      intro rightRoot _hrightRoot
      rw [show (do
          let selection ← materializedRootAwareAvoidingOrdinalSelection ordinal parameter target
            leftRoot rightRoot signer computation candidates state fuel table cache
          pure (rightRoot, selection)) =
        (fun selection => (rightRoot, selection)) <$>
          materializedRootAwareAvoidingOrdinalSelection ordinal parameter target leftRoot rightRoot
            signer computation candidates state fuel table cache by
          simp [map_eq_bind_pure_comp],
        show (do
          let selection ← reference
          pure (rightRoot, selection)) =
        (fun selection => (rightRoot, selection)) <$> reference by
          simp [map_eq_bind_pure_comp], probEvent_map, probEvent_map]
      exact probEvent_materializedRootAwareAvoidingOrdinalSelection_match_le_actual_guard ordinal
        parameter target leftRoot rightRoot rightRoot signer computation candidates state fuel table
        cache
    _ ≤ Pr[fun result : Digest × Option Probe =>
          materializedOrdinalSelectionAt target result.2 ∧
            result.1 = selectedProbeDigest result.2 | do
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        let selection ← reference
        pure (rightRoot, selection)] := by
      apply probEvent_mono
      intro result _hresult hmatch
      exact ⟨materializedOrdinalSelectionAt_of_matches hmatch,
        materializedOrdinalSelectionMatches_root_eq_selectedProbeDigest hmatch⟩
    _ ≤ _ := by
      apply probEvent_uniform_root_matches_distribution_independent_guess_le_mul
        (fun _rightRoot => reference) reference
      intro rightRoot
      rfl


set_option maxRecDepth 100000 in
theorem probEvent_uniformActualRoot_materializedRootAwareSelectionFamilyMatches_le_mul
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (output : Digest → HashOutput)
    (htruncate : ∀ root, truncateHash (output root) = root)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (context : DeferredContext)
    (hhidden : context.state.values (.position target) = none)
    (hprivate : Coordinate.position target ∉ context.state.revealed)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (cache : Digest → SplitHashCache)
    (htargetCache : ∀ root,
      cache root (.hidden (.position target)) = some (output root))
    (hcacheSwap : ∀ leftRoot rightRoot,
      fullSwapRootCache parameter target leftRoot rightRoot (output rightRoot)
        (cache leftRoot) = cache rightRoot) :
    let rootContext := fun root =>
      { context with values := context.values.install target (output root) }
    Pr[fun result : Digest × Digest × Option Probe =>
        materializedOrdinalSelectionMatches target result.1 result.2.2 | do
      let leftRoot ← ($ᵗ Digest : ProbComp Digest)
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      let selection ← materializedActualRootAwareAvoidingOrdinalSelection ordinal parameter
        publicRoot target leftRoot rightRoot ftsSecret computation candidates
        (materializedDeferredState (rootContext leftRoot)) fuel table (cache leftRoot)
      pure (leftRoot, rightRoot, selection)] ≤
      Pr[fun result : Digest × Option Probe =>
          materializedOrdinalSelectionAt target result.2 | do
        let leftRoot ← ($ᵗ Digest : ProbComp Digest)
        let selection ← materializedActualRootAwareAvoidingOrdinalSelection ordinal parameter
          publicRoot target leftRoot leftRoot ftsSecret computation candidates
          (materializedDeferredState (rootContext leftRoot)) fuel table (cache leftRoot)
        pure (leftRoot, selection)] *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  dsimp only
  let run : Digest → Digest → ProbComp (Option Probe) :=
    fun leftRoot rightRoot =>
      materializedActualRootAwareAvoidingOrdinalSelection ordinal parameter publicRoot target leftRoot
        rightRoot ftsSecret computation candidates
        (materializedDeferredState
          { context with values := context.values.install target (output leftRoot) })
        fuel table (cache leftRoot)
  let reference : Digest → ProbComp (Option Probe) :=
    fun leftRoot =>
      materializedActualRootAwareAvoidingOrdinalSelection ordinal parameter publicRoot target leftRoot
        leftRoot ftsSecret computation candidates
        (materializedDeferredState
          { context with values := context.values.install target (output leftRoot) })
        fuel table (cache leftRoot)
  apply probEvent_uniformActualRoot_match_le_of_swap_of_comparison_mul target run reference
  · intro leftRoot rightRoot
    exact evalDist_materializedActualRootAwareAvoidingOrdinalSelection_family_swap ordinal parameter
      publicRoot target hroot output htruncate ftsSecret computation candidates context hhidden
      hprivate fuel table cache htargetCache hcacheSwap leftRoot rightRoot
  · intro leftRoot
    exact probEvent_sampledComparisonRoot_materializedRootAwareSelectionMatches_le_mul ordinal parameter
      target leftRoot (maskedSign parameter publicRoot ftsSecret) computation candidates
      (materializedDeferredState
        { context with values := context.values.install target (output leftRoot) })
      fuel table (cache leftRoot)


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_materializedActualRootAwareOutcome_optionalSelection
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    RelTriple
      (materializedActualRootAwareOrdinalSelectionOutcome ordinal parameter publicRoot target
        leftRoot rightRoot ftsSecret computation candidates state fuel table cache)
      (materializedActualRootAwareAvoidingOrdinalSelection ordinal parameter publicRoot target
        leftRoot rightRoot ftsSecret computation candidates state fuel table cache)
      (MaterializedOutcomeOptionRel target leftRoot) := by
  induction computation using OracleComp.inductionOn generalizing candidates state fuel cache with
  | pure value =>
      simp only [materializedActualRootAwareOrdinalSelectionOutcome,
        materializedActualRootAwareAvoidingOrdinalSelection,
        materializedRootAwareAvoidingOrdinalSelection, OracleComp.construct_pure]
      by_cases hselected : ordinal < candidates.length <;>
        simp only [hselected, ↓reduceDIte] <;>
        exact relTriple_pure_pure (fun hmatch => hmatch)
  | query_bind query next ih =>
      rw [materializedActualRootAwareOrdinalSelectionOutcome,
        OracleComp.construct_query_bind,
        materializedActualRootAwareAvoidingOrdinalSelection,
        materializedRootAwareAvoidingOrdinalSelection, OracleComp.construct_query_bind]
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte]
        exact relTriple_pure_pure (fun hmatch => hmatch)
      · simp only [hselected, ↓reduceDIte]
        cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                change Fin (n + 1) → OracleComp (OracleWorld + SigningSpec) α at next
                let outcomeObserve : LazyRevealProbe.State Coordinate → Nat → Fin (n + 1) →
                    SplitHashCache → List Probe → ProbComp MaterializedSelectionOutcome :=
                  fun nextState remaining output nextCache laterCandidates =>
                    materializedActualRootAwareOrdinalSelectionOutcome ordinal parameter publicRoot
                      target leftRoot rightRoot ftsSecret (next output) laterCandidates nextState
                      remaining table nextCache
                let optionObserve : LazyRevealProbe.State Coordinate → Nat → Fin (n + 1) →
                    SplitHashCache → List Probe → ProbComp (Option Probe) :=
                  fun nextState remaining output nextCache laterCandidates =>
                    materializedActualRootAwareAvoidingOrdinalSelection ordinal parameter
                      publicRoot target leftRoot rightRoot ftsSecret (next output) laterCandidates
                      nextState remaining table nextCache
                apply relTriple_of_evalDist_eq_right
                  (evalDist_runDetailedMaterializedSelection_eq_clean target optionObserve
                    candidates state fuel table ((splitUniformImpl n).run cache))
                apply relTriple_bind
                  (relTriple_refl
                    (runDirectResolvedDetailedFromTable (directDeferredContext state) fuel table
                      ((splitUniformImpl n).run cache)))
                intro leftResult rightResult hresult
                subst rightResult
                apply relTriple_finishMaterializedOutcome_option target leftRoot table
                  outcomeObserve optionObserve candidates leftResult
                intro resolved hcompletable hprivate
                simpa [outcomeObserve, optionObserve] using
                  ih resolved.value.1 candidates resolved.context.state resolved.remaining
                    resolved.value.2
            | inr input =>
                change HashOutput → OracleComp (OracleWorld + SigningSpec) α at next
                let publicContext := materializedCanonicalContext table state
                let plan := purePlanProbingHashQuery parameter input publicContext.state
                let candidate? := rootAwareCandidateForPlan? parameter input plan
                let nextCandidates := appendPlannedCandidate candidates candidate?
                by_cases hnextSelected : ordinal < nextCandidates.length
                · have hactual : ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state))).length := by
                    simpa [publicContext, plan, candidate?, nextCandidates] using hnextSelected
                  simp only [hactual, ↓reduceDIte]
                  exact relTriple_pure_pure (fun hmatch => hmatch)
                · have hactual : ¬ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state))).length := by
                    simpa [publicContext, plan, candidate?, nextCandidates] using hnextSelected
                  simp only [hactual, ↓reduceDIte]
                  by_cases hsafe : RootAwareCandidateAvoidsRoots target leftRoot rightRoot candidate?
                  · have hsafeActual : RootAwareCandidateAvoidsRoots target leftRoot rightRoot
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state)) := by
                      simpa [publicContext, plan, candidate?] using hsafe
                    simp only [hsafeActual, ↓reduceIte]
                    let outcomeObserve : LazyRevealProbe.State Coordinate → Nat → HashOutput →
                        SplitHashCache → List Probe → ProbComp MaterializedSelectionOutcome :=
                      fun nextState remaining output nextCache laterCandidates =>
                        materializedActualRootAwareOrdinalSelectionOutcome ordinal parameter
                          publicRoot target leftRoot rightRoot ftsSecret (next output)
                          laterCandidates nextState remaining table nextCache
                    let optionObserve : LazyRevealProbe.State Coordinate → Nat → HashOutput →
                        SplitHashCache → List Probe → ProbComp (Option Probe) :=
                      fun nextState remaining output nextCache laterCandidates =>
                        materializedActualRootAwareAvoidingOrdinalSelection ordinal parameter
                          publicRoot target leftRoot rightRoot ftsSecret (next output)
                          laterCandidates nextState remaining table nextCache
                    let inner :=
                      (probingHashQueryAfterRootAwarePublicPlan parameter input publicContext.state
                        plan).run cache
                    apply relTriple_of_evalDist_eq_right
                      (evalDist_runDetailedMaterializedSelection_eq_clean target optionObserve
                        nextCandidates state fuel table inner)
                    apply relTriple_bind
                      (relTriple_refl
                        (runDirectResolvedDetailedFromTable (directDeferredContext state) fuel table
                          inner))
                    intro leftResult rightResult hresult
                    subst rightResult
                    apply relTriple_finishMaterializedOutcome_option target leftRoot table
                      outcomeObserve optionObserve nextCandidates leftResult
                    intro resolved hcompletable hprivate
                    simpa [outcomeObserve, optionObserve] using
                      ih resolved.value.1 nextCandidates resolved.context.state
                        resolved.remaining resolved.value.2
                  · have hsafeActual : ¬RootAwareCandidateAvoidsRoots target leftRoot rightRoot
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state)) := by
                      simpa [publicContext, plan, candidate?] using hsafe
                    simp only [hsafeActual, ↓reduceIte]
                    exact relTriple_pure_pure (fun hmatch => hmatch)
        | inr message =>
            change Option Signature → OracleComp (OracleWorld + SigningSpec) α at next
            let outcomeObserve : LazyRevealProbe.State Coordinate → Nat → Option Signature →
                SplitHashCache → List Probe → ProbComp MaterializedSelectionOutcome :=
              fun nextState remaining output nextCache laterCandidates =>
                materializedActualRootAwareOrdinalSelectionOutcome ordinal parameter publicRoot
                  target leftRoot rightRoot ftsSecret (next output) laterCandidates nextState
                  remaining table nextCache
            let optionObserve : LazyRevealProbe.State Coordinate → Nat → Option Signature →
                SplitHashCache → List Probe → ProbComp (Option Probe) :=
              fun nextState remaining output nextCache laterCandidates =>
                materializedActualRootAwareAvoidingOrdinalSelection ordinal parameter publicRoot
                  target leftRoot rightRoot ftsSecret (next output) laterCandidates nextState
                  remaining table nextCache
            let inner := (maskedSign parameter publicRoot ftsSecret message).run cache
            apply relTriple_of_evalDist_eq_right
              (evalDist_runDetailedMaterializedSelection_eq_clean target optionObserve candidates
                state fuel table inner)
            apply relTriple_bind
              (relTriple_refl
                (runDirectResolvedDetailedFromTable (directDeferredContext state) fuel table inner))
            intro leftResult rightResult hresult
            subst rightResult
            apply relTriple_finishMaterializedOutcome_option target leftRoot table outcomeObserve
              optionObserve candidates leftResult
            intro resolved hcompletable hprivate
            simpa [outcomeObserve, optionObserve] using
              ih resolved.value.1 candidates resolved.context.state resolved.remaining
                resolved.value.2

end SphincsSecurity.Concrete.OtsProbeSimulation
