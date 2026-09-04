import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalSourceDelayedRootSwapEncoding

/-!
# Root-avoiding permissive delayed selector

This selector retains the delayed source schedule and rejects only when the next recorded root
candidate is one of the two distinguished roots. The guard is symmetric in those roots.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable

noncomputable def continuePermissiveRootAvoidingDetailedOrdinalSelection
    (target : Position)
    (observe : LazyRevealProbe.State Coordinate → Nat → α → SplitHashCache →
      List Probe → ProbComp (Option PermissivePrivateOrdinalSelection))
    (state : LazyRevealProbe.State Coordinate) (remaining : Nat) (value : α)
    (cache : SplitHashCache) (candidates : List Probe) :
    ProbComp (Option PermissivePrivateOrdinalSelection) :=
  if Coordinate.position target ∈ state.revealed then pure none
  else observe state remaining value cache candidates

noncomputable def permissiveRootAvoidingDetailedOrdinalSelection
    (ordinal : Nat) (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest)
    (signer : Message → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) (Option Signature))
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
                (continuePermissiveRootAvoidingDetailedOrdinalSelection target
                  (fun nextState remaining value nextCache laterCandidates =>
                    recursivelyRun value laterCandidates nextState remaining table nextCache))
                candidates
        | .inl (.inr input) =>
            let nextCandidates := permissiveRootAwareCandidates parameter input table state
              candidates
            if hnextSelected : ordinal < nextCandidates.length then
              pure (some ⟨nextCandidates.get ⟨ordinal, hnextSelected⟩, state,
                nextCandidates⟩)
            else
              let publicContext := materializedCanonicalContext table state
              let plan := purePlanProbingHashQuery parameter input publicContext.state
              let candidate? := rootAwareCandidateForPlan? parameter input plan
              if RootAwareCandidateAvoidsRoots target leftRoot rightRoot candidate? then
                runPermissiveFromTable state fuel table
                    (delayedPermissivePublicAction parameter input table state cache) >>=
                  finishPermissiveDetailedPrivateOrdinalSelection
                    (continuePermissiveRootAvoidingDetailedOrdinalSelection target
                      (fun nextState remaining value nextCache laterCandidates =>
                        recursivelyRun value laterCandidates nextState remaining table nextCache))
                    nextCandidates
              else pure none
        | .inr message =>
            runPermissiveFromTable state fuel table ((signer message).run cache) >>=
              finishPermissiveDetailedPrivateOrdinalSelection
                (continuePermissiveRootAvoidingDetailedOrdinalSelection target
                  (fun nextState remaining value nextCache laterCandidates =>
                    recursivelyRun value laterCandidates nextState remaining table nextCache))
                candidates)
    computation candidates state fuel table cache

noncomputable def permissiveActualRootAvoidingDetailedOrdinalSelection
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ProbComp (Option PermissivePrivateOrdinalSelection) :=
  permissiveRootAvoidingDetailedOrdinalSelection ordinal parameter target leftRoot rightRoot
    (maskedSign parameter publicRoot ftsSecret) computation candidates state fuel table cache

noncomputable def permissiveComparisonRootAvoidingDetailedOrdinalSelection
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (leftOutput rightOutput : HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ProbComp (Option PermissivePrivateOrdinalSelection) :=
  permissiveRootAvoidingDetailedOrdinalSelection ordinal parameter target
    (truncateHash leftOutput) (truncateHash rightOutput)
    (maskedSignWithTargetComparison parameter publicRoot target (truncateHash rightOutput)
      ftsSecret)
    computation candidates state fuel table cache

set_option maxRecDepth 100000 in
theorem permissiveRootAvoidingDetailedOrdinalSelection_swap_roots
    (ordinal : Nat) (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest)
    (signer : Message → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) (Option Signature))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    permissiveRootAvoidingDetailedOrdinalSelection ordinal parameter target leftRoot rightRoot
        signer computation candidates state fuel table cache =
      permissiveRootAvoidingDetailedOrdinalSelection ordinal parameter target rightRoot leftRoot
        signer computation candidates state fuel table cache := by
  induction computation using OracleComp.inductionOn generalizing candidates state fuel cache with
  | pure value => simp [permissiveRootAvoidingDetailedOrdinalSelection]
  | query_bind query next ih =>
      rw [permissiveRootAvoidingDetailedOrdinalSelection, OracleComp.construct_query_bind,
        permissiveRootAvoidingDetailedOrdinalSelection, OracleComp.construct_query_bind]
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
                    simp only [finishPermissiveDetailedPrivateOrdinalSelection]
                    unfold continuePermissiveRootAvoidingDetailedOrdinalSelection
                    by_cases hrevealed : Coordinate.position target ∈ result.state.revealed
                    · simp [hrevealed]
                    · simp only [hrevealed, ↓reduceIte]
                      exact ih result.value.1 candidates result.state result.remaining
                        result.value.2
            | inr input =>
                let nextCandidates := permissiveRootAwareCandidates parameter input table state
                  candidates
                by_cases hnextSelected : ordinal < nextCandidates.length
                · have hactual : ordinal <
                      (permissiveRootAwareCandidates parameter input table state candidates).length := by
                    simpa [nextCandidates] using hnextSelected
                  simp [hactual]
                · have hactual : ¬ordinal <
                      (permissiveRootAwareCandidates parameter input table state candidates).length := by
                    simpa [nextCandidates] using hnextSelected
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
                        simp only [finishPermissiveDetailedPrivateOrdinalSelection]
                        unfold continuePermissiveRootAvoidingDetailedOrdinalSelection
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
                simp only [finishPermissiveDetailedPrivateOrdinalSelection]
                unfold continuePermissiveRootAvoidingDetailedOrdinalSelection
                by_cases hrevealed : Coordinate.position target ∈ result.state.revealed
                · simp [hrevealed]
                · simp only [hrevealed, ↓reduceIte]
                  exact ih result.value.1 candidates result.state result.remaining result.value.2

theorem evalDist_finishPermissiveSelection_eq_of_rootEncoding
    (observeLeft observeRight : LazyRevealProbe.State Coordinate → Nat → α →
      SplitHashCache → List Probe → ProbComp (Option PermissivePrivateOrdinalSelection))
    (candidates : List Probe)
    (left right : Option (CleanRunResult (α × SplitHashCache)))
    (hrel : RootEncodingPermissiveStoredRel parameter target leftRoot rightRoot left right)
    (hnext : ∀ leftResult rightResult,
      RootEncodingPermissiveStoredRel parameter target leftRoot rightRoot
        (some leftResult) (some rightResult) →
      evalDist (observeLeft leftResult.state leftResult.remaining leftResult.value.1
          leftResult.value.2 candidates) =
        evalDist (observeRight rightResult.state rightResult.remaining rightResult.value.1
          rightResult.value.2 candidates)) :
    evalDist (finishPermissiveDetailedPrivateOrdinalSelection observeLeft candidates left) =
      evalDist (finishPermissiveDetailedPrivateOrdinalSelection observeRight candidates right) := by
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some right => simp [RootEncodingPermissiveStoredRel] at hrel
  | some left =>
      cases right with
      | none => simp [RootEncodingPermissiveStoredRel] at hrel
      | some right =>
          simp only [finishPermissiveDetailedPrivateOrdinalSelection]
          exact hnext left right hrel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem evalDist_permissiveRootAvoidingDetailedOrdinalSelection_encoding
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
        (permissiveActualRootAvoidingDetailedOrdinalSelection ordinal parameter publicRoot target
          (truncateHash leftOutput) (truncateHash rightOutput) ftsSecret computation candidates
          state fuel table leftCache) =
      evalDist
        (permissiveComparisonRootAvoidingDetailedOrdinalSelection ordinal parameter publicRoot
          target leftOutput rightOutput ftsSecret computation candidates state fuel table
          rightCache) := by
  induction computation using OracleComp.inductionOn generalizing
      candidates state fuel leftCache rightCache with
  | pure value =>
      simp [permissiveActualRootAvoidingDetailedOrdinalSelection,
        permissiveComparisonRootAvoidingDetailedOrdinalSelection,
        permissiveRootAvoidingDetailedOrdinalSelection]
  | query_bind query next ih =>
      unfold permissiveActualRootAvoidingDetailedOrdinalSelection
        permissiveComparisonRootAvoidingDetailedOrdinalSelection
      rw [permissiveRootAvoidingDetailedOrdinalSelection, OracleComp.construct_query_bind,
        permissiveRootAvoidingDetailedOrdinalSelection, OracleComp.construct_query_bind]
      by_cases hselected : ordinal < candidates.length
      · simp [hselected]
      · simp only [hselected, ↓reduceDIte]
        cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                let leftObserve := continuePermissiveRootAvoidingDetailedOrdinalSelection target
                  fun nextState remaining value nextCache laterCandidates =>
                    permissiveActualRootAvoidingDetailedOrdinalSelection ordinal parameter
                      publicRoot target (truncateHash leftOutput) (truncateHash rightOutput)
                      ftsSecret (next value) laterCandidates nextState remaining table nextCache
                let rightObserve := continuePermissiveRootAvoidingDetailedOrdinalSelection target
                  fun nextState remaining value nextCache laterCandidates =>
                    permissiveComparisonRootAvoidingDetailedOrdinalSelection ordinal parameter
                      publicRoot target leftOutput rightOutput ftsSecret (next value)
                      laterCandidates nextState remaining table nextCache
                apply evalDist_bind_eq_of_relTriple_next _ _ _ _ _
                  ((rootEncodingPermissiveCouples_splitUniformImpl parameter target
                    (truncateHash leftOutput) (truncateHash rightOutput) n).toStored
                    leftCache rightCache hcache state fuel table hstored)
                intro leftResult rightResult hresult
                apply evalDist_finishPermissiveSelection_eq_of_rootEncoding leftObserve
                  rightObserve candidates leftResult rightResult hresult
                intro nextLeft nextRight hnext
                rcases hnext with ⟨⟨hstate, hremaining, htable, hvalue, hnextCache⟩,
                  hnextStored⟩
                rw [← hstate, ← hremaining, ← hvalue]
                simp only [leftObserve, rightObserve]
                unfold continuePermissiveRootAvoidingDetailedOrdinalSelection
                by_cases hrevealed : Coordinate.position target ∈ nextLeft.state.revealed
                · simp [hrevealed]
                · simp only [hrevealed, ↓reduceIte]
                  exact ih nextLeft.value.1 candidates nextLeft.state nextLeft.remaining
                    nextLeft.value.2 nextRight.value.2 hnextCache hnextStored
            | inr input =>
                let nextCandidates := permissiveRootAwareCandidates parameter input table state
                  candidates
                by_cases hnextSelected : ordinal < nextCandidates.length
                · have hactual : ordinal <
                      (permissiveRootAwareCandidates parameter input table state candidates).length := by
                    simpa [nextCandidates] using hnextSelected
                  simp [hactual]
                · have hactual : ¬ordinal <
                      (permissiveRootAwareCandidates parameter input table state candidates).length := by
                    simpa [nextCandidates] using hnextSelected
                  simp only [hactual, ↓reduceDIte]
                  let publicContext := materializedCanonicalContext table state
                  let plan := purePlanProbingHashQuery parameter input publicContext.state
                  let candidate? := rootAwareCandidateForPlan? parameter input plan
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
                    let leftObserve :=
                      continuePermissiveRootAvoidingDetailedOrdinalSelection target
                        fun nextState remaining value nextCache laterCandidates =>
                          permissiveActualRootAvoidingDetailedOrdinalSelection ordinal parameter
                            publicRoot target (truncateHash leftOutput) (truncateHash rightOutput)
                            ftsSecret (next value) laterCandidates nextState remaining table
                              nextCache
                    let rightObserve :=
                      continuePermissiveRootAvoidingDetailedOrdinalSelection target
                        fun nextState remaining value nextCache laterCandidates =>
                          permissiveComparisonRootAvoidingDetailedOrdinalSelection ordinal
                            parameter publicRoot target leftOutput rightOutput ftsSecret
                            (next value) laterCandidates nextState remaining table nextCache
                    apply evalDist_bind_eq_of_relTriple_next _ _ _ _ _
                      ((rootEncodingPermissiveCouples_probingHashQueryAfterPublicPlan_avoids
                        parameter target (truncateHash leftOutput) (truncateHash rightOutput)
                        input publicContext.state plan hinput).toStored leftCache rightCache hcache
                          state fuel table hstored)
                    intro leftResult rightResult hresult
                    apply evalDist_finishPermissiveSelection_eq_of_rootEncoding leftObserve
                      rightObserve nextCandidates leftResult rightResult hresult
                    intro nextLeft nextRight hnext
                    rcases hnext with
                      ⟨⟨hstate, hremaining, htable, hvalue, hnextCache⟩, hnextStored⟩
                    rw [← hstate, ← hremaining, ← hvalue]
                    simp only [leftObserve, rightObserve]
                    unfold continuePermissiveRootAvoidingDetailedOrdinalSelection
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
            let leftObserve := continuePermissiveRootAvoidingDetailedOrdinalSelection target
              fun nextState remaining value nextCache laterCandidates =>
                permissiveActualRootAvoidingDetailedOrdinalSelection ordinal parameter publicRoot
                  target (truncateHash leftOutput) (truncateHash rightOutput) ftsSecret
                  (next value) laterCandidates nextState remaining table nextCache
            let rightObserve := continuePermissiveRootAvoidingDetailedOrdinalSelection target
              fun nextState remaining value nextCache laterCandidates =>
                permissiveComparisonRootAvoidingDetailedOrdinalSelection ordinal parameter
                  publicRoot target leftOutput rightOutput ftsSecret (next value) laterCandidates
                  nextState remaining table nextCache
            apply evalDist_bind_eq_of_relTriple_next _ _ _ _ _
              (rootEncodingPermissiveRelatesStored_maskedSign_targetComparison parameter
                publicRoot target hroot (truncateHash leftOutput) (truncateHash rightOutput)
                ftsSecret message leftCache rightCache hcache state fuel table hstored)
            intro leftResult rightResult hresult
            apply evalDist_finishPermissiveSelection_eq_of_rootEncoding leftObserve rightObserve
              candidates leftResult rightResult hresult
            intro nextLeft nextRight hnext
            rcases hnext with ⟨⟨hstate, hremaining, htable, hvalue, hnextCache⟩,
              hnextStored⟩
            rw [← hstate, ← hremaining, ← hvalue]
            simp only [leftObserve, rightObserve]
            unfold continuePermissiveRootAvoidingDetailedOrdinalSelection
            by_cases hrevealed : Coordinate.position target ∈ nextLeft.state.revealed
            · simp [hrevealed]
            · simp only [hrevealed, ↓reduceIte]
              exact ih nextLeft.value.1 candidates nextLeft.state nextLeft.remaining
                nextLeft.value.2 nextRight.value.2 hnextCache hnextStored

def RootHiddenPermissiveSelectionRel
    (target : Position) (leftOutput rightOutput : HashOutput) :
    Option PermissivePrivateOrdinalSelection →
      Option PermissivePrivateOrdinalSelection → Prop
  | none, none => True
  | some left, some right =>
      left.candidate = right.candidate ∧ left.candidates = right.candidates ∧
        RootHiddenStateRel target leftOutput rightOutput left.state right.state
  | _, _ => False

theorem relTriple_finishPermissiveSelection_of_rootHidden
    (target : Position) (leftOutput rightOutput : HashOutput)
    (observeLeft observeRight : LazyRevealProbe.State Coordinate → Nat → α →
      SplitHashCache → List Probe → ProbComp (Option PermissivePrivateOrdinalSelection))
    (candidates : List Probe)
    (left right : Option (CleanRunResult (α × SplitHashCache)))
    (hrel : RootHiddenCleanRelWith target leftOutput rightOutput (fun x y => x = y) left right)
    (hnext : ∀ leftResult rightResult,
      RootHiddenCleanRelWith target leftOutput rightOutput (fun x y => x = y)
        (some leftResult) (some rightResult) →
      RelTriple
        (observeLeft leftResult.state leftResult.remaining leftResult.value.1
          leftResult.value.2 candidates)
        (observeRight rightResult.state rightResult.remaining rightResult.value.1
          rightResult.value.2 candidates)
        (RootHiddenPermissiveSelectionRel target leftOutput rightOutput)) :
    RelTriple
      (finishPermissiveDetailedPrivateOrdinalSelection observeLeft candidates left)
      (finishPermissiveDetailedPrivateOrdinalSelection observeRight candidates right)
      (RootHiddenPermissiveSelectionRel target leftOutput rightOutput) := by
  cases left with
  | none =>
      cases right with
      | none => exact relTriple_pure_pure trivial
      | some right => simp [RootHiddenCleanRelWith] at hrel
  | some left =>
      cases right with
      | none => simp [RootHiddenCleanRelWith] at hrel
      | some right =>
          simp only [finishPermissiveDetailedPrivateOrdinalSelection]
          exact hnext left right hrel

theorem runPermissiveFromTable_publishOrdinaryInput
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (input : HashInput) (output : HashOutput)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat) (cache : SplitHashCache) :
    runPermissiveFromTable state fuel table
        ((publishOrdinaryInput coordinate input output).run cache) =
      pure (some
        { state := state.publish coordinate
          remaining := fuel
          value := (output, Function.update cache (.ordinary input) (some output))
          table := table }) := by
  unfold publishOrdinaryInput
  rw [StateT.run_bind, runPermissiveFromTable_bind]
  unfold publishCoordinate LazyRevealProbe.publishQuery
  rw [StateT.run_liftM, runPermissiveFromTable_publish_query_bind]
  simp [StateT.run_modify, runPermissiveFromTable]

theorem runPermissiveFromTable_revealPublishOrdinaryInput_of_value
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (input : HashInput) (state : LazyRevealProbe.State Coordinate)
    (fuel : Nat) (cache : SplitHashCache) (output : HashOutput)
    (hvalue : state.values coordinate = some output) :
    runPermissiveFromTable state fuel table
        ((revealPublishOrdinaryInput coordinate input).run cache) =
      pure (some
        { state := state.publish coordinate
          remaining := fuel
          value := (output, Function.update
            (Function.update cache (.hidden coordinate) (some output))
            (.ordinary input) (some output))
          table := table }) := by
  unfold revealPublishOrdinaryInput
  rw [StateT.run_bind, runPermissiveFromTable_bind, revealCoordinateOutput_run_eq,
    LazyRevealProbe.revealQuery, runPermissiveFromTable_reveal_query_bind, hvalue]
  simp only [runPermissiveFromTable, OracleComp.construct_pure, pure_bind]
  change runPermissiveFromTable state fuel table
      ((publishOrdinaryInput coordinate input output).run
        (Function.update cache (.hidden coordinate) (some output))) = _
  exact runPermissiveFromTable_publishOrdinaryInput table coordinate input output state fuel
    (Function.update cache (.hidden coordinate) (some output))

set_option maxRecDepth 100000 in
theorem relTriple_targetPublicResolve_then_finishPermissive
    (parameter : PublicParameter) (target : Position)
    (leftOutput rightOutput : HashOutput)
    (publicState : LazyRevealProbe.State Coordinate) (input : HashInput)
    (leftState rightState : LazyRevealProbe.State Coordinate)
    (hstate : RootHiddenStateRel target leftOutput rightOutput leftState rightState)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (leftCache rightCache : SplitHashCache)
    (hcache : RootHiddenCacheRel target leftOutput rightOutput leftCache rightCache)
    (leftObserve rightObserve : LazyRevealProbe.State Coordinate → Nat → HashOutput →
      SplitHashCache → List Probe → ProbComp (Option PermissivePrivateOrdinalSelection))
    (candidates : List Probe)
    (hrecursive : ∀ leftResult rightResult,
      RootHiddenCleanRelWith target leftOutput rightOutput (fun x y => x = y)
        (some leftResult) (some rightResult) →
      RelTriple
        (continuePermissiveRootAvoidingDetailedOrdinalSelection target leftObserve
          leftResult.state leftResult.remaining leftResult.value.1 leftResult.value.2 candidates)
        (continuePermissiveRootAvoidingDetailedOrdinalSelection target rightObserve
          rightResult.state rightResult.remaining rightResult.value.1 rightResult.value.2
          candidates)
        (RootHiddenPermissiveSelectionRel target leftOutput rightOutput)) :
    RelTriple
      (runPermissiveFromTable leftState fuel table
          ((resolvePublicKnownInput parameter publicState (.position target) input).run
            leftCache) >>=
        finishPermissiveDetailedPrivateOrdinalSelection
          (continuePermissiveRootAvoidingDetailedOrdinalSelection target leftObserve) candidates)
      (runPermissiveFromTable rightState fuel table
          ((resolvePublicKnownInput parameter publicState (.position target) input).run
            rightCache) >>=
        finishPermissiveDetailedPrivateOrdinalSelection
          (continuePermissiveRootAvoidingDetailedOrdinalSelection target rightObserve) candidates)
      (RootHiddenPermissiveSelectionRel target leftOutput rightOutput) := by
  unfold resolvePublicKnownInput
  cases hknown : purePeekTableInput parameter publicState (.position target) with
  | none =>
      apply relTriple_bind
        (rootHiddenPermissiveRelates_splitHashQuery_ordinary target leftOutput rightOutput input
          leftState rightState hstate fuel table leftCache rightCache hcache)
      intro leftResult rightResult hresult
      exact relTriple_finishPermissiveSelection_of_rootHidden target leftOutput rightOutput _ _
        candidates leftResult rightResult hresult hrecursive
  | some knownInput =>
      by_cases heq : knownInput = input
      · simp only [heq, ↓reduceIte]
        change RelTriple
          (runPermissiveFromTable leftState fuel table
              ((revealPublishOrdinaryInput (.position target) input).run leftCache) >>=
            finishPermissiveDetailedPrivateOrdinalSelection
              (continuePermissiveRootAvoidingDetailedOrdinalSelection target leftObserve)
              candidates)
          (runPermissiveFromTable rightState fuel table
              ((revealPublishOrdinaryInput (.position target) input).run rightCache) >>=
            finishPermissiveDetailedPrivateOrdinalSelection
              (continuePermissiveRootAvoidingDetailedOrdinalSelection target rightObserve)
              candidates)
          (RootHiddenPermissiveSelectionRel target leftOutput rightOutput)
        rw [runPermissiveFromTable_revealPublishOrdinaryInput_of_value table
            (.position target) input leftState fuel leftCache leftOutput hstate.left_target,
          runPermissiveFromTable_revealPublishOrdinaryInput_of_value table
            (.position target) input rightState fuel rightCache rightOutput hstate.right_target]
        simp [finishPermissiveDetailedPrivateOrdinalSelection,
          continuePermissiveRootAvoidingDetailedOrdinalSelection,
          LazyRevealProbe.State.publish, RootHiddenPermissiveSelectionRel]
      · simp only [heq, ↓reduceIte]
        apply relTriple_bind
          (rootHiddenPermissiveRelates_splitHashQuery_ordinary target leftOutput rightOutput input
            leftState rightState hstate fuel table leftCache rightCache hcache)
        intro leftResult rightResult hresult
        exact relTriple_finishPermissiveSelection_of_rootHidden target leftOutput rightOutput _ _
          candidates leftResult rightResult hresult hrecursive

set_option maxRecDepth 100000 in
theorem relTriple_targetPublicPlan_then_finishPermissive
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
      SplitHashCache → List Probe → ProbComp (Option PermissivePrivateOrdinalSelection))
    (candidates : List Probe)
    (hrecursive : ∀ leftResult rightResult,
      RootHiddenCleanRelWith target leftOutput rightOutput (fun x y => x = y)
        (some leftResult) (some rightResult) →
      RelTriple
        (continuePermissiveRootAvoidingDetailedOrdinalSelection target leftObserve
          leftResult.state leftResult.remaining leftResult.value.1 leftResult.value.2 candidates)
        (continuePermissiveRootAvoidingDetailedOrdinalSelection target rightObserve
          rightResult.state rightResult.remaining rightResult.value.1 rightResult.value.2
          candidates)
        (RootHiddenPermissiveSelectionRel target leftOutput rightOutput)) :
    RelTriple
      (runPermissiveFromTable leftState fuel table
          ((probingHashQueryAfterPublicPlan parameter input publicState plan).run leftCache) >>=
        finishPermissiveDetailedPrivateOrdinalSelection
          (continuePermissiveRootAvoidingDetailedOrdinalSelection target leftObserve) candidates)
      (runPermissiveFromTable rightState fuel table
          ((probingHashQueryAfterPublicPlan parameter input publicState plan).run rightCache) >>=
        finishPermissiveDetailedPrivateOrdinalSelection
          (continuePermissiveRootAvoidingDetailedOrdinalSelection target rightObserve) candidates)
      (RootHiddenPermissiveSelectionRel target leftOutput rightOutput) := by
  unfold probingHashQueryAfterPublicPlan
  rw [haction, StateT.run_bind, StateT.run_bind,
    runPermissiveFromTable_bind, runPermissiveFromTable_bind]
  simp only [bind_assoc]
  apply relTriple_bind
    (rootHiddenPermissiveRelates_executeCandidate target leftOutput rightOutput plan.candidate?
      leftState rightState hstate fuel table leftCache rightCache hcache)
  intro leftResult rightResult hresult
  cases leftResult with
  | none =>
      cases rightResult with
      | none => exact relTriple_pure_pure trivial
      | some right => simp [RootHiddenCleanRelWith] at hresult
  | some left =>
      cases rightResult with
      | none => simp [RootHiddenCleanRelWith] at hresult
      | some right =>
          rcases hresult with ⟨hnextState, hremaining, htable, _hvalue, hnextCache⟩
          simp only
          rw [← hremaining, ← htable]
          exact relTriple_targetPublicResolve_then_finishPermissive parameter target leftOutput
            rightOutput publicState input left.state right.state hnextState left.remaining left.table
            left.value.2 right.value.2 hnextCache leftObserve rightObserve candidates hrecursive

set_option maxRecDepth 100000 in
theorem relTriple_permissiveRootAvoiding_hash_hidden
    (ordinal : Nat) (parameter : PublicParameter) (target : Position)
    (leftOutput rightOutput : HashOutput) (input : HashInput)
    (candidates : List Probe)
    (leftState rightState : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (leftCache rightCache : SplitHashCache)
    (hstate : RootHiddenStateRel target leftOutput rightOutput leftState rightState)
    (hcache : RootHiddenCacheRel target leftOutput rightOutput leftCache rightCache)
    (leftObserve rightObserve : LazyRevealProbe.State Coordinate → Nat → HashOutput →
      SplitHashCache → List Probe → ProbComp (Option PermissivePrivateOrdinalSelection))
    (hrecursive : ∀ leftResult rightResult,
      RootHiddenCleanRelWith target leftOutput rightOutput (fun x y => x = y)
        (some leftResult) (some rightResult) →
      RelTriple
        (continuePermissiveRootAvoidingDetailedOrdinalSelection target leftObserve
          leftResult.state leftResult.remaining leftResult.value.1 leftResult.value.2
          (permissiveRootAwareCandidates parameter input table leftState candidates))
        (continuePermissiveRootAvoidingDetailedOrdinalSelection target rightObserve
          rightResult.state rightResult.remaining rightResult.value.1 rightResult.value.2
          (permissiveRootAwareCandidates parameter input table rightState candidates))
        (RootHiddenPermissiveSelectionRel target leftOutput rightOutput)) :
    RelTriple
      (if hselected : ordinal <
          (permissiveRootAwareCandidates parameter input table leftState candidates).length then
        pure (some
          ⟨(permissiveRootAwareCandidates parameter input table leftState candidates).get
            ⟨ordinal, hselected⟩, leftState,
            permissiveRootAwareCandidates parameter input table leftState candidates⟩)
      else
        let publicContext := materializedCanonicalContext table leftState
        let plan := purePlanProbingHashQuery parameter input publicContext.state
        let candidate? := rootAwareCandidateForPlan? parameter input plan
        if RootAwareCandidateAvoidsRoots target (truncateHash leftOutput)
            (truncateHash rightOutput) candidate? then
          runPermissiveFromTable leftState fuel table
              (delayedPermissivePublicAction parameter input table leftState leftCache) >>=
            finishPermissiveDetailedPrivateOrdinalSelection
              (continuePermissiveRootAvoidingDetailedOrdinalSelection target leftObserve)
              (permissiveRootAwareCandidates parameter input table leftState candidates)
        else pure none)
      (if hselected : ordinal <
          (permissiveRootAwareCandidates parameter input table rightState candidates).length then
        pure (some
          ⟨(permissiveRootAwareCandidates parameter input table rightState candidates).get
            ⟨ordinal, hselected⟩, rightState,
            permissiveRootAwareCandidates parameter input table rightState candidates⟩)
      else
        let publicContext := materializedCanonicalContext table rightState
        let plan := purePlanProbingHashQuery parameter input publicContext.state
        let candidate? := rootAwareCandidateForPlan? parameter input plan
        if RootAwareCandidateAvoidsRoots target (truncateHash leftOutput)
            (truncateHash rightOutput) candidate? then
          runPermissiveFromTable rightState fuel table
              (delayedPermissivePublicAction parameter input table rightState rightCache) >>=
            finishPermissiveDetailedPrivateOrdinalSelection
              (continuePermissiveRootAvoidingDetailedOrdinalSelection target rightObserve)
              (permissiveRootAwareCandidates parameter input table rightState candidates)
        else pure none)
      (RootHiddenPermissiveSelectionRel target leftOutput rightOutput) := by
  have hpublic := materializedCanonicalContext_state_eq_of_rootHidden hstate table
  have hcandidates :
      permissiveRootAwareCandidates parameter input table leftState candidates =
        permissiveRootAwareCandidates parameter input table rightState candidates := by
    unfold permissiveRootAwareCandidates permissiveRootAwarePlan
    rw [hpublic]
  by_cases hselected : ordinal <
      (permissiveRootAwareCandidates parameter input table leftState candidates).length
  · have hselectedRight : ordinal <
        (permissiveRootAwareCandidates parameter input table rightState candidates).length := by
      rw [← hcandidates]
      exact hselected
    simp only [hselected, hselectedRight, ↓reduceDIte]
    apply relTriple_pure_pure
    simp [RootHiddenPermissiveSelectionRel, hcandidates, hstate]
  · have hselectedRight : ¬ordinal <
        (permissiveRootAwareCandidates parameter input table rightState candidates).length := by
      rw [← hcandidates]
      exact hselected
    simp only [hselected, hselectedRight, ↓reduceDIte]
    have hcandidate :
        rootAwareCandidateForPlan? parameter input
            (purePlanProbingHashQuery parameter input
              (materializedCanonicalContext table leftState).state) =
          rootAwareCandidateForPlan? parameter input
            (purePlanProbingHashQuery parameter input
              (materializedCanonicalContext table rightState).state) := by
      rw [hpublic]
    by_cases hsafe : RootAwareCandidateAvoidsRoots target (truncateHash leftOutput)
        (truncateHash rightOutput)
        (rootAwareCandidateForPlan? parameter input
          (purePlanProbingHashQuery parameter input
            (materializedCanonicalContext table leftState).state))
    · have hsafeRight : RootAwareCandidateAvoidsRoots target (truncateHash leftOutput)
          (truncateHash rightOutput)
          (rootAwareCandidateForPlan? parameter input
            (purePlanProbingHashQuery parameter input
              (materializedCanonicalContext table rightState).state)) := by
        rw [← hcandidate]
        exact hsafe
      simp only [hsafe, hsafeRight, ↓reduceIte]
      let publicState := (materializedCanonicalContext table leftState).state
      let plan := purePlanProbingHashQuery parameter input publicState
      have hleftAction :
          delayedPermissivePublicAction parameter input table leftState leftCache =
            (probingHashQueryAfterPublicPlan parameter input publicState plan).run leftCache := by
        rfl
      have hrightAction :
          delayedPermissivePublicAction parameter input table rightState rightCache =
            (probingHashQueryAfterPublicPlan parameter input publicState plan).run rightCache := by
        unfold delayedPermissivePublicAction
        dsimp only
        rw [← hpublic]
      rw [hleftAction, hrightAction, ← hcandidates]
      letI : Decidable (plan.action = PlannedHashAction.resolve (.position target)) :=
        Classical.propDecidable _
      by_cases haction : plan.action = .resolve (.position target)
      · exact relTriple_targetPublicPlan_then_finishPermissive parameter target leftOutput
          rightOutput publicState input plan haction leftState rightState hstate fuel table leftCache
          rightCache hcache leftObserve rightObserve
          (permissiveRootAwareCandidates parameter input table leftState candidates)
          (by simpa [hcandidates] using hrecursive)
      · apply relTriple_bind
          (rootHiddenPermissiveRelates_probingHashQueryAfterPublicPlan parameter target leftOutput
            rightOutput input publicState plan haction leftState rightState hstate fuel table
            leftCache rightCache hcache)
        intro leftResult rightResult hresult
        apply relTriple_finishPermissiveSelection_of_rootHidden target leftOutput rightOutput _ _
          (permissiveRootAwareCandidates parameter input table leftState candidates)
          leftResult rightResult hresult
        simpa [hcandidates] using hrecursive
    · have hsafeRight : ¬RootAwareCandidateAvoidsRoots target (truncateHash leftOutput)
          (truncateHash rightOutput)
          (rootAwareCandidateForPlan? parameter input
            (purePlanProbingHashQuery parameter input
              (materializedCanonicalContext table rightState).state)) := by
        rw [← hcandidate]
        exact hsafe
      simp [hsafe, hsafeRight, RootHiddenPermissiveSelectionRel]

set_option maxHeartbeats 100000 in
set_option maxRecDepth 100000 in
theorem relTriple_permissiveRootAvoidingDetailedOrdinalSelection_hidden
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
    RelTriple
      (permissiveComparisonRootAvoidingDetailedOrdinalSelection ordinal parameter publicRoot
        target leftOutput rightOutput ftsSecret computation candidates leftState fuel table
        leftCache)
      (permissiveActualRootAvoidingDetailedOrdinalSelection ordinal parameter publicRoot target
        (truncateHash leftOutput) (truncateHash rightOutput) ftsSecret computation candidates
        rightState fuel table rightCache)
      (RootHiddenPermissiveSelectionRel target leftOutput rightOutput) := by
  classical
  induction computation using OracleComp.inductionOn generalizing
      candidates leftState rightState fuel leftCache rightCache with
  | pure value =>
      simp only [permissiveComparisonRootAvoidingDetailedOrdinalSelection,
        permissiveActualRootAvoidingDetailedOrdinalSelection,
        permissiveRootAvoidingDetailedOrdinalSelection, OracleComp.construct_pure]
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte]
        exact relTriple_pure_pure ⟨rfl, rfl, hstate⟩
      · simp only [hselected, ↓reduceDIte]
        exact relTriple_pure_pure trivial
  | query_bind query next ih =>
      unfold permissiveComparisonRootAvoidingDetailedOrdinalSelection
        permissiveActualRootAvoidingDetailedOrdinalSelection
      rw [permissiveRootAvoidingDetailedOrdinalSelection, OracleComp.construct_query_bind,
        permissiveRootAvoidingDetailedOrdinalSelection, OracleComp.construct_query_bind]
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte]
        exact relTriple_pure_pure ⟨rfl, rfl, hstate⟩
      · simp only [hselected, ↓reduceDIte]
        cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                let leftObserve :=
                  fun nextState remaining value nextCache laterCandidates =>
                    permissiveComparisonRootAvoidingDetailedOrdinalSelection ordinal parameter
                      publicRoot target leftOutput rightOutput ftsSecret (next value)
                      laterCandidates nextState remaining table nextCache
                let rightObserve :=
                  fun nextState remaining value nextCache laterCandidates =>
                    permissiveActualRootAvoidingDetailedOrdinalSelection ordinal parameter
                      publicRoot target (truncateHash leftOutput) (truncateHash rightOutput)
                      ftsSecret (next value) laterCandidates nextState remaining table nextCache
                apply relTriple_bind
                  (rootHiddenPermissiveRelates_splitUniformImpl target leftOutput rightOutput n
                    leftState rightState hstate fuel table leftCache rightCache hcache)
                intro leftResult rightResult hresult
                apply relTriple_finishPermissiveSelection_of_rootHidden target leftOutput
                  rightOutput _ _ candidates leftResult rightResult hresult
                intro nextLeft nextRight hnext
                rcases hnext with ⟨hnextState, hremaining, htable, hvalue, hnextCache⟩
                rw [← hremaining, ← hvalue]
                simp only [leftObserve, rightObserve]
                unfold continuePermissiveRootAvoidingDetailedOrdinalSelection
                have hreveal := hnextState.revealed
                by_cases hrevealed : Coordinate.position target ∈ nextLeft.state.revealed
                · have hrightRevealed :
                      Coordinate.position target ∈ nextRight.state.revealed := by
                    rwa [← hreveal]
                  simp [hrevealed, hrightRevealed, RootHiddenPermissiveSelectionRel]
                · have hrightRevealed :
                      Coordinate.position target ∉ nextRight.state.revealed := by
                    intro hmem
                    exact hrevealed (by rwa [hreveal])
                  simp only [hrevealed, hrightRevealed, ↓reduceIte]
                  exact ih nextLeft.value.1 candidates nextLeft.state nextRight.state
                    nextLeft.remaining nextLeft.value.2 nextRight.value.2 hnextState hnextCache
            | inr input =>
                let leftObserve :=
                  fun nextState remaining value nextCache laterCandidates =>
                    permissiveComparisonRootAvoidingDetailedOrdinalSelection ordinal parameter
                      publicRoot target leftOutput rightOutput ftsSecret (next value)
                      laterCandidates nextState remaining table nextCache
                let rightObserve :=
                  fun nextState remaining value nextCache laterCandidates =>
                    permissiveActualRootAvoidingDetailedOrdinalSelection ordinal parameter
                      publicRoot target (truncateHash leftOutput) (truncateHash rightOutput)
                      ftsSecret (next value) laterCandidates nextState remaining table nextCache
                apply relTriple_permissiveRootAvoiding_hash_hidden ordinal parameter target
                  leftOutput rightOutput input candidates leftState rightState fuel table leftCache
                  rightCache hstate hcache leftObserve rightObserve
                intro nextLeft nextRight hnext
                rcases hnext with ⟨hnextState, hremaining, _htable, hvalue, hnextCache⟩
                rw [← hremaining, ← hvalue]
                simp only [leftObserve, rightObserve]
                unfold continuePermissiveRootAvoidingDetailedOrdinalSelection
                have hcandidates :
                    permissiveRootAwareCandidates parameter input table leftState candidates =
                      permissiveRootAwareCandidates parameter input table rightState candidates := by
                  unfold permissiveRootAwareCandidates permissiveRootAwarePlan
                  rw [materializedCanonicalContext_state_eq_of_rootHidden hstate table]
                rw [← hcandidates]
                have hreveal := hnextState.revealed
                by_cases hrevealed : Coordinate.position target ∈ nextLeft.state.revealed
                · have hrightRevealed :
                      Coordinate.position target ∈ nextRight.state.revealed := by
                    rwa [← hreveal]
                  simp [hrevealed, hrightRevealed, RootHiddenPermissiveSelectionRel]
                · have hrightRevealed :
                      Coordinate.position target ∉ nextRight.state.revealed := by
                    intro hmem
                    exact hrevealed (by rwa [hreveal])
                  simp only [hrevealed, hrightRevealed, ↓reduceIte]
                  exact ih nextLeft.value.1
                    (permissiveRootAwareCandidates parameter input table leftState candidates)
                    nextLeft.state nextRight.state nextLeft.remaining nextLeft.value.2
                    nextRight.value.2 hnextState hnextCache
        | inr message =>
            let leftObserve :=
              fun nextState remaining value nextCache laterCandidates =>
                permissiveComparisonRootAvoidingDetailedOrdinalSelection ordinal parameter
                  publicRoot target leftOutput rightOutput ftsSecret (next value) laterCandidates
                  nextState remaining table nextCache
            let rightObserve :=
              fun nextState remaining value nextCache laterCandidates =>
                permissiveActualRootAvoidingDetailedOrdinalSelection ordinal parameter publicRoot
                  target (truncateHash leftOutput) (truncateHash rightOutput) ftsSecret
                  (next value) laterCandidates nextState remaining table nextCache
            apply relTriple_bind
              (rootHiddenPermissiveRelates_maskedSignWithTargetComparison_actual parameter
                publicRoot ftsSecret target hroot leftOutput rightOutput message leftState rightState
                hstate fuel table leftCache rightCache hcache)
            intro leftResult rightResult hresult
            apply relTriple_finishPermissiveSelection_of_rootHidden target leftOutput rightOutput
              _ _ candidates leftResult rightResult hresult
            intro nextLeft nextRight hnext
            rcases hnext with ⟨hnextState, hremaining, _htable, hvalue, hnextCache⟩
            rw [← hremaining, ← hvalue]
            simp only [leftObserve, rightObserve]
            unfold continuePermissiveRootAvoidingDetailedOrdinalSelection
            have hreveal := hnextState.revealed
            by_cases hrevealed : Coordinate.position target ∈ nextLeft.state.revealed
            · have hrightRevealed :
                  Coordinate.position target ∈ nextRight.state.revealed := by
                rwa [← hreveal]
              simp [hrevealed, hrightRevealed, RootHiddenPermissiveSelectionRel]
            · have hrightRevealed :
                  Coordinate.position target ∉ nextRight.state.revealed := by
                intro hmem
                exact hrevealed (by rwa [hreveal])
              simp only [hrevealed, hrightRevealed, ↓reduceIte]
              exact ih nextLeft.value.1 candidates nextLeft.state nextRight.state
                nextLeft.remaining nextLeft.value.2 nextRight.value.2 hnextState hnextCache

theorem RootHiddenPermissiveSelectionRel.erase
    {target : Position} {leftOutput rightOutput : HashOutput}
    {left right : Option PermissivePrivateOrdinalSelection}
    (hrel : RootHiddenPermissiveSelectionRel target leftOutput rightOutput left right) :
    erasePermissivePrivateOrdinalSelection left =
      erasePermissivePrivateOrdinalSelection right := by
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some right => simp [RootHiddenPermissiveSelectionRel] at hrel
  | some left =>
      cases right with
      | none => simp [RootHiddenPermissiveSelectionRel] at hrel
      | some right =>
          simp only [RootHiddenPermissiveSelectionRel] at hrel
          simp [erasePermissivePrivateOrdinalSelection, hrel.1]

theorem evalDist_map_erase_permissiveRootAvoidingDetailedOrdinalSelection_hidden
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
        (erasePermissivePrivateOrdinalSelection <$>
          permissiveComparisonRootAvoidingDetailedOrdinalSelection ordinal parameter publicRoot
            target leftOutput rightOutput ftsSecret computation candidates leftState fuel table
            leftCache) =
      evalDist
        (erasePermissivePrivateOrdinalSelection <$>
          permissiveActualRootAvoidingDetailedOrdinalSelection ordinal parameter publicRoot target
            (truncateHash leftOutput) (truncateHash rightOutput) ftsSecret computation candidates
            rightState fuel table rightCache) := by
  have hrel := relTriple_permissiveRootAvoidingDetailedOrdinalSelection_hidden ordinal parameter
    publicRoot target hroot leftOutput rightOutput ftsSecret computation candidates leftState
    rightState fuel table leftCache rightCache hstate hcache
  have hprojected := relTriple_post_mono hrel fun left right relation => relation.erase
  have hmapped : RelTriple
      (erasePermissivePrivateOrdinalSelection <$>
        permissiveComparisonRootAvoidingDetailedOrdinalSelection ordinal parameter publicRoot
          target leftOutput rightOutput ftsSecret computation candidates leftState fuel table
          leftCache)
      (erasePermissivePrivateOrdinalSelection <$>
        permissiveActualRootAvoidingDetailedOrdinalSelection ordinal parameter publicRoot target
          (truncateHash leftOutput) (truncateHash rightOutput) ftsSecret computation candidates
          rightState fuel table rightCache)
      (fun left right => left = right) := relTriple_map hprojected
  exact evalDist_eq_of_relTriple_eqRel hmapped

end SphincsSecurity.Concrete.OtsProbeSimulation
