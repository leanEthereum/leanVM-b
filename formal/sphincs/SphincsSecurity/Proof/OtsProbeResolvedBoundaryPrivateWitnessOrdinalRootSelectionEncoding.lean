import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootSelectionMaterialized

/-!
# Encoding-side materialized selection coupling

On a prefix whose earlier candidates guess neither distinguished root, the actual signer and the
target-aware comparison signer preserve the encoding cache quotient. The selected candidate has
the same distribution in both runs.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

theorem rootEncodingCacheCouples_splitHashQuery_avoids
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (input : HashInput)
    (havoid : RootInputAvoids parameter target leftRoot rightRoot input) :
    RootEncodingCacheCouples parameter target leftRoot rightRoot
      (splitHashQuery (.ordinary input)) := by
  intro leftCache rightCache hcache state fuel table
  exact relTriple_splitHashQuery_same_avoids parameter target leftRoot rightRoot input havoid
    leftCache rightCache hcache state fuel table

theorem rootEncodingCacheCouples_resolvePublicKnownInput_avoids
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest)
    (publicState : LazyRevealProbe.State Coordinate)
    (coordinate : Coordinate) (input : HashInput)
    (havoid : RootInputAvoids parameter target leftRoot rightRoot input) :
    RootEncodingCacheCouples parameter target leftRoot rightRoot
      (resolvePublicKnownInput parameter publicState coordinate input) := by
  unfold resolvePublicKnownInput
  cases hknown : purePeekTableInput parameter publicState coordinate with
  | none =>
      exact rootEncodingCacheCouples_splitHashQuery_avoids parameter target leftRoot
        rightRoot input havoid
  | some knownInput =>
      by_cases heq : knownInput = input
      · simp only [heq, ↓reduceIte]
        apply (rootEncodingCacheCouples_revealCoordinateOutput parameter target leftRoot
          rightRoot coordinate).bind
        intro output
        apply (rootEncodingCacheCouples_publishCoordinate parameter target leftRoot rightRoot
          coordinate).bind
        intro _
        apply (rootEncodingCacheCouples_modifyOrdinary_avoids parameter target leftRoot rightRoot
          input havoid output).bind
        intro _
        exact rootEncodingCacheCouples_pure parameter target leftRoot rightRoot output
      · simp only [heq, ↓reduceIte]
        exact rootEncodingCacheCouples_splitHashQuery_avoids parameter target leftRoot
          rightRoot input havoid

theorem rootEncodingCacheCouples_probingHashQueryAfterPublicPlan_avoids
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (input : HashInput)
    (publicState : LazyRevealProbe.State Coordinate) (plan : PlannedHashQuery)
    (havoid : RootInputAvoids parameter target leftRoot rightRoot input) :
    RootEncodingCacheCouples parameter target leftRoot rightRoot
      (probingHashQueryAfterPublicPlan parameter input publicState plan) := by
  unfold probingHashQueryAfterPublicPlan
  apply (rootEncodingCacheCouples_executeCandidate parameter target leftRoot rightRoot
    plan.candidate?).bind
  intro _
  cases plan.action with
  | ordinary =>
      exact rootEncodingCacheCouples_splitHashQuery_avoids parameter target leftRoot
        rightRoot input havoid
  | resolve coordinate =>
      exact rootEncodingCacheCouples_resolvePublicKnownInput_avoids parameter target leftRoot
        rightRoot publicState coordinate input havoid

theorem evalDist_finishMaterializedSelection_eq_of_rootEncoding
    (observeLeft observeRight : LazyRevealProbe.State Coordinate → Nat → α →
      SplitHashCache → List Probe → ProbComp (Option Probe))
    (candidates : List Probe)
    (left right : Option (CleanRunResult (α × SplitHashCache)))
    (hrel : RootEncodingStoredCleanSameRel parameter target leftRoot rightRoot left right)
    (hnext : ∀ leftResult rightResult,
      RootEncodingStoredCleanSameRel parameter target leftRoot rightRoot
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
      | some rightResult => simp [RootEncodingStoredCleanSameRel] at hrel
  | some leftResult =>
      cases right with
      | none => simp [RootEncodingStoredCleanSameRel] at hrel
      | some rightResult => exact hnext leftResult rightResult hrel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem evalDist_materializedRootAvoidingOrdinalSelection_encoding
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
        (materializedActualRootAvoidingOrdinalSelection ordinal parameter publicRoot target
          (truncateHash leftOutput) (truncateHash rightOutput) ftsSecret computation candidates
          state fuel table leftCache) =
      evalDist
        (materializedComparisonRootAvoidingOrdinalSelection ordinal parameter publicRoot target
          leftOutput rightOutput ftsSecret computation candidates state fuel table rightCache) := by
  induction computation using OracleComp.inductionOn generalizing
      candidates state fuel leftCache rightCache with
  | pure value =>
      simp [materializedActualRootAvoidingOrdinalSelection,
        materializedComparisonRootAvoidingOrdinalSelection,
        materializedRootAvoidingOrdinalSelection]
  | query_bind query next ih =>
      unfold materializedActualRootAvoidingOrdinalSelection
        materializedComparisonRootAvoidingOrdinalSelection
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
                  by_cases hsafe : RootSafePlannedHash target
                      (truncateHash leftOutput) (truncateHash rightOutput) plan candidate?
                  · have hsafeActual : RootSafePlannedHash target
                        (truncateHash leftOutput) (truncateHash rightOutput)
                        (purePlanProbingHashQuery parameter input
                          (materializedCanonicalContext table state).state)
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state)) := by
                      simpa [publicContext, plan, candidate?] using hsafe
                    simp only [hsafeActual, ↓reduceIte]
                    have hinput : RootInputAvoids parameter target
                        (truncateHash leftOutput) (truncateHash rightOutput) input := by
                      apply rootInputAvoids_of_rootAwareCandidateAvoidsRoots
                      simpa [rootAwareCandidateForPlan?_purePlan] using hsafeActual.1
                    apply evalDist_bind_eq_of_relTriple_next _ _ _ _ _
                      (((rootEncodingCacheCouples_probingHashQueryAfterPublicPlan_avoids parameter
                        target (truncateHash leftOutput) (truncateHash rightOutput) input
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
                  · have hsafeActual : ¬RootSafePlannedHash target
                        (truncateHash leftOutput) (truncateHash rightOutput)
                        (purePlanProbingHashQuery parameter input
                          (materializedCanonicalContext table state).state)
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

end SphincsSecurity.Concrete.OtsProbeSimulation
