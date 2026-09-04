import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedProjection
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryDirect

/-!
# Hidden chain-start observations are unreachable

The masked signer reveals every materialized chain coordinate before returning to the adversary.
The published root and signer computations are probe-free, and the direct hash handler performs its
single probe before its probe-free public action. Consequently no retained observation can see a
materialized but hidden chain start.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

def NoExistingHiddenChainStartHits (observations : List CleanProbeObservation) : Prop :=
  ∀ observation ∈ observations, ¬observation.ExistingHiddenChainStartHit

theorem not_existingHiddenChainStartHit_cleanProbeObservation_of_chainValid
    (state : LazyRevealProbe.State Coordinate)
    (hvalid : ChainState.ValidFor (fun _ => True) state)
    (coordinate : Coordinate) (candidate : Digest) :
    ¬(cleanProbeObservation state coordinate candidate).ExistingHiddenChainStartHit := by
  intro hhit
  have hhidden := hhit.1.1
  obtain ⟨output, hvalue, _hcandidate⟩ := hhit.1.2
  obtain ⟨index, hcoordinate⟩ := hhit.2
  change coordinate = index.coordinate at hcoordinate
  have hchain : IsChainCoordinate coordinate := by
    rw [hcoordinate]
    simp [IsChainCoordinate, OtsSecretIndex.coordinate]
  have hstored : state.values coordinate ≠ none := by
    simp [cleanProbeObservation] at hvalue
    simp [hvalue]
  have hrevealed := (hvalid coordinate hchain).1 hstored
  simp [cleanProbeObservation, hrevealed] at hhidden

set_option maxRecDepth 100000 in
theorem chainValid_of_mem_runObservedCleanFromTable
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ObservedCleanRunResult (α × SplitHashCache))
    (hpreserves : PreservesChainValid (fun _ => True) computation)
    (hvalid : ChainState.ValidFor (fun _ => True) state)
    (hresult : some result ∈ support
      (runObservedCleanFromTable observations state fuel table (computation.run cache))) :
    ChainState.ValidFor (fun _ => True) result.state := by
  have hclean : some result.toClean ∈ support
      (runCleanFromTable state fuel table (computation.run cache)) := by
    rw [← map_projectObservedCleanRun_runObservedCleanFromTable
      (computation.run cache) observations state fuel table, support_map]
    exact ⟨some result, hresult, rfl⟩
  have hraw := mem_support_runRaw_done_of_mem_runCleanFromTable_some
    (computation.run cache) state fuel table result.toClean hclean
  rcases hvalue : result.value with ⟨value, finalCache⟩
  exact hpreserves state cache fuel result.state result.remaining value finalCache hvalid (by
    simpa [ObservedCleanRunResult.toClean, hvalue] using hraw)

theorem NoExistingHiddenChainStartHits.append_cleanProbeObservation
    {observations : List CleanProbeObservation}
    (hobservations : NoExistingHiddenChainStartHits observations)
    (state : LazyRevealProbe.State Coordinate)
    (hvalid : ChainState.ValidFor (fun _ => True) state)
    (coordinate : Coordinate) (candidate : Digest) :
    NoExistingHiddenChainStartHits
      (observations ++ [cleanProbeObservation state coordinate candidate]) := by
  intro observation hobservation
  simp only [List.mem_append, List.mem_singleton] at hobservation
  rcases hobservation with hold | rfl
  · exact hobservations observation hold
  · exact not_existingHiddenChainStartHit_cleanProbeObservation_of_chainValid
      state hvalid coordinate candidate

theorem preservesChainValid_probingHashQueryPublicAction_true
    (parameter : PublicParameter) (input : HashInput)
    (publicState : LazyRevealProbe.State Coordinate) (action : PlannedHashAction) :
    PreservesChainValid (fun _ => True)
      (probingHashQueryPublicAction parameter input publicState action) := by
  cases action with
  | ordinary => exact preservesChainValid_splitHashQuery_ordinary (fun _ => True) input
  | resolve coordinate =>
      simp only [probingHashQueryPublicAction]
      unfold resolvePublicKnownInput
      cases purePeekTableInput parameter publicState coordinate with
      | none => exact preservesChainValid_splitHashQuery_ordinary (fun _ => True) input
      | some knownInput =>
          by_cases heq : knownInput = input
          · simp only [heq, ↓reduceIte]
            exact preservesChainValid_revealPublishOrdinary (fun _ => True) coordinate input
              (fun _ => trivial)
          · simp only [heq, ↓reduceIte]
            exact preservesChainValid_splitHashQuery_ordinary (fun _ => True) input

set_option maxRecDepth 100000 in
theorem rootAwarePublic_invariants_of_mem_runObservedCleanFromTable
    (parameter : PublicParameter) (input : HashInput)
    (publicState : LazyRevealProbe.State Coordinate) (plan : PlannedHashQuery)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ObservedCleanRunResult (HashOutput × SplitHashCache))
    (hobservations : NoExistingHiddenChainStartHits observations)
    (hvalid : ChainState.ValidFor (fun _ => True) state)
    (hresult : some result ∈ support
      (runObservedCleanFromTable observations state fuel table
        ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run cache))) :
    ChainState.ValidFor (fun _ => True) result.state ∧
      NoExistingHiddenChainStartHits result.observations := by
  let publicAction := probingHashQueryPublicAction parameter input publicState plan.action
  have hpreserves : PreservesChainValid (fun _ => True) publicAction :=
    preservesChainValid_probingHashQueryPublicAction_true parameter input publicState plan.action
  have hprobeFree (workingCache : SplitHashCache) :
      (publicAction.run workingCache).IsQueryBoundP
        (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 0 :=
    probingHashQueryPublicAction_probeFree parameter input publicState plan.action workingCache
  cases hcandidate : rootAwareCandidateForPlan? parameter input plan with
  | none =>
      rw [runObservedCleanFromTable_rootAwarePublic_of_none parameter input publicState plan
        observations state fuel table cache hcandidate] at hresult
      have hfinalValid := chainValid_of_mem_runObservedCleanFromTable publicAction observations
        state fuel table cache result hpreserves hvalid hresult
      have hobservationsEq := observations_eq_of_mem_runObservedCleanFromTable_of_probeFree
        (publicAction.run cache) observations state fuel table result (hprobeFree cache) hresult
      exact ⟨hfinalValid, hobservationsEq ▸ hobservations⟩
  | some candidate =>
      cases fuel with
      | zero =>
          unfold probingHashQueryAfterRootAwarePublicPlan at hresult
          rw [StateT.run_bind] at hresult
          simp [executeCandidate?, hcandidate, probe, LazyRevealProbe.probeQuery,
            runObservedCleanFromTable] at hresult
      | succ remaining =>
          have hnextObservations := hobservations.append_cleanProbeObservation state hvalid
            candidate.coordinate candidate.candidate
          by_cases hrevealed : candidate.coordinate ∈ state.revealed
          · rw [runObservedCleanFromTable_rootAwarePublic_of_revealed parameter input publicState
              plan candidate observations state remaining table cache hcandidate hrevealed]
              at hresult
            have hfinalValid := chainValid_of_mem_runObservedCleanFromTable publicAction
              (observations ++ [cleanProbeObservation state candidate.coordinate
                candidate.candidate]) state remaining table cache result hpreserves hvalid hresult
            have hobservationsEq := observations_eq_of_mem_runObservedCleanFromTable_of_probeFree
              (publicAction.run cache)
              (observations ++ [cleanProbeObservation state candidate.coordinate
                candidate.candidate]) state remaining table result (hprobeFree cache) hresult
            exact ⟨hfinalValid, hobservationsEq ▸ hnextObservations⟩
          · rw [runObservedCleanFromTable_rootAwarePublic_of_hidden parameter input publicState
              plan candidate observations state remaining table cache hcandidate hrevealed]
              at hresult
            have hnextValid := hvalid.addPending candidate.coordinate candidate.candidate
            have hfinalValid := chainValid_of_mem_runObservedCleanFromTable publicAction
              (observations ++ [cleanProbeObservation state candidate.coordinate
                candidate.candidate])
              (state.addPending candidate.coordinate candidate.candidate) remaining table cache
              result hpreserves hnextValid hresult
            have hobservationsEq := observations_eq_of_mem_runObservedCleanFromTable_of_probeFree
              (publicAction.run cache)
              (observations ++ [cleanProbeObservation state candidate.coordinate
                candidate.candidate])
              (state.addPending candidate.coordinate candidate.candidate) remaining table result
              (hprobeFree cache) hresult
            exact ⟨hfinalValid, hobservationsEq ▸ hnextObservations⟩

set_option maxRecDepth 100000 in
theorem probeFree_invariants_of_mem_runObservedCleanFromTable
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ObservedCleanRunResult (α × SplitHashCache))
    (hpreserves : PreservesChainValid (fun _ => True) computation)
    (hprobeFree : (computation.run cache).IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 0)
    (hobservations : NoExistingHiddenChainStartHits observations)
    (hvalid : ChainState.ValidFor (fun _ => True) state)
    (hresult : some result ∈ support
      (runObservedCleanFromTable observations state fuel table (computation.run cache))) :
    ChainState.ValidFor (fun _ => True) result.state ∧
      NoExistingHiddenChainStartHits result.observations := by
  have hfinalValid := chainValid_of_mem_runObservedCleanFromTable computation observations state
    fuel table cache result hpreserves hvalid hresult
  have hobservationsEq := observations_eq_of_mem_runObservedCleanFromTable_of_probeFree
    (computation.run cache) observations state fuel table result hprobeFree hresult
  exact ⟨hfinalValid, hobservationsEq ▸ hobservations⟩

set_option maxRecDepth 100000 in
theorem observedMaterializedBoundary_chain_invariants
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ObservedCleanRunResult (α × SplitHashCache))
    (hobservations : NoExistingHiddenChainStartHits observations)
    (hvalid : ChainState.ValidFor (fun _ => True) state)
    (hresult : some result ∈ support
      (observedMaterializedBoundary parameter root ftsSecret computation observations state fuel
        table cache)) :
    ChainState.ValidFor (fun _ => True) result.state ∧
      NoExistingHiddenChainStartHits result.observations := by
  induction computation using OracleComp.inductionOn generalizing
      observations state fuel table cache with
  | pure value =>
      simp [observedMaterializedBoundary] at hresult
      obtain rfl := hresult
      exact ⟨hvalid, hobservations⟩
  | query_bind query next ih =>
      rw [observedMaterializedBoundary, OracleComp.construct_query_bind] at hresult
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              rw [mem_support_bind_iff] at hresult
              obtain ⟨step?, hstep, hrest⟩ := hresult
              cases step? with
              | none => simp at hrest
              | some step =>
                  have hnext := probeFree_invariants_of_mem_runObservedCleanFromTable
                    (splitUniformImpl n) observations state fuel table cache step
                    (preservesChainValid_splitUniformImpl (fun _ => True) n)
                    (splitUniformImpl_probeFree n cache) hobservations hvalid hstep
                  exact ih step.value.1 step.observations step.state step.remaining table
                    step.value.2 hnext.2 hnext.1 (by
                      simpa only [observedMaterializedBoundary] using hrest)
          | inr input =>
              rw [mem_support_bind_iff] at hresult
              obtain ⟨step?, hstep, hrest⟩ := hresult
              cases step? with
              | none => simp at hrest
              | some step =>
                  let publicContext := materializedCanonicalContext table state
                  let plan := purePlanProbingHashQuery parameter input publicContext.state
                  have hnext := rootAwarePublic_invariants_of_mem_runObservedCleanFromTable
                    parameter input publicContext.state plan observations state fuel table cache
                    step hobservations hvalid hstep
                  exact ih step.value.1 step.observations step.state step.remaining table
                    step.value.2 hnext.2 hnext.1 (by
                      simpa only [observedMaterializedBoundary] using hrest)
      | inr message =>
          rw [mem_support_bind_iff] at hresult
          obtain ⟨step?, hstep, hrest⟩ := hresult
          cases step? with
          | none => simp at hrest
          | some step =>
              have hnext := probeFree_invariants_of_mem_runObservedCleanFromTable
                (maskedSign parameter root ftsSecret message) observations state fuel table cache
                step (preservesChainValid_maskedSign_true parameter root ftsSecret message)
                (maskedSign_probeFree parameter root ftsSecret message cache) hobservations hvalid
                hstep
              exact ih step.value.1 step.observations step.state step.remaining table
                step.value.2 hnext.2 hnext.1 (by
                  simpa only [observedMaterializedBoundary] using hrest)

theorem NoExistingHiddenChainStartHits.not_firstAt
    {observations : List CleanProbeObservation}
    (hobservations : NoExistingHiddenChainStartHits observations) (ordinal : Nat) :
    ¬FirstExistingHiddenChainStartHitAt observations ordinal := by
  rintro ⟨selected, _hordinal, hhit, _hfirst⟩
  exact hobservations (observations.get selected) (List.get_mem observations selected) hhit

def ObservedMaterializedOutputNoHiddenChainStartHits :
    Option (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) → Prop
  | none => True
  | some result => NoExistingHiddenChainStartHits result.observations

attribute [local irreducible] maskedPublishedTreeRoot in
set_option maxRecDepth 100000 in
theorem observedMaterializedOutputNoHiddenChainStartHits_of_mem_retainedRunFromTable
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (output : Option (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)))
    (houtput : output ∈ support
      (observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table)) :
    ObservedMaterializedOutputNoHiddenChainStartHits output := by
  unfold observedMaterializedRetainedRunFromTable at houtput
  rw [mem_support_bind_iff] at houtput
  obtain ⟨rootResult?, hroot, hrest⟩ := houtput
  cases rootResult? with
  | none =>
      simp at hrest
      subst output
      trivial
  | some rootResult =>
      rw [mem_support_bind_iff] at hrest
      obtain ⟨restResult?, hrestResult, hreturn⟩ := hrest
      cases restResult? with
      | none =>
          simp at hreturn
          subst output
          trivial
      | some restResult =>
          simp only [support_pure, Set.mem_singleton_iff] at hreturn
          subst output
          have hrootInvariants := probeFree_invariants_of_mem_runObservedCleanFromTable
            maskedPublishedTreeRoot [] LazyRevealProbe.State.empty fuel table emptySplitHashCache
            rootResult preservesChainValid_maskedPublishedTreeRoot_true
            (maskedPublishedTreeRoot_probeFree emptySplitHashCache)
            (by intro observation hobservation; simp at hobservation)
            (ChainState.validFor_empty (fun _ => True)) hroot
          have hrestInvariants := observedMaterializedBoundary_chain_invariants parameter
            rootResult.value.1
            ftsSecret (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩)
            rootResult.observations rootResult.state rootResult.remaining table rootResult.value.2
            restResult hrootInvariants.2 hrootInvariants.1 hrestResult
          exact hrestInvariants.2

end SphincsSecurity.Concrete.OtsProbeSimulation
