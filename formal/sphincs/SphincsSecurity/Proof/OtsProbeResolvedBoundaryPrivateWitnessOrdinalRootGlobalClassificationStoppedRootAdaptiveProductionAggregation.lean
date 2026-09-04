import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveProductionCommonization

/-!
# Aggregating common root-production fibers

Every comparison probe emitted by the root-aware handler has a structural parent. The root fibers
can therefore be summed against the one target-independent selector.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

def CleanProbeObservationsHaveStructuralParents
    (observations : List CleanProbeObservation) : Prop :=
  ∀ observation ∈ observations, observation.toProbe.HasStructuralParent

theorem CleanProbeObservationsHaveStructuralParents.afterCandidate
    {observations : List CleanProbeObservation}
    {state : LazyRevealProbe.State Coordinate} {candidate? : Option Probe}
    (hobservations : CleanProbeObservationsHaveStructuralParents observations)
    (hcandidate : ∀ candidate, candidate? = some candidate → candidate.HasStructuralParent) :
    CleanProbeObservationsHaveStructuralParents
      (observationsAfterCandidate observations state candidate?) := by
  intro observation hobservation
  cases hoption : candidate? with
  | none =>
      have hmem : observation ∈ observations := by
        simpa [observationsAfterCandidate, hoption] using hobservation
      exact hobservations observation hmem
  | some candidate =>
      have hmem : observation ∈ observations ∨
          observation = cleanProbeObservation state candidate.coordinate candidate.candidate := by
        simpa [observationsAfterCandidate, hoption] using hobservation
      rcases hmem with hobservation | rfl
      · exact hobservations observation hobservation
      · simpa [CleanProbeObservation.toProbe, cleanProbeObservation] using
          hcandidate candidate hoption

set_option maxRecDepth 100000 in
theorem observationsHaveStructuralParents_of_mem_observedMaterializedBoundary
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ObservedCleanRunResult (α × SplitHashCache))
    (hparents : CleanProbeObservationsHaveStructuralParents observations)
    (hresult : some result ∈ support
      (observedMaterializedBoundary parameter root ftsSecret computation observations state fuel
        table cache)) :
    CleanProbeObservationsHaveStructuralParents result.observations := by
  induction computation using OracleComp.inductionOn generalizing
      observations state fuel table cache with
  | pure value =>
      simp [observedMaterializedBoundary] at hresult
      obtain rfl := hresult
      exact hparents
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
                  have heq := observations_eq_of_mem_runObservedCleanFromTable_of_probeFree
                    ((splitUniformImpl n).run cache) observations state fuel table step
                    (splitUniformImpl_probeFree n cache) hstep
                  apply ih step.value.1 step.observations step.state step.remaining table
                    step.value.2 (heq ▸ hparents)
                  simpa only [observedMaterializedBoundary] using hrest
          | inr input =>
              rw [mem_support_bind_iff] at hresult
              obtain ⟨step?, hstep, hrest⟩ := hresult
              cases step? with
              | none => simp at hrest
              | some step =>
                  let publicContext := materializedCanonicalContext table state
                  let plan := purePlanProbingHashQuery parameter input publicContext.state
                  have heq := observations_eq_of_mem_runObservedCleanFromTable_rootAwarePublic
                    parameter input publicContext.state plan observations state fuel table cache
                    step hstep
                  have hcandidates : ∀ candidate,
                      rootAwareCandidateForPlan? parameter input plan = some candidate →
                        candidate.HasStructuralParent := by
                    intro candidate hcandidate
                    rw [rootAwareCandidateForPlan?_purePlan] at hcandidate
                    exact rootAwarePlannedCandidate?_hasStructuralParent hcandidate
                  have hnext : CleanProbeObservationsHaveStructuralParents step.observations := by
                    rw [heq]
                    exact hparents.afterCandidate hcandidates
                  apply ih step.value.1 step.observations step.state step.remaining table
                    step.value.2 hnext
                  simpa only [observedMaterializedBoundary] using hrest
      | inr message =>
          rw [mem_support_bind_iff] at hresult
          obtain ⟨step?, hstep, hrest⟩ := hresult
          cases step? with
          | none => simp at hrest
          | some step =>
              have heq := observations_eq_of_mem_runObservedCleanFromTable_of_probeFree
                ((maskedSign parameter root ftsSecret message).run cache) observations state fuel
                table step (maskedSign_probeFree parameter root ftsSecret message cache) hstep
              apply ih step.value.1 step.observations step.state step.remaining table step.value.2
                (heq ▸ hparents)
              simpa only [observedMaterializedBoundary] using hrest

def ObservedMaterializedOutputHasStructuralParents :
    Option (ObservedCleanRunResult α) → Prop
  | none => True
  | some result => CleanProbeObservationsHaveStructuralParents result.observations

attribute [local irreducible] maskedPublishedTreeRoot in
set_option maxRecDepth 100000 in
theorem observedMaterializedOutputHasStructuralParents_of_mem_retainedRunFromTable
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (output : Option (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)))
    (houtput : output ∈ support
      (observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table)) :
    ObservedMaterializedOutputHasStructuralParents output := by
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
          have hrootObservations := observations_eq_of_mem_runObservedCleanFromTable_of_probeFree
            (maskedPublishedTreeRoot.run emptySplitHashCache) [] LazyRevealProbe.State.empty fuel
            table rootResult (maskedPublishedTreeRoot_probeFree emptySplitHashCache) hroot
          have hparents :
              CleanProbeObservationsHaveStructuralParents rootResult.observations := by
            rw [hrootObservations]
            intro observation hobservation
            simp at hobservation
          exact observationsHaveStructuralParents_of_mem_observedMaterializedBoundary parameter
            rootResult.value.1 ftsSecret
            (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩)
            rootResult.observations rootResult.state rootResult.remaining table rootResult.value.2
            restResult hparents hrestResult

attribute [local irreducible] maskedPublishedTreeRoot in
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem root_and_parent_of_successfulDoomedFirstRootHitAtTarget
    {adversary : Adversary} {parameter : PublicParameter}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    {fuel : Nat} {table : OtsSecretIndex → HashOutput}
    {ordinal : Nat} {target : Position}
    (observed : Option (ObservedCleanRunResult (RetainedGameResult × SplitHashCache))) :
    observed ∈ support
        (observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table) →
      ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget
          table ordinal target observed →
      IsLayerRoot target ∧ ∃ parent, Position.parentOf target = some parent := by
  cases observed with
  | none =>
      intro _hsupport hhit
      simp [ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget,
        ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt] at hhit
  | some result =>
      intro hsupport hhit
      have hparents : CleanProbeObservationsHaveStructuralParents result.observations := by
        unfold observedMaterializedRetainedRunFromTable at hsupport
        rw [mem_support_bind_iff] at hsupport
        obtain ⟨rootResult?, hrootResult, hrest⟩ := hsupport
        cases rootResult? with
        | none => simp at hrest
        | some rootResult =>
            rw [mem_support_bind_iff] at hrest
            obtain ⟨restResult?, hrestResult, hreturn⟩ := hrest
            cases restResult? with
            | none => simp at hreturn
            | some restResult =>
                simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at hreturn
                have hrootObservations :=
                  observations_eq_of_mem_runObservedCleanFromTable_of_probeFree
                    (maskedPublishedTreeRoot.run emptySplitHashCache) []
                    LazyRevealProbe.State.empty fuel table rootResult
                    (maskedPublishedTreeRoot_probeFree emptySplitHashCache) hrootResult
                have hrootParents :
                    CleanProbeObservationsHaveStructuralParents rootResult.observations := by
                  rw [hrootObservations]
                  intro observation hobservation
                  simp at hobservation
                have hrestParents :=
                  observationsHaveStructuralParents_of_mem_observedMaterializedBoundary parameter
                    rootResult.value.1 ftsSecret
                    (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩)
                    rootResult.observations rootResult.state rootResult.remaining table
                    rootResult.value.2 restResult hrootParents hrestResult
                rw [hreturn]
                exact hrestParents
      obtain ⟨⟨_final, _hdoomed, selected, hselected, _hfirst, _hroot⟩, hposition⟩ := hhit
      have hlt : ordinal < result.observations.length := by
        rw [← hselected]
        exact selected.isLt
      simp only [observedFirstLayerRootPosition?, hlt, ↓reduceDIte] at hposition
      have hindex : (⟨ordinal, hlt⟩ : Fin result.observations.length) = selected :=
        Fin.ext hselected.symm
      rw [candidateLayerRootPosition?_eq_some_iff, hindex] at hposition
      have hcandidateParent := hparents (result.observations.get selected)
        (List.get_mem result.observations selected)
      have hcoordinate :
          (result.observations.get selected).toProbe.coordinate = .position target := hposition.1
      unfold Probe.HasStructuralParent at hcandidateParent
      rw [hcoordinate] at hcandidateParent
      exact ⟨hposition.2, hcandidateParent⟩

attribute [local irreducible] maskedPublishedTreeRoot in
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem root_and_parent_of_existing_successfulDoomedFirstRootFiber
    {adversary : Adversary} {parameter : PublicParameter}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    {fuel : Nat} {table : OtsSecretIndex → HashOutput}
    {ordinal : Nat} {target : Position}
    (hexists : ∃ observed ∈ support
        (observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table),
        ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt table ordinal observed ∧
          observedFirstLayerRootPosition? ordinal observed = some target) :
    IsLayerRoot target ∧ ∃ parent, Position.parentOf target = some parent := by
  obtain ⟨observed, hsupport, hevent, hposition⟩ := hexists
  exact root_and_parent_of_successfulDoomedFirstRootHitAtTarget observed hsupport
    ⟨hevent, hposition⟩

attribute [local irreducible] maskedPublishedTreeRoot in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem probEvent_successfulDoomedFirstRoot_le_commonDetailed
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (q : Nat) (hordinal : ordinal < q)
    (hfuel : 2 * q < Fintype.card Digest)
    (hbound : ∀ root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ securityBits) :
    Pr[ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt table ordinal |
      observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table] ≤
      2 * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  apply probEvent_le_of_common_position_fibers
    (leftPosition := observedFirstLayerRootPosition? ordinal)
    (common := permissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter
      ftsSecret (2 * q) table)
    (commonPosition := permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition?)
  · intro observed hevent hnone
    exact not_successfulDoomedFirstRoot_of_position_eq_none hnone hevent
  · intro target
    by_cases hexists : ∃ observed ∈ support
        (observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table),
        ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt table ordinal observed ∧
          observedFirstLayerRootPosition? ordinal observed = some target
    · have hstructure :=
        root_and_parent_of_existing_successfulDoomedFirstRootFiber hexists
      simpa [ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget] using
        probEvent_successfulDoomedFirstRootFiber_le_commonDetailedFiber ordinal adversary
          parameter table ftsSecret q target hstructure.1 hstructure.2 hordinal hfuel hbound hq
    · simp only [not_exists, not_and] at hexists
      have hzero : Pr[fun observed =>
          ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt
              table ordinal observed ∧
            observedFirstLayerRootPosition? ordinal observed = some target |
          observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table] =
          0 := by
        apply probEvent_eq_zero
        intro observed hsupport hevent
        exact hexists observed hsupport hevent.1 hevent.2
      rw [hzero]
      exact zero_le

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
theorem probEvent_sampledDiagnostic_successfulDoomed_firstRoot_le
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (q : Nat) (hordinal : ordinal < q)
    (hfuel : 2 * q < Fintype.card Digest)
    (hbound : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ securityBits) :
    Pr[fun outcome => outcome.SuccessfulDoomed ∧
          outcome.FirstExistingHiddenRootHitAt ordinal |
        sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] ≤
      2 * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  apply probEvent_sampledDiagnostic_successfulDoomed_firstExistingHiddenRootHitAt_le_of_forall
  intro table
  exact probEvent_successfulDoomedFirstRoot_le_commonDetailed ordinal adversary parameter table
    ftsSecret q hordinal hfuel (hbound table) hq

end SphincsSecurity.Concrete.OtsProbeSimulation
