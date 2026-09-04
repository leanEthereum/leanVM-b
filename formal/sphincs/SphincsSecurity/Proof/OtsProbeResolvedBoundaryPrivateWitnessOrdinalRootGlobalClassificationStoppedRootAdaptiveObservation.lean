import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptivePrefix

/-!
# Adaptive selected-query observations

The selected hash query appends exactly the observation at the chosen ordinal. Supported suffix
results retain that observation and the complete strict prefix.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

set_option maxRecDepth 100000 in
theorem selected_observation_eq_of_mem_observedMaterializedBoundary_hash_query
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : HashInput) (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (candidate : Probe)
    (hordinal : observations.length = ordinal)
    (hcandidate : rootAwareCandidateForPlan? parameter input
      (purePlanProbingHashQuery parameter input
        (materializedCanonicalContext table state).state) = some candidate)
    (result : ObservedCleanRunResult (α × SplitHashCache))
    (hresult : some result ∈ support
      (observedMaterializedBoundary parameter publicRoot ftsSecret
        (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
          (Sum.inl (Sum.inr input))) >>= next)
        observations state fuel table cache))
    (selected : Fin result.observations.length) (hselected : selected.val = ordinal) :
    result.observations.get selected =
      cleanProbeObservation state candidate.coordinate candidate.candidate := by
  rw [observedMaterializedBoundary_hash_query_bind, mem_support_bind_iff] at hresult
  obtain ⟨step?, hstep, hrest⟩ := hresult
  cases step? with
  | none => simp at hrest
  | some step =>
      let observation := cleanProbeObservation state candidate.coordinate candidate.candidate
      have hstepObservations : step.observations = observations ++ [observation] := by
        have hobservations :=
          observations_eq_of_mem_runObservedCleanFromTable_rootAwarePublic parameter input
            (materializedCanonicalContext table state).state
            (purePlanProbingHashQuery parameter input
              (materializedCanonicalContext table state).state)
            observations state fuel table cache step hstep
        simpa [observationsAfterCandidate, hcandidate, observation] using hobservations
      have htail : some result ∈ support
          (observedMaterializedBoundary parameter publicRoot ftsSecret (next step.value.1)
            step.observations step.state step.remaining table step.value.2) := by
        simpa only [observedMaterializedBoundary] using hrest
      have hprefix := observations_prefix_of_mem_observedMaterializedBoundary parameter publicRoot
        ftsSecret (next step.value.1) step.observations step.state step.remaining table step.value.2
        result htail
      have hstepIndex : observations.length < step.observations.length := by
        simp [hstepObservations]
      have hresultIndex : observations.length < result.observations.length :=
        lt_of_lt_of_le hstepIndex hprefix.length_le
      have hselectedEq : selected = ⟨observations.length, hresultIndex⟩ := by
        exact Fin.ext (hselected.trans hordinal.symm)
      rw [hselectedEq]
      have hget := hprefix.getElem hstepIndex
      have hstepGet : step.observations[observations.length] = observation := by
        simp [hstepObservations, observation]
      have hget' := hget.symm
      change result.observations[observations.length] =
        step.observations[observations.length] at hget'
      exact hget'.trans hstepGet

set_option maxRecDepth 100000 in
theorem earlier_observation_avoids_of_mem_observedMaterializedBoundary
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (target : Position) (digest : Digest)
    (hordinal : observations.length = ordinal)
    (havoid : CandidatesAvoidRoot target digest
      (observations.map CleanProbeObservation.toProbe))
    (result : ObservedCleanRunResult (α × SplitHashCache))
    (hresult : some result ∈ support
      (observedMaterializedBoundary parameter publicRoot ftsSecret computation observations state
        fuel table cache))
    (earlier : Fin result.observations.length) (hearlier : earlier.val < ordinal) :
    (result.observations.get earlier).toProbe ≠ ⟨.position target, digest⟩ := by
  have hprefix := observations_prefix_of_mem_observedMaterializedBoundary parameter publicRoot
    ftsSecret computation observations state fuel table cache result hresult
  have hinitial : earlier.val < observations.length := by omega
  have hget := hprefix.getElem hinitial
  have hmember : (observations.get ⟨earlier.val, hinitial⟩).toProbe ∈
      observations.map CleanProbeObservation.toProbe := by
    exact List.mem_map.mpr ⟨observations.get ⟨earlier.val, hinitial⟩,
      List.get_mem observations _, rfl⟩
  intro heq
  apply havoid _ hmember
  have hget' : result.observations.get earlier =
      observations.get ⟨earlier.val, hinitial⟩ := by
    have hget' := hget.symm
    change result.observations[earlier.val] = observations[earlier.val] at hget'
    exact hget'
  rw [hget'] at heq
  exact heq

open OracleComp.ProgramLogic.Relational

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem relTriple_delayedSelectedRootIndicator_hash_query
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (output : HashOutput)
    (rightRoot : Digest) (hroot : IsLayerRoot target)
    (input : HashInput)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) RetainedRestResult)
    (observations : List CleanProbeObservation)
    (selection : PrivateOrdinalSelection)
    (hgood : selection.GoodForRoots target output rightRoot ordinal)
    (hcovered : PendingCoveredBy (selection.candidates.take ordinal) selection.context)
    (hordinal : observations.length = ordinal)
    (havoid : CandidatesAvoidRoot target (truncateHash output)
      (observations.map CleanProbeObservation.toProbe))
    (fuel : Nat) (cache : SplitHashCache)
    (hqueryCandidate : ∀ (resolved : DeferredResolution),
      some resolved ∈ support
          (resolveDeferredPositionValue target selection.context) →
        rootAwareCandidateForPlan? parameter input
            (purePlanProbingHashQuery parameter input
              (materializedCanonicalContext table
                (materializedDeferredState resolved.toDeferredContext)).state) =
          some ⟨.position target, truncateHash output⟩) :
    RelTriple
      (delayedSelectedRootIndicator ordinal parameter publicRoot ftsSecret table target rightRoot
        (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
          (Sum.inl (Sum.inr input))) >>= next)
        observations selection fuel cache)
      (fixedComparisonRootIndicator table ordinal target publicRoot rightRoot <$>
        observedMaterializedBoundary parameter publicRoot ftsSecret
          (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
            (Sum.inl (Sum.inr input))) >>= next)
          (observations.map (installPositionValueAtProbe target output))
          (materializedDeferredState
            { selection.context with
              values := selection.context.values.install target output })
          fuel table cache)
      SuccessfulObservedIndicatorRel := by
  apply relTriple_delayedSelectedRootIndicator_supported ordinal parameter publicRoot ftsSecret
    table target output rightRoot hroot
    (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
      (Sum.inl (Sum.inr input))) >>= next)
    observations selection hgood hcovered fuel cache
  · intro resolved hresolved result hresult _hresultGood selected hselected
    have hprivate : Coordinate.position target ∉
        (materializedDeferredState resolved.toDeferredContext).revealed := by
      rw [materializedDeferredState_revealed,
        resolveDeferredPositionValue_state_eq_clearPending target selection.context resolved
          hresolved]
      simpa [LazyRevealProbe.State.clearPending] using hgood.2.2.1
    have hobservation :=
      selected_observation_eq_of_mem_observedMaterializedBoundary_hash_query ordinal parameter
        publicRoot ftsSecret input next observations
        (materializedDeferredState resolved.toDeferredContext) fuel table cache
        ⟨.position target, truncateHash output⟩ hordinal (hqueryCandidate resolved hresolved)
        result hresult selected hselected
    rw [hobservation]
    refine ⟨rfl, ?_, rfl⟩
    simp only [cleanProbeObservation, decide_eq_false_iff_not]
    simpa only [materializedDeferredState_revealed] using hprivate
  · intro resolved hresolved result hresult _hresultGood earlier hearlier
    exact earlier_observation_avoids_of_mem_observedMaterializedBoundary ordinal parameter
      publicRoot ftsSecret
      (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
        (Sum.inl (Sum.inr input))) >>= next)
      observations (materializedDeferredState resolved.toDeferredContext) fuel table cache target
      (truncateHash output) hordinal havoid result hresult earlier hearlier

end SphincsSecurity.Concrete.OtsProbeSimulation
