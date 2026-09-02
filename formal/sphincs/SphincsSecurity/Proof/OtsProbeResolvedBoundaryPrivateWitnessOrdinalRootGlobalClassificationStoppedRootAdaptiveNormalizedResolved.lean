import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveNormalizedAfterRoot

/-!
# Resolved adaptive selected-root bridge

The selected hash boundary composes the delayed fixed-output handoff with the administrative
normalization of its materialized state and observation prefix.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

theorem relTriple_boolImp_of_not_reverse
    (left right : ProbComp Bool)
    (hreverse : RelTriple (Bool.not <$> right) (Bool.not <$> left) BoolImp) :
    RelTriple left right BoolImp := by
  have hcontra : RelTriple (Bool.not <$> right) (Bool.not <$> left)
      (fun rightNot leftNot => BoolImp (!leftNot) (!rightNot)) := by
    apply relTriple_post_mono hreverse
    intro rightNot leftNot himp
    cases rightNot <;> cases leftNot <;> simp [BoolImp] at himp ⊢
  have hmapped := relTriple_map
    (R := fun rightValue leftValue : Bool => BoolImp leftValue rightValue)
    (f := Bool.not) (g := Bool.not) hcontra
  simp only [Functor.map_map, Bool.not_not] at hmapped
  simpa only [show (fun value : Bool => value) = id from rfl, id_map] using
    relTriple_symm hmapped

theorem runObservedCleanFromTable_splitUniformImpl
    (n fuel : Nat) (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    runObservedCleanFromTable observations state fuel table ((splitUniformImpl n).run cache) = (do
      let output ← liftM (unifSpec.query n)
      pure (some ⟨state, fuel, (output, cache), table, observations⟩)) := by
  rfl

set_option maxRecDepth 100000 in
theorem relTriple_directDelayed_uniform_observed
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (n : Nat)
    (next : Fin (n + 1) → OracleComp (OracleWorld + SigningSpec) RetainedRestResult)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hselected : ¬ordinal < snapshots.length)
    (hcompletable : DeferredCompletable table context)
    (hpublished : PublishedValues context.state)
    (hcanonical : CanonicalMaterializedValues table context)
    (hrecursive : ∀ output,
      RelTriple
        (directDelayedSelectedRootIndicator ordinal parameter publicRoot ftsSecret table target
          rightRoot (next output) snapshots observations context fuel cache)
        ((successfulObservedRootComparisonIndicator table ordinal target ∘
            fun observed ↦ (observed, rightRoot)) <$>
          observedMaterializedBoundary parameter publicRoot ftsSecret (next output) observations
            (materializedDeferredState context) fuel table cache)
        SuccessfulObservedIndicatorRel) :
    RelTriple
      (directDelayedSelectedRootIndicator ordinal parameter publicRoot ftsSecret table target
        rightRoot
        (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
          (Sum.inl (Sum.inl n))) >>= next)
        snapshots observations context fuel cache)
      ((successfulObservedRootComparisonIndicator table ordinal target ∘
          fun observed ↦ (observed, rightRoot)) <$>
        observedMaterializedBoundary parameter publicRoot ftsSecret
          (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
            (Sum.inl (Sum.inl n))) >>= next)
          observations (materializedDeferredState context) fuel table cache)
      SuccessfulObservedIndicatorRel := by
  rw [directDelayedSelectedRootIndicator_uniform_eq ordinal parameter publicRoot ftsSecret table
    target rightRoot n next snapshots observations context fuel cache hselected]
  rw [observedMaterializedBoundary_uniform_query_bind]
  rw [runDirectResolvedWitnessFromTable_splitUniformImpl,
    runObservedCleanFromTable_splitUniformImpl]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind]
  apply relTriple_bind (relTriple_refl (liftM (unifSpec.query n)))
  intro output _ houtput
  subst output
  simp only [finishDirectDelayedSelectedRootIndicator]
  unfold canonicalizeDirectDelayedSelectedRootIndicator
  rw [canonicalizeMaterializedValues_eq_of_canonical table context hcanonical]
  simp only [not_privateStructuralHit_of_deferredCompletable hcompletable,
    hpublished, hcompletable, ↓reduceIte]
  exact hrecursive _

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem relTriple_directDelayed_selected_hash_observed_of_good
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (output : HashOutput) (hroot : IsLayerRoot target)
    (input : HashInput)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) RetainedRestResult)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hbefore : snapshots.length = ordinal)
    (hcandidate : rootAwareCandidateForPlan? parameter input
      (purePlanProbingHashQuery parameter input context.state) =
        some ⟨.position target, truncateHash output⟩)
    (hstate : context.state.values (.position target) = none)
    (hhidden : Coordinate.position target ∉ context.state.revealed)
    (hprivate : context.values target = some output)
    (havoid : CandidatesAvoidRoots target (truncateHash output) rightRoot
      (snapshots.map PlannedProbeSnapshot.toProbe))
    (hcovered : PendingCoveredBy
      (snapshots.map PlannedProbeSnapshot.toProbe) context)
    (hvalid : context.Valid)
    (hcompletable : DeferredCompletable table context)
    (hpublished : PublishedValues context.state)
    (hcanonical : CanonicalMaterializedValues table context)
    (hobservationLength : observations.length = ordinal)
    (hprobes : observations.map CleanProbeObservation.toProbe =
      snapshots.map PlannedProbeSnapshot.toProbe)
    (hnoHit : ∀ observation ∈ observations, ¬observation.ExistingHiddenHit) :
    RelTriple
      (directDelayedSelectedRootIndicator ordinal parameter publicRoot ftsSecret table target
        rightRoot
        (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
          (Sum.inl (Sum.inr input))) >>= next)
        snapshots observations context fuel cache)
      ((successfulObservedRootComparisonIndicator table ordinal target ∘
          fun observed ↦ (observed, rightRoot)) <$>
        observedMaterializedBoundary parameter publicRoot ftsSecret
          (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
            (Sum.inl (Sum.inr input))) >>= next)
          observations (materializedDeferredState context) fuel table cache)
      SuccessfulObservedIndicatorRel := by
  let candidate : Probe := ⟨.position target, truncateHash output⟩
  let nextSnapshots := snapshots ++ [(⟨candidate, context⟩ : PlannedProbeSnapshot)]
  have hnotSelected : ¬ordinal < snapshots.length := by omega
  have hselected : ordinal < nextSnapshots.length := by
    simp [nextSnapshots, hbefore]
  have hget : nextSnapshots.get ⟨ordinal, hselected⟩ =
      (⟨candidate, context⟩ : PlannedProbeSnapshot) := by
    subst ordinal
    simp [nextSnapshots, List.get_eq_getElem]
  let selection : PrivateOrdinalSelection :=
    ⟨candidate, context, nextSnapshots.map PlannedProbeSnapshot.toProbe⟩
  have hselectionGood : selection.GoodForRoots target output rightRoot ordinal := by
    refine ⟨rfl, hstate, hhidden, hprivate, ?_⟩
    simpa [selection, nextSnapshots, hbefore] using havoid
  have hselectionCovered :
      PendingCoveredBy (selection.candidates.take ordinal) selection.context := by
    simpa [selection, nextSnapshots, hbefore] using hcovered
  have hselectedEq :
      directDelayedSelectedRootIndicator ordinal parameter publicRoot ftsSecret table target
          rightRoot
          (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
            (Sum.inl (Sum.inr input))) >>= next)
          snapshots observations context fuel cache =
        delayedSelectedRootIndicator ordinal parameter publicRoot ftsSecret table target
          rightRoot
          (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
            (Sum.inl (Sum.inr input))) >>= next)
          observations selection fuel cache := by
    rw [directDelayedSelectedRootIndicator_hash_eq_selected ordinal parameter publicRoot
      ftsSecret table target rightRoot input next snapshots observations context fuel cache
      hnotSelected]
    · rw [show
        (appendPlannedSnapshot snapshots
          (rootAwareCandidateForPlan? parameter input
            (purePlanProbingHashQuery parameter input context.state)) context).get
            ⟨ordinal, by simpa [appendPlannedSnapshot, hcandidate, candidate, nextSnapshots]
              using hselected⟩ =
          (⟨candidate, context⟩ : PlannedProbeSnapshot) by
            simpa [appendPlannedSnapshot, hcandidate, candidate, nextSnapshots] using hget]
      simp [selection, appendPlannedSnapshot, hcandidate, candidate, nextSnapshots]
    · simpa [appendPlannedSnapshot, hcandidate, candidate, nextSnapshots] using hselected
  rw [hselectedEq]
  have hqueryCandidate : ∀ (resolved : DeferredResolution),
      some resolved ∈ support
          (resolveDeferredPositionValue target selection.context) →
        rootAwareCandidateForPlan? parameter input
            (purePlanProbingHashQuery parameter input
              (materializedCanonicalContext table
                (materializedDeferredState resolved.toDeferredContext)).state) =
          some ⟨.position target, truncateHash output⟩ := by
    intro resolved hresolved
    have hresolvedValid := hvalid.of_resolveDeferredPositionValue target resolved hresolved
    have hresolvedCompletable :=
      hcompletable.of_resolveDeferredPositionValue hvalid target resolved hresolved
    have hresolvedCanonical := canonicalMaterializedValues_of_resolveDeferredPositionValue
      table target context resolved hpublished hcanonical hresolved
    have hcontextLE := finalizationContextLE_materializedDeferredContext hresolvedValid
      hresolvedCompletable
    have hvalues :
        (materializedCanonicalContext table
          (materializedDeferredState resolved.toDeferredContext)).state.values =
          resolved.state.values := by
      exact canonicalized_right_values_eq_of_finalizationContextLE hcontextLE rfl
        hresolvedCanonical
    have hpreserved := resolveDeferredPositionValue_preserves_state_values target context
      resolved hresolved
    rw [purePlanProbingHashQuery_eq_of_values_eq hvalues parameter input,
      purePlanProbingHashQuery_eq_of_values_eq hpreserved parameter input]
    exact hcandidate
  have hselectedBridge := relTriple_delayedSelectedRootIndicator_hash_query ordinal parameter
    publicRoot ftsSecret table target output rightRoot hroot input next observations selection
    hselectionGood hselectionCovered hobservationLength
    (by
      intro probe hprobe
      exact (havoid probe (by simpa [hprobes] using hprobe)).1)
    fuel cache hqueryCandidate
  have hinstalledState :
      materializedDeferredState
          { selection.context with
            values := selection.context.values.install target output } =
        materializedDeferredState context := by
    simpa [selection] using
      materializedDeferredState_install_eq_of_value context target output hprivate
  have hinstalledNoHit :
      ∀ observation ∈ observations.map (installPositionValueAtProbe target output),
        ¬observation.ExistingHiddenHit := by
    apply no_existingHiddenHit_map_installPositionValueAtProbe_of_avoids target output
    · intro observation hobservation
      exact hnoHit observation hobservation
    · intro probe hprobe
      exact (havoid probe (by simpa [hprobes] using hprobe)).1
  let computation :=
    liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
      (Sum.inl (Sum.inr input))) >>= next
  let installedRun := observedMaterializedBoundary parameter publicRoot ftsSecret computation
    (observations.map (installPositionValueAtProbe target output))
    (materializedDeferredState context) fuel table cache
  let actualRun := observedMaterializedBoundary parameter publicRoot ftsSecret computation
    observations (materializedDeferredState context) fuel table cache
  have hretain : RelTriple
      (fixedComparisonRootIndicator table ordinal target publicRoot rightRoot <$> installedRun)
      ((successfulObservedRootComparisonIndicator table ordinal target ∘
          fun observed ↦ (observed, rightRoot)) <$> installedRun)
      SuccessfulObservedIndicatorRel := by
    apply relTriple_map
    apply relTriple_post_mono (relTriple_refl installedRun)
    intro left right heq hgood
    subst right
    change successfulObservedRootComparisonIndicator table ordinal target
      (retainObservedRoot publicRoot left, rightRoot) = true at hgood
    change successfulObservedRootComparisonIndicator table ordinal target
      (left, rightRoot) = true
    rw [successfulObservedRootComparisonIndicator_eq_true_iff] at hgood ⊢
    exact successfulDoomedFirstRootGoodForComparisonAt_of_retainObservedRoot table ordinal target
      publicRoot rightRoot left hgood
  have hprefixed : RelTriple
      ((successfulObservedRootComparisonIndicator table ordinal target ∘
          fun observed ↦ (observed, rightRoot)) <$> installedRun)
      ((successfulObservedRootComparisonIndicator table ordinal target ∘
          fun observed ↦ (observed, rightRoot)) <$> actualRun)
      SuccessfulObservedIndicatorRel := by
    apply relTriple_indicator_observedMaterializedBoundary_ordinaryCache ordinal parameter
      publicRoot rightRoot ftsSecret table target computation
      (observations.map (installPositionValueAtProbe target output)) observations
      (materializedDeferredState context) fuel cache cache rfl
    · simpa using hobservationLength
    · exact map_toProbe_map_installPositionValueAtProbe target output observations
    · exact hinstalledNoHit
    · exact hnoHit
  rw [hinstalledState] at hselectedBridge
  change RelTriple _ (fixedComparisonRootIndicator table ordinal target publicRoot rightRoot <$>
    installedRun) SuccessfulObservedIndicatorRel at hselectedBridge
  have hfirst := SphincsSecurity.relTriple_trans_exists hselectedBridge hretain
  have hsecond := SphincsSecurity.relTriple_trans_exists hfirst hprefixed
  apply relTriple_post_mono hsecond
  intro source actual hrelation
  obtain ⟨middle, hsource, hactual⟩ := hrelation
  obtain ⟨retained, hfirst, hsecond⟩ := hsource
  exact fun htrue ↦ hactual (hsecond (hfirst htrue))

end SphincsSecurity.Concrete.OtsProbeSimulation
