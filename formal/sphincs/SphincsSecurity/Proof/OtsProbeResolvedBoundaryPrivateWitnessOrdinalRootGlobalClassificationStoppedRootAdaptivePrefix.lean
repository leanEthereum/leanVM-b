import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveBridge

/-!
# Adaptive selected-root prefix

This file keeps the deferred prefix and its chronological observations together. When the chosen
ordinal is appended, it resolves that root and hands the complete current query and suffix to the
compiled selected-root bridge.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable

noncomputable def delayedSelectedRootIndicator
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (selection : PrivateOrdinalSelection) (fuel : Nat) (cache : SplitHashCache) :
    ProbComp Bool := do
  let resolved ← resolveDeferredPositionValue target selection.context
  match resolved with
  | none => pure false
  | some resolved =>
      if CandidatesAvoidRoots target (truncateHash resolved.output) rightRoot
          (selection.candidates.take ordinal) then
        (successfulObservedRootComparisonIndicator table ordinal target ∘
            fun observed => (observed, rightRoot)) <$>
          observedMaterializedBoundary parameter root ftsSecret computation observations
            (materializedDeferredState resolved.toDeferredContext) fuel table cache
      else pure false

theorem successfulDoomedFirstRootGoodForComparisonAt_retainObservedRoot
    (table : OtsSecretIndex → HashOutput) (ordinal : Nat) (target : Position)
    (root rightRoot : Digest)
    (observed : Option
      (ObservedCleanRunResult (RetainedRestResult × SplitHashCache)))
    (hgood : ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
      table ordinal target rightRoot observed) :
    ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
      table ordinal target rightRoot (retainObservedRoot root observed) := by
  cases observed with
  | none =>
      simp [ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt,
        ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget,
        ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt] at hgood
  | some result =>
      simp only [retainObservedRoot]
      rcases hgood with ⟨⟨⟨hfinish, hdoomed, hfirst⟩, hposition⟩, havoid⟩
      refine ⟨⟨⟨?_, hdoomed, ?_⟩, ?_⟩, ?_⟩
      · obtain ⟨finalResult, hfinalResult⟩ := hfinish
        unfold finishObservedCleanRunFromTable at hfinalResult
        rw [mem_support_bind_iff] at hfinalResult
        obtain ⟨finalized, hfinalized, hreturn⟩ := hfinalResult
        cases finalized with
        | none => simp at hreturn
        | some finalized =>
            obtain ⟨finalState, finalTable⟩ := finalized
            refine ⟨⟨finalState, result.remaining,
              ((root, result.value.1), result.value.2), finalTable,
              result.observations⟩, ?_⟩
            unfold finishObservedCleanRunFromTable
            rw [mem_support_bind_iff]
            exact ⟨some (finalState, finalTable), hfinalized, by simp⟩
      · simpa [ObservedCleanRunOption.FirstExistingHiddenRootHitAt,
          FirstExistingHiddenHitAt, ExistingHiddenHitAtOrdinal] using hfirst
      · simpa [observedFirstLayerRootPosition?] using hposition
      · simpa [observedPrefixProbes] using havoid

theorem successfulDoomedFirstRootGoodForComparisonAt_of_retainObservedRoot
    (table : OtsSecretIndex → HashOutput) (ordinal : Nat) (target : Position)
    (root rightRoot : Digest)
    (observed : Option
      (ObservedCleanRunResult (RetainedRestResult × SplitHashCache)))
    (hgood : ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
      table ordinal target rightRoot (retainObservedRoot root observed)) :
    ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
      table ordinal target rightRoot observed := by
  cases observed with
  | none =>
      simp [retainObservedRoot,
        ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt,
        ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget,
        ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt] at hgood
  | some result =>
      simp only [retainObservedRoot] at hgood
      rcases hgood with ⟨⟨⟨hfinish, hdoomed, hfirst⟩, hposition⟩, havoid⟩
      refine ⟨⟨⟨?_, hdoomed, ?_⟩, ?_⟩, ?_⟩
      · obtain ⟨finalResult, hfinalResult⟩ := hfinish
        unfold finishObservedCleanRunFromTable at hfinalResult
        rw [mem_support_bind_iff] at hfinalResult
        obtain ⟨finalized, hfinalized, hreturn⟩ := hfinalResult
        cases finalized with
        | none => simp at hreturn
        | some finalized =>
            obtain ⟨finalState, finalTable⟩ := finalized
            refine ⟨⟨finalState, result.remaining, result.value, finalTable,
              result.observations⟩, ?_⟩
            unfold finishObservedCleanRunFromTable
            rw [mem_support_bind_iff]
            exact ⟨some (finalState, finalTable), hfinalized, by simp⟩
      · simpa [ObservedCleanRunOption.FirstExistingHiddenRootHitAt,
          FirstExistingHiddenHitAt, ExistingHiddenHitAtOrdinal] using hfirst
      · simpa [observedFirstLayerRootPosition?] using hposition
      · simpa [observedPrefixProbes] using havoid

theorem successfulDoomedFirstRootGoodForComparisonAt_retainObservedRoot_iff
    (table : OtsSecretIndex → HashOutput) (ordinal : Nat) (target : Position)
    (root rightRoot : Digest)
    (observed : Option
      (ObservedCleanRunResult (RetainedRestResult × SplitHashCache))) :
    ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
        table ordinal target rightRoot (retainObservedRoot root observed) ↔
      ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
        table ordinal target rightRoot observed := by
  constructor
  · exact successfulDoomedFirstRootGoodForComparisonAt_of_retainObservedRoot
      table ordinal target root rightRoot observed
  · exact successfulDoomedFirstRootGoodForComparisonAt_retainObservedRoot
      table ordinal target root rightRoot observed

set_option maxRecDepth 100000 in
theorem relTriple_delayedSelectedRootIndicator
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (output : HashOutput)
    (rightRoot : Digest) (hroot : IsLayerRoot target)
    (computation : OracleComp (OracleWorld + SigningSpec) RetainedRestResult)
    (observations : List CleanProbeObservation)
    (selection : PrivateOrdinalSelection)
    (hgood : selection.GoodForRoots target output rightRoot ordinal)
    (hcovered : PendingCoveredBy (selection.candidates.take ordinal) selection.context)
    (fuel : Nat) (cache : SplitHashCache)
    (hselectedHit : ∀ result : ObservedCleanRunResult (RetainedRestResult × SplitHashCache),
      ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
          table ordinal target rightRoot (some result) →
        ∀ selected : Fin result.observations.length, selected.val = ordinal →
          (result.observations.get selected).coordinate = .position target ∧
            (result.observations.get selected).revealedAtProbe = false ∧
            truncateHash output = (result.observations.get selected).candidate)
    (hactualAvoid : ∀ result : ObservedCleanRunResult (RetainedRestResult × SplitHashCache),
      ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
          table ordinal target rightRoot (some result) →
        ∀ earlier : Fin result.observations.length, earlier.val < ordinal →
          (result.observations.get earlier).toProbe ≠
            ⟨.position target, truncateHash output⟩) :
    RelTriple
      (delayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
        computation observations selection fuel cache)
      (fixedComparisonRootIndicator table ordinal target root rightRoot <$>
        observedMaterializedBoundary parameter root ftsSecret computation
          (observations.map (installPositionValueAtProbe target output))
          (materializedDeferredState
            { selection.context with
              values := selection.context.values.install target output })
          fuel table cache)
      SuccessfulObservedIndicatorRel := by
  rw [delayedSelectedRootIndicator,
    resolveDeferredPositionValue_eq_good_output hgood hcovered]
  simp only [pure_bind, hgood.2.2.2.2, ↓reduceIte]
  let eager := observedMaterializedBoundary parameter root ftsSecret computation
    (observations.map (installPositionValueAtProbe target output))
    (materializedDeferredState
      { selection.context with
        values := selection.context.values.install target output })
    fuel table cache
  have hselected :=
    relTriple_indicator_resolveSelectedRoot_then_observedMaterializedBoundary parameter root
      ftsSecret target output rightRoot ordinal hroot selection hgood hcovered computation
      observations fuel table cache hselectedHit hactualAvoid
  rw [resolveDeferredPositionValue_eq_good_output hgood hcovered] at hselected
  simp only [pure_bind] at hselected
  have hretain : RelTriple
      ((successfulObservedRootComparisonIndicator table ordinal target ∘
          fun observed => (observed, rightRoot)) <$> eager)
      (fixedComparisonRootIndicator table ordinal target root rightRoot <$> eager)
      SuccessfulObservedIndicatorRel := by
    have hbase : RelTriple eager eager (fun left right =>
        SuccessfulObservedIndicatorRel
          ((successfulObservedRootComparisonIndicator table ordinal target ∘
            fun observed => (observed, rightRoot)) left)
          (fixedComparisonRootIndicator table ordinal target root rightRoot right)) := by
      apply relTriple_post_mono (relTriple_refl eager)
      intro left right hright hlazy
      subst right
      change successfulObservedRootComparisonIndicator table ordinal target
        (left, rightRoot) = true at hlazy
      change successfulObservedRootComparisonIndicator table ordinal target
        (retainObservedRoot root left, rightRoot) = true
      rw [successfulObservedRootComparisonIndicator_eq_true_iff] at hlazy ⊢
      exact successfulDoomedFirstRootGoodForComparisonAt_retainObservedRoot table ordinal target
        root rightRoot left hlazy
    exact relTriple_map
      (f := successfulObservedRootComparisonIndicator table ordinal target ∘
        fun observed => (observed, rightRoot))
      (g := fixedComparisonRootIndicator table ordinal target root rightRoot)
      hbase
  have hglued := SphincsSecurity.relTriple_trans_exists hselected hretain
  apply relTriple_post_mono hglued
  intro lazy retained hrelation
  obtain ⟨eagerResult, hlazy, hretained⟩ := hrelation
  exact fun htrue => hretained (hlazy htrue)

set_option maxRecDepth 100000 in
theorem relTriple_delayedSelectedRootIndicator_supported
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (output : HashOutput)
    (rightRoot : Digest) (hroot : IsLayerRoot target)
    (computation : OracleComp (OracleWorld + SigningSpec) RetainedRestResult)
    (observations : List CleanProbeObservation)
    (selection : PrivateOrdinalSelection)
    (hgood : selection.GoodForRoots target output rightRoot ordinal)
    (hcovered : PendingCoveredBy (selection.candidates.take ordinal) selection.context)
    (fuel : Nat) (cache : SplitHashCache)
    (hselectedHit : ∀ (resolved : DeferredResolution)
        (hresolved : some resolved ∈ support
          (resolveDeferredPositionValue target selection.context))
        (result : ObservedCleanRunResult (RetainedRestResult × SplitHashCache)),
      some result ∈ support
          (observedMaterializedBoundary parameter root ftsSecret computation observations
            (materializedDeferredState resolved.toDeferredContext) fuel table cache) →
        ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
            table ordinal target rightRoot (some result) →
          ∀ selected : Fin result.observations.length, selected.val = ordinal →
            (result.observations.get selected).coordinate = .position target ∧
              (result.observations.get selected).revealedAtProbe = false ∧
              truncateHash output = (result.observations.get selected).candidate)
    (hactualAvoid : ∀ (resolved : DeferredResolution)
        (hresolved : some resolved ∈ support
          (resolveDeferredPositionValue target selection.context))
        (result : ObservedCleanRunResult (RetainedRestResult × SplitHashCache)),
      some result ∈ support
          (observedMaterializedBoundary parameter root ftsSecret computation observations
            (materializedDeferredState resolved.toDeferredContext) fuel table cache) →
        ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
            table ordinal target rightRoot (some result) →
          ∀ earlier : Fin result.observations.length, earlier.val < ordinal →
            (result.observations.get earlier).toProbe ≠
              ⟨.position target, truncateHash output⟩) :
    RelTriple
      (delayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
        computation observations selection fuel cache)
      (fixedComparisonRootIndicator table ordinal target root rightRoot <$>
        observedMaterializedBoundary parameter root ftsSecret computation
          (observations.map (installPositionValueAtProbe target output))
          (materializedDeferredState
            { selection.context with
              values := selection.context.values.install target output })
          fuel table cache)
      SuccessfulObservedIndicatorRel := by
  rw [delayedSelectedRootIndicator,
    resolveDeferredPositionValue_eq_good_output hgood hcovered]
  simp only [pure_bind, hgood.2.2.2.2, ↓reduceIte]
  let eager := observedMaterializedBoundary parameter root ftsSecret computation
    (observations.map (installPositionValueAtProbe target output))
    (materializedDeferredState
      { selection.context with
        values := selection.context.values.install target output })
    fuel table cache
  have hselected :=
    relTriple_indicator_resolveSelectedRoot_then_observedMaterializedBoundary_supported
      parameter root ftsSecret target output rightRoot ordinal hroot selection hgood hcovered
      computation observations fuel table cache hselectedHit hactualAvoid
  rw [resolveDeferredPositionValue_eq_good_output hgood hcovered] at hselected
  simp only [pure_bind] at hselected
  have hretain : RelTriple
      ((successfulObservedRootComparisonIndicator table ordinal target ∘
          fun observed => (observed, rightRoot)) <$> eager)
      (fixedComparisonRootIndicator table ordinal target root rightRoot <$> eager)
      SuccessfulObservedIndicatorRel := by
    have hbase : RelTriple eager eager (fun left right =>
        SuccessfulObservedIndicatorRel
          ((successfulObservedRootComparisonIndicator table ordinal target ∘
            fun observed => (observed, rightRoot)) left)
          (fixedComparisonRootIndicator table ordinal target root rightRoot right)) := by
      apply relTriple_post_mono (relTriple_refl eager)
      intro left right hright hlazy
      subst right
      change successfulObservedRootComparisonIndicator table ordinal target
        (left, rightRoot) = true at hlazy
      change successfulObservedRootComparisonIndicator table ordinal target
        (retainObservedRoot root left, rightRoot) = true
      rw [successfulObservedRootComparisonIndicator_eq_true_iff] at hlazy ⊢
      exact successfulDoomedFirstRootGoodForComparisonAt_retainObservedRoot table ordinal target
        root rightRoot left hlazy
    exact relTriple_map
      (f := successfulObservedRootComparisonIndicator table ordinal target ∘
        fun observed => (observed, rightRoot))
      (g := fixedComparisonRootIndicator table ordinal target root rightRoot)
      hbase
  have hglued := SphincsSecurity.relTriple_trans_exists hselected hretain
  apply relTriple_post_mono hglued
  intro lazy retained hrelation
  obtain ⟨eagerResult, hlazy, hretained⟩ := hrelation
  exact fun htrue => hretained (hlazy htrue)

noncomputable def finishDirectDelayedSelectedRootIndicator
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      List CleanProbeObservation → ProbComp Bool)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation) : DirectWitnessResult α → ProbComp Bool
  | .stoppedFuel => pure false
  | .stoppedOrdinary => pure false
  | .stoppedPrivate _ => pure false
  | .done result =>
      observe result.context result.remaining result.value snapshots observations

noncomputable def canonicalizeDirectDelayedSelectedRootIndicator
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      List CleanProbeObservation → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (value : α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation) : ProbComp Bool := by
  classical
  let canonical := canonicalizeMaterializedValues table context
  exact if PrivateStructuralHit canonical then pure false
    else if PublishedValues context.state then
      if DeferredCompletable table canonical then
        observe canonical fuel value snapshots observations
      else pure false
    else pure false

noncomputable def directDelayedSelectedRootIndicator
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) : ProbComp Bool := by
  classical
  exact OracleComp.construct
    (C := fun _ : OracleComp (OracleWorld + SigningSpec) α =>
      List PlannedProbeSnapshot → List CleanProbeObservation → DeferredContext → Nat →
        SplitHashCache → ProbComp Bool)
    (fun _value snapshots observations context fuel cache =>
      if hselected : ordinal < snapshots.length then
        delayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
          (pure _value) observations
          ⟨(snapshots.get ⟨ordinal, hselected⟩).probe,
            (snapshots.get ⟨ordinal, hselected⟩).context,
            snapshots.map PlannedProbeSnapshot.toProbe⟩ fuel cache
      else pure false)
    (fun query _next recursivelyRun snapshots observations context fuel cache =>
      if hselected : ordinal < snapshots.length then
        delayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
          (liftM (OracleSpec.query query) >>= _next) observations
          ⟨(snapshots.get ⟨ordinal, hselected⟩).probe,
            (snapshots.get ⟨ordinal, hselected⟩).context,
            snapshots.map PlannedProbeSnapshot.toProbe⟩ fuel cache
      else
        match query with
        | .inl (.inl n) =>
            runDirectResolvedWitnessFromTable context fuel table ((splitUniformImpl n).run cache) >>=
              finishDirectDelayedSelectedRootIndicator
                (canonicalizeDirectDelayedSelectedRootIndicator table
                  (fun nextContext remaining value laterSnapshots laterObservations =>
                    recursivelyRun value.1 laterSnapshots laterObservations nextContext remaining
                      value.2)) snapshots observations
        | .inl (.inr input) =>
            let plan := purePlanProbingHashQuery parameter input context.state
            let candidate? := rootAwareCandidateForPlan? parameter input plan
            let nextSnapshots := appendPlannedSnapshot snapshots candidate? context
            let nextObservations := observationsAfterCandidate observations
              (materializedDeferredState context) candidate?
            if hnextSelected : ordinal < nextSnapshots.length then
              delayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
                ((liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
                    (Sum.inl (Sum.inr input))) :
                    OracleComp (OracleWorld + SigningSpec) HashOutput) >>= _next) observations
                ⟨(nextSnapshots.get ⟨ordinal, hnextSelected⟩).probe,
                  (nextSnapshots.get ⟨ordinal, hnextSelected⟩).context,
                  nextSnapshots.map PlannedProbeSnapshot.toProbe⟩ fuel cache
            else
              runDirectResolvedWitnessFromTable context fuel table
                  ((probingHashQueryAfterPlan parameter input plan).run cache) >>=
                finishDirectDelayedSelectedRootIndicator
                  (canonicalizeDirectDelayedSelectedRootIndicator table
                    (fun nextContext remaining value laterSnapshots laterObservations =>
                      recursivelyRun value.1 laterSnapshots laterObservations nextContext remaining
                        value.2)) nextSnapshots nextObservations
        | .inr message =>
            runDirectResolvedWitnessFromTable context fuel table
                ((maskedSign parameter root ftsSecret message).run cache) >>=
              finishDirectDelayedSelectedRootIndicator
                (canonicalizeDirectDelayedSelectedRootIndicator table
                  (fun nextContext remaining value laterSnapshots laterObservations =>
                    recursivelyRun value.1 laterSnapshots laterObservations nextContext remaining
                      value.2)) snapshots observations)
    computation snapshots observations context fuel cache

theorem directDelayedSelectedRootIndicator_eq_selected
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hselected : ordinal < snapshots.length) :
    directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
        computation snapshots observations context fuel cache =
      delayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
        computation observations
        ⟨(snapshots.get ⟨ordinal, hselected⟩).probe,
          (snapshots.get ⟨ordinal, hselected⟩).context,
          snapshots.map PlannedProbeSnapshot.toProbe⟩ fuel cache := by
  induction computation using OracleComp.inductionOn generalizing
      snapshots observations context fuel cache with
  | pure value =>
      rw [directDelayedSelectedRootIndicator, OracleComp.construct_pure]
      simp only [hselected, ↓reduceDIte]
  | query_bind query next ih =>
      rw [directDelayedSelectedRootIndicator, OracleComp.construct_query_bind]
      simp only [hselected, ↓reduceDIte]

theorem directDelayedSelectedRootIndicator_hash_eq_selected
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (input : HashInput)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hbefore : ¬ordinal < snapshots.length)
    (hselected : ordinal <
      (appendPlannedSnapshot snapshots
        (rootAwareCandidateForPlan? parameter input
          (purePlanProbingHashQuery parameter input context.state)) context).length) :
    directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
        (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
          (Sum.inl (Sum.inr input))) >>= next)
        snapshots observations context fuel cache =
      delayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
        (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
          (Sum.inl (Sum.inr input))) >>= next)
        observations
        ⟨((appendPlannedSnapshot snapshots
            (rootAwareCandidateForPlan? parameter input
              (purePlanProbingHashQuery parameter input context.state)) context).get
              ⟨ordinal, hselected⟩).probe,
          ((appendPlannedSnapshot snapshots
            (rootAwareCandidateForPlan? parameter input
              (purePlanProbingHashQuery parameter input context.state)) context).get
              ⟨ordinal, hselected⟩).context,
          (appendPlannedSnapshot snapshots
            (rootAwareCandidateForPlan? parameter input
              (purePlanProbingHashQuery parameter input context.state)) context).map
                PlannedProbeSnapshot.toProbe⟩ fuel cache := by
  rw [directDelayedSelectedRootIndicator, OracleComp.construct_query_bind]
  simp only [hbefore, ↓reduceDIte]
  exact dif_pos hselected

theorem directDelayedSelectedRootIndicator_hash_eq_not_selected
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (input : HashInput)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hbefore : ¬ordinal < snapshots.length)
    (hselected : ¬ordinal <
      (appendPlannedSnapshot snapshots
        (rootAwareCandidateForPlan? parameter input
          (purePlanProbingHashQuery parameter input context.state)) context).length) :
    directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
        (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
          (Sum.inl (Sum.inr input))) >>= next)
        snapshots observations context fuel cache =
      runDirectResolvedWitnessFromTable context fuel table
          ((probingHashQueryAfterPlan parameter input
            (purePlanProbingHashQuery parameter input context.state)).run cache) >>=
        finishDirectDelayedSelectedRootIndicator
          (canonicalizeDirectDelayedSelectedRootIndicator table
            (fun nextContext remaining value laterSnapshots laterObservations =>
              directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
                rightRoot (next value.1) laterSnapshots laterObservations nextContext remaining
                value.2))
          (appendPlannedSnapshot snapshots
            (rootAwareCandidateForPlan? parameter input
              (purePlanProbingHashQuery parameter input context.state)) context)
          (observationsAfterCandidate observations
            (materializedDeferredState context)
            (rootAwareCandidateForPlan? parameter input
              (purePlanProbingHashQuery parameter input context.state))) := by
  rw [directDelayedSelectedRootIndicator, OracleComp.construct_query_bind]
  simp only [hbefore, ↓reduceDIte]
  exact dif_neg hselected

theorem directDelayedSelectedRootIndicator_uniform_eq
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (n : Nat) (next : Fin (n + 1) → OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hselected : ¬ordinal < snapshots.length) :
    directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
        (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
          (Sum.inl (Sum.inl n))) >>= next)
        snapshots observations context fuel cache =
      runDirectResolvedWitnessFromTable context fuel table ((splitUniformImpl n).run cache) >>=
        finishDirectDelayedSelectedRootIndicator
          (canonicalizeDirectDelayedSelectedRootIndicator table
            (fun nextContext remaining value laterSnapshots laterObservations ↦
              directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
                rightRoot (next value.1) laterSnapshots laterObservations nextContext remaining
                value.2))
          snapshots observations := by
  conv_lhs =>
    rw [directDelayedSelectedRootIndicator, OracleComp.construct_query_bind]
  simp only [hselected, ↓reduceDIte]
  change (runDirectResolvedWitnessFromTable context fuel table
      ((splitUniformImpl n).run cache) >>=
    finishDirectDelayedSelectedRootIndicator
      (canonicalizeDirectDelayedSelectedRootIndicator table
        (fun nextContext remaining value laterSnapshots laterObservations ↦
          directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
            rightRoot (next value.1) laterSnapshots laterObservations nextContext remaining
            value.2)) snapshots observations) = _
  rfl

theorem directDelayedSelectedRootIndicator_signing_eq
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (message : Message)
    (next : Option Signature → OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hselected : ¬ordinal < snapshots.length) :
    directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
        (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec) (Sum.inr message)) >>= next)
        snapshots observations context fuel cache =
      runDirectResolvedWitnessFromTable context fuel table
          ((maskedSign parameter root ftsSecret message).run cache) >>=
        finishDirectDelayedSelectedRootIndicator
          (canonicalizeDirectDelayedSelectedRootIndicator table
            (fun nextContext remaining value laterSnapshots laterObservations ↦
              directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
                rightRoot (next value.1) laterSnapshots laterObservations nextContext remaining
                value.2))
          snapshots observations := by
  conv_lhs =>
    rw [directDelayedSelectedRootIndicator, OracleComp.construct_query_bind]
  simp only [hselected, ↓reduceDIte]
  change (runDirectResolvedWitnessFromTable context fuel table
      ((maskedSign parameter root ftsSecret message).run cache) >>=
    finishDirectDelayedSelectedRootIndicator
      (canonicalizeDirectDelayedSelectedRootIndicator table
        (fun nextContext remaining value laterSnapshots laterObservations ↦
          directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
            rightRoot (next value.1) laterSnapshots laterObservations nextContext remaining
            value.2)) snapshots observations) = _
  rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
