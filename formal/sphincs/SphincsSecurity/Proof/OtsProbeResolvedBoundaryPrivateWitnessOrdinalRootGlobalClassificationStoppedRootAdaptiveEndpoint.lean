import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveReverse
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveNormalizedAfterRoot

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedPublishedTreeRoot

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 1000000 in
theorem relTriple_eagerProxy_resolvedObservedAtRoot_afterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (q : Nat) (target : Position) (rightRoot : Digest)
    (rootResult : CleanRunResult (Digest × SplitHashCache))
    (hresult : some rootResult ∈ support
      (runCleanFromTable
        (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) (2 * q) table
        (maskedPublishedTreeRoot.run emptySplitHashCache)))
    (hbound :
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, rootResult.value.1, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
            SecretKey))
        (retainedGameRestComputation adversary
          ⟨rootResult.value.1, parameter⟩)).IsQueryBoundP
            (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ securityBits)
    (hroot : IsLayerRoot target) :
    RelTriple
      (eagerDirectDelayedSelectedRootIndicator ordinal parameter rootResult.value.1 ftsSecret table
        target rightRoot
        (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) [] []
        (canonicalizeMaterializedValues table (directDeferredContext rootResult.state)) q
        rootResult.value.2)
      (fixedComparisonRootIndicator table ordinal target rootResult.value.1 rightRoot <$>
        resolvedEagerObservedRootComparisonAtRoot adversary parameter ftsSecret target rootResult)
      SuccessfulObservedIndicatorRel := by
  have hinitial := directDeferredContext_invariants_afterRootResult table (2 * q) rootResult hresult
  have hrootRaw := mem_support_runRaw_done_of_mem_runCleanFromTable_some
    (maskedPublishedTreeRoot.run emptySplitHashCache)
    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) (2 * q) table rootResult hresult
  have hrootPublished : PublishedValues rootResult.state :=
    preservesPublishedValues_maskedPublishedTreeRoot
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) emptySplitHashCache (2 * q)
      rootResult.state rootResult.remaining rootResult.value.1 rootResult.value.2
      publishedValues_empty hrootRaw
  have htable : rootResult.table = table ∧ StartTableAgrees rootResult.state table :=
    startTableAgrees_of_mem_runCleanFromTable
      (maskedPublishedTreeRoot.run emptySplitHashCache)
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) (2 * q) table
      (startTableAgrees_empty table) rootResult hresult
  have hrootChainValid : ChainState.ValidFor (fun _ ↦ True) rootResult.state :=
    preservesChainValid_maskedPublishedTreeRoot_true
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) emptySplitHashCache (2 * q)
      rootResult.state rootResult.remaining rootResult.value.1 rootResult.value.2
      (by simp [ChainState.ValidFor, LazyRevealProbe.State.empty]) hrootRaw
  have hrootPending : rootResult.state.pending = ∅ :=
    pending_eq_empty_of_mem_runCleanFromTable_maskedPublishedTreeRoot (2 * q) table rootResult
      hresult
  have hremaining : rootResult.remaining = 2 * q := by
    let observed : ObservedCleanRunResult (Digest × SplitHashCache) :=
      ⟨rootResult.state, rootResult.remaining, rootResult.value, rootResult.table, []⟩
    have hobserved : some observed ∈ support
        (runObservedCleanFromTable [] LazyRevealProbe.State.empty (2 * q) table
          (maskedPublishedTreeRoot.run emptySplitHashCache)) := by
      rw [← map_attachCleanProbeObservations_runCleanFromTable_of_probeFree
        (maskedPublishedTreeRoot.run emptySplitHashCache) [] LazyRevealProbe.State.empty (2 * q)
        table (maskedPublishedTreeRoot_probeFree emptySplitHashCache), support_map]
      exact ⟨some rootResult, hresult, rfl⟩
    simpa [observed] using
      (remaining_eq_fuel_of_mem_observed_of_probeFree
        (maskedPublishedTreeRoot.run emptySplitHashCache) [] LazyRevealProbe.State.empty (2 * q)
        table observed (maskedPublishedTreeRoot_probeFree emptySplitHashCache) hobserved)
  have hcapacity : 2 * q < Fintype.card Digest := by
    rw [show Fintype.card Digest = 2 ^ digestBits by simp]
    norm_num [securityBits, digestBits] at hq ⊢
    omega
  unfold eagerDirectDelayedSelectedRootIndicator
  simp only [List.length_nil, Nat.not_lt_zero, ↓reduceIte]
  unfold resolvedEagerObservedRootComparisonAtRoot
  simp only [map_eq_bind_pure_comp, bind_assoc]
  have hresolve := relTriple_resolveDeferredPositionValue_canonical_afterRootResult table (2 * q)
    target rootResult hresult
  have hleft := SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hresolve
    (fun resolved ↦ resolved ∈ support
      (resolveDeferredPositionValue target
        (canonicalizeMaterializedValues table (directDeferredContext rootResult.state))))
    (fun _ hsupport ↦ hsupport)
  have hboth := SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleft
  apply relTriple_bind hboth
  intro left right hrelation
  rcases hrelation with ⟨⟨hresolution, hleftSupport⟩, hrightSupport⟩
  cases left with
  | none =>
      cases right with
      | none => exact relTriple_pure_pure (fun hfalse ↦ (Bool.false_ne_true hfalse).elim)
      | some right => simp [FinalizationResolutionEq] at hresolution
  | some left =>
      cases right with
      | none => simp [FinalizationResolutionEq] at hresolution
      | some right =>
          simp only [pure_bind]
          let initial := canonicalizeMaterializedValues table
            (directDeferredContext rootResult.state)
          have hinitialCanonical := valid_completable_canonicalizeMaterializedValues table
            (directDeferredContext rootResult.state) hinitial.1 hinitial.2.1
          have hleftValid : left.toDeferredContext.Valid :=
            hinitialCanonical.1.of_resolveDeferredPositionValue target left hleftSupport
          have hleftCompletable : DeferredCompletable table left.toDeferredContext :=
            hinitialCanonical.2.of_resolveDeferredPositionValue hinitialCanonical.1 target left
              hleftSupport
          have hleftCanonical := left_resolution_canonical_afterRootResult table (2 * q) target
            rootResult hresult left hleftSupport
          have hleftState := resolveDeferredPositionValue_state_eq_clearPending target initial left
            hleftSupport
          have hinitialPublished : PublishedValues initial.state := by
            apply PublishedValues.to_canonicalizedMaterializedValues
              (context := directDeferredContext rootResult.state)
            simpa [directDeferredContext] using hrootPublished
          have hleftPublished : PublishedValues left.state := by
            rw [hleftState]
            intro coordinate hrevealed
            have hnonempty := hinitialPublished coordinate (by
              simpa [LazyRevealProbe.State.clearPending] using hrevealed)
            simpa [LazyRevealProbe.State.clearPending] using hnonempty
          have hleftChainValid : ChainState.ValidFor (fun _ ↦ True) left.state := by
            intro coordinate hcoordinate
            constructor
            · intro hsome
              by_contra hhidden
              rw [hleftCanonical] at hsome
              simp [publicMaterializedValues, hhidden] at hsome
            · exact ⟨hleftPublished coordinate, fun _ ↦ trivial⟩
          have hleftPrivate : left.toDeferredContext.values target = some left.output :=
            resolveDeferredPositionValue_installs target initial left hleftSupport
          have hleftPending : left.state.pending = ∅ := by
            rw [resolveDeferredPositionValue_pending target initial left hleftSupport]
            simp [initial, canonicalizeMaterializedValues, directDeferredContext, hrootPending,
              LazyRevealProbe.State.pendingAway]
          have hshadow := relTriple_directDelayed_observed_shadow ordinal parameter
            rootResult.value.1 rightRoot ftsSecret table target left.output hroot
            (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) [] []
            left.toDeferredContext q (2 * q) q q rootResult.value.2 hbound hleftValid
            hleftCompletable hleftPublished hleftCanonical hleftChainValid hleftPrivate
            (by simp [SnapshotsObservedAt]) (by simp [SnapshotsBefore])
            (by simp [CleanProbeObservationsTrackedBy])
            (by simp [CleanProbeObservationsCoverPending, hleftPending]) (by simp)
            (by simp [PendingCoveredBy, hleftPending]) (by simp) le_rfl le_rfl (by omega)
            (by simpa [hleftPending] using hcapacity)
          have hcanonicalized := canonicalized_resolutions_afterRootResult table target
            rootResult.state left right hleftSupport hrightSupport hresolution
          let leftCanonical := canonicalizeMaterializedValues table left.toDeferredContext
          let rightCanonical := canonicalizeMaterializedValues table right.toDeferredContext
          have hleftCanonicalEq : leftCanonical = left.toDeferredContext := by
            exact canonicalizeMaterializedValues_eq_of_canonical table left.toDeferredContext
              hleftCanonical
          have hrightState := resolveDeferredPositionValue_state_eq_clearPending target
            (directDeferredContext rootResult.state) right hrightSupport
          have hrightStarts : StartTableAgrees right.state table := by
            rw [hrightState]
            intro index output hvalue
            apply htable.2 index output
            simpa [directDeferredContext, LazyRevealProbe.State.clearPending] using hvalue
          have hrightChainValid : ChainState.ValidFor (fun _ ↦ True) right.state := by
            rw [hrightState]
            intro coordinate hcoordinate
            simpa [directDeferredContext, LazyRevealProbe.State.clearPending] using
              hrootChainValid coordinate hcoordinate
          have hrightMaterialized : materializedDeferredState rightCanonical =
              materializedDeferredState right.toDeferredContext := by
            exact ScratchLocal.materializedDeferredState_canonicalize_eq table
              right.toDeferredContext hrightStarts hrightChainValid
              hresolution.2.2.2.1.valuesConsistent
          have hstateEq : CompletionSafeStateEq table
              (materializedDeferredState left.toDeferredContext)
              (materializedDeferredState right.toDeferredContext) := by
            have hsafe := hcanonicalized.2.2.2
            rw [canonicalizeMaterializedValues_eq_of_canonical table left.toDeferredContext
              hleftCanonical,
              ScratchLocal.materializedDeferredState_canonicalize_eq table
                right.toDeferredContext hrightStarts hrightChainValid
                hresolution.2.2.2.1.valuesConsistent] at hsafe
            exact hsafe
          let leftObserved := observedMaterializedBoundary parameter rootResult.value.1 ftsSecret
            (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
            (materializedDeferredState left.toDeferredContext) (2 * q) table rootResult.value.2
          let rightObserved := observedMaterializedBoundary parameter rootResult.value.1 ftsSecret
            (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
            (materializedDeferredState right.toDeferredContext) (2 * q) table rootResult.value.2
          have hstateBridge : RelTriple
              ((successfulObservedRootComparisonIndicator table ordinal target ∘
                  fun observed ↦ (observed, rightRoot)) <$> leftObserved)
              ((successfulObservedRootComparisonIndicator table ordinal target ∘
                  fun observed ↦ (observed, rightRoot)) <$> rightObserved)
              (EqRel Bool) := by
            apply relTriple_indicator_observedMaterializedBoundary_completionSafeEq ordinal
              parameter rootResult.value.1 rightRoot ftsSecret table target
              (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
              (materializedDeferredState left.toDeferredContext)
              (materializedDeferredState right.toDeferredContext) (2 * q) rootResult.value.2
              hstateEq
            intro index output hvalue
            rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
            apply hresolution.2.1.leftStarts ⟨lay, tree, leafIdx, chainIdx⟩ output
            simpa [materializedDeferredState, OtsSecretIndex.coordinate] using hvalue
          have hstateImp : RelTriple
              ((successfulObservedRootComparisonIndicator table ordinal target ∘
                  fun observed ↦ (observed, rightRoot)) <$> leftObserved)
              ((successfulObservedRootComparisonIndicator table ordinal target ∘
                  fun observed ↦ (observed, rightRoot)) <$> rightObserved)
              SuccessfulObservedIndicatorRel := by
            apply relTriple_post_mono hstateBridge
            intro leftValue rightValue heq
            intro htrue
            rw [← heq]
            exact htrue
          change RelTriple _
            (fixedComparisonRootIndicator table ordinal target rootResult.value.1 rightRoot <$>
              observedMaterializedBoundary parameter rootResult.value.1 ftsSecret
                (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
                (materializedDeferredState right.toDeferredContext) rootResult.remaining
                rootResult.table
                (replaceHiddenRootCache target right.output rootResult.value.2))
            SuccessfulObservedIndicatorRel
          rw [hremaining, htable.1]
          have hfirst := SphincsSecurity.relTriple_trans_exists hshadow hstateImp
          let installedObserved := observedMaterializedBoundary parameter rootResult.value.1
            ftsSecret
            (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
            (materializedDeferredState right.toDeferredContext) (2 * q) table
            (replaceHiddenRootCache target right.output rootResult.value.2)
          have hordinary : ordinaryQueryCache rootResult.value.2 =
              ordinaryQueryCache
                (replaceHiddenRootCache target right.output rootResult.value.2) := by
            simpa [replaceHiddenRootCache] using
              (ordinaryQueryCache_update_hidden rootResult.value.2 (.position target) right.output).symm
          have hcacheBase := relTriple_observedMaterializedBoundary_ordinaryCache parameter
            rootResult.value.1 ftsSecret
            (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) [] []
            (materializedDeferredState right.toDeferredContext) (2 * q) table rootResult.value.2
            (replaceHiddenRootCache target right.output rootResult.value.2) hordinary
          have hcacheBridge : RelTriple
              ((successfulObservedRootComparisonIndicator table ordinal target ∘
                  fun observed ↦ (observed, rightRoot)) <$> rightObserved)
              ((successfulObservedRootComparisonIndicator table ordinal target ∘
                  fun observed ↦ (observed, rightRoot)) <$> installedObserved)
              SuccessfulObservedIndicatorRel := by
            apply relTriple_map
            apply relTriple_post_mono hcacheBase
            intro leftResult rightResult hrelation hleftGood
            cases leftResult with
            | none =>
              cases rightResult with
                | none => exact hleftGood
                | some rightResult => simp [ObservedOrdinaryCacheRel] at hrelation
            | some leftResult =>
                cases rightResult with
                | none => simp [ObservedOrdinaryCacheRel] at hrelation
                | some rightResult =>
                    rcases hrelation with
                      ⟨hstate, hremaining, htable, hvalue, _hcache, suffix,
                        hleftObservations, hrightObservations⟩
                    change successfulObservedRootComparisonIndicator table ordinal target
                      (some leftResult, rightRoot) = true at hleftGood
                    rw [successfulObservedRootComparisonIndicator_eq_true_iff] at hleftGood
                    change successfulObservedRootComparisonIndicator table ordinal target
                      (some rightResult, rightRoot) = true
                    rw [successfulObservedRootComparisonIndicator_eq_true_iff]
                    have hobservations : leftResult.observations = rightResult.observations := by
                      rw [hleftObservations, hrightObservations]
                    rcases hleftGood with
                      ⟨⟨⟨hfinish, hdoomed, hfirstRoot⟩, hposition⟩, hcomparison⟩
                    have hrightFinish := exists_finishObservedCleanRunFromTable_of_state_table_eq
                      leftResult rightResult hstate htable hfinish
                    have hrightDoomed :
                        ¬DeferredCompletable table (directDeferredContext rightResult.state) := by
                      rw [← hstate]
                      exact hdoomed
                    have hrightPosition :
                        observedFirstLayerRootPosition? ordinal (some rightResult) = some target := by
                      rw [← observedFirstLayerRootPosition?_eq_of_observations_eq ordinal
                        leftResult rightResult hobservations]
                      exact hposition
                    obtain ⟨_selected, _hselected, hfirst, _hroot⟩ := hfirstRoot
                    have hrightFirst := firstExistingHiddenHitAt_of_observations_eq leftResult
                      rightResult ordinal hobservations hfirst
                    have hrightFirstRoot :
                        ObservedCleanRunOption.FirstExistingHiddenRootHitAt ordinal
                          (some rightResult) :=
                      firstExistingHiddenRootHitAt_of_first_of_position rightResult ordinal target
                        hrightFirst hrightPosition
                    have hrightComparison : CandidatesAvoidRoot target rightRoot
                        (observedPrefixProbes ordinal (some rightResult)) := by
                      rw [← observedPrefixProbes_eq_of_observations_eq ordinal leftResult
                        rightResult hobservations]
                      exact hcomparison
                    exact ⟨⟨⟨hrightFinish, hrightDoomed, hrightFirstRoot⟩,
                      hrightPosition⟩, hrightComparison⟩
          have hsecond := SphincsSecurity.relTriple_trans_exists hfirst hcacheBridge
          have hretain : RelTriple
              ((successfulObservedRootComparisonIndicator table ordinal target ∘
                  fun observed ↦ (observed, rightRoot)) <$> installedObserved)
              (fixedComparisonRootIndicator table ordinal target rootResult.value.1 rightRoot <$>
                installedObserved)
              (EqRel Bool) := by
            apply relTriple_map
            apply relTriple_post_mono (relTriple_refl installedObserved)
            intro leftResult rightResult heq
            subst rightResult
            apply Bool.eq_iff_iff.mpr
            simp only [Function.comp_apply]
            unfold fixedComparisonRootIndicator
            rw [successfulObservedRootComparisonIndicator_eq_true_iff,
              successfulObservedRootComparisonIndicator_eq_true_iff]
            change
              ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt table ordinal
                  target rightRoot leftResult ↔
                ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt table ordinal
                  target rightRoot (retainObservedRoot rootResult.value.1 leftResult)
            exact (successfulDoomedFirstRootGoodForComparisonAt_retainObservedRoot_iff table
              ordinal target rootResult.value.1 rightRoot leftResult).symm
          have hretainImp : RelTriple
              ((successfulObservedRootComparisonIndicator table ordinal target ∘
                  fun observed ↦ (observed, rightRoot)) <$> installedObserved)
              (fixedComparisonRootIndicator table ordinal target rootResult.value.1 rightRoot <$>
                installedObserved)
              SuccessfulObservedIndicatorRel := by
            apply relTriple_post_mono hretain
            intro leftValue rightValue heq htrue
            rwa [← heq]
          have hfinal := SphincsSecurity.relTriple_trans_exists hsecond hretainImp
          apply relTriple_post_mono hfinal
          intro source retained hrelation
          obtain ⟨installed, htoInstalled, hretainResult⟩ := hrelation
          obtain ⟨rightState, htoRightState, hcacheResult⟩ := htoInstalled
          obtain ⟨leftState, hshadowResult, hstateResult⟩ := htoRightState
          exact fun htrue ↦
            hretainResult (hcacheResult (hstateResult (hshadowResult htrue)))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 1000000 in
theorem probEvent_observedRootComparison_le_production_mul
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (q : Nat) (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (hfuel : 2 * q < Fintype.card Digest)
    (hbound : ∀ root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ securityBits) :
    Pr[fun result : Option
          (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) × Digest ↦
        ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
          table ordinal target result.2 result.1 | do
      let observed ← observedMaterializedRetainedRunFromTable adversary parameter ftsSecret
        (2 * q) table
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      pure (observed, rightRoot)] ≤
      Pr[fun result ↦ materializedOrdinalSelectionAt target result.2 |
          materializedRootAwareOrdinalProductionExperimentAfterTable ordinal adversary parameter
            ftsSecret target (2 * q) table] *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  apply probEvent_observedRootComparison_le_production_mul_of_eagerProxy ordinal adversary
    parameter table ftsSecret q target hroot hparent hfuel hbound hq
  intro rootResult hresult rightRoot
  exact relTriple_eagerProxy_resolvedObservedAtRoot_afterRootResult ordinal adversary parameter
    table ftsSecret q target rightRoot rootResult hresult (hbound rootResult.value.1) hq hroot

end SphincsSecurity.Concrete.OtsProbeSimulation
