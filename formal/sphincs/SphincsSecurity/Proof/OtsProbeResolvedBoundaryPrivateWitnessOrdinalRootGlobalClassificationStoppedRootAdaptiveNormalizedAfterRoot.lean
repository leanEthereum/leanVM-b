import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveAfterRoot
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveNormalizeStructural

/-!
# Normalized adaptive coupling after the public root

The initialized adaptive coupling lands in the eager target-resolution proxy by exact structural
normalization. The remaining bridge from that proxy to the fully observed eager run is kept
directional.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedPublishedTreeRoot

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 1000000 in
theorem relTriple_indicator_observed_eagerDirectDelayed_afterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (q : Nat) (target : Position) (rightRoot : Digest)
    (rootResult : CleanRunResult (Digest × SplitHashCache))
    (hresult : some rootResult ∈ support
      (runCleanFromTable
        (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) (2 * q) table
        (maskedPublishedTreeRoot.run emptySplitHashCache)))
    (hbound : (retainedGameRestComputation adversary
      ⟨rootResult.value.1, parameter⟩).IsQueryBoundP IsOuterHash q)
    (hq : q ≤ 2 ^ securityBits)
    (hroot : IsLayerRoot target) :
    RelTriple
      ((successfulObservedRootComparisonIndicator table ordinal target ∘
          fun observed ↦ (observed, rightRoot)) <$>
        observedMaterializedBoundary parameter rootResult.value.1 ftsSecret
          (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
          rootResult.state rootResult.remaining table rootResult.value.2)
      (eagerDirectDelayedSelectedRootIndicator ordinal parameter rootResult.value.1 ftsSecret table
        target rightRoot
        (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) [] []
        (canonicalizeMaterializedValues table (directDeferredContext rootResult.state)) q
        rootResult.value.2)
      SuccessfulObservedIndicatorRel := by
  have hdelayed := relTriple_indicator_observed_directDelayed_afterRootResult ordinal adversary
    parameter table ftsSecret q target rightRoot rootResult hresult hbound hq hroot
  have hpending := pending_eq_empty_of_mem_runCleanFromTable_maskedPublishedTreeRoot
    (2 * q) table rootResult hresult
  have hvalid : (directDeferredContext rootResult.state).Valid := by
    constructor
    · intro position output hvalue
      simpa [directDeferredContext, directDeferredValues] using hvalue
    · intro coordinate output _hvalue hhit
      simp [directDeferredContext, LazyRevealProbe.State.hitAt,
        LazyRevealProbe.State.pendingAt, hpending] at hhit
  have htable := startTableAgrees_of_mem_runCleanFromTable
    (maskedPublishedTreeRoot.run emptySplitHashCache)
    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) (2 * q) table
    (startTableAgrees_empty table) rootResult hresult
  have hcompletable : DeferredCompletable table (directDeferredContext rootResult.state) := by
    apply deferredCompletable_of_valid_of_no_boundary_hit table
      (directDeferredContext rootResult.state) hvalid htable.2
    · rintro ⟨position, output, _hhidden, _hvalue, hhit⟩
      simp [directDeferredContext, LazyRevealProbe.State.hitAt,
        LazyRevealProbe.State.pendingAt, hpending] at hhit
    · rintro ⟨index, _hvalue, hhit⟩
      simp [directDeferredContext, LazyRevealProbe.State.hitAt,
        LazyRevealProbe.State.pendingAt, hpending] at hhit
    · simp [directDeferredContext, hpending]
  have hcanonical := valid_completable_canonicalizeMaterializedValues table
    (directDeferredContext rootResult.state) hvalid hcompletable
  apply relTriple_of_evalDist_eq_right _ hdelayed
  exact (evalDist_eagerDirectDelayedSelectedRootIndicator_eq
    (α := RetainedRestResult) ordinal parameter rootResult.value.1 ftsSecret table target rightRoot
    (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) [] []
    (canonicalizeMaterializedValues table (directDeferredContext rootResult.state)) q
    rootResult.value.2 (by simp) (by simp) (by simp) hcanonical.1 hcanonical.2).symm

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 1000000 in
theorem relTriple_indicator_afterRootResult_of_eagerProxy
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (q : Nat) (target : Position)
    (rootResult : CleanRunResult (Digest × SplitHashCache))
    (hresult : some rootResult ∈ support
      (runCleanFromTable
        (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) (2 * q) table
        (maskedPublishedTreeRoot.run emptySplitHashCache)))
    (hbound : (retainedGameRestComputation adversary
      ⟨rootResult.value.1, parameter⟩).IsQueryBoundP IsOuterHash q)
    (hq : q ≤ 2 ^ securityBits)
    (hroot : IsLayerRoot target)
    (hproxy : ∀ rightRoot,
      RelTriple
        (eagerDirectDelayedSelectedRootIndicator ordinal parameter rootResult.value.1 ftsSecret
          table target rightRoot
          (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) [] []
          (canonicalizeMaterializedValues table (directDeferredContext rootResult.state)) q
          rootResult.value.2)
        (fixedComparisonRootIndicator table ordinal target rootResult.value.1 rightRoot <$>
          resolvedEagerObservedRootComparisonAtRoot adversary parameter ftsSecret target
            rootResult)
        SuccessfulObservedIndicatorRel) :
    RelTriple
      (successfulObservedRootComparisonIndicator table ordinal target <$> (do
        let observed ← observedMaterializedBoundary parameter rootResult.value.1 ftsSecret
          (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
          rootResult.state rootResult.remaining table rootResult.value.2
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (retainObservedRoot rootResult.value.1 observed, rightRoot)))
      (successfulObservedRootComparisonIndicator table ordinal target <$>
        resolvedEagerObservedRootComparisonAfterRootResult adversary parameter ftsSecret target
          rootResult)
      SuccessfulObservedIndicatorRel := by
  apply relTriple_indicator_afterRootResult_of_fixedComparisonRoot ordinal adversary parameter
    table ftsSecret target rootResult
  intro rightRoot
  have hleft := relTriple_indicator_observed_eagerDirectDelayed_afterRootResult ordinal adversary
    parameter table ftsSecret q target rightRoot rootResult hresult hbound hq hroot
  let observed := observedMaterializedBoundary parameter rootResult.value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
    rootResult.state rootResult.remaining table rootResult.value.2
  have hretain : RelTriple
      (fixedComparisonRootIndicator table ordinal target rootResult.value.1 rightRoot <$> observed)
      ((successfulObservedRootComparisonIndicator table ordinal target ∘
          fun result ↦ (result, rightRoot)) <$> observed)
      SuccessfulObservedIndicatorRel := by
    apply relTriple_map
    apply relTriple_post_mono (relTriple_refl observed)
    intro left right heq hgood
    subst right
    change successfulObservedRootComparisonIndicator table ordinal target
      (retainObservedRoot rootResult.value.1 left, rightRoot) = true at hgood
    change successfulObservedRootComparisonIndicator table ordinal target
      (left, rightRoot) = true
    rw [successfulObservedRootComparisonIndicator_eq_true_iff] at hgood ⊢
    exact successfulDoomedFirstRootGoodForComparisonAt_of_retainObservedRoot table ordinal target
      rootResult.value.1 rightRoot left hgood
  have hfirst := SphincsSecurity.relTriple_trans_exists hretain hleft
  have hsecond := SphincsSecurity.relTriple_trans_exists hfirst (hproxy rightRoot)
  apply relTriple_post_mono hsecond
  intro observed resolved hrelation
  obtain ⟨proxy, hchain, heager⟩ := hrelation
  obtain ⟨middle, hretained, hnormalized⟩ := hchain
  exact fun htrue ↦ heager (hnormalized (hretained htrue))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 1000000 in
theorem probEvent_observedRootComparison_le_production_mul_of_eagerProxy
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (q : Nat) (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (hfuel : 2 * q < Fintype.card Digest)
    (hbound : ∀ root,
      (retainedGameRestComputation adversary ⟨root, parameter⟩).IsQueryBoundP IsOuterHash q)
    (hq : q ≤ 2 ^ securityBits)
    (hproxy : ∀ (rootResult : CleanRunResult (Digest × SplitHashCache)),
      some rootResult ∈ support
        (runCleanFromTable
          (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) (2 * q) table
          (maskedPublishedTreeRoot.run emptySplitHashCache)) →
      ∀ rightRoot,
        RelTriple
          (eagerDirectDelayedSelectedRootIndicator ordinal parameter rootResult.value.1 ftsSecret
            table target rightRoot
            (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) [] []
            (canonicalizeMaterializedValues table (directDeferredContext rootResult.state)) q
            rootResult.value.2)
          (fixedComparisonRootIndicator table ordinal target rootResult.value.1 rightRoot <$>
            resolvedEagerObservedRootComparisonAtRoot adversary parameter ftsSecret target
              rootResult)
          SuccessfulObservedIndicatorRel) :
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
  apply probEvent_observedRootComparison_le_production_mul_of_afterRootResult ordinal adversary
    parameter table ftsSecret q target hroot hparent hfuel
  intro rootResult hresult
  exact relTriple_indicator_afterRootResult_of_eagerProxy ordinal adversary parameter table
    ftsSecret q target rootResult hresult (hbound rootResult.value.1) hq hroot
    (hproxy rootResult hresult)

end SphincsSecurity.Concrete.OtsProbeSimulation
