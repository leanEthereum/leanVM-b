import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveLift
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAwareSharedSemantic

/-!
# Adaptive selected-root coupling after the public root

This module initializes the adaptive selected-root relation at one supported result of the
probe-free public-root computation. The remaining target-resolution normalization is kept separate.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedPublishedTreeRoot

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem relTriple_indicator_observed_directDelayed_afterRootResult
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
      (directDelayedSelectedRootIndicator ordinal parameter rootResult.value.1 ftsSecret table
        target rightRoot
        (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) [] []
        (canonicalizeMaterializedValues table (directDeferredContext rootResult.state)) q
        rootResult.value.2)
      SuccessfulObservedIndicatorRel := by
  have hpending : rootResult.state.pending = ∅ :=
    pending_eq_empty_of_mem_runCleanFromTable_maskedPublishedTreeRoot (2 * q) table rootResult
      hresult
  have htable : rootResult.table = table ∧ StartTableAgrees rootResult.state table :=
    startTableAgrees_of_mem_runCleanFromTable
      (maskedPublishedTreeRoot.run emptySplitHashCache)
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) (2 * q) table
      (startTableAgrees_empty table) rootResult hresult
  have hraw := mem_support_runRaw_done_of_mem_runCleanFromTable_some
    (maskedPublishedTreeRoot.run emptySplitHashCache)
    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) (2 * q) table rootResult
    hresult
  have hpublished : PublishedValues rootResult.state :=
    preservesPublishedValues_maskedPublishedTreeRoot
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) emptySplitHashCache (2 * q)
      rootResult.state rootResult.remaining rootResult.value.1 rootResult.value.2
      publishedValues_empty hraw
  have hchainValid : ChainState.ValidFor (fun _ ↦ True) rootResult.state :=
    preservesChainValid_maskedPublishedTreeRoot_true
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) emptySplitHashCache (2 * q)
      rootResult.state rootResult.remaining rootResult.value.1 rootResult.value.2
      (by simp [ChainState.ValidFor, LazyRevealProbe.State.empty]) hraw
  let right := directDeferredContext rootResult.state
  have hvalid : right.Valid := by
    constructor
    · intro position output hvalue
      simpa [right, directDeferredContext, directDeferredValues] using hvalue
    · intro coordinate output _hvalue hhit
      simp [right, directDeferredContext, LazyRevealProbe.State.hitAt,
        LazyRevealProbe.State.pendingAt, hpending] at hhit
  have hprivate : ¬PrivateStructuralHit right := by
    rintro ⟨position, output, _hhidden, _hvalue, hhit⟩
    simp [right, directDeferredContext, LazyRevealProbe.State.hitAt,
      LazyRevealProbe.State.pendingAt, hpending] at hhit
  have hstart : ¬MissingChainStartHit table right := by
    rintro ⟨index, _hvalue, hhit⟩
    simp [right, directDeferredContext, LazyRevealProbe.State.hitAt,
      LazyRevealProbe.State.pendingAt, hpending] at hhit
  have hcard : right.state.pending.card < Fintype.card Digest := by
    simp [right, directDeferredContext, hpending]
  have hcompletable : DeferredCompletable table right :=
    deferredCompletable_of_valid_of_no_boundary_hit table right hvalid htable.2 hprivate hstart
      hcard
  have hclean : ∀ coordinate output,
      resolvedCompletionValue table right coordinate = some output →
        ¬right.state.hitAt coordinate output := by
    intro coordinate output _hvalue
    simp [right, directDeferredContext, LazyRevealProbe.State.hitAt,
      LazyRevealProbe.State.pendingAt, hpending]
  have hbase : FinalizationContextLE table right right :=
    { view := FinalizationViewLE.refl table right hvalid htable.2 hclean
      leftValid := hvalid
      rightValid := hvalid
      rightCompletable := hcompletable }
  let left := canonicalizeMaterializedValues table right
  have hcontext : FinalizationContextLE table left right := hbase.canonicalize_left
  have hvalues : LazyRevealProbe.ValuesLE left.state right.state :=
    valuesLE_canonicalizeMaterializedValues_left table right htable.2 hpublished
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
        table observed
        (maskedPublishedTreeRoot_probeFree emptySplitHashCache) hobserved)
  have hcapacity : 2 * q < Fintype.card Digest := by
    rw [show Fintype.card Digest = 2 ^ digestBits by simp]
    norm_num [securityBits, digestBits] at hq ⊢
    omega
  have hbudget : rootResult.remaining + right.state.pending.card < Fintype.card Digest := by
    rw [hremaining]
    change 2 * q + rootResult.state.pending.card < Fintype.card Digest
    rw [hpending]
    simpa using hcapacity
  have hrel := relTriple_indicator_observed_directDelayed ordinal parameter rootResult.value.1
    rightRoot ftsSecret table target hroot
    (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) [] [] [] left right q
    rootResult.remaining rootResult.value.2 rootResult.value.2 q q hbound hcontext rfl rfl
    hvalues hpublished.to_canonicalizedMaterializedValues rfl hchainValid
    (canonicalizeMaterializedValues_canonical table right hvalid.valuesConsistent)
    (by simp [SnapshotsObservedAt]) (by simp [SnapshotsBefore])
    (by simp [CleanProbeObservationsTrackedBy])
    (by simp [CleanProbeObservationsCoverPending, right, directDeferredContext, hpending])
    (by simp) (by simp) (by simp)
    (by simp [PendingCoveredBy, left, canonicalizeMaterializedValues, right, directDeferredContext,
      hpending]) le_rfl le_rfl (by omega) hbudget
  dsimp [left, right] at hrel
  simpa [directDeferredContext] using hrel

end SphincsSecurity.Concrete.OtsProbeSimulation
