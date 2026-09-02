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

end SphincsSecurity.Concrete.OtsProbeSimulation
