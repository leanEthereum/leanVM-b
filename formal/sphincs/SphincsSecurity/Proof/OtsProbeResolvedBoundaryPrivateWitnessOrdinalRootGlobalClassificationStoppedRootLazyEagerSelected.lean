import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootLazyEagerSuffix

/-!
# Selected-root lazy and eager handoff

At the selected query boundary, strict-prefix coverage makes resolution of the selected root
deterministic and collision-free. This file composes that fact with the synchronized suffix, so the
outer adaptive lift does not have to inspect the root-output sampler.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem relTriple_indicator_resolveSelectedRoot_then_observedMaterializedBoundary
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (output : HashOutput) (rightRoot : Digest)
    (ordinal : Nat) (hroot : IsLayerRoot target)
    (selection : PrivateOrdinalSelection)
    (hgood : selection.GoodForRoots target output rightRoot ordinal)
    (hcovered : PendingCoveredBy (selection.candidates.take ordinal) selection.context)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (cache : SplitHashCache)
    (hselectedHit : ∀ result : ObservedCleanRunResult (α × SplitHashCache),
      ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
          table ordinal target rightRoot (some result) →
        ∀ selected : Fin result.observations.length, selected.val = ordinal →
          (result.observations.get selected).coordinate = .position target ∧
            (result.observations.get selected).revealedAtProbe = false ∧
            truncateHash output = (result.observations.get selected).candidate)
    (hactualAvoid : ∀ result : ObservedCleanRunResult (α × SplitHashCache),
      ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
          table ordinal target rightRoot (some result) →
        ∀ earlier : Fin result.observations.length, earlier.val < ordinal →
          (result.observations.get earlier).toProbe ≠
            ⟨.position target, truncateHash output⟩) :
    RelTriple
      (resolveDeferredPositionValue target selection.context >>= fun resolved =>
        match resolved with
        | none => pure false
        | some resolved =>
            (successfulObservedRootComparisonIndicator table ordinal target ∘
                fun observed => (observed, rightRoot)) <$>
              observedMaterializedBoundary parameter root ftsSecret computation observations
                (materializedDeferredState resolved.toDeferredContext) fuel table cache)
      ((successfulObservedRootComparisonIndicator table ordinal target ∘
          fun observed => (observed, rightRoot)) <$>
        observedMaterializedBoundary parameter root ftsSecret computation
          (observations.map (installPositionValueAtProbe target output))
          (materializedDeferredState
            { selection.context with
              values := selection.context.values.install target output })
          fuel table cache)
      (fun lazy eager => lazy = true → eager = true) := by
  let resolved : DeferredResolution :=
    ⟨{ state := selection.context.state.clearPending (.position target)
       values := selection.context.values }, output⟩
  have hresolve : resolveDeferredPositionValue target selection.context = pure (some resolved) := by
    simpa [resolved] using resolveDeferredPositionValue_eq_good_output hgood hcovered
  have hresolved : some resolved ∈ support
      (resolveDeferredPositionValue target selection.context) := by
    rw [hresolve]
    simp
  rw [hresolve]
  simp only [pure_bind]
  exact relTriple_indicator_observedMaterializedBoundary_after_target_resolution parameter root
    ftsSecret target output rightRoot ordinal hroot selection hgood hcovered resolved hresolved
    computation observations fuel table cache hselectedHit hactualAvoid

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem relTriple_indicator_resolveSelectedRoot_then_observedMaterializedBoundary_supported
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (output : HashOutput) (rightRoot : Digest)
    (ordinal : Nat) (hroot : IsLayerRoot target)
    (selection : PrivateOrdinalSelection)
    (hgood : selection.GoodForRoots target output rightRoot ordinal)
    (hcovered : PendingCoveredBy (selection.candidates.take ordinal) selection.context)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (cache : SplitHashCache)
    (hselectedHit : ∀ (resolved : DeferredResolution)
        (hresolved : some resolved ∈ support
          (resolveDeferredPositionValue target selection.context))
        (result : ObservedCleanRunResult (α × SplitHashCache)),
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
        (result : ObservedCleanRunResult (α × SplitHashCache)),
      some result ∈ support
          (observedMaterializedBoundary parameter root ftsSecret computation observations
            (materializedDeferredState resolved.toDeferredContext) fuel table cache) →
        ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
            table ordinal target rightRoot (some result) →
          ∀ earlier : Fin result.observations.length, earlier.val < ordinal →
            (result.observations.get earlier).toProbe ≠
              ⟨.position target, truncateHash output⟩) :
    RelTriple
      (resolveDeferredPositionValue target selection.context >>= fun resolved =>
        match resolved with
        | none => pure false
        | some resolved =>
            (successfulObservedRootComparisonIndicator table ordinal target ∘
                fun observed => (observed, rightRoot)) <$>
              observedMaterializedBoundary parameter root ftsSecret computation observations
                (materializedDeferredState resolved.toDeferredContext) fuel table cache)
      ((successfulObservedRootComparisonIndicator table ordinal target ∘
          fun observed => (observed, rightRoot)) <$>
        observedMaterializedBoundary parameter root ftsSecret computation
          (observations.map (installPositionValueAtProbe target output))
          (materializedDeferredState
            { selection.context with
              values := selection.context.values.install target output })
          fuel table cache)
      (fun lazy eager => lazy = true → eager = true) := by
  let resolved : DeferredResolution :=
    ⟨{ state := selection.context.state.clearPending (.position target)
       values := selection.context.values }, output⟩
  have hresolve : resolveDeferredPositionValue target selection.context = pure (some resolved) := by
    simpa [resolved] using resolveDeferredPositionValue_eq_good_output hgood hcovered
  have hresolved : some resolved ∈ support
      (resolveDeferredPositionValue target selection.context) := by
    rw [hresolve]
    simp
  rw [hresolve]
  simp only [pure_bind]
  exact relTriple_indicator_observedMaterializedBoundary_after_target_resolution_supported
    parameter root ftsSecret target output rightRoot ordinal hroot selection hgood hcovered
    resolved hresolved computation observations fuel table cache
    (hselectedHit resolved hresolved) (hactualAvoid resolved hresolved)

end SphincsSecurity.Concrete.OtsProbeSimulation
