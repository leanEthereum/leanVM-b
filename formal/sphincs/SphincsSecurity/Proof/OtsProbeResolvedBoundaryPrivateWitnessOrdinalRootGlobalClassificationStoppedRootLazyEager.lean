import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAwareSharedSemantic
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootLazyEagerObservation
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootLazyEagerState
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootLazyEagerSuffix
import SphincsSecurity.Proof.OtsProbeResolvedPrivateRetainedCommutation

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local irreducible] maskedPublishedTreeRoot

noncomputable def resolvedEagerObservedRootComparisonAfterRootResult
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache)) :
    ProbComp
      (Option (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) × Digest) := do
  let resolved ← resolveDeferredPositionValue target (directDeferredContext rootResult.state)
  let rightRoot ← ($ᵗ Digest : ProbComp Digest)
  match resolved with
  | none => pure (none, rightRoot)
  | some resolved => do
      let observed ← observedMaterializedBoundary parameter rootResult.value.1 ftsSecret
        (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
        (materializedDeferredState resolved.toDeferredContext) rootResult.remaining rootResult.table
        (replaceHiddenRootCache target resolved.output rootResult.value.2)
      pure (retainObservedRoot rootResult.value.1 observed, rightRoot)

theorem evalDist_resolvedEagerObservedRootComparisonAfterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache))
    (habsent : rootResult.state.values (.position target) = none)
    (hpending : rootResult.state.pending = ∅) :
    evalDist
      (resolvedEagerObservedRootComparisonAfterRootResult adversary parameter ftsSecret target
        rootResult) =
      evalDist ((fun sampled => (sampled.2.2, sampled.2.1)) <$>
        sampledHighEagerObservedRootAwareAfterRootResult ordinal adversary parameter ftsSecret
          target rootResult) := by
  unfold resolvedEagerObservedRootComparisonAfterRootResult
  rw [resolveDeferredPositionValue_fresh target (directDeferredContext rootResult.state)]
  · have hhit : ∀ output, ¬rootResult.state.hitAt (.position target) output := by
      intro output
      simp [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt, hpending]
    simp only [directDeferredContext, hhit, ↓reduceIte]
    unfold sampledHighEagerObservedRootAwareAfterRootResult
    simp only [map_eq_bind_pure_comp, bind_assoc]
    simp only [pure_bind]
    have hclear : rootResult.state.clearPending (.position target) = rootResult.state := by
      rcases hstate : rootResult.state with ⟨pending, values, revealed, ensured⟩
      simp only [LazyRevealProbe.State.clearPending]
      have hp : pending = ∅ := by simpa only [hstate] using hpending
      simp [LazyRevealProbe.State.pendingAway, hp]
    rw [hclear]
    unfold rootInstalledCache
    let parts : ProbComp HashOutput := do
      let high ← ($ᵗ RootOutputHigh : ProbComp RootOutputHigh)
      let root ← ($ᵗ Digest : ProbComp Digest)
      pure (rootOutputOfParts root high)
    have hparts : evalDist parts = evalDist LazyRevealProbe.sampleHashOutput := by
      calc
        _ = evalDist (do
              let root ← ($ᵗ Digest : ProbComp Digest)
              let high ← ($ᵗ RootOutputHigh : ProbComp RootOutputHigh)
              pure (rootOutputOfParts root high)) := by
            exact OracleComp.DeferredSampling.evalDist_bind_comm
              ($ᵗ RootOutputHigh : ProbComp RootOutputHigh)
              ($ᵗ Digest : ProbComp Digest)
              (fun high root => pure (rootOutputOfParts root high))
        _ = _ := evalDist_sample_rootOutputOfParts
    let continuation := fun output : HashOutput => do
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      let observed ← observedMaterializedBoundary parameter rootResult.value.1 ftsSecret
        (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
        (materializedDeferredState
          { state := rootResult.state
            values := (directDeferredValues rootResult.state).install target output })
        rootResult.remaining rootResult.table
        (replaceHiddenRootCache target output rootResult.value.2)
      pure (retainObservedRoot rootResult.value.1 observed, rightRoot)
    calc
      _ = evalDist (LazyRevealProbe.sampleHashOutput >>= continuation) := by
        rfl
      _ = evalDist (parts >>= continuation) := by
        rw [evalDist_bind, evalDist_bind, hparts]
      _ = _ := by
        simp [parts, continuation, directDeferredContext, bind_assoc]
  · simpa [directDeferredContext] using habsent
  · simpa [directDeferredContext, directDeferredValues] using habsent

noncomputable def resolvedEagerObservedRootComparisonExperimentAfterTable
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    ProbComp
      (Option (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) × Digest) := do
  let rootResult ← runCleanFromTable
    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel table
    (maskedPublishedTreeRoot.run emptySplitHashCache)
  match rootResult with
  | none => pure (none, 0)
  | some result =>
      resolvedEagerObservedRootComparisonAfterRootResult adversary parameter ftsSecret target result

set_option maxRecDepth 100000 in
theorem evalDist_resolvedEagerObservedRootComparisonExperimentAfterTable
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    evalDist
      (resolvedEagerObservedRootComparisonExperimentAfterTable adversary parameter ftsSecret
        target fuel table) =
      evalDist
        (eagerObservedRootComparisonExperimentAfterTable ordinal adversary parameter ftsSecret
          target fuel table) := by
  unfold resolvedEagerObservedRootComparisonExperimentAfterTable
    eagerObservedRootComparisonExperimentAfterTable
  apply evalDist_bind_congr
  intro rootResult hresult
  cases rootResult with
  | none => rfl
  | some result =>
      have habsent := target_absent_of_mem_runCleanFromTable_maskedPublishedTreeRoot target hroot
        hparent fuel table result hresult
      have hpending := pending_eq_empty_of_mem_runCleanFromTable_maskedPublishedTreeRoot fuel table
        result hresult
      exact evalDist_resolvedEagerObservedRootComparisonAfterRootResult ordinal adversary parameter
        ftsSecret target result habsent.1 hpending

end SphincsSecurity.Concrete.OtsProbeSimulation
