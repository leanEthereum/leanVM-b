import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootLazyEager

/-!
# Fixed-root lazy and eager prefix bridge

The public-root computation is probe-free, so its observed result is just the clean result with an
empty observation list attached. This file factors that common prefix out of the remaining
event-preserving coupling.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedPublishedTreeRoot

noncomputable def lazyObservedRootComparisonExperimentAfterTable
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    ProbComp
      (Option (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) × Digest) := do
  let rootResult ← runCleanFromTable
    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel table
    (maskedPublishedTreeRoot.run emptySplitHashCache)
  match rootResult with
  | none => do
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      pure (none, rightRoot)
  | some result => do
      let observed ← observedMaterializedBoundary parameter result.value.1 ftsSecret
        (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩) [] result.state
        result.remaining table result.value.2
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      pure (retainObservedRoot result.value.1 observed, rightRoot)

set_option maxRecDepth 100000 in
theorem evalDist_lazyObservedRootComparisonExperimentAfterTable
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    evalDist (lazyObservedRootComparisonExperimentAfterTable adversary parameter ftsSecret
        fuel table) =
      evalDist (do
        let observed ← observedMaterializedRetainedRunFromTable adversary parameter ftsSecret
          fuel table
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (observed, rightRoot)) := by
  unfold lazyObservedRootComparisonExperimentAfterTable
    observedMaterializedRetainedRunFromTable
  rw [← map_attachCleanProbeObservations_runCleanFromTable_of_probeFree
    (maskedPublishedTreeRoot.run emptySplitHashCache) [] LazyRevealProbe.State.empty fuel table
    (maskedPublishedTreeRoot_probeFree emptySplitHashCache)]
  simp only [map_eq_bind_pure_comp, bind_assoc]
  apply evalDist_bind_congr
  intro rootResult _hrootResult
  cases rootResult with
  | none => rfl
  | some result =>
      simp only [Function.comp_apply, pure_bind, attachCleanProbeObservations]
      simp only [bind_assoc]
      apply evalDist_bind_congr
      intro observed _hobserved
      cases observed <;> rfl

def SuccessfulObservedIndicatorRel : Bool → Bool → Prop :=
  fun lazy eager ↦ lazy = true → eager = true

set_option maxRecDepth 100000 in
theorem relTriple_indicator_lazyObserved_resolvedEager_of_afterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (target : Position)
    (hbridge : ∀ rootResult : CleanRunResult (Digest × SplitHashCache),
      some rootResult ∈ support
        (runCleanFromTable
          (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel table
          (maskedPublishedTreeRoot.run emptySplitHashCache)) →
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
        SuccessfulObservedIndicatorRel) :
    RelTriple
      (successfulObservedRootComparisonIndicator table ordinal target <$>
        lazyObservedRootComparisonExperimentAfterTable adversary parameter ftsSecret fuel table)
      (successfulObservedRootComparisonIndicator table ordinal target <$>
        resolvedEagerObservedRootComparisonExperimentAfterTable adversary parameter ftsSecret
          target fuel table)
      SuccessfulObservedIndicatorRel := by
  unfold lazyObservedRootComparisonExperimentAfterTable
    resolvedEagerObservedRootComparisonExperimentAfterTable
  have hroot := SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support
    (relTriple_refl
      (runCleanFromTable
        (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel table
        (maskedPublishedTreeRoot.run emptySplitHashCache)))
    (fun result ↦ result ∈ support
      (runCleanFromTable
        (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel table
        (maskedPublishedTreeRoot.run emptySplitHashCache)))
    (fun _ hresult ↦ hresult)
  simp only [map_eq_bind_pure_comp, bind_assoc]
  apply relTriple_bind hroot
  intro leftRoot rightRoot hrelation
  obtain ⟨rfl, hleftRoot⟩ := hrelation
  cases leftRoot with
  | none =>
      apply relTriple_of_evalDist_eq_left
        (show evalDist
            (successfulObservedRootComparisonIndicator table ordinal target <$> (do
              let rightRoot ← ($ᵗ Digest : ProbComp Digest)
              pure (none, rightRoot))) = evalDist (pure false : ProbComp Bool) by
          simp [successfulObservedRootComparisonIndicator,
            ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt,
            ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget,
            ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt]
          rw [map_eq_bind_pure_comp]
          apply SPMF.ext
          intro output
          change Pr[= output | liftM (PMF.uniformOfFintype Digest) >>= fun _ =>
            (pure false : SPMF Bool)] = Pr[= output | (pure false : SPMF Bool)]
          rw [probOutput_bind_const]
          have hzero : Pr[⊥ | (liftM (PMF.uniformOfFintype Digest) : SPMF Digest)] = 0 :=
            probFailure_of_liftM_PMF _
          rw [hzero]
          simp)
      have hpure : RelTriple (pure false : ProbComp Bool) (pure false : ProbComp Bool)
          SuccessfulObservedIndicatorRel :=
        relTriple_pure_pure (fun hfalse ↦ by simp at hfalse)
      simpa [successfulObservedRootComparisonIndicator,
        ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt,
        ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget,
        ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt] using hpure
  | some rootResult =>
      simpa only [map_eq_bind_pure_comp] using hbridge rootResult hleftRoot

theorem relTriple_indicator_observedRootComparison_resolvedEager_of_afterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (target : Position)
    (hbridge : ∀ rootResult : CleanRunResult (Digest × SplitHashCache),
      some rootResult ∈ support
        (runCleanFromTable
          (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel table
          (maskedPublishedTreeRoot.run emptySplitHashCache)) →
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
        SuccessfulObservedIndicatorRel) :
    RelTriple
      (successfulObservedRootComparisonIndicator table ordinal target <$> (do
        let observed ← observedMaterializedRetainedRunFromTable adversary parameter ftsSecret
          fuel table
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (observed, rightRoot)))
      (successfulObservedRootComparisonIndicator table ordinal target <$>
        resolvedEagerObservedRootComparisonExperimentAfterTable adversary parameter ftsSecret
          target fuel table)
      SuccessfulObservedIndicatorRel := by
  apply relTriple_of_evalDist_eq_left
    (show evalDist
        (successfulObservedRootComparisonIndicator table ordinal target <$> (do
          let observed ← observedMaterializedRetainedRunFromTable adversary parameter ftsSecret
            fuel table
          let rightRoot ← ($ᵗ Digest : ProbComp Digest)
          pure (observed, rightRoot))) =
        evalDist
          (successfulObservedRootComparisonIndicator table ordinal target <$>
            lazyObservedRootComparisonExperimentAfterTable adversary parameter ftsSecret
              fuel table) by
      simp only [evalDist_map]
      rw [evalDist_lazyObservedRootComparisonExperimentAfterTable])
  exact relTriple_indicator_lazyObserved_resolvedEager_of_afterRootResult ordinal adversary
    parameter table ftsSecret fuel target hbridge

end SphincsSecurity.Concrete.OtsProbeSimulation
