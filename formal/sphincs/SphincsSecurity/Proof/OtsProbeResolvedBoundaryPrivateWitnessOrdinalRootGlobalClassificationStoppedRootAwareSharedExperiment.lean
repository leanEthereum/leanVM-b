import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAwareOutcome
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootJoint

/-!
# Sampled shared root prefix

This is the concrete joint experiment whose left projection is the eagerly resolved observed run
and whose right projection is the failure-retaining root-aware outcome. Running the common prefix
once is what preserves the successful stopped gate while the outcome is classified.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option linter.constructorNameAsVariable false
attribute [local irreducible] maskedPublishedTreeRoot

noncomputable def sampledHighObservedRootAwareSharedAfterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache)) :
    ProbComp
      (Digest × Digest ×
        Option (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) ×
          MaterializedSelectionOutcome) := do
  let high ← ($ᵗ RootOutputHigh : ProbComp RootOutputHigh)
  let leftRoot ← ($ᵗ Digest : ProbComp Digest)
  let rightRoot ← ($ᵗ Digest : ProbComp Digest)
  let output := fun root => rootOutputOfParts root high
  let context : DeferredContext := directDeferredContext rootResult.state
  let rootContext :=
    { context with values := context.values.install target (output leftRoot) }
  let pair ← observedRootSelectionSharedPrefix ordinal parameter rootResult.value.1 target leftRoot
    rightRoot ftsSecret
    (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) [] []
    (materializedDeferredState rootContext) rootResult.remaining rootResult.table
    (rootInstalledCache target output rootResult.value.2 leftRoot)
  pure (leftRoot, rightRoot, retainObservedRoot rootResult.value.1 pair.1, pair.2)

noncomputable def sampledHighEagerObservedRootAwareAfterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache)) :
    ProbComp
      (Digest × Digest ×
        Option (ObservedCleanRunResult (RetainedGameResult × SplitHashCache))) := do
  let high ← ($ᵗ RootOutputHigh : ProbComp RootOutputHigh)
  let leftRoot ← ($ᵗ Digest : ProbComp Digest)
  let rightRoot ← ($ᵗ Digest : ProbComp Digest)
  let output := fun root => rootOutputOfParts root high
  let context : DeferredContext := directDeferredContext rootResult.state
  let rootContext :=
    { context with values := context.values.install target (output leftRoot) }
  let observed ← observedMaterializedBoundary parameter rootResult.value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
    (materializedDeferredState rootContext) rootResult.remaining rootResult.table
    (rootInstalledCache target output rootResult.value.2 leftRoot)
  pure (leftRoot, rightRoot, retainObservedRoot rootResult.value.1 observed)

noncomputable def observedRootAwareSharedExperimentAfterTable
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    ProbComp
      (Digest × Digest ×
        Option (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) ×
          MaterializedSelectionOutcome) := do
  let rootResult ← runCleanFromTable
    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel table
    (maskedPublishedTreeRoot.run emptySplitHashCache)
  match rootResult with
  | none => pure (0, 0, none, .failed)
  | some result =>
      sampledHighObservedRootAwareSharedAfterRootResult ordinal adversary parameter
        ftsSecret target result

end SphincsSecurity.Concrete.OtsProbeSimulation
