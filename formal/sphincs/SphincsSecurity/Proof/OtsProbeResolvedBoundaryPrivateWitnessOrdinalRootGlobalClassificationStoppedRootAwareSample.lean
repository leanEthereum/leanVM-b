import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAwareBoundary

/-!
# Root-aware selector sampling

The installed-cache bound is averaged over the high half of the selected layer-root output while the public top-root result remains fixed.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

set_option linter.constructorNameAsVariable false
attribute [local irreducible] maskedPublishedTreeRoot

noncomputable def sampledHighMaterializedRootAwareSelectionAfterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache)) :
    ProbComp (Digest × Digest × Option Probe) := do
  let high ← ($ᵗ RootOutputHigh : ProbComp RootOutputHigh)
  let leftRoot ← ($ᵗ Digest : ProbComp Digest)
  let rightRoot ← ($ᵗ Digest : ProbComp Digest)
  let output := fun root => rootOutputOfParts root high
  let context : DeferredContext := directDeferredContext rootResult.state
  let rootContext :=
    { context with values := context.values.install target (output leftRoot) }
  let selection ← materializedActualRootAwareAvoidingOrdinalSelection ordinal parameter
    rootResult.value.1 target leftRoot rightRoot ftsSecret
    (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
    (materializedDeferredState rootContext) rootResult.remaining rootResult.table
    (rootInstalledCache target output rootResult.value.2 leftRoot)
  pure (leftRoot, rightRoot, selection)

noncomputable def sampledHighMaterializedRootAwareSelectionProductionAfterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache)) :
    ProbComp (Digest × Option Probe) := do
  let high ← ($ᵗ RootOutputHigh : ProbComp RootOutputHigh)
  let leftRoot ← ($ᵗ Digest : ProbComp Digest)
  let output := fun root => rootOutputOfParts root high
  let context : DeferredContext := directDeferredContext rootResult.state
  let rootContext :=
    { context with values := context.values.install target (output leftRoot) }
  let selection ← materializedActualRootAwareAvoidingOrdinalSelection ordinal parameter
    rootResult.value.1 target leftRoot leftRoot ftsSecret
    (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
    (materializedDeferredState rootContext) rootResult.remaining rootResult.table
    (rootInstalledCache target output rootResult.value.2 leftRoot)
  pure (leftRoot, selection)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_sampledHigh_materializedRootAwareSelectionAfterRootResult_le_mul_of_neutral
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (rootResult : CleanRunResult (Digest × SplitHashCache))
    (hhidden : rootResult.state.values (.position target) = none)
    (hprivate : Coordinate.position target ∉ rootResult.state.revealed)
    (hbase : ∀ leftRoot rightRoot,
      swapCanonicalRootEncodingCache parameter target leftRoot rightRoot rootResult.value.2 =
        rootResult.value.2) :
    Pr[fun result => materializedOrdinalSelectionMatches target result.1 result.2.2 |
        sampledHighMaterializedRootAwareSelectionAfterRootResult ordinal adversary parameter
          ftsSecret target rootResult] ≤
      Pr[fun result => materializedOrdinalSelectionAt target result.2 |
          sampledHighMaterializedRootAwareSelectionProductionAfterRootResult ordinal adversary
            parameter ftsSecret target rootResult] *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  unfold sampledHighMaterializedRootAwareSelectionAfterRootResult
    sampledHighMaterializedRootAwareSelectionProductionAfterRootResult
  apply probEvent_bind_le_bind_mul_of_forall
  intro high _hhigh
  apply probEvent_uniformActualRoot_materializedRootAwareRootInstalledMatches_le_mul ordinal
    parameter rootResult.value.1 target hroot (fun root => rootOutputOfParts root high)
    (fun root => truncateHash_rootOutputOfParts root high) ftsSecret
    (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
    (directDeferredContext rootResult.state) hhidden hprivate rootResult.remaining
    rootResult.table rootResult.value.2
  intro leftRoot rightRoot
  exact hbase leftRoot rightRoot

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_sampledHigh_materializedRootAwareSelectionAfterRootResult_le_mul
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (rootResult : CleanRunResult (Digest × SplitHashCache))
    (hresult : some rootResult ∈ support
      (runCleanFromTable (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
        fuel table (maskedPublishedTreeRoot.run emptySplitHashCache))) :
    Pr[fun result => materializedOrdinalSelectionMatches target result.1 result.2.2 |
        sampledHighMaterializedRootAwareSelectionAfterRootResult ordinal adversary parameter
          ftsSecret target rootResult] ≤
      Pr[fun result => materializedOrdinalSelectionAt target result.2 |
          sampledHighMaterializedRootAwareSelectionProductionAfterRootResult ordinal adversary
            parameter ftsSecret target rootResult] *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  have habsent :
      rootResult.state.values (.position target) = none ∧
        Coordinate.position target ∉ rootResult.state.revealed :=
    target_absent_of_mem_runCleanFromTable_maskedPublishedTreeRoot target hroot hparent fuel table
      rootResult hresult
  apply
    probEvent_sampledHigh_materializedRootAwareSelectionAfterRootResult_le_mul_of_neutral ordinal
      adversary parameter ftsSecret target hroot rootResult habsent.1 habsent.2
  intro leftRoot rightRoot
  exact swapCanonicalRootEncodingCache_of_mem_runCleanFromTable_maskedPublishedTreeRoot parameter
    target leftRoot rightRoot (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
    fuel table rootResult hresult

end SphincsSecurity.Concrete.OtsProbeSimulation
