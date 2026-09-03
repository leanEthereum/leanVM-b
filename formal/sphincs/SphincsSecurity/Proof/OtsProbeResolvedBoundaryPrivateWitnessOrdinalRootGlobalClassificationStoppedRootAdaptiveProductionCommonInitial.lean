import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveProductionCommonSelectionSampling

/-!
# Initial facts for common root production

This module packages the initial root computation facts before they are used under the larger
probability expressions of the common selector.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local irreducible] maskedPublishedTreeRoot

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem initialRootResult_target_absent_pending_empty
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (rootResult : CleanRunResult (Digest × SplitHashCache))
    (hresult : some rootResult ∈ support (rootAwareProductionInitialRun fuel table)) :
    rootResult.state.values (.position target) = none ∧
      Coordinate.position target ∉ rootResult.state.revealed ∧
      rootResult.state.pending = ∅ := by
  have hraw : LazyRevealProbe.RawResult.done rootResult.state rootResult.remaining
      rootResult.value ∈ support
        (LazyRevealProbe.runRaw
          (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel
          (maskedPublishedTreeRoot.run emptySplitHashCache)) := by
    unfold rootAwareProductionInitialRun at hresult
    exact mem_support_runRaw_done_of_mem_runCleanFromTable_some
      (maskedPublishedTreeRoot.run emptySplitHashCache)
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel table rootResult hresult
  have hne := layerRootPosition_ne_top_of_parent hroot hparent
  have hsame := preservesCoordinate_maskedPublishedTreeRoot_of_ne target hne
    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) emptySplitHashCache fuel
    rootResult.state rootResult.remaining rootResult.value.1 rootResult.value.2 hraw
  have habsent : rootResult.state.values (.position target) = none ∧
      Coordinate.position target ∉ rootResult.state.revealed := by
    constructor
    · rw [hsame.1]
      rfl
    · intro hrevealed
      have : Coordinate.position target ∈
          (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate).revealed :=
        hsame.2.mp hrevealed
      simp [LazyRevealProbe.State.empty] at this
  have hpending : rootResult.state.pending = ∅ := by
    have hsubset := pending_subset_of_done_runRaw_of_probeFree
      (maskedPublishedTreeRoot.run emptySplitHashCache)
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) rootResult.state fuel
      rootResult.remaining rootResult.value (maskedPublishedTreeRoot_probeFree emptySplitHashCache)
      hraw
    simpa [LazyRevealProbe.State.empty] using hsubset
  exact ⟨habsent.1, habsent.2, hpending⟩

def InitialRootOptionFacts (target : Position) :
    Option (CleanRunResult (Digest × SplitHashCache)) → Prop
  | none => True
  | some rootResult =>
      rootResult.state.values (.position target) = none ∧
        Coordinate.position target ∉ rootResult.state.revealed ∧
        rootResult.state.pending = ∅

set_option maxRecDepth 100000 in
theorem initialRootOptionFacts_of_mem
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (rootResult? : Option (CleanRunResult (Digest × SplitHashCache))) :
    rootResult? ∈ support (rootAwareProductionInitialRun fuel table) →
      InitialRootOptionFacts target rootResult? := by
  cases rootResult? with
  | none => simp [InitialRootOptionFacts]
  | some rootResult =>
      intro hresult
      exact initialRootResult_target_absent_pending_empty target hroot hparent fuel table
        rootResult hresult

end SphincsSecurity.Concrete.OtsProbeSimulation
