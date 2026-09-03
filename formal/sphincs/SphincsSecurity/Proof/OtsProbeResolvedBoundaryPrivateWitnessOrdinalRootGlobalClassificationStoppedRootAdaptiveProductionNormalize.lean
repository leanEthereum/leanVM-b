import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveProduction

/-!
# Common production normalization

The target-specific production experiment first samples the selected structural output as its
low digest and independent high bits. This module rewrites that eager draw as the ordinary deferred
resolution of the selected position. The remaining normalization can therefore commute one
`resolveDeferredPositionValue` through the target-independent selector.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local irreducible] maskedPublishedTreeRoot

noncomputable def resolvedInstalledPermissiveRootAwareSelectionAfterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache)) :
    ProbComp (Digest × Option Probe) := do
  let resolved ← resolveDeferredPositionValue target
    (directDeferredContext rootResult.state)
  match resolved with
  | none => pure (0, none)
  | some resolved =>
      let selection ← permissiveRootAwareOrdinalSelection ordinal parameter
        rootResult.value.1 ftsSecret
        (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
        (materializedDeferredState resolved.toDeferredContext) rootResult.remaining
        rootResult.table
        (replaceHiddenRootCache target resolved.output rootResult.value.2)
      pure (truncateHash resolved.output, selection)

set_option maxRecDepth 100000 in
theorem evalDist_sampledHighInstalledPermissive_eq_resolved
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache))
    (hstate : rootResult.state.values (.position target) = none)
    (hpending : rootResult.state.pending = ∅) :
    evalDist
        (sampledHighInstalledPermissiveRootAwareSelectionAfterRootResult ordinal adversary
          parameter ftsSecret target rootResult) =
      evalDist
        (resolvedInstalledPermissiveRootAwareSelectionAfterRootResult ordinal adversary
          parameter ftsSecret target rootResult) := by
  unfold resolvedInstalledPermissiveRootAwareSelectionAfterRootResult
  rw [resolveDeferredPositionValue_fresh target (directDeferredContext rootResult.state)]
  · have hhit : ∀ output, ¬rootResult.state.hitAt (.position target) output := by
      intro output
      simp [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt, hpending]
    simp only [directDeferredContext, hhit, ↓reduceIte]
    have hclear : rootResult.state.clearPending (.position target) = rootResult.state := by
      rcases hrootState : rootResult.state with ⟨pending, values, revealed, ensured⟩
      simp only [LazyRevealProbe.State.clearPending]
      have hp : pending = ∅ := by simpa only [hrootState] using hpending
      simp [LazyRevealProbe.State.pendingAway, hp]
    rw [hclear]
    unfold sampledHighInstalledPermissiveRootAwareSelectionAfterRootResult rootInstalledCache
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
      let selection ← permissiveRootAwareOrdinalSelection ordinal parameter
        rootResult.value.1 ftsSecret
        (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) []
        (materializedDeferredState
          { state := rootResult.state
            values := (directDeferredValues rootResult.state).install target output })
        rootResult.remaining rootResult.table
        (replaceHiddenRootCache target output rootResult.value.2)
      pure (truncateHash output, selection)
    calc
      _ = evalDist (parts >>= continuation) := by
        simp [parts, continuation, directDeferredContext, bind_assoc]
      _ = evalDist (LazyRevealProbe.sampleHashOutput >>= continuation) := by
        exact evalDist_bind_eq_of_evalDist_eq hparts continuation
      _ = _ := by rfl
  · simpa [directDeferredContext] using hstate
  · simpa [directDeferredContext, directDeferredValues] using hstate

theorem evalDist_sampledHighInstalledPermissive_eq_resolved_afterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (rootResult : CleanRunResult (Digest × SplitHashCache))
    (hresult : some rootResult ∈ support
      (runCleanFromTable
        (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel table
        (maskedPublishedTreeRoot.run emptySplitHashCache))) :
    evalDist
        (sampledHighInstalledPermissiveRootAwareSelectionAfterRootResult ordinal adversary
          parameter ftsSecret target rootResult) =
      evalDist
        (resolvedInstalledPermissiveRootAwareSelectionAfterRootResult ordinal adversary
          parameter ftsSecret target rootResult) := by
  have habsent := target_absent_of_mem_runCleanFromTable_maskedPublishedTreeRoot target hroot
    hparent fuel table rootResult hresult
  have hpending := pending_eq_empty_of_mem_runCleanFromTable_maskedPublishedTreeRoot fuel table
    rootResult hresult
  exact evalDist_sampledHighInstalledPermissive_eq_resolved ordinal adversary parameter ftsSecret
    target rootResult habsent.1 hpending

theorem probEvent_sampledHighInstalledPermissive_eq_resolved_afterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (rootResult : CleanRunResult (Digest × SplitHashCache))
    (hresult : some rootResult ∈ support
      (runCleanFromTable
        (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel table
        (maskedPublishedTreeRoot.run emptySplitHashCache))) :
    Pr[fun result ↦ materializedOrdinalSelectionAt target result.2 |
        sampledHighInstalledPermissiveRootAwareSelectionAfterRootResult ordinal adversary
          parameter ftsSecret target rootResult] =
      Pr[fun result ↦ materializedOrdinalSelectionAt target result.2 |
        resolvedInstalledPermissiveRootAwareSelectionAfterRootResult ordinal adversary
          parameter ftsSecret target rootResult] := by
  apply OracleComp.probEvent_congr' (fun _ _ ↦ Iff.rfl)
  exact evalDist_sampledHighInstalledPermissive_eq_resolved_afterRootResult ordinal adversary
    parameter ftsSecret target hroot hparent fuel table rootResult hresult

end SphincsSecurity.Concrete.OtsProbeSimulation
