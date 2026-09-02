import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAwareSample

/-!
# Root-aware selector experiment

The sampled fixed-root bound is averaged over the public top-root computation while keeping the production factor in the same experiment.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

set_option linter.constructorNameAsVariable false
attribute [local irreducible] maskedPublishedTreeRoot

noncomputable def materializedRootAwareOrdinalMatchExperimentAfterTable
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    ProbComp (Digest × Digest × Option Probe) := do
  let rootResult ← runCleanFromTable
    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel table
    (maskedPublishedTreeRoot.run emptySplitHashCache)
  match rootResult with
  | none => pure (0, 0, none)
  | some result =>
      sampledHighMaterializedRootAwareSelectionAfterRootResult ordinal adversary parameter
        ftsSecret target result

noncomputable def materializedRootAwareOrdinalProductionExperimentAfterTable
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    ProbComp (Digest × Option Probe) := do
  let rootResult ← runCleanFromTable
    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel table
    (maskedPublishedTreeRoot.run emptySplitHashCache)
  match rootResult with
  | none => pure (0, none)
  | some result =>
      sampledHighMaterializedRootAwareSelectionProductionAfterRootResult ordinal adversary
        parameter ftsSecret target result

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_materializedRootAwareOrdinalMatchExperimentAfterTable_le_mul
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    Pr[fun result => materializedOrdinalSelectionMatches target result.1 result.2.2 |
        materializedRootAwareOrdinalMatchExperimentAfterTable ordinal adversary parameter
          ftsSecret target fuel table] ≤
      Pr[fun result => materializedOrdinalSelectionAt target result.2 |
          materializedRootAwareOrdinalProductionExperimentAfterTable ordinal adversary parameter
            ftsSecret target fuel table] *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  classical
  unfold materializedRootAwareOrdinalMatchExperimentAfterTable
    materializedRootAwareOrdinalProductionExperimentAfterTable
  apply probEvent_bind_le_bind_mul_of_forall
  intro rootResult hrootResult
  cases rootResult with
  | none =>
      rw [probEvent_pure, probEvent_pure]
      simp [materializedOrdinalSelectionMatches, materializedOrdinalSelectionAt]
  | some result =>
      exact probEvent_sampledHigh_materializedRootAwareSelectionAfterRootResult_le_mul ordinal
        adversary parameter ftsSecret target hroot hparent fuel table result hrootResult

end SphincsSecurity.Concrete.OtsProbeSimulation
