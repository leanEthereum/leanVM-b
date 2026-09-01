import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootEager

/-!
# Joint stopped layer-root endpoint

The successful stopped diagnostic must remain correlated with the materialized root-selection
outcome. This file packages the exact relation required by the terminal probability argument. Its
postcondition sends a clean selected source root directly to a materialized match, without admitting
the conservative failure arm of the unconditioned root-selection bridge.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

def CleanRootMaterializedMatchRel
    (table : OtsSecretIndex → HashOutput) (ordinal : Nat) (target : Position) :
    (PrivateWitnessSnapshotOutput × Digest) →
      (Digest × Digest × MaterializedSelectionOutcome) → Prop :=
  fun source outcome =>
    SelectedPrivateSnapshotCleanRootGoodForComparisonAt
        table source.1 ordinal target source.2 →
      outcome.2.2.Matches target outcome.1

theorem probEvent_cleanRootGoodForComparison_le_materializedMatch
    (table : OtsSecretIndex → HashOutput)
    (source : ProbComp PrivateWitnessSnapshotOutput)
    (outcome : ProbComp (Digest × Digest × MaterializedSelectionOutcome))
    (ordinal : Nat) (target : Position)
    (hrel : RelTriple
      (do
        let result ← source
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (result, rightRoot))
      outcome (CleanRootMaterializedMatchRel table ordinal target)) :
    Pr[fun result : PrivateWitnessSnapshotOutput × Digest =>
        SelectedPrivateSnapshotCleanRootGoodForComparisonAt
          table result.1 ordinal target result.2 | do
      let result ← source
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      pure (result, rightRoot)] ≤
      Pr[fun result => result.2.2.Matches target result.1 | outcome] := by
  apply probEvent_le_of_relTriple hrel
  intro left right hrelation hgood
  exact hrelation hgood

theorem probEvent_cleanRootGoodForComparison_le_production_mul
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (fuel : Nat)
    (hrel : RelTriple
      (do
        let source ← granularAllCanonicalPrivateWitnessSnapshot adversary parameter table
          ftsSecret fuel
        let rightRoot ← ($ᵗ Digest : ProbComp Digest)
        pure (source, rightRoot))
      (materializedRootOrdinalOutcomeExperimentAfterTable ordinal adversary parameter ftsSecret
        target fuel table)
      (CleanRootMaterializedMatchRel table ordinal target)) :
    Pr[fun result : PrivateWitnessSnapshotOutput × Digest =>
        SelectedPrivateSnapshotCleanRootGoodForComparisonAt
          table result.1 ordinal target result.2 | do
      let source ← granularAllCanonicalPrivateWitnessSnapshot adversary parameter table
        ftsSecret fuel
      let rightRoot ← ($ᵗ Digest : ProbComp Digest)
      pure (source, rightRoot)] ≤
      Pr[fun result => materializedOrdinalSelectionAt target result.2 |
          materializedRootOrdinalProductionExperimentAfterTable ordinal adversary parameter
            ftsSecret target fuel table] *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  calc
    _ ≤ Pr[fun result => result.2.2.Matches target result.1 |
          materializedRootOrdinalOutcomeExperimentAfterTable ordinal adversary parameter ftsSecret
            target fuel table] :=
      probEvent_cleanRootGoodForComparison_le_materializedMatch table
        (granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret fuel)
        (materializedRootOrdinalOutcomeExperimentAfterTable ordinal adversary parameter ftsSecret
          target fuel table) ordinal target hrel
    _ ≤ _ := probEvent_materializedRootOrdinalOutcome_match_le ordinal adversary parameter ftsSecret
      target hroot hparent fuel table

end SphincsSecurity.Concrete.OtsProbeSimulation
