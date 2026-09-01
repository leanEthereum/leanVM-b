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

theorem not_target_hitAt_of_goodForRoots_of_pendingCovered
    {target : Position} {leftOutput : HashOutput} {rightRoot : Digest}
    {ordinal : Nat} {selection : PrivateOrdinalSelection}
    (hgood : selection.GoodForRoots target leftOutput rightRoot ordinal)
    (hcovered : PendingCoveredBy (selection.candidates.take ordinal) selection.context) :
    ¬selection.context.state.hitAt (.position target) leftOutput := by
  intro hhit
  have hpending : (Coordinate.position target, truncateHash leftOutput) ∈
      selection.context.state.pending := by
    rw [← LazyRevealProbe.State.mem_pendingAt_iff]
    exact hhit
  obtain ⟨candidate, hcandidate, hcoordinate, hdigest⟩ := hcovered _ hpending
  have havoid := hgood.2.2.2.2 candidate hcandidate
  apply havoid.1
  cases candidate
  simp only [Probe.mk.injEq]
  exact ⟨hcoordinate, hdigest⟩

theorem resolveDeferredPositionValue_eq_good_output
    {target : Position} {leftOutput : HashOutput} {rightRoot : Digest}
    {ordinal : Nat} {selection : PrivateOrdinalSelection}
    (hgood : selection.GoodForRoots target leftOutput rightRoot ordinal)
    (hcovered : PendingCoveredBy (selection.candidates.take ordinal) selection.context) :
    resolveDeferredPositionValue target selection.context =
      pure (some (DeferredResolution.mk
        { state := selection.context.state.clearPending (.position target)
          values := selection.context.values }
        leftOutput)) := by
  rw [resolveDeferredPositionValue_of_deferred_value target selection.context leftOutput
    hgood.2.1 hgood.2.2.2.1]
  simp [not_target_hitAt_of_goodForRoots_of_pendingCovered hgood hcovered]

def PrivateOrdinalGoodRel
    (target : Position) (rightRoot : Digest) (ordinal : Nat) :
    Option PrivateOrdinalSelection → Option PrivateOrdinalSelection → Prop :=
  fun left right =>
    privateOrdinalSelectionGoodForSomeOutput target rightRoot ordinal left →
      privateOrdinalSelectionGoodForSomeOutput target rightRoot ordinal right

theorem goodForRoots_clearPending_target
    {target : Position} {leftOutput : HashOutput} {rightRoot : Digest}
    {ordinal : Nat} {selection : PrivateOrdinalSelection}
    (hgood : selection.GoodForRoots target leftOutput rightRoot ordinal) :
    ({ selection with
        context := { selection.context with
          state := selection.context.state.clearPending (.position target) } } :
      PrivateOrdinalSelection).GoodForRoots target leftOutput rightRoot ordinal := by
  rcases hgood with ⟨hcandidate, hstate, hrevealed, hvalue, havoid⟩
  exact ⟨hcandidate, by simpa [LazyRevealProbe.State.clearPending] using hstate,
    by simpa [LazyRevealProbe.State.clearPending] using hrevealed, hvalue, havoid⟩

theorem relTriple_goodSelection_resolveDeferredPositionValue
    (target : Position) (rightRoot : Digest) (ordinal : Nat)
    (selection : PrivateOrdinalSelection)
    (hcovered : PendingCoveredBy (selection.candidates.take ordinal) selection.context) :
    RelTriple
      (pure (some selection) : ProbComp (Option PrivateOrdinalSelection))
      (resolveDeferredPositionValue target selection.context >>= fun resolved =>
        match resolved with
        | none => pure none
        | some resolved => pure (some
            { selection with context := resolved.toDeferredContext }))
      (PrivateOrdinalGoodRel target rightRoot ordinal) := by
  by_cases hgood : privateOrdinalSelectionGoodForSomeOutput target rightRoot ordinal (some selection)
  · obtain ⟨leftOutput, hgood⟩ := hgood
    rw [resolveDeferredPositionValue_eq_good_output hgood hcovered]
    simp only [pure_bind]
    apply relTriple_pure_pure
    intro _hleft
    exact ⟨leftOutput, by
      simpa [DeferredResolution.toDeferredContext] using goodForRoots_clearPending_target hgood⟩
  · apply relTriple_post_mono
      (SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support
        (relTriple_true
          (pure (some selection) : ProbComp (Option PrivateOrdinalSelection))
          (show ProbComp (Option PrivateOrdinalSelection) from
            resolveDeferredPositionValue target selection.context >>= fun resolved =>
              match resolved with
              | none => pure none
              | some resolved => pure (some
                  { selection with context := resolved.toDeferredContext })))
        (fun left => left = some selection) (by intro left hleft; simpa using hleft))
    intro left _right _hrelation hleft
    exact (hgood (_hrelation.2 ▸ hleft)).elim

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
