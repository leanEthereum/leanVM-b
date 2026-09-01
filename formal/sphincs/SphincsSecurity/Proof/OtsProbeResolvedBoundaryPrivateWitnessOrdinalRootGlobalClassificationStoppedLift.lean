import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedHash

/-!
# Adaptive stopped lift

The recursive lift stays aligned while the materialized comparison is completable. A completed
local step either supplies the ordinary aligned result or a persistent missing-chain obstruction.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def WitnessObservedFirstStoppedStepRel
    (table : OtsSecretIndex → HashOutput)
    (observations : List CleanProbeObservation)
    (left : DirectWitnessResult (α × SplitHashCache))
    (right : Option (ObservedCleanRunResult (α × SplitHashCache))) : Prop :=
  right = none ∨
    (∃ leftResult rightResult,
      left = .done leftResult ∧
      right = some (observedResolvedResult observations rightResult) ∧
      OrdinaryMaterializedRunEq table leftResult rightResult) ∨
    ∃ rightResult,
      right = some (observedResolvedResult observations rightResult) ∧
      OrdinaryMaterializedDoomedRun table rightResult ∧
      MissingChainStartHit table rightResult.context

set_option maxRecDepth 100000 in
theorem relTriple_finishWitnessObservedFirstStoppedStep
    (parameter : PublicParameter) (rootOf : α → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (next : α → OracleComp (OracleWorld + SigningSpec) β)
    (leftObserve : DeferredContext → Nat → (α × SplitHashCache) →
      List PlannedProbeSnapshot → ProbComp PrivateWitnessSnapshotOutput)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (table : OtsSecretIndex → HashOutput)
    (leftResult : DirectWitnessResult (α × SplitHashCache))
    (rightResult : Option (ObservedCleanRunResult (α × SplitHashCache)))
    (hrelation : WitnessObservedFirstStoppedStepRel table observations leftResult rightResult)
    (hrecursive : ∀ left right,
      leftResult = .done left →
      rightResult = some (observedResolvedResult observations right) →
      OrdinaryMaterializedRunEq table left right →
      RelTriple
        (canonicalizeDirectWitnessSnapshotObserve table leftObserve left.context left.remaining
          (left.value.1, left.value.2) snapshots)
        (observedMaterializedBoundary parameter (rootOf right.value.1) ftsSecret
          (next right.value.1) observations right.context.state right.remaining table
          right.value.2)
        (SnapshotObservedFirstStoppedRel table)) :
    RelTriple
      (finishDirectWitnessSnapshotObserve
        (canonicalizeDirectWitnessSnapshotObserve table leftObserve) snapshots leftResult)
      (match rightResult with
        | none => pure none
        | some result =>
            observedMaterializedBoundary parameter (rootOf result.value.1) ftsSecret
              (next result.value.1) result.observations result.state result.remaining table
              result.value.2)
      (SnapshotObservedFirstStoppedRel table) := by
  rcases hrelation with hfailed | haligned | hmissing
  · subst rightResult
    have hbase := relTriple_true
      (finishDirectWitnessSnapshotObserve
        (canonicalizeDirectWitnessSnapshotObserve table leftObserve) snapshots leftResult)
      (pure none : ProbComp (Option (ObservedCleanRunResult (β × SplitHashCache))))
    have hsupported :=
      SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hbase
    apply relTriple_post_mono hsupported
    intro source observed hsupport
    have : observed = none := by simpa using hsupport.2
    exact Or.inl this
  · obtain ⟨left, right, hleft, hright, hclean⟩ := haligned
    subst leftResult
    subst rightResult
    simp only [finishDirectWitnessSnapshotObserve, observedResolvedResult]
    exact hrecursive left right rfl rfl hclean
  · obtain ⟨right, hright, hdoomed, hmissing⟩ := hmissing
    subst rightResult
    exact relTriple_any_observedMaterializedBoundary_firstStopped_of_cause parameter
      (rootOf right.value.1) ftsSecret (next right.value.1)
      (finishDirectWitnessSnapshotObserve
        (canonicalizeDirectWitnessSnapshotObserve table leftObserve) snapshots leftResult)
      observations right.context.state right.remaining table right.value.2
      (by rw [← hdoomed.2]; exact hdoomed.1.2) (Or.inl (by rwa [← hdoomed.2]))

