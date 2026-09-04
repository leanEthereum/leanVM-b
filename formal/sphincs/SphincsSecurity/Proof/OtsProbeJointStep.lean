import SphincsSecurity.Proof.OtsProbeJointFinalization

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option linter.constructorNameAsVariable false

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem relTriple_finishJointWitnessObservedStep
    (parameter : PublicParameter) (rootOf : α → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (next : α → OracleComp (OracleWorld + SigningSpec) β)
    (leftObserve : DeferredContext → Nat → (α × SplitHashCache) →
      List PlannedProbeSnapshot → ProbComp BoundaryWitnessSnapshotOutput)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (table : OtsSecretIndex → HashOutput)
    (leftResult : DirectWitnessResult (α × SplitHashCache))
    (rightResult : Option (ObservedCleanRunResult (α × SplitHashCache)))
    (hrelation : WitnessObservedStepRel table observations leftResult rightResult)
    (haligned : SnapshotsObservedAt table snapshots observations)
    (hrecursive : ∀ left right,
      leftResult = .done left →
      rightResult = some (observedResolvedResult observations right) →
      OrdinaryMaterializedRunEq table left right →
      RelTriple
        (canonicalizeDirectBoundaryWitnessSnapshotObserve table leftObserve left.context left.remaining
          ((left.value.1, left.value.2)) snapshots)
        (observedMaterializedBoundary parameter (rootOf right.value.1) ftsSecret
          (next right.value.1)
          observations right.context.state right.remaining table right.value.2 >>= finishObservedMaterializedDiagnostic table)
        (BoundarySnapshotDiagnosticRel table)) :
    RelTriple
      (finishDirectBoundaryWitnessSnapshotObserve
        (canonicalizeDirectBoundaryWitnessSnapshotObserve table leftObserve) snapshots leftResult)
      (match rightResult with
        | none => finishObservedMaterializedDiagnostic table none
        | some result =>
            observedMaterializedBoundary parameter (rootOf result.value.1) ftsSecret
              (next result.value.1)
              result.observations result.state result.remaining table result.value.2 >>=
                finishObservedMaterializedDiagnostic table)
      (BoundarySnapshotDiagnosticRel table) := by
  obtain ⟨detailed, hproject, hstable⟩ := hrelation
  cases detailed with
  | stopped reason =>
      have hright : rightResult = none := by
        simpa [projectDirectDetailedObserved] using hproject.symm
      subst rightResult
      exact relTriple_any_finishDiagnostic_none table _

  | done right =>
      have hright : rightResult = some
          (observedResolvedResult observations right) := by
        simpa [projectDirectDetailedObserved, observedResolvedResult] using hproject.symm
      subst rightResult
      simp only [projectDirectDetailedObserved, finishDirectBoundaryWitnessSnapshotObserve]
      cases leftResult with
      | stoppedFuel =>
          change RelTriple (pure ⟨.ordinaryFailure, none, snapshots⟩)
            (observedMaterializedBoundary parameter (rootOf right.value.1) ftsSecret
              (next right.value.1)
              observations right.context.state right.remaining table right.value.2 >>= finishObservedMaterializedDiagnostic table)
            (BoundarySnapshotDiagnosticRel table)
          exact relTriple_pure_snapshot_observedDiagnostic parameter
            (rootOf right.value.1) ftsSecret
            (next right.value.1) ⟨.ordinaryFailure, none, snapshots⟩ observations right.context.state
            right.remaining table right.value.2
            haligned
            (Or.inr (by rw [← hstable.2]; exact hstable.1.2))
      | stoppedOrdinary =>
          change RelTriple (pure ⟨.ordinaryFailure, none, snapshots⟩)
            (observedMaterializedBoundary parameter (rootOf right.value.1) ftsSecret
              (next right.value.1)
              observations right.context.state right.remaining table right.value.2 >>= finishObservedMaterializedDiagnostic table)
            (BoundarySnapshotDiagnosticRel table)
          exact relTriple_pure_snapshot_observedDiagnostic parameter
            (rootOf right.value.1) ftsSecret
            (next right.value.1) ⟨.ordinaryFailure, none, snapshots⟩ observations right.context.state
            right.remaining table right.value.2
            haligned
            (Or.inr (by rw [← hstable.2]; exact hstable.1.2))
      | stoppedPrivate witness =>
          change RelTriple (pure ⟨.privateStructuralFailure, some witness, snapshots⟩)
            (observedMaterializedBoundary parameter (rootOf right.value.1) ftsSecret
              (next right.value.1)
              observations right.context.state right.remaining table right.value.2 >>= finishObservedMaterializedDiagnostic table)
            (BoundarySnapshotDiagnosticRel table)
          rcases hstable with hstored | hdoomed
          · exact relTriple_pure_snapshot_observedDiagnostic parameter
              (rootOf right.value.1) ftsSecret
              (next right.value.1) ⟨.privateStructuralFailure, some witness, snapshots⟩ observations right.context.state
              right.remaining table right.value.2
              haligned
              (Or.inl ⟨(by
                intro other hother
                have : other = witness := Option.some.inj hother.symm
                subst other
                exact hstored.1), (by intro _; rfl)⟩)
          · exact relTriple_pure_snapshot_observedDiagnostic parameter
              (rootOf right.value.1) ftsSecret
              (next right.value.1) ⟨.privateStructuralFailure, some witness, snapshots⟩ observations right.context.state
              right.remaining table right.value.2
              haligned
              (Or.inr (by rw [← hdoomed.2]; exact hdoomed.1.2))
      | done left =>
          change RelTriple
            (canonicalizeDirectBoundaryWitnessSnapshotObserve table leftObserve left.context
              left.remaining left.value snapshots)
            (observedMaterializedBoundary parameter (rootOf right.value.1) ftsSecret
              (next right.value.1)
              observations right.context.state right.remaining table right.value.2 >>= finishObservedMaterializedDiagnostic table)
            (BoundarySnapshotDiagnosticRel table)
          rcases hstable with hclean | hdoomed
          · exact hrecursive left right rfl hright hclean
          · exact relTriple_any_observedDiagnostic_of_doomed parameter
              (rootOf right.value.1) ftsSecret
              (next right.value.1)
              (canonicalizeDirectBoundaryWitnessSnapshotObserve table leftObserve left.context
                left.remaining left.value snapshots)
              observations right.context.state right.remaining table right.value.2
              (by rw [← hdoomed.2]; exact hdoomed.1.2)


end SphincsSecurity.Concrete.OtsProbeSimulation
