import SphincsSecurity.Proof.OtsProbeJointTopKernel
import SphincsSecurity.Proof.OtsProbeJointRootMap

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedPublishedTreeRoot
set_option linter.constructorNameAsVariable false

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem relTriple_finishJointAfterPublishedRoot
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hbound : ∀ root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
            SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (leftResult : DirectWitnessResult (Digest × SplitHashCache))
    (rightResult : Option (ObservedCleanRunResult (Digest × SplitHashCache)))
    (hstep : WitnessObservedStepRel table [] leftResult rightResult)
    (hleftSupport : leftResult ∈ support
      (runDirectResolvedWitnessFromTable emptyWitnessDeferredContext q table
        (maskedPublishedTreeRoot.run emptySplitHashCache)))
    (hrightSupport : rightResult ∈ support
      (runObservedCleanFromTable [] LazyRevealProbe.State.empty (2 * q) table
        (maskedPublishedTreeRoot.run emptySplitHashCache))) :
    RelTriple
      (finishDirectBoundaryWitnessSnapshotObserve
        (canonicalizeDirectBoundaryWitnessSnapshotObserve table
          (retainedJointSnapshotObserve adversary parameter table ftsSecret)) [] leftResult)
      ((match rightResult with
      | none => pure none
      | some rootResult => do
          let restResult ← observedMaterializedBoundary parameter rootResult.value.1 ftsSecret
            (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩)
            rootResult.observations rootResult.state rootResult.remaining table rootResult.value.2
          match restResult with
          | none => pure none
          | some restResult => pure (some
              { restResult with
                value := ((rootResult.value.1, restResult.value.1), restResult.value.2) })) >>=
        finishObservedMaterializedDiagnostic table)
      (BoundarySnapshotDiagnosticRel table) := by
  have hfinish := relTriple_finishJointWitnessObservedStep (α := Digest)
    (β := RetainedRestResult) parameter id ftsSecret
      (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩)
      (retainedJointSnapshotObserve adversary parameter table ftsSecret) [] [] table leftResult
      rightResult hstep (by simp [SnapshotsObservedAt]) (by
      intro nextLeft nextRight hleftEq hrightEq hclean
      have hleftDone : DirectWitnessResult.done nextLeft ∈ support
          (runDirectResolvedWitnessFromTable emptyWitnessDeferredContext q table
            (maskedPublishedTreeRoot.run emptySplitHashCache)) := by
        rw [← hleftEq]
        exact hleftSupport
      have hrightDone : some (observedResolvedResult [] nextRight) ∈ support
          (runObservedCleanFromTable [] LazyRevealProbe.State.empty (2 * q) table
            (maskedPublishedTreeRoot.run emptySplitHashCache)) := by
        rw [← hrightEq]
        exact hrightSupport
      exact relTriple_jointAfterPublishedRoot adversary parameter ftsSecret q table hbound nextLeft
        nextRight hleftDone hrightDone hclean)
  cases rightResult with
  | none =>
      have hretained := relTriple_post_mono hfinish
        (fun source observed hrelation => hrelation.retainRoot 0)
      have hmapped := relTriple_map (f := id) (g := retainDiagnosticRoot 0) hretained
      rw [id_map] at hmapped
      simpa only [finishObservedMaterializedDiagnostic, map_pure, retainDiagnosticRoot,
        retainObservedRoot, pure_bind] using hmapped
  | some rootResult =>
      have hretained := relTriple_post_mono hfinish
        (fun source observed hrelation => hrelation.retainRoot rootResult.value.1)
      have hmapped := relTriple_map (f := id)
        (g := retainDiagnosticRoot rootResult.value.1) hretained
      rw [id_map] at hmapped
      rw [map_retainDiagnosticRoot_bind_finish, map_retainObservedRoot_eq] at hmapped
      convert hmapped using 1
      simp only [bind_assoc, id_eq]
      rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
