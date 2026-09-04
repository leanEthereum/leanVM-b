import SphincsSecurity.Proof.OtsProbeJointLift

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedPublishedTreeRoot
set_option linter.constructorNameAsVariable false

noncomputable def retainedJointSnapshotObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    DeferredContext → Nat → (Digest × SplitHashCache) →
      List PlannedProbeSnapshot → ProbComp BoundaryWitnessSnapshotOutput :=
  granularDetailedRetainedRestNormalizedBoundaryWitnessSnapshotObserve adversary parameter table
    ftsSecret

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_jointAfterPublishedRoot
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
    (left right : ResolvedRunResult (Digest × SplitHashCache))
    (hleftSupport : DirectWitnessResult.done left ∈ support
      (runDirectResolvedWitnessFromTable emptyWitnessDeferredContext q table
        (maskedPublishedTreeRoot.run emptySplitHashCache)))
    (hrightSupport : some (observedResolvedResult [] right) ∈ support
      (runObservedCleanFromTable [] LazyRevealProbe.State.empty (2 * q) table
        (maskedPublishedTreeRoot.run emptySplitHashCache)))
    (hclean : OrdinaryMaterializedRunEq table left right) :
    RelTriple
      (canonicalizeDirectBoundaryWitnessSnapshotObserve table
        (retainedJointSnapshotObserve adversary parameter table ftsSecret)
        left.context left.remaining left.value [])
      (observedMaterializedBoundary parameter right.value.1 ftsSecret
        (retainedGameRestComputation adversary ⟨right.value.1, parameter⟩)
        [] right.context.state right.remaining table right.value.2 >>=
        finishObservedMaterializedDiagnostic table)
      (BoundarySnapshotDiagnosticRel table) := by
  have hcanonicalRun := hclean.canonicalize_left
  let canonical := canonicalizeMaterializedValues table left.context
  have hleftCompletable : DeferredCompletable table canonical :=
    hcanonicalRun.context_le.leftCompletable
  have hnotPrivate : ¬PrivateStructuralHit canonical :=
    not_privateStructuralHit_of_deferredCompletable hleftCompletable
  have hleftFuelPreserved : q ≤ left.remaining :=
    fuel_le_remaining_of_doneWitness_maskedPublishedTreeRoot table q left hleftSupport
  have hrightFuelPreserved : 2 * q ≤ right.remaining :=
    fuel_le_remaining_of_mem_observed_maskedPublishedTreeRoot table (2 * q) right hrightSupport
  have hleftRemainingUpper : left.remaining ≤ q :=
    remaining_le_fuel_of_doneWitness_maskedPublishedTreeRoot table q left hleftSupport
  unfold canonicalizeDirectBoundaryWitnessSnapshotObserve classifyDirectBoundaryWitnessSnapshotObserve
  simp only [canonical, hnotPrivate, ↓reduceDIte, hclean.left_published, ↓reduceIte,
    hleftCompletable]
  rw [← hclean.value_eq]
  simpa [retainedJointSnapshotObserve,
    granularDetailedRetainedRestNormalizedBoundaryWitnessSnapshotObserve] using
    (relTriple_directJointSnapshotBoundary_diagnostic parameter left.value.1 ftsSecret
      (retainedGameRestComputation adversary ⟨left.value.1, parameter⟩)
      [] [] canonical right.context left.remaining right.remaining table
      left.value.2 right.value.2 q q (hbound left.value.1)
      hcanonicalRun.context_le hcanonicalRun.cache_eq hcanonicalRun.revealed_eq
      hcanonicalRun.values_le hcanonicalRun.left_published hcanonicalRun.right_materialized
      (canonicalizeMaterializedValues_canonical table left.context
        hclean.context_le.view.leftConsistent)
      (by simp [SnapshotsObservedAt]) (by omega) (by omega) (by omega))

end SphincsSecurity.Concrete.OtsProbeSimulation
