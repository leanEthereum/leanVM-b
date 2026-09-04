import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalTopFuel

/-!
# Published-root continuation kernel

This module isolates the continuation after the probe-free public-root computation. Keeping this
kernel separate prevents the complete root wrapper from serializing one deeply nested proof term.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedPublishedTreeRoot

noncomputable def retainedSnapshotObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    DeferredContext → Nat → (Digest × SplitHashCache) →
      List PlannedProbeSnapshot → ProbComp PrivateWitnessSnapshotOutput :=
  granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve adversary parameter table
    ftsSecret

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_afterPublishedRoot
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
      (canonicalizeDirectWitnessSnapshotObserve table
        (retainedSnapshotObserve adversary parameter table ftsSecret)
        left.context left.remaining left.value [])
      (observedMaterializedBoundary parameter right.value.1 ftsSecret
        (retainedGameRestComputation adversary ⟨right.value.1, parameter⟩)
        [] right.context.state right.remaining table right.value.2)
      (SnapshotObservedPrefixStableRel table) := by
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
  unfold canonicalizeDirectWitnessSnapshotObserve classifyDirectWitnessSnapshotObserve
  simp only [canonical, hnotPrivate, ↓reduceDIte, hclean.left_published, ↓reduceIte,
    hleftCompletable]
  rw [← hclean.value_eq]
  simpa [retainedSnapshotObserve,
    granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve] using
    (relTriple_directSnapshotBoundary_observedMaterialized parameter left.value.1 ftsSecret
      (retainedGameRestComputation adversary ⟨left.value.1, parameter⟩)
      [] [] canonical right.context left.remaining right.remaining table
      left.value.2 right.value.2 q q (hbound left.value.1)
      hcanonicalRun.context_le hcanonicalRun.cache_eq hcanonicalRun.revealed_eq
      hcanonicalRun.values_le hcanonicalRun.left_published hcanonicalRun.right_materialized
      (canonicalizeMaterializedValues_canonical table left.context
        hclean.context_le.view.leftConsistent)
      (by simp [SnapshotsObservedAt]) (by omega) (by omega) (by omega))

end SphincsSecurity.Concrete.OtsProbeSimulation
