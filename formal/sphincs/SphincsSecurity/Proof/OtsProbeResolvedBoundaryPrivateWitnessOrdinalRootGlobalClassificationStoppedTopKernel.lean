import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedLift
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalTopKernel

/-!
# Stopped published-root continuation kernel

The probe-free public-root computation initializes the adaptive stopped lift with an empty,
tracked observation log and enough digest-space slack for every remaining pending probe.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedPublishedTreeRoot

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_afterPublishedRoot_firstStopped
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
    (hq : q ≤ 2 ^ securityBits)
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
      (SnapshotObservedFirstStoppedRel table) := by
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
  have hinitialTracked : CleanProbeObservationsTrackedBy []
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) := by
    simp [CleanProbeObservationsTrackedBy]
  have hinitialCovered : CleanProbeObservationsCoverPending []
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) := by
    simp [CleanProbeObservationsCoverPending, LazyRevealProbe.State.empty]
  have hrightTracked : CleanProbeObservationsTrackedBy [] right.context.state := by
    simpa [observedResolvedResult] using
      (cleanProbeObservationsTrackedBy_of_mem_runObservedCleanFromTable
        (maskedPublishedTreeRoot.run emptySplitHashCache) [] LazyRevealProbe.State.empty
        (2 * q) table hinitialTracked (observedResolvedResult [] right) hrightSupport)
  have hrightCovered : CleanProbeObservationsCoverPending [] right.context.state := by
    simpa [observedResolvedResult] using
      (cleanProbeObservationsCoverPending_of_mem_runObservedCleanFromTable
        (maskedPublishedTreeRoot.run emptySplitHashCache) [] LazyRevealProbe.State.empty
        (2 * q) table hinitialCovered (observedResolvedResult [] right) hrightSupport)
  have hcapacity : 2 * q < Fintype.card Digest := by
    rw [show Fintype.card Digest = 2 ^ digestBits by simp]
    norm_num [securityBits, digestBits] at hq ⊢
    omega
  have hbudget : right.remaining + right.context.state.pending.card <
      Fintype.card Digest := by
    have hremaining := remaining_add_pending_card_le_of_mem_runObservedCleanFromTable
      (maskedPublishedTreeRoot.run emptySplitHashCache) [] LazyRevealProbe.State.empty
      (2 * q) table (observedResolvedResult [] right) hrightSupport
    simp only [observedResolvedResult] at hremaining
    exact hremaining.trans_lt (by simpa [LazyRevealProbe.State.empty] using hcapacity)
  unfold canonicalizeDirectWitnessSnapshotObserve classifyDirectWitnessSnapshotObserve
  simp only [canonical, hnotPrivate, ↓reduceDIte, hclean.left_published, ↓reduceIte,
    hleftCompletable]
  rw [← hclean.value_eq]
  simpa [retainedSnapshotObserve,
    granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve] using
    (relTriple_directSnapshotBoundary_observedMaterialized_firstStopped parameter left.value.1
      ftsSecret (retainedGameRestComputation adversary ⟨left.value.1, parameter⟩)
      [] [] canonical right.context left.remaining right.remaining table
      left.value.2 right.value.2 q q (hbound left.value.1)
      hcanonicalRun.context_le hcanonicalRun.cache_eq hcanonicalRun.revealed_eq
      hcanonicalRun.values_le hcanonicalRun.left_published hcanonicalRun.right_materialized
      (canonicalizeMaterializedValues_canonical table left.context
        hclean.context_le.view.leftConsistent)
      (by simp [SnapshotsObservedAt]) (SnapshotsBefore.nil canonical)
      hrightTracked hrightCovered (by simp)
      (by omega) (by omega) (by omega) hbudget)

end SphincsSecurity.Concrete.OtsProbeSimulation
