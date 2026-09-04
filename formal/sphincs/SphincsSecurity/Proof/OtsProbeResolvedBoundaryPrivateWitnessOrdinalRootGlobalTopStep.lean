import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalTopKernel

/-!
# Published-root result step

This module packages the retained continuation for one coupled result of the probe-free public-root
computation. It keeps the complete root wrapper small enough to elaborate independently.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedPublishedTreeRoot

def retainObservedRoot (root : Digest) :
    Option (ObservedCleanRunResult (RetainedRestResult × SplitHashCache)) →
      Option (ObservedCleanRunResult (RetainedGameResult × SplitHashCache))
  | none => none
  | some result => some
      { result with value := ((root, result.value.1), result.value.2) }

theorem SnapshotObservedPrefixStableRel.retainRoot
    {table : OtsSecretIndex → HashOutput}
    {source : PrivateWitnessSnapshotOutput}
    {observed : Option
      (ObservedCleanRunResult (RetainedRestResult × SplitHashCache))}
    (hrelation : SnapshotObservedPrefixStableRel table source observed)
    (root : Digest) :
    SnapshotObservedPrefixStableRel table source (retainObservedRoot root observed) := by
  rcases hrelation with hfailed | hsuccess | hdoomed
  · left
    subst observed
    rfl
  · right
    left
    obtain ⟨result, aligned, hresult, hprefix, haligned, hstored⟩ := hsuccess
    subst observed
    exact ⟨_, aligned, rfl, hprefix, haligned, hstored⟩
  · right
    right
    obtain ⟨result, hresult, hdoomed⟩ := hdoomed
    subst observed
    exact ⟨_, rfl, hdoomed⟩

theorem map_retainObservedRoot_eq
    (root : Digest)
    (run : ProbComp
      (Option (ObservedCleanRunResult (RetainedRestResult × SplitHashCache)))) :
    retainObservedRoot root <$> run =
      (run >>= fun result =>
        match result with
        | none => pure none
        | some result => pure (some
            { result with value := ((root, result.value.1), result.value.2) })) := by
  rw [map_eq_bind_pure_comp]
  apply bind_congr
  intro result
  cases result <;> rfl

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem relTriple_finishAfterPublishedRoot
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
      (finishDirectWitnessSnapshotObserve
        (canonicalizeDirectWitnessSnapshotObserve table
          (retainedSnapshotObserve adversary parameter table ftsSecret)) [] leftResult)
      (match rightResult with
      | none => pure none
      | some rootResult => do
          let restResult ← observedMaterializedBoundary parameter rootResult.value.1 ftsSecret
            (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩)
            rootResult.observations rootResult.state rootResult.remaining table rootResult.value.2
          match restResult with
          | none => pure none
          | some restResult => pure (some
              { restResult with
                value := ((rootResult.value.1, restResult.value.1), restResult.value.2) }))
      (SnapshotObservedPrefixStableRel table) := by
  have hfinish := relTriple_finishWitnessObservedStep (α := Digest)
    (β := RetainedRestResult) parameter id ftsSecret
      (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩)
      (retainedSnapshotObserve adversary parameter table ftsSecret) [] [] table leftResult
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
      exact relTriple_afterPublishedRoot adversary parameter ftsSecret q table hbound nextLeft
        nextRight hleftDone hrightDone hclean)
  cases rightResult with
  | none =>
      have hretained := relTriple_post_mono hfinish
        (fun source observed hrelation => hrelation.retainRoot 0)
      have hmapped := relTriple_map (f := id) (g := retainObservedRoot 0) hretained
      rw [id_map] at hmapped
      rw [map_retainObservedRoot_eq, pure_bind] at hmapped
      exact hmapped
  | some rootResult =>
      have hretained := relTriple_post_mono hfinish
        (fun source observed hrelation => hrelation.retainRoot rootResult.value.1)
      have hmapped := relTriple_map (f := id)
        (g := retainObservedRoot rootResult.value.1) hretained
      rw [id_map] at hmapped
      rw [map_retainObservedRoot_eq] at hmapped
      exact hmapped

end SphincsSecurity.Concrete.OtsProbeSimulation
