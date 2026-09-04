import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedTopKernel
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalTopStep

/-!
# Stopped public-root lift

The first-stopped relation is carried through the probe-free public-root computation and the root
is restored in the retained game result.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedPublishedTreeRoot

theorem SnapshotObservedFirstStoppedRel.retainRoot
    {table : OtsSecretIndex → HashOutput}
    {source : PrivateWitnessSnapshotOutput}
    {observed : Option
      (ObservedCleanRunResult (RetainedRestResult × SplitHashCache))}
    (hrelation : SnapshotObservedFirstStoppedRel table source observed)
    (root : Digest) :
    SnapshotObservedFirstStoppedRel table source (retainObservedRoot root observed) := by
  rcases hrelation with hfailed | haligned | hselected | hstopped
  · left
    subst observed
    rfl
  · right
    left
    obtain ⟨result, aligned, hresult, hprefix, hsnapshots, hnoHit, hstored⟩ := haligned
    subst observed
    exact ⟨_, aligned, rfl, hprefix, hsnapshots, hnoHit, hstored⟩
  · right
    right
    left
    obtain ⟨result, ordinal, hresult, htable, hdoomed, hfirst, hselected⟩ := hselected
    subst observed
    exact ⟨_, ordinal, rfl, htable, hdoomed, hfirst, hselected⟩
  · right
    right
    right
    obtain ⟨result, hresult, htable, hdoomed, hcause⟩ := hstopped
    subst observed
    exact ⟨_, rfl, htable, hdoomed, hcause⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem relTriple_finishAfterPublishedRoot_firstStopped
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
    (leftResult : DirectWitnessResult (Digest × SplitHashCache))
    (rightResult : Option (ObservedCleanRunResult (Digest × SplitHashCache)))
    (hstep : WitnessObservedFirstStoppedStepRel table [] leftResult rightResult)
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
      (SnapshotObservedFirstStoppedRel table) := by
  have hfinish := relTriple_finishWitnessObservedFirstStoppedStep (α := Digest)
    (β := RetainedRestResult) parameter id ftsSecret
      (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩)
      (retainedSnapshotObserve adversary parameter table ftsSecret) [] [] table leftResult
      rightResult hstep (by
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
      exact relTriple_afterPublishedRoot_firstStopped adversary parameter ftsSecret q table hbound
        hq nextLeft nextRight hleftDone hrightDone hclean)
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

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem relTriple_granularAllSnapshot_observedMaterializedRetained_firstStopped
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
    (hq : q ≤ 2 ^ securityBits) :
    RelTriple
      (granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret q)
      (observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table)
      (SnapshotObservedFirstStoppedRel table) := by
  let initial : DeferredContext := emptyWitnessDeferredContext
  have hcontext : FinalizationContextLE table initial
      (directDeferredContext
        (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)) :=
    finalizationContextLE_empty table
  have hbase := (witnessMaterializedStableCouples_maskedPublishedTreeRoot table)
    initial (directDeferredContext
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate))
    q (2 * q) emptySplitHashCache emptySplitHashCache hcontext (by omega) rfl rfl
    (fun _ _ hvalue => hvalue) publishedValues_empty rfl
  have hcapacity : 2 * q < Fintype.card Digest := by
    rw [show Fintype.card Digest = 2 ^ digestBits by simp]
    norm_num [securityBits, digestBits] at hq ⊢
    omega
  have hlocal := relTriple_runDirectResolvedWitness_observed_firstStopped_of_probeFree table
    (maskedPublishedTreeRoot.run emptySplitHashCache)
    (maskedPublishedTreeRoot.run emptySplitHashCache) [] initial
    (directDeferredContext
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate))
    q (2 * q) hbase (maskedPublishedTreeRoot_probeFree emptySplitHashCache)
    (maskedPublishedTreeRoot_probeFree emptySplitHashCache) hcontext.leftValid
    hcontext.leftCompletable rfl (by simp [CleanProbeObservationsTrackedBy])
    (by simp [CleanProbeObservationsCoverPending, directDeferredContext,
      LazyRevealProbe.State.empty]) (by simp)
    (by simpa [directDeferredContext, LazyRevealProbe.State.empty] using hcapacity)
  have hleftSupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hlocal
      (fun result => result ∈ support
        (runDirectResolvedWitnessFromTable initial q table
          (maskedPublishedTreeRoot.run emptySplitHashCache)))
      (fun result hresult => hresult)
  have hbothSupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleftSupported
  unfold granularAllCanonicalPrivateWitnessSnapshot
    observedMaterializedRetainedRunFromTable runDirectWitnessSnapshotObserve
  change RelTriple
    (runDirectResolvedWitnessFromTable emptyWitnessDeferredContext q table
        (maskedPublishedTreeRoot.run emptySplitHashCache) >>=
      finishDirectWitnessSnapshotObserve
        (canonicalizeDirectWitnessSnapshotObserve table
          (granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve adversary parameter
            table ftsSecret)) [])
    (runObservedCleanFromTable [] LazyRevealProbe.State.empty (2 * q) table
        (maskedPublishedTreeRoot.run emptySplitHashCache) >>= fun rootResult =>
      match rootResult with
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
    (SnapshotObservedFirstStoppedRel table)
  apply relTriple_bind hbothSupported
  intro leftResult rightResult hstep
  rcases hstep with ⟨⟨hstep, hleftSupport⟩, hrightSupport⟩
  exact relTriple_finishAfterPublishedRoot_firstStopped adversary parameter ftsSecret q table
    hbound hq leftResult rightResult hstep (by simpa [initial] using hleftSupport) hrightSupport

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem relTriple_sampledGranularAllCanonical_observedMaterializedRetained_firstStopped
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ table root,
        (simulateQ
          (SphincsSecurity.expandedAdversaryImpl
            (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
              SecretKey))
          (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ securityBits) :
    RelTriple
      (sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q)
      (sampleOtsHashTable >>= fun table =>
        observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table)
      (fun source observed => ∃ table, SnapshotObservedFirstStoppedRel table source observed) := by
  unfold sampledGranularAllCanonicalPrivateWitnessSnapshot
  apply relTriple_bind (relTriple_refl sampleOtsHashTable)
  intro leftTable rightTable htable
  subst rightTable
  apply relTriple_post_mono
    (relTriple_granularAllSnapshot_observedMaterializedRetained_firstStopped adversary parameter
      ftsSecret q leftTable (hbound leftTable) hq)
  intro source observed hrelation
  exact ⟨leftTable, hrelation⟩

end SphincsSecurity.Concrete.OtsProbeSimulation
