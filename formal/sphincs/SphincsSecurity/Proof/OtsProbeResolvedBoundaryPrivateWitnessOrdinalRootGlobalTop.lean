import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalTopStep

/-!
# Published-root materialized observation lift

The retained-rest comparison is attached to the probe-free public root computation here, after the
adaptive induction has been compiled as its own module.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedPublishedTreeRoot

noncomputable def granularAllCanonicalPrivateWitnessSnapshot
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp PrivateWitnessSnapshotOutput :=
  runDirectWitnessSnapshotObserve
    (canonicalizeDirectWitnessSnapshotObserve table
      (granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve adversary parameter
        table ftsSecret))
    [] emptyWitnessDeferredContext fuel table
      (maskedPublishedTreeRoot.run emptySplitHashCache)

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem relTriple_granularAllSnapshot_observedMaterializedRetained
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hbound : ∀ root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
            SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q) :
    RelTriple
      (granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret q)
      (observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table)
      (SnapshotObservedPrefixStableRel table) := by
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
  have hlocal := relTriple_runDirectResolvedWitness_observed_of_probeFree table
    (maskedPublishedTreeRoot.run emptySplitHashCache)
    (maskedPublishedTreeRoot.run emptySplitHashCache) [] initial
    (directDeferredContext
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate))
    q (2 * q) hbase (maskedPublishedTreeRoot_probeFree emptySplitHashCache) rfl
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
    (SnapshotObservedPrefixStableRel table)
  apply relTriple_bind hbothSupported
  intro leftResult rightResult hstep
  rcases hstep with ⟨⟨hstep, hleftSupport⟩, hrightSupport⟩
  exact relTriple_finishAfterPublishedRoot adversary parameter ftsSecret q table hbound leftResult
    rightResult hstep (by simpa [initial] using hleftSupport) hrightSupport

end SphincsSecurity.Concrete.OtsProbeSimulation
