import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalFinish

/-!
# Fixed-table and sampled materialized comparison

The completed fixed-table comparison is named here before its source invariant and observation
tracking are compiled in separate modules.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

noncomputable def sampledGranularAllCanonicalPrivateWitnessSnapshot
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp PrivateWitnessSnapshotOutput := do
  let table ← sampleOtsHashTable
  granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret fuel

noncomputable def finishedObservedMaterializedRunFromTable
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    ProbComp (Option
      (ObservedCleanRunResult (RetainedGameResult × SplitHashCache))) :=
  observedMaterializedRetainedRunFromTable adversary parameter ftsSecret fuel table >>=
    finishObservedMaterializedCleanRunFromTable table

theorem relTriple_granularAllCanonical_finishedMaterialized
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hbound : ∀ root,
      (retainedGameRestComputation adversary ⟨root, parameter⟩).IsQueryBoundP
        IsOuterHash q) :
    RelTriple
      (granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret q)
      (observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table >>=
        finishObservedMaterializedCleanRunFromTable table)
      (SnapshotObservedPrefixValueRel table) :=
  relTriple_finishObservedMaterialized_of_stable table _ _
    (relTriple_granularAllSnapshot_observedMaterializedRetained adversary parameter ftsSecret q
      table hbound)

theorem relTriple_granularAllCanonical_finishedMaterializedRunFromTable
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hbound : ∀ root,
      (retainedGameRestComputation adversary ⟨root, parameter⟩).IsQueryBoundP
        IsOuterHash q) :
    RelTriple
      (granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret q)
      (finishedObservedMaterializedRunFromTable adversary parameter ftsSecret (2 * q) table)
      (SnapshotObservedPrefixValueRel table) := by
  unfold finishedObservedMaterializedRunFromTable
  exact relTriple_granularAllCanonical_finishedMaterialized adversary parameter ftsSecret q table
    hbound

set_option maxRecDepth 100000 in
theorem relTriple_sampledGranularAllCanonical_finishedMaterialized
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ root,
      (retainedGameRestComputation adversary ⟨root, parameter⟩).IsQueryBoundP
        IsOuterHash q) :
    RelTriple
      (sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q)
      (sampledObservedMaterializedClean adversary parameter ftsSecret (2 * q))
      (fun source observed => ∃ table, SnapshotObservedPrefixValueRel table source observed) := by
  unfold sampledGranularAllCanonicalPrivateWitnessSnapshot sampledObservedMaterializedClean
  apply relTriple_bind (relTriple_refl sampleOtsHashTable)
  intro leftTable rightTable htable
  subst rightTable
  apply relTriple_post_mono
    (relTriple_granularAllCanonical_finishedMaterialized adversary parameter ftsSecret q leftTable
      hbound)
  intro source observed hrelation
  exact ⟨leftTable, hrelation⟩

attribute [local irreducible] maskedPublishedTreeRoot in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem sourceSnapshotStopInvariant_of_mem_granularAllCanonical
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret fuel)) :
    SourceSnapshotStopInvariant output := by
  change output ∈ support (runDirectWitnessSnapshotObserve
    (canonicalizeDirectWitnessSnapshotObserve table
      (granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve adversary parameter
        table ftsSecret)) [] emptyWitnessDeferredContext fuel table
    (maskedPublishedTreeRoot.run emptySplitHashCache)) at houtput
  have hbefore : SnapshotsBefore ([] : List PlannedProbeSnapshot) emptyWitnessDeferredContext :=
    SnapshotsBefore.nil emptyWitnessDeferredContext
  have hpreserves : DirectWitnessPreservesPublished maskedPublishedTreeRoot :=
    directWitnessPreservesPublished_maskedPublishedTreeRoot
  have hpreservesResult := fun result =>
    hpreserves.result emptyWitnessDeferredContext emptySplitHashCache fuel table result
      publishedValues_empty
  apply sourceSnapshotStopInvariant_of_mem_runDirectWitnessSnapshotObserve
    (observe := canonicalizeDirectWitnessSnapshotObserve table
      (granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve adversary parameter
        table ftsSecret))
    (snapshots := []) (context := emptyWitnessDeferredContext) (fuel := fuel) (table := table)
    (computation := maskedPublishedTreeRoot.run emptySplitHashCache)
    hbefore hpreservesResult _ output houtput
  intro result nextOutput _ hnextBefore hpublished hnext
  apply sourceSnapshotStopInvariant_of_mem_canonicalizeDirectWitnessSnapshotObserve table _
    result.context result.remaining result.value [] hnextBefore hpublished _ nextOutput hnext
  intro finalOutput hfinal
  exact sourceSnapshotStopInvariant_of_mem_granularDetailedRetainedRest adversary parameter table
    ftsSecret (canonicalizeMaterializedValues table result.context) result.remaining result.value []
    (hnextBefore.canonicalize_right table) hpublished.to_canonicalizedMaterializedValues
    finalOutput hfinal

end SphincsSecurity.Concrete.OtsProbeSimulation
