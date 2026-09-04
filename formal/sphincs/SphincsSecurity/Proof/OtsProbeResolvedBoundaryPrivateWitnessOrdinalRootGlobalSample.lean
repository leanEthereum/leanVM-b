import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalSampleTracking

/-!
# Sampled global root relation

The canonical source and materialized comparison are related through table sampling after their
fixed-table chronology and observation invariants have been established.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def SnapshotObservedRootOrDoomedRel
    (table : OtsSecretIndex → HashOutput)
    (source : PrivateWitnessSnapshotOutput)
    (observed : Option
      (ObservedCleanRunResult (RetainedGameResult × SplitHashCache))) : Prop :=
  observed = none ∨
    (∃ result, observed = some result ∧
    (WitnessFirstUsesSomeLayerRoot (erasePrivateWitnessSnapshotOutput source) →
        WitnessFirstUsesSomeDelayedLayerRootSnapshot source)) ∨
    ∃ result, observed = some result ∧
      DoomedResolvedContext table (directDeferredContext result.state)

attribute [local irreducible] observedMaterializedRetainedRunFromTable in
set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem relTriple_granularAllCanonical_observedMaterialized_rootOrDoomed
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
      (SnapshotObservedRootOrDoomedRel table) := by
  have hrelation := relTriple_granularAllSnapshot_observedMaterializedRetained adversary parameter
    ftsSecret q table hbound
  have hleft :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hrelation
      SourceSnapshotStopInvariant
      (sourceSnapshotStopInvariant_of_mem_granularAllCanonical adversary parameter table
        ftsSecret q)
  have htracked : RelTriple
      (granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret q)
      (observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table)
      (fun source observed =>
        (SnapshotObservedPrefixStableRel table source observed ∧
          SourceSnapshotStopInvariant source) ∧
        ObservedMaterializedOutputTracked observed) :=
    relTriple_and_observedMaterializedOutputTracked
      (adversary := adversary) (parameter := parameter) (ftsSecret := ftsSecret)
      (fuel := 2 * q) (table := table)
      (source := granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret q)
      (relation := fun source observed =>
        SnapshotObservedPrefixStableRel table source observed ∧
          SourceSnapshotStopInvariant source)
      hleft
  apply relTriple_post_mono htracked
  intro source observed hfacts
  rcases hfacts with ⟨⟨hstable, hsource⟩, htrackedOutput⟩
  rcases hstable with hfailed | hsuccess | hdoomed
  · exact Or.inl hfailed
  · obtain ⟨result, aligned, hresult, hprefix, haligned, hstored⟩ := hsuccess
    have hvalue : SnapshotObservedPrefixValueRel table source observed :=
      Or.inr ⟨result, aligned, hresult, hprefix, haligned, hstored⟩
    have hroot : SnapshotObservedRootRel source observed := hvalue.to_rootRel hsource (by
      intro trackedResult htrackedResult
      have heq : trackedResult = result := Option.some.inj (htrackedResult.symm.trans hresult)
      subst trackedResult
      simpa only [hresult, ObservedMaterializedOutputTracked] using htrackedOutput)
    rcases hroot with hfailed | himplication
    · exact Or.inl hfailed
    · exact Or.inr (Or.inl ⟨result, hresult, himplication⟩)
  · obtain ⟨result, hresult, hdoomed⟩ := hdoomed
    exact Or.inr (Or.inr ⟨result, hresult, hdoomed⟩)

theorem relTriple_pure_finishObservedMaterialized_of_rootOrDoomed
    (table : OtsSecretIndex → HashOutput)
    (source : PrivateWitnessSnapshotOutput)
    (observed : Option
      (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)))
    (hrelation : SnapshotObservedRootOrDoomedRel table source observed) :
    RelTriple
      (pure source : ProbComp PrivateWitnessSnapshotOutput)
      (finishObservedMaterializedCleanRunFromTable table observed)
      SnapshotObservedRootRel := by
  rcases hrelation with hfailed | hsuccess | hdoomed
  · subst observed
    simp [finishObservedMaterializedCleanRunFromTable, SnapshotObservedRootRel]
  · obtain ⟨result, hresult, himplication⟩ := hsuccess
    subst observed
    by_cases hcompletable :
        DeferredCompletable table (directDeferredContext result.state)
    · simp only [finishObservedMaterializedCleanRunFromTable, hcompletable, ↓reduceIte]
      have hbase := relTriple_true (pure source : ProbComp PrivateWitnessSnapshotOutput)
        (finishObservedCleanRunFromTable (some result))
      have hleft :=
        SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
          (fun output => output = source) (by intro output houtput; simpa using houtput)
      apply relTriple_post_mono hleft
      intro left final hfacts
      rw [hfacts.2]
      cases final with
      | none => exact Or.inl rfl
      | some _ => exact Or.inr himplication
    · simp [finishObservedMaterializedCleanRunFromTable, hcompletable,
        SnapshotObservedRootRel]
  · obtain ⟨result, hresult, hdoomedContext⟩ := hdoomed
    subst observed
    simp [finishObservedMaterializedCleanRunFromTable, hdoomedContext.2.2,
      SnapshotObservedRootRel]

set_option maxRecDepth 100000 in
theorem relTriple_finishObservedMaterialized_of_rootOrDoomed
    (table : OtsSecretIndex → HashOutput)
    (source : ProbComp PrivateWitnessSnapshotOutput)
    (observed : ProbComp (Option
      (ObservedCleanRunResult (RetainedGameResult × SplitHashCache))))
    (hrelation : RelTriple source observed (SnapshotObservedRootOrDoomedRel table)) :
    RelTriple source
      (observed >>= finishObservedMaterializedCleanRunFromTable table)
      SnapshotObservedRootRel := by
  have hbound := relTriple_bind hrelation fun sourceOutput observedOutput houtput =>
    relTriple_pure_finishObservedMaterialized_of_rootOrDoomed table sourceOutput observedOutput
      houtput
  simpa using hbound

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem relTriple_granularAllCanonical_finishedMaterialized_rootRel
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
      (finishedObservedMaterializedRunFromTable adversary parameter ftsSecret (2 * q) table)
      SnapshotObservedRootRel := by
  unfold finishedObservedMaterializedRunFromTable
  exact relTriple_finishObservedMaterialized_of_rootOrDoomed table _ _
    (relTriple_granularAllCanonical_observedMaterialized_rootOrDoomed adversary parameter ftsSecret
      q table hbound)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem relTriple_sampledGranularAllCanonical_finishedMaterialized_rootRel
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
            SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q) :
    RelTriple
      (sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q)
      (sampledObservedMaterializedClean adversary parameter ftsSecret (2 * q))
      SnapshotObservedRootRel := by
  unfold sampledGranularAllCanonicalPrivateWitnessSnapshot sampledObservedMaterializedClean
  change RelTriple
    (sampleOtsHashTable >>= fun table =>
      granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret q)
    (sampleOtsHashTable >>= fun table =>
      finishedObservedMaterializedRunFromTable adversary parameter ftsSecret (2 * q) table)
    SnapshotObservedRootRel
  apply relTriple_bind (relTriple_refl sampleOtsHashTable)
  intro leftTable rightTable htable
  subst rightTable
  exact relTriple_granularAllCanonical_finishedMaterialized_rootRel adversary parameter ftsSecret q
    leftTable (hbound leftTable)

theorem probEvent_sampledGranularAllCanonical_root_le_materializedFailure_add_delayed
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
            SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q) :
    Pr[fun output =>
        WitnessFirstUsesSomeLayerRoot (erasePrivateWitnessSnapshotOutput output) |
      sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] ≤
      Pr[= none | sampledObservedMaterializedClean adversary parameter ftsSecret (2 * q)] +
        Pr[WitnessFirstUsesSomeDelayedLayerRootSnapshot |
          sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] := by
  exact probEvent_root_le_observedFailure_add_delayed_of_relTriple _ _
    (relTriple_sampledGranularAllCanonical_finishedMaterialized_rootRel adversary parameter
      ftsSecret q hbound)

end SphincsSecurity.Concrete.OtsProbeSimulation
