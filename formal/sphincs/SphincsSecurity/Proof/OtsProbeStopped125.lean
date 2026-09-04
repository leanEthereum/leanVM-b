import SphincsSecurity.Proof.OtsProbeRootRisk125

namespace SphincsSecurity.Concrete.OtsProbeSimulation.Range125

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

attribute [local irreducible] maskedPublishedTreeRoot

set_option linter.constructorNameAsVariable false

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
    (hq : q ≤ 2 ^ 125)
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

set_option maxHeartbeats 4000000 in
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
    (hq : q ≤ 2 ^ 125)
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

set_option maxHeartbeats 4000000 in
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
    (hq : q ≤ 2 ^ 125) :
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

set_option maxHeartbeats 4000000 in
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
    (hq : q ≤ 2 ^ 125) :
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

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem probEvent_sampledSuccessfulFirstHit_le_selectedSnapshot_add_chainStartAt
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q ordinal : Nat)
    (hbound : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
            SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
        (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 125) :
    Pr[ObservedCleanRunOption.SuccessfulFirstExistingHiddenHitAt ordinal | do
        let table ← sampleOtsHashTable
        observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table] ≤
      Pr[fun source => SelectedPrivateSnapshotHitAt source ordinal |
          sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] +
        Pr[fun observed => (match observed with
          | none => False
          | some result => FirstExistingHiddenChainStartHitAt result.observations ordinal) | do
          let table ← sampleOtsHashTable
          observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table] := by
  let source := sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q
  let observed := do
    let table ← sampleOtsHashTable
    observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table
  apply probEvent_le_failure_add_residual_of_relTriple observed source
    (fun observed source => ∃ table, SnapshotObservedFirstStoppedRel table source observed)
    (ObservedCleanRunOption.SuccessfulFirstExistingHiddenHitAt ordinal)
    (fun observed => match observed with
      | none => False
      | some result => FirstExistingHiddenChainStartHitAt result.observations ordinal)
    (fun source => SelectedPrivateSnapshotHitAt source ordinal)
    (relTriple_symm
      (relTriple_sampledGranularAllCanonical_observedMaterializedRetained_firstStopped adversary
        parameter ftsSecret q hbound hq))
  intro right left hrelation hevent hnotChain
  obtain ⟨table, hrelation⟩ := hrelation
  cases right with
  | none => simp [ObservedCleanRunOption.SuccessfulFirstExistingHiddenHitAt] at hevent
  | some result =>
      obtain ⟨⟨finalResult, hfinish⟩, hfirst⟩ := hevent
      rcases hrelation.selected_or_chain_of_successful_firstHit finalResult hfinish ordinal hfirst
        with hselected | hchain
      · exact hselected
      · exact (hnotChain hchain).elim

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem probEvent_sampledSuccessfulFirstHit_le_selectedSnapshot
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q ordinal : Nat)
    (hbound : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
            SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
        (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 125) :
    Pr[ObservedCleanRunOption.SuccessfulFirstExistingHiddenHitAt ordinal | do
        let table ← sampleOtsHashTable
        observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table] ≤
      Pr[fun source => SelectedPrivateSnapshotHitAt source ordinal |
          sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] := by
  calc
    _ ≤ Pr[fun source => SelectedPrivateSnapshotHitAt source ordinal |
          sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret q] +
        Pr[fun observed => (match observed with
          | none => False
          | some result => FirstExistingHiddenChainStartHitAt result.observations ordinal) | do
          let table ← sampleOtsHashTable
          observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table] := by
      exact probEvent_sampledSuccessfulFirstHit_le_selectedSnapshot_add_chainStartAt adversary
        parameter ftsSecret q ordinal hbound hq
    _ = _ := by
      have hzero := probEvent_sampled_firstExistingHiddenChainStartHitAt_eq_zero adversary
        parameter ftsSecret (2 * q) ordinal
      change Pr[fun observed => (match observed with
        | none => False
        | some result => FirstExistingHiddenChainStartHitAt result.observations ordinal) | do
        let table ← sampleOtsHashTable
        observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table] = 0
        at hzero
      rw [hzero]
      simp

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem probEvent_observedMaterialized_successfulDoomed_firstNonRoot_le_selectedNonRoot
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q ordinal : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hbound : ∀ root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
            SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
        (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 125) :
    Pr[ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenNonRootHitAt table ordinal |
        observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table] ≤
      Pr[fun source => SelectedPrivateSnapshotNonRootHitAt source ordinal |
        granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret q] := by
  let source := granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret q
  let observed := observedMaterializedRetainedRunFromTable adversary parameter ftsSecret
    (2 * q) table
  calc
    _ ≤ Pr[fun source => SelectedPrivateSnapshotNonRootHitAt source ordinal | source] +
        Pr[ObservedMaterializedOutput.FirstExistingHiddenChainStartHitAt ordinal | observed] := by
      apply probEvent_le_failure_add_residual_of_relTriple observed source
        (fun observed source => SnapshotObservedFirstStoppedRel table source observed)
        (ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenNonRootHitAt table ordinal)
        (ObservedMaterializedOutput.FirstExistingHiddenChainStartHitAt ordinal)
        (fun source => SelectedPrivateSnapshotNonRootHitAt source ordinal)
        (relTriple_symm
          (relTriple_granularAllSnapshot_observedMaterializedRetained_firstStopped adversary
            parameter ftsSecret q table hbound hq))
      intro right left hrelation hevent hnotChain
      cases right with
      | none =>
          simp [ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenNonRootHitAt] at hevent
      | some result =>
          obtain ⟨⟨finalResult, hfinish⟩, _hdoomed, selected, hselected, hfirst,
            hnonRoot⟩ := hevent
          exact hrelation.selectedNonRoot_of_successful_firstNonRoot finalResult hfinish ordinal
            selected hselected hfirst hnonRoot hnotChain
    _ = _ := by
      rw [probEvent_firstExistingHiddenChainStartHitAt_eq_zero adversary parameter ftsSecret
        (2 * q) ordinal table]
      simp [source]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem probEvent_sampledDiagnostic_successfulDoomed_firstNonRoot_le
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q ordinal : Nat)
    (hbound : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
            SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
        (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ 125) :
    Pr[fun outcome => outcome.SuccessfulDoomed ∧
          outcome.FirstExistingHiddenNonRootHitAt ordinal |
        sampledObservedMaterializedDiagnostic adversary parameter ftsSecret (2 * q)] ≤
      ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  apply probEvent_sampledDiagnostic_successfulDoomed_firstExistingHiddenNonRootHitAt_le_of_forall
  intro table
  calc
    _ ≤ Pr[fun source => SelectedPrivateSnapshotNonRootHitAt source ordinal |
        granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret q] :=
      probEvent_observedMaterialized_successfulDoomed_firstNonRoot_le_selectedNonRoot adversary
        parameter ftsSecret q ordinal table (hbound table) hq
    _ ≤ _ := probEvent_granularAllCanonical_selectedNonRoot_le ordinal adversary parameter
      table ftsSecret q

end SphincsSecurity.Concrete.OtsProbeSimulation.Range125
