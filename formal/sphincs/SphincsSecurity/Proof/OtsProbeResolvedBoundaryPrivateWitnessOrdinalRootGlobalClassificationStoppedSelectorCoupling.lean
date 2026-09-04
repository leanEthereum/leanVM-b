import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedProbability

/-!
# Snapshot to ordinal-selector coupling

The chronological snapshot source and the ordinal selector follow the same direct execution until
the selected candidate is appended. The selector then stops, while every later source output keeps
that exact prefix.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.constructorNameAsVariable false

def SnapshotOrdinalSelectionRel
    (ordinal : Nat) (source : PrivateWitnessSnapshotOutput)
    (selection : Option PrivateOrdinalSelection) : Prop :=
  selectedPrivateSnapshotOrdinal? ordinal source.2 = selection

theorem privateOrdinalSelectionOfSnapshot_eq_of_prefix
    {initial final : List PlannedProbeSnapshot} (hprefix : initial <+: final)
    {ordinal : Nat} (hselected : ordinal < initial.length) :
    privateOrdinalSelectionOfSnapshot (⟨ordinal, hselected.trans_le hprefix.length_le⟩ :
        Fin final.length) =
      privateOrdinalSelectionOfSnapshot (⟨ordinal, hselected⟩ : Fin initial.length) := by
  obtain ⟨tail, rfl⟩ := hprefix
  have htake : ordinal + 1 ≤ initial.length := by omega
  simp [privateOrdinalSelectionOfSnapshot, List.get_eq_getElem,
    hselected, List.map_take, List.take_append_of_le_length, htake]

theorem selectedPrivateSnapshotOrdinal?_eq_of_prefix
    {initial final : List PlannedProbeSnapshot} (hprefix : initial <+: final)
    {ordinal : Nat} (hselected : ordinal < initial.length) :
    selectedPrivateSnapshotOrdinal? ordinal final =
      some (privateOrdinalSelectionOfSnapshot ⟨ordinal, hselected⟩) := by
  have hfinal : ordinal < final.length := hselected.trans_le hprefix.length_le
  rw [selectedPrivateSnapshotOrdinal?_eq_some hfinal]
  exact congrArg some (privateOrdinalSelectionOfSnapshot_eq_of_prefix hprefix hselected)

theorem privateOrdinalSelectionOfSnapshot_eq_selected_of_last
    {snapshots : List PlannedProbeSnapshot} {ordinal : Nat}
    (hlength : snapshots.length = ordinal + 1) :
    privateOrdinalSelectionOfSnapshot
        (⟨ordinal, by omega⟩ : Fin snapshots.length) =
      ⟨(snapshots.map PlannedProbeSnapshot.toProbe).get
          ⟨ordinal, by simpa [hlength]⟩,
        (snapshots.get ⟨ordinal, by omega⟩).context,
        snapshots.map PlannedProbeSnapshot.toProbe⟩ := by
  simp [privateOrdinalSelectionOfSnapshot, snapshotProbeOrdinal, hlength]

theorem relTriple_source_pure_lastSnapshotSelection
    (ordinal : Nat) (snapshots : List PlannedProbeSnapshot)
    (hlength : snapshots.length = ordinal + 1)
    (source : ProbComp PrivateWitnessSnapshotOutput)
    (hextends : ∀ output ∈ support source,
      PrivateWitnessSnapshotExtends snapshots output) :
    RelTriple source
      (pure (some
        ⟨(snapshots.map PlannedProbeSnapshot.toProbe).get
            ⟨ordinal, by simpa [hlength]⟩,
          (snapshots.get ⟨ordinal, by omega⟩).context,
          snapshots.map PlannedProbeSnapshot.toProbe⟩) :
        ProbComp (Option PrivateOrdinalSelection))
      (SnapshotOrdinalSelectionRel ordinal) := by
  have hbase := relTriple_true source
    (pure (some
      ⟨(snapshots.map PlannedProbeSnapshot.toProbe).get
          ⟨ordinal, by simpa [hlength]⟩,
        (snapshots.get ⟨ordinal, by omega⟩).context,
        snapshots.map PlannedProbeSnapshot.toProbe⟩) :
      ProbComp (Option PrivateOrdinalSelection))
  have hleft :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun output => PrivateWitnessSnapshotExtends snapshots output) hextends
  have hboth :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleft
  apply relTriple_post_mono hboth
  intro output selection hrelation
  have hselection : selection = some
      ⟨(snapshots.map PlannedProbeSnapshot.toProbe).get
          ⟨ordinal, by simpa [hlength]⟩,
        (snapshots.get ⟨ordinal, by omega⟩).context,
        snapshots.map PlannedProbeSnapshot.toProbe⟩ := by
    simpa using hrelation.2
  subst selection
  unfold SnapshotOrdinalSelectionRel
  rw [selectedPrivateSnapshotOrdinal?_eq_of_prefix hrelation.1.2 (by omega)]
  congr 1
  exact privateOrdinalSelectionOfSnapshot_eq_selected_of_last hlength

theorem relTriple_pureSnapshot_pure_none
    (ordinal : Nat) (witness : Option PrivateHitWitness)
    (snapshots : List PlannedProbeSnapshot)
    (hnotSelected : ¬ordinal < snapshots.length) :
    RelTriple
      (pure (witness, snapshots) : ProbComp PrivateWitnessSnapshotOutput)
      (pure none : ProbComp (Option PrivateOrdinalSelection))
      (SnapshotOrdinalSelectionRel ordinal) := by
  apply relTriple_pure_pure
  unfold SnapshotOrdinalSelectionRel selectedPrivateSnapshotOrdinal?
  simp [hnotSelected]

theorem relTriple_finishSnapshot_privateOrdinalSelection
    (ordinal : Nat)
    (sourceObserve : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp PrivateWitnessSnapshotOutput)
    (selectionObserve : DeferredContext → Nat → α → List Probe →
      ProbComp (Option PrivateOrdinalSelection))
    (snapshots : List PlannedProbeSnapshot) (result : DirectWitnessResult α)
    (hnotSelected : ¬ordinal < snapshots.length)
    (hcontinuation : ∀ resolved, result = .done resolved →
      RelTriple
        (sourceObserve resolved.context resolved.remaining resolved.value snapshots)
        (selectionObserve resolved.context resolved.remaining resolved.value
          (snapshots.map PlannedProbeSnapshot.toProbe))
        (SnapshotOrdinalSelectionRel ordinal)) :
    RelTriple
      (finishDirectWitnessSnapshotObserve sourceObserve snapshots result)
      (finishDirectPrivateOrdinalSelection selectionObserve
        (snapshots.map PlannedProbeSnapshot.toProbe) result)
      (SnapshotOrdinalSelectionRel ordinal) := by
  cases result with
  | stoppedFuel => exact relTriple_pureSnapshot_pure_none ordinal none snapshots hnotSelected
  | stoppedOrdinary => exact relTriple_pureSnapshot_pure_none ordinal none snapshots hnotSelected
  | stoppedPrivate witness =>
      exact relTriple_pureSnapshot_pure_none ordinal (some witness) snapshots hnotSelected
  | done resolved => exact hcontinuation resolved rfl

theorem relTriple_canonicalizeSnapshot_privateOrdinalSelection
    (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (sourceObserve : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp PrivateWitnessSnapshotOutput)
    (selectionObserve : DeferredContext → Nat → α → List Probe →
      ProbComp (Option PrivateOrdinalSelection))
    (context : DeferredContext) (fuel : Nat) (value : α)
    (snapshots : List PlannedProbeSnapshot)
    (hnotSelected : ¬ordinal < snapshots.length)
    (hcontinuation :
      RelTriple
        (sourceObserve (canonicalizeMaterializedValues table context) fuel value snapshots)
        (selectionObserve (canonicalizeMaterializedValues table context) fuel value
          (snapshots.map PlannedProbeSnapshot.toProbe))
        (SnapshotOrdinalSelectionRel ordinal)) :
    RelTriple
      (canonicalizeDirectWitnessSnapshotObserve table sourceObserve context fuel value snapshots)
      (canonicalizeDirectPrivateOrdinalSelection table selectionObserve context fuel value
        (snapshots.map PlannedProbeSnapshot.toProbe))
      (SnapshotOrdinalSelectionRel ordinal) := by
  classical
  unfold canonicalizeDirectWitnessSnapshotObserve canonicalizeDirectPrivateOrdinalSelection
  let canonical := canonicalizeMaterializedValues table context
  by_cases hhit : PrivateStructuralHit canonical
  · simp only [canonical, hhit, ↓reduceDIte, if_pos]
    exact relTriple_pureSnapshot_pure_none ordinal
      (some (privateHitWitnessOf canonical hhit)) snapshots hnotSelected
  · simp only [canonical, hhit, ↓reduceDIte, if_neg]
    change ¬PrivateStructuralHit (canonicalizeMaterializedValues table context) at hhit
    by_cases hpublished : PublishedValues context.state
    · simp only [hpublished, ↓reduceIte]
      unfold classifyDirectWitnessSnapshotObserve
      by_cases hcompletable : DeferredCompletable table canonical
      · change DeferredCompletable table
          (canonicalizeMaterializedValues table context) at hcompletable
        simpa [hhit, hcompletable] using hcontinuation
      · change ¬DeferredCompletable table
          (canonicalizeMaterializedValues table context) at hcompletable
        simpa [hhit, hcompletable] using
          (relTriple_pureSnapshot_pure_none ordinal none snapshots hnotSelected)
    · simp only [hpublished, ↓reduceIte]
      exact relTriple_pureSnapshot_pure_none ordinal none snapshots hnotSelected

theorem relTriple_retainedFinalizationSnapshot_pure_none
    (table : OtsSecretIndex → HashOutput) (root : Digest) (ordinal : Nat)
    (context : DeferredContext) (fuel : Nat)
    (value : RetainedRestResult × SplitHashCache)
    (snapshots : List PlannedProbeSnapshot)
    (hnotSelected : ¬ordinal < snapshots.length) :
    RelTriple
      (retainedResolvedFinalizationPrivateWitnessSnapshotObserve table root context fuel value
        snapshots)
      (pure none : ProbComp (Option PrivateOrdinalSelection))
      (SnapshotOrdinalSelectionRel ordinal) := by
  unfold retainedResolvedFinalizationPrivateWitnessSnapshotObserve
  by_cases hhit : PrivateStructuralHit context
  · simp only [hhit, ↓reduceDIte]
    exact relTriple_pureSnapshot_pure_none ordinal
      (some (privateHitWitnessOf context hhit)) snapshots hnotSelected
  · simp only [hhit, ↓reduceDIte]
    exact relTriple_pureSnapshot_pure_none ordinal none snapshots hnotSelected

theorem relTriple_runSnapshot_privateOrdinalSelection
    (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (sourceObserve : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp PrivateWitnessSnapshotOutput)
    (selectionObserve : DeferredContext → Nat → α → List Probe →
      ProbComp (Option PrivateOrdinalSelection))
    (snapshots : List PlannedProbeSnapshot) (context : DeferredContext) (fuel : Nat)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hnotSelected : ¬ordinal < snapshots.length)
    (hcontinuation : ∀ result : ResolvedRunResult α,
      DirectWitnessResult.done result ∈ support
        (runDirectResolvedWitnessFromTable context fuel table computation) →
      RelTriple
        (sourceObserve (canonicalizeMaterializedValues table result.context)
          result.remaining result.value snapshots)
        (selectionObserve (canonicalizeMaterializedValues table result.context)
          result.remaining result.value (snapshots.map PlannedProbeSnapshot.toProbe))
        (SnapshotOrdinalSelectionRel ordinal)) :
    RelTriple
      (runDirectWitnessSnapshotObserve
        (canonicalizeDirectWitnessSnapshotObserve table sourceObserve)
        snapshots context fuel table computation)
      (runDirectResolvedWitnessFromTable context fuel table computation >>=
        finishDirectPrivateOrdinalSelection
          (canonicalizeDirectPrivateOrdinalSelection table selectionObserve)
          (snapshots.map PlannedProbeSnapshot.toProbe))
      (SnapshotOrdinalSelectionRel ordinal) := by
  unfold runDirectWitnessSnapshotObserve
  have hbase := relTriple_refl
    (runDirectResolvedWitnessFromTable context fuel table computation)
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun result => result ∈ support
        (runDirectResolvedWitnessFromTable context fuel table computation))
      (fun result hresult => hresult)
  apply relTriple_bind hsupported
  intro leftResult rightResult hresult
  cases hresult.1
  apply relTriple_finishSnapshot_privateOrdinalSelection ordinal _ _ snapshots leftResult
    hnotSelected
  intro resolved heq
  subst leftResult
  apply relTriple_canonicalizeSnapshot_privateOrdinalSelection table ordinal _ _
    resolved.context resolved.remaining resolved.value snapshots hnotSelected
  exact hcontinuation resolved hresult.2

set_option maxHeartbeats 4000000 in
theorem relTriple_directSnapshot_privateOrdinalSelection
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (terminalObserve : DeferredContext → Nat → (α × SplitHashCache) →
      List PlannedProbeSnapshot → ProbComp PrivateWitnessSnapshotOutput)
    (snapshots : List PlannedProbeSnapshot) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hterminal : ∀ nextContext remaining value nextSnapshots,
      ¬ordinal < nextSnapshots.length →
      RelTriple
        (terminalObserve nextContext remaining value nextSnapshots)
        (pure none : ProbComp (Option PrivateOrdinalSelection))
        (SnapshotOrdinalSelectionRel ordinal))
    (hterminalExtends : ∀ nextContext remaining value nextSnapshots output,
      output ∈ support (terminalObserve nextContext remaining value nextSnapshots) →
      PrivateWitnessSnapshotExtends nextSnapshots output)
    (hnotSelected : ¬ordinal < snapshots.length) :
    RelTriple
      (directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve parameter root ftsSecret
        computation terminalObserve
        snapshots context fuel table cache)
      (directDetailedBoundaryPrivateOrdinalSelection ordinal parameter root ftsSecret computation
        (snapshots.map PlannedProbeSnapshot.toProbe) context fuel table cache)
      (SnapshotOrdinalSelectionRel ordinal) := by
  induction computation using OracleComp.inductionOn generalizing snapshots context fuel cache with
  | pure value =>
      rw [directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve, OracleComp.construct_pure,
        directDetailedBoundaryPrivateOrdinalSelection, OracleComp.construct_pure]
      have hnotMapped : ¬ordinal <
          (snapshots.map PlannedProbeSnapshot.toProbe).length := by simpa using hnotSelected
      simp only [selectedPrivateOrdinal?, hnotMapped, ↓reduceDIte]
      exact hterminal context fuel (value, cache) snapshots hnotSelected
  | query_bind query next ih =>
      rw [directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve,
        OracleComp.construct_query_bind, directDetailedBoundaryPrivateOrdinalSelection,
        OracleComp.construct_query_bind]
      have hnotMapped : ¬ordinal <
          (snapshots.map PlannedProbeSnapshot.toProbe).length := by simpa using hnotSelected
      simp only [hnotMapped, ↓reduceDIte]
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              change Fin (n + 1) → OracleComp (OracleWorld + SigningSpec) α at next
              let sourceObserve : DeferredContext → Nat →
                  (Fin (n + 1) × SplitHashCache) → List PlannedProbeSnapshot →
                    ProbComp PrivateWitnessSnapshotOutput :=
                fun nextContext remaining value nextSnapshots =>
                  directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve parameter root
                    ftsSecret (next value.1) terminalObserve
                    nextSnapshots nextContext remaining table value.2
              let selectionObserve : DeferredContext → Nat →
                  (Fin (n + 1) × SplitHashCache) → List Probe →
                    ProbComp (Option PrivateOrdinalSelection) :=
                fun nextContext remaining value candidates =>
                  directDetailedBoundaryPrivateOrdinalSelection ordinal parameter root ftsSecret
                    (next value.1) candidates nextContext remaining table value.2
              apply relTriple_runSnapshot_privateOrdinalSelection table ordinal sourceObserve
                selectionObserve snapshots context fuel ((splitUniformImpl n).run cache)
                hnotSelected
              intro result _hresult
              simpa [sourceObserve, selectionObserve] using
                (ih result.value.1 snapshots
                  (canonicalizeMaterializedValues table result.context) result.remaining
                  result.value.2 hnotSelected)
          | inr input =>
              change HashOutput → OracleComp (OracleWorld + SigningSpec) α at next
              simp only
              let plan := purePlanProbingHashQuery parameter input context.state
              let candidate? := rootAwarePlannedCandidate? parameter input context.state
              let nextSnapshots := appendPlannedSnapshot snapshots candidate? context
              let nextCandidates := appendPlannedCandidate
                (snapshots.map PlannedProbeSnapshot.toProbe) candidate?
              have hmap : nextSnapshots.map PlannedProbeSnapshot.toProbe = nextCandidates := by
                exact map_toProbe_appendPlannedSnapshot snapshots candidate? context
              change RelTriple
                (runDirectWitnessSnapshotObserve
                  (canonicalizeDirectWitnessSnapshotObserve table
                    (fun nextContext remaining value laterSnapshots =>
                      directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve parameter root
                        ftsSecret (next value.1) terminalObserve laterSnapshots nextContext remaining
                        table value.2))
                  nextSnapshots context fuel table
                  ((probingHashQueryAfterPlan parameter input plan).run cache))
                (if hnext : ordinal < nextCandidates.length then
                  pure (some ⟨nextCandidates.get ⟨ordinal, hnext⟩, context, nextCandidates⟩)
                else
                  runDirectResolvedWitnessFromTable context fuel table
                      ((probingHashQueryAfterPlan parameter input plan).run cache) >>=
                    finishDirectPrivateOrdinalSelection
                      (canonicalizeDirectPrivateOrdinalSelection table
                        (fun nextContext remaining value laterCandidates =>
                          directDetailedBoundaryPrivateOrdinalSelection ordinal parameter root
                            ftsSecret (next value.1) laterCandidates nextContext remaining table
                            value.2))
                      nextCandidates)
                (SnapshotOrdinalSelectionRel ordinal)
              by_cases hnextSelected : ordinal < nextSnapshots.length
              · have hnextMapped : ordinal < nextCandidates.length := by simpa [← hmap]
                  using hnextSelected
                have hlength : nextSnapshots.length = ordinal + 1 := by
                  cases hcandidate : candidate? with
                  | none =>
                      simp [nextSnapshots, appendPlannedSnapshot, hcandidate] at hnextSelected
                      exact False.elim (hnotSelected hnextSelected)
                  | some candidate =>
                      simp [nextSnapshots, appendPlannedSnapshot, hcandidate] at hnextSelected ⊢
                      omega
                obtain ⟨candidate, hcandidate⟩ : ∃ candidate, candidate? = some candidate := by
                  cases hcandidate : candidate? with
                  | none =>
                      simp [nextSnapshots, appendPlannedSnapshot, hcandidate] at hnextSelected
                      exact False.elim (hnotSelected hnextSelected)
                  | some candidate => exact ⟨candidate, rfl⟩
                have hordinal : ordinal = snapshots.length := by
                  simp [nextSnapshots, appendPlannedSnapshot, hcandidate] at hnextSelected
                  omega
                have hcandidateActual :
                    rootAwarePlannedCandidate? parameter input context.state = some candidate := by
                  simpa [candidate?] using hcandidate
                let source :=
                  runDirectWitnessSnapshotObserve
                    (canonicalizeDirectWitnessSnapshotObserve table
                      (fun nextContext remaining value laterSnapshots =>
                        directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve parameter
                          root ftsSecret (next value.1) terminalObserve
                          laterSnapshots nextContext remaining table value.2))
                    nextSnapshots context fuel table
                    ((probingHashQueryAfterPlan parameter input plan).run cache)
                have hextends : ∀ output ∈ support source,
                    PrivateWitnessSnapshotExtends nextSnapshots output := by
                  intro output houtput
                  unfold source at houtput
                  apply privateWitnessSnapshotExtends_of_mem_runDirectWitnessSnapshotObserve _
                    nextSnapshots context fuel table
                    ((probingHashQueryAfterPlan parameter input plan).run cache)
                    (output := output) (houtput := houtput)
                  intro result _hresult nextOutput hnextOutput
                  apply privateWitnessSnapshotExtends_of_mem_canonicalizeDirectWitnessSnapshotObserve
                    table _ result.context result.remaining result.value nextSnapshots
                    (output := nextOutput) (houtput := hnextOutput)
                  intro finalOutput hfinalOutput
                  apply privateWitnessSnapshotExtends_of_mem_directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve
                    parameter root ftsSecret (next result.value.1)
                    terminalObserve
                    nextSnapshots (canonicalizeMaterializedValues table result.context)
                    result.remaining table result.value.2 (output := finalOutput)
                    (houtput := hfinalOutput)
                  intro finalContext finalRemaining finalValue finalSnapshots retainedOutput
                    hretained
                  exact hterminalExtends finalContext finalRemaining finalValue finalSnapshots
                    retainedOutput hretained
                have hselectedRel := relTriple_source_pure_lastSnapshotSelection ordinal
                  nextSnapshots hlength source hextends
                have hactual : snapshots.length <
                    (appendPlannedCandidate (snapshots.map PlannedProbeSnapshot.toProbe)
                      (rootAwarePlannedCandidate? parameter input context.state)).length := by
                  simp [hcandidateActual, appendPlannedCandidate]
                simpa [source, plan, nextSnapshots, nextCandidates, hcandidate, hcandidateActual,
                  hordinal, hactual, appendPlannedSnapshot, appendPlannedCandidate]
                  using hselectedRel
              · have hnextMapped : ¬ordinal < nextCandidates.length := by
                  simpa [← hmap] using hnextSelected
                have hactual : ¬ordinal <
                    (appendPlannedCandidate (snapshots.map PlannedProbeSnapshot.toProbe)
                      (rootAwarePlannedCandidate? parameter input context.state)).length := by
                  simpa [candidate?, nextCandidates] using hnextMapped
                let sourceObserve : DeferredContext → Nat →
                    (HashOutput × SplitHashCache) → List PlannedProbeSnapshot →
                      ProbComp PrivateWitnessSnapshotOutput :=
                  fun nextContext remaining value laterSnapshots =>
                    directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve parameter root
                      ftsSecret (next value.1) terminalObserve
                      laterSnapshots nextContext remaining table value.2
                let selectionObserve : DeferredContext → Nat →
                    (HashOutput × SplitHashCache) → List Probe →
                      ProbComp (Option PrivateOrdinalSelection) :=
                  fun nextContext remaining value candidates =>
                    directDetailedBoundaryPrivateOrdinalSelection ordinal parameter root ftsSecret
                      (next value.1) candidates nextContext remaining table value.2
                have hrel := relTriple_runSnapshot_privateOrdinalSelection table ordinal
                  sourceObserve selectionObserve nextSnapshots context fuel
                  ((probingHashQueryAfterPlan parameter input plan).run cache) hnextSelected
                  (by
                    intro result _hresult
                    simpa [sourceObserve, selectionObserve, hmap] using
                      (ih result.value.1 nextSnapshots
                        (canonicalizeMaterializedValues table result.context) result.remaining
                        result.value.2 hnextSelected))
                simpa [sourceObserve, selectionObserve, plan, candidate?, nextSnapshots,
                  nextCandidates, hmap, hnextMapped, hactual] using hrel
      | inr message =>
          change Option Signature → OracleComp (OracleWorld + SigningSpec) α at next
          let sourceObserve : DeferredContext → Nat →
              (Option Signature × SplitHashCache) → List PlannedProbeSnapshot →
                ProbComp PrivateWitnessSnapshotOutput :=
            fun nextContext remaining value nextSnapshots =>
              directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve parameter root
                ftsSecret (next value.1) terminalObserve
                nextSnapshots nextContext remaining table value.2
          let selectionObserve : DeferredContext → Nat →
              (Option Signature × SplitHashCache) → List Probe →
                ProbComp (Option PrivateOrdinalSelection) :=
            fun nextContext remaining value candidates =>
              directDetailedBoundaryPrivateOrdinalSelection ordinal parameter root ftsSecret
                (next value.1) candidates nextContext remaining table value.2
          apply relTriple_runSnapshot_privateOrdinalSelection table ordinal sourceObserve
            selectionObserve snapshots context fuel
            ((maskedSign parameter root ftsSecret message).run cache) hnotSelected
          intro result _hresult
          simpa [sourceObserve, selectionObserve] using
            (ih result.value.1 snapshots
              (canonicalizeMaterializedValues table result.context) result.remaining
              result.value.2 hnotSelected)

theorem relTriple_granularRetainedSnapshot_privateOrdinalSelection
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (snapshots : List PlannedProbeSnapshot)
    (hnotSelected : ¬ordinal < snapshots.length) :
    RelTriple
      (granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve adversary parameter
        table ftsSecret context fuel value snapshots)
      (directDetailedBoundaryPrivateOrdinalSelection ordinal parameter value.1 ftsSecret
        (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
        (snapshots.map PlannedProbeSnapshot.toProbe) context fuel table value.2)
      (SnapshotOrdinalSelectionRel ordinal) := by
  unfold granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve
  apply relTriple_directSnapshot_privateOrdinalSelection ordinal parameter value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
    (retainedResolvedFinalizationPrivateWitnessSnapshotObserve table value.1)
    snapshots context fuel table value.2
  · intro nextContext remaining nextValue nextSnapshots hnot
    exact relTriple_retainedFinalizationSnapshot_pure_none table value.1 ordinal nextContext
      remaining nextValue nextSnapshots hnot
  · intro nextContext remaining nextValue nextSnapshots output houtput
    exact privateWitnessSnapshotExtends_of_mem_retainedResolvedFinalizationPrivateWitnessSnapshotObserve
      table value.1 nextContext remaining nextValue nextSnapshots output houtput
  · exact hnotSelected

end SphincsSecurity.Concrete.OtsProbeSimulation
