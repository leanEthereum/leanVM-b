import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStopped

/-!
# Monotone stopped-source snapshots

The source experiment only appends planned snapshots. A snapshot selected when the comparison first
stops therefore remains an exact prefix entry after an arbitrary source continuation.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def PrivateWitnessSnapshotExtends
    (snapshots : List PlannedProbeSnapshot) (output : PrivateWitnessSnapshotOutput) : Prop :=
  snapshots <+: output.2

theorem privateWitnessSnapshotExtends_of_mem_finishDirectWitnessSnapshotObserve
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp PrivateWitnessSnapshotOutput)
    (snapshots : List PlannedProbeSnapshot) (result : DirectWitnessResult α)
    (hobserve : ∀ resolved : ResolvedRunResult α,
      result = .done resolved →
      ∀ output ∈ support (observe resolved.context resolved.remaining resolved.value snapshots),
        PrivateWitnessSnapshotExtends snapshots output)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (finishDirectWitnessSnapshotObserve observe snapshots result)) :
    PrivateWitnessSnapshotExtends snapshots output := by
  cases result with
  | stoppedFuel =>
      simp [finishDirectWitnessSnapshotObserve] at houtput
      subst output
      simp [PrivateWitnessSnapshotExtends]
  | stoppedOrdinary =>
      simp [finishDirectWitnessSnapshotObserve] at houtput
      subst output
      simp [PrivateWitnessSnapshotExtends]
  | stoppedPrivate witness =>
      simp [finishDirectWitnessSnapshotObserve] at houtput
      subst output
      simp [PrivateWitnessSnapshotExtends]
  | done resolved => exact hobserve resolved rfl output houtput

theorem privateWitnessSnapshotExtends_of_mem_runDirectWitnessSnapshotObserve
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp PrivateWitnessSnapshotOutput)
    (snapshots : List PlannedProbeSnapshot) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hobserve : ∀ result : ResolvedRunResult α,
      DirectWitnessResult.done result ∈ support
        (runDirectResolvedWitnessFromTable context fuel table computation) →
      ∀ output ∈ support (observe result.context result.remaining result.value snapshots),
        PrivateWitnessSnapshotExtends snapshots output)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (runDirectWitnessSnapshotObserve observe snapshots context fuel table computation)) :
    PrivateWitnessSnapshotExtends snapshots output := by
  unfold runDirectWitnessSnapshotObserve at houtput
  rw [mem_support_bind_iff] at houtput
  obtain ⟨result, hresult, hfinish⟩ := houtput
  exact privateWitnessSnapshotExtends_of_mem_finishDirectWitnessSnapshotObserve observe snapshots
    result (by
      intro resolved heq
      subst result
      exact hobserve resolved hresult)
    output hfinish

theorem privateWitnessSnapshotExtends_of_mem_classifyDirectWitnessSnapshotObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp PrivateWitnessSnapshotOutput)
    (context : DeferredContext) (fuel : Nat) (value : α)
    (snapshots : List PlannedProbeSnapshot)
    (hobserve : ∀ output ∈ support (observe context fuel value snapshots),
      PrivateWitnessSnapshotExtends snapshots output)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (classifyDirectWitnessSnapshotObserve table observe context fuel value snapshots)) :
    PrivateWitnessSnapshotExtends snapshots output := by
  unfold classifyDirectWitnessSnapshotObserve at houtput
  by_cases hhit : PrivateStructuralHit context
  · simp [hhit] at houtput
    subst output
    simp [PrivateWitnessSnapshotExtends]
  · simp only [hhit, ↓reduceDIte] at houtput
    by_cases hcompletable : DeferredCompletable table context
    · simp only [hcompletable, ↓reduceIte] at houtput
      exact hobserve output houtput
    · simp [hcompletable] at houtput
      subst output
      simp [PrivateWitnessSnapshotExtends]

theorem privateWitnessSnapshotExtends_of_mem_canonicalizeDirectWitnessSnapshotObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp PrivateWitnessSnapshotOutput)
    (context : DeferredContext) (fuel : Nat) (value : α)
    (snapshots : List PlannedProbeSnapshot)
    (hobserve : ∀ output ∈ support
      (observe (canonicalizeMaterializedValues table context) fuel value snapshots),
      PrivateWitnessSnapshotExtends snapshots output)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (canonicalizeDirectWitnessSnapshotObserve table observe context fuel value snapshots)) :
    PrivateWitnessSnapshotExtends snapshots output := by
  unfold canonicalizeDirectWitnessSnapshotObserve at houtput
  let canonical := canonicalizeMaterializedValues table context
  by_cases hhit : PrivateStructuralHit canonical
  · simp [canonical, hhit] at houtput
    subst output
    simp [PrivateWitnessSnapshotExtends]
  · simp only [canonical, hhit, ↓reduceDIte] at houtput
    by_cases hpublished : PublishedValues context.state
    · simp only [hpublished, ↓reduceIte] at houtput
      exact privateWitnessSnapshotExtends_of_mem_classifyDirectWitnessSnapshotObserve table observe
        canonical fuel value snapshots hobserve output houtput
    · simp [hpublished] at houtput
      subst output
      simp [PrivateWitnessSnapshotExtends]

set_option maxRecDepth 100000 in
theorem privateWitnessSnapshotExtends_of_mem_directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) →
      List PlannedProbeSnapshot → ProbComp PrivateWitnessSnapshotOutput)
    (snapshots : List PlannedProbeSnapshot) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hobserve : ∀ nextContext remaining value nextSnapshots output,
      output ∈ support (observe nextContext remaining value nextSnapshots) →
      PrivateWitnessSnapshotExtends nextSnapshots output)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve parameter root ftsSecret
        computation observe snapshots context fuel table cache)) :
    PrivateWitnessSnapshotExtends snapshots output := by
  induction computation using OracleComp.inductionOn generalizing snapshots context fuel cache output with
  | pure value =>
      rw [directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve,
        OracleComp.construct_pure] at houtput
      exact hobserve context fuel (value, cache) snapshots output houtput
  | query_bind query next ih =>
      rw [directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve,
        OracleComp.construct_query_bind] at houtput
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              apply privateWitnessSnapshotExtends_of_mem_runDirectWitnessSnapshotObserve _
                snapshots context fuel table ((splitUniformImpl n).run cache) (output := output)
                (houtput := houtput)
              intro result _hresult nextOutput hnextOutput
              apply privateWitnessSnapshotExtends_of_mem_canonicalizeDirectWitnessSnapshotObserve
                table _ result.context result.remaining result.value snapshots
                (output := nextOutput) (houtput := hnextOutput)
              intro finalOutput hfinalOutput
              exact ih result.value.1 snapshots
                (canonicalizeMaterializedValues table result.context) result.remaining
                result.value.2 finalOutput hfinalOutput
          | inr input =>
              let plan := purePlanProbingHashQuery parameter input context.state
              let nextSnapshots := appendPlannedSnapshot snapshots
                (rootAwarePlannedCandidate? parameter input context.state) context
              have hprefix : snapshots <+: nextSnapshots := by
                cases hcandidate : rootAwarePlannedCandidate? parameter input context.state <;>
                  simp [nextSnapshots, appendPlannedSnapshot, hcandidate]
              have hnext : PrivateWitnessSnapshotExtends nextSnapshots output := by
                apply privateWitnessSnapshotExtends_of_mem_runDirectWitnessSnapshotObserve _
                  nextSnapshots context fuel table
                  ((probingHashQueryAfterPlan parameter input plan).run cache) (output := output)
                  (houtput := houtput)
                intro result _hresult nextOutput hnextOutput
                apply privateWitnessSnapshotExtends_of_mem_canonicalizeDirectWitnessSnapshotObserve
                  table _ result.context result.remaining result.value nextSnapshots
                  (output := nextOutput) (houtput := hnextOutput)
                intro finalOutput hfinalOutput
                exact ih result.value.1 nextSnapshots
                  (canonicalizeMaterializedValues table result.context) result.remaining
                  result.value.2 finalOutput hfinalOutput
              exact hprefix.trans hnext
      | inr message =>
          apply privateWitnessSnapshotExtends_of_mem_runDirectWitnessSnapshotObserve _ snapshots
            context fuel table ((maskedSign parameter root ftsSecret message).run cache)
            (output := output) (houtput := houtput)
          intro result _hresult nextOutput hnextOutput
          apply privateWitnessSnapshotExtends_of_mem_canonicalizeDirectWitnessSnapshotObserve
            table _ result.context result.remaining result.value snapshots
            (output := nextOutput) (houtput := hnextOutput)
          intro finalOutput hfinalOutput
          exact ih result.value.1 snapshots
            (canonicalizeMaterializedValues table result.context) result.remaining result.value.2
            finalOutput hfinalOutput

theorem privateWitnessSnapshotExtends_of_mem_retainedResolvedFinalizationPrivateWitnessSnapshotObserve
    (table : OtsSecretIndex → HashOutput) (root : Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : RetainedRestResult × SplitHashCache)
    (snapshots : List PlannedProbeSnapshot)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (retainedResolvedFinalizationPrivateWitnessSnapshotObserve table root context fuel value
        snapshots)) :
    PrivateWitnessSnapshotExtends snapshots output := by
  unfold retainedResolvedFinalizationPrivateWitnessSnapshotObserve at houtput
  by_cases hhit : PrivateStructuralHit context <;>
    simp [hhit] at houtput <;> subst output <;> simp [PrivateWitnessSnapshotExtends]

theorem privateWitnessSnapshotExtends_of_mem_granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (snapshots : List PlannedProbeSnapshot)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve adversary parameter
        table ftsSecret context fuel value snapshots)) :
    PrivateWitnessSnapshotExtends snapshots output := by
  unfold granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve at houtput
  apply privateWitnessSnapshotExtends_of_mem_directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve
    parameter value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
    (retainedResolvedFinalizationPrivateWitnessSnapshotObserve table value.1)
    snapshots context fuel table value.2 (output := output) (houtput := houtput)
  intro nextContext remaining nextValue nextSnapshots nextOutput hnextOutput
  exact privateWitnessSnapshotExtends_of_mem_retainedResolvedFinalizationPrivateWitnessSnapshotObserve
    table value.1 nextContext remaining nextValue nextSnapshots nextOutput hnextOutput

def SelectedPrivateSnapshotHitAt
    (source : PrivateWitnessSnapshotOutput) (ordinal : Nat) : Prop :=
  ∃ selected : Fin source.2.length, selected.val = ordinal ∧
    ∃ position output,
      (source.2.get selected).probe = ⟨.position position, truncateHash output⟩ ∧
      (source.2.get selected).context.state.values (.position position) = none ∧
      Coordinate.position position ∉ (source.2.get selected).context.state.revealed ∧
      (source.2.get selected).context.values position = some output ∧
      CandidatesAvoidRoot position (truncateHash output)
        ((source.2.map PlannedProbeSnapshot.toProbe).take ordinal)

def SelectedSnapshotObservationAlignedAt
    (table : OtsSecretIndex → HashOutput) (source : PrivateWitnessSnapshotOutput)
    (result : ObservedCleanRunResult α) (ordinal : Nat) : Prop :=
  ∃ sourceOrdinal : Fin source.2.length,
    ∃ observedOrdinal : Fin result.observations.length,
      sourceOrdinal.val = ordinal ∧ observedOrdinal.val = ordinal ∧
        (source.2.get sourceOrdinal).probe =
          (result.observations.get observedOrdinal).toProbe ∧
        (source.2.map PlannedProbeSnapshot.toProbe).take ordinal =
          (result.observations.map CleanProbeObservation.toProbe).take ordinal ∧
        SnapshotsObservedAt table (source.2.take ordinal)
          (result.observations.take ordinal)

theorem SelectedSnapshotObservationAlignedAt.prefix
    {source : PrivateWitnessSnapshotOutput}
    {before : ObservedCleanRunResult α} {after : ObservedCleanRunResult β}
    {ordinal : Nat}
    (haligned : SelectedSnapshotObservationAlignedAt table source before ordinal)
    (hprefix : before.observations <+: after.observations) :
    SelectedSnapshotObservationAlignedAt table source after ordinal := by
  obtain ⟨sourceOrdinal, observedOrdinal, hsource, hobserved, heq, hprefixEq,
    hsnapshots⟩ := haligned
  have hlt : observedOrdinal.val < after.observations.length :=
    observedOrdinal.isLt.trans_le hprefix.length_le
  let observedOrdinal' : Fin after.observations.length := ⟨observedOrdinal.val, hlt⟩
  refine ⟨sourceOrdinal, observedOrdinal', hsource, hobserved, ?_, ?_, ?_⟩
  have hget : after.observations[observedOrdinal.val] =
      before.observations[observedOrdinal.val] := (hprefix.getElem observedOrdinal.isLt).symm
  simpa [observedOrdinal', hget] using heq
  obtain ⟨tail, htail⟩ := hprefix
  rw [← htail]
  rw [List.map_append, List.take_append_of_le_length]
  · exact hprefixEq
  · simpa using Nat.le_of_lt (hobserved ▸ observedOrdinal.isLt)
  obtain ⟨tail, htail⟩ := hprefix
  rw [← htail]
  simpa [List.take_append_of_le_length (Nat.le_of_lt (hobserved ▸
    observedOrdinal.isLt))] using hsnapshots

theorem privateCandidate_eq_of_addPending_privateStructuralHit
    (candidate : Probe) (context : DeferredContext)
    (hclean : ¬PrivateStructuralHit context)
    (hhit : PrivateStructuralHit
      ({ context with
        state := context.state.addPending candidate.coordinate candidate.candidate } :
        DeferredContext)) :
    ∃ position output,
      candidate = ⟨.position position, truncateHash output⟩ ∧
      context.state.values (.position position) = none ∧
      context.values position = some output := by
  obtain ⟨position, output, hvalue, hprivate, hpending⟩ := hhit
  have hvalue' : context.state.values (.position position) = none := by
    simpa [LazyRevealProbe.State.addPending] using hvalue
  have hprivate' : context.values position = some output := by simpa using hprivate
  have hmember :
      (Coordinate.position position, truncateHash output) ∈
        (context.state.addPending candidate.coordinate candidate.candidate).pending := by
    rw [← LazyRevealProbe.State.mem_pendingAt_iff]
    exact hpending
  rw [LazyRevealProbe.State.addPending] at hmember
  simp only [Finset.mem_insert] at hmember
  rcases hmember with hnew | hold
  · refine ⟨position, output, ?_, hvalue', hprivate'⟩
    cases candidate with
    | mk coordinate digest =>
        cases hnew
        rfl
  · exact (hclean ⟨position, output, hvalue', hprivate', by
      unfold LazyRevealProbe.State.hitAt
      rw [LazyRevealProbe.State.mem_pendingAt_iff]
      exact hold⟩).elim

theorem selectedPrivateSnapshotHitAt_of_appended_privateStructuralHit
    (snapshots : List PlannedProbeSnapshot) (candidate : Probe)
    (context : DeferredContext) (source : PrivateWitnessSnapshotOutput)
    (hextends : PrivateWitnessSnapshotExtends
      (snapshots ++ [(⟨candidate, context⟩ : PlannedProbeSnapshot)]) source)
    (hcompletable : DeferredCompletable table context)
    (hhidden : candidate.coordinate ∉ context.state.revealed)
    (havoid : ∀ position output,
      candidate = ⟨.position position, truncateHash output⟩ →
      context.state.values (.position position) = none →
      context.values position = some output →
      CandidatesAvoidRoot position (truncateHash output)
        (snapshots.map PlannedProbeSnapshot.toProbe))
    (hhit : PrivateStructuralHit
      ({ context with
        state := context.state.addPending candidate.coordinate candidate.candidate } :
        DeferredContext)) :
    SelectedPrivateSnapshotHitAt source snapshots.length := by
  have hclean : ¬PrivateStructuralHit context :=
    not_privateStructuralHit_of_deferredCompletable hcompletable
  obtain ⟨position, output, hcandidate, hvalue, hprivate⟩ :=
    privateCandidate_eq_of_addPending_privateStructuralHit candidate context hclean hhit
  have hltCurrent : snapshots.length <
      (snapshots ++ [(⟨candidate, context⟩ : PlannedProbeSnapshot)]).length := by
    simp
  have hltSource : snapshots.length < source.2.length :=
    hltCurrent.trans_le hextends.length_le
  let selected : Fin source.2.length := ⟨snapshots.length, hltSource⟩
  have hselected : source.2.get selected = ⟨candidate, context⟩ := by
    change source.2[snapshots.length] = ⟨candidate, context⟩
    have hpref :
        (snapshots ++ [(⟨candidate, context⟩ : PlannedProbeSnapshot)])[snapshots.length] =
          source.2[snapshots.length] := hextends.getElem hltCurrent
    rw [← hpref]
    simp
  refine ⟨selected, rfl, position, output, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hselected]
    simpa using hcandidate
  · rw [hselected]
    exact hvalue
  · rw [hselected]
    rw [hcandidate] at hhidden
    exact hhidden
  · rw [hselected]
    exact hprivate
  · rw [← List.map_take]
    obtain ⟨tail, htail⟩ := hextends
    rw [← htail]
    simp only [List.append_assoc, List.take_left]
    exact havoid position output hcandidate hvalue hprivate

theorem FirstExistingHiddenHitAt.prefix
    {before : ObservedCleanRunResult α} {after : ObservedCleanRunResult β}
    {ordinal : Nat}
    (hfirst : FirstExistingHiddenHitAt before ordinal)
    (hprefix : before.observations <+: after.observations) :
    FirstExistingHiddenHitAt after ordinal := by
  obtain ⟨selected, hordinal, hhit, hbefore⟩ := hfirst
  have hselectedLt : selected.val < after.observations.length :=
    selected.isLt.trans_le hprefix.length_le
  let selected' : Fin after.observations.length := ⟨selected.val, hselectedLt⟩
  refine ⟨selected', hordinal, ?_, ?_⟩
  · have hget : after.observations[selected.val] = before.observations[selected.val] :=
      (hprefix.getElem selected.isLt).symm
    simpa [ExistingHiddenHitAtOrdinal, selected', hget] using hhit
  · intro earlier hearlier
    have hearlierBefore : earlier.val < before.observations.length := by
      have : earlier.val < selected.val := by omega
      exact this.trans selected.isLt
    let earlier' : Fin before.observations.length := ⟨earlier.val, hearlierBefore⟩
    have hget : after.observations[earlier.val] = before.observations[earlier.val] :=
      (hprefix.getElem hearlierBefore).symm
    simpa [ExistingHiddenHitAtOrdinal, earlier', hget] using
      hbefore earlier' (by omega)

theorem firstExistingHiddenHitAt_append_of_privateStructuralHit
    (table : OtsSecretIndex → HashOutput)
    (candidate : Probe) (observations : List CleanProbeObservation)
    (left right : DeferredContext)
    (hcontext : FinalizationContextLE table left right)
    (hrightMaterialized : right = directDeferredContext right.state)
    (hhidden : candidate.coordinate ∉ right.state.revealed)
    (hnoEarlier : ∀ observation ∈ observations,
      ¬observation.ExistingHiddenHit)
    (hhit : PrivateStructuralHit
      ({ left with
        state := left.state.addPending candidate.coordinate candidate.candidate } :
        DeferredContext)) :
    FirstExistingHiddenHitAt
      (⟨right.state, 0, (), table,
        observations ++ [cleanProbeObservation right.state
          candidate.coordinate candidate.candidate]⟩ : ObservedCleanRunResult Unit)
      observations.length := by
  have hclean : ¬PrivateStructuralHit left :=
    not_privateStructuralHit_of_deferredCompletable hcontext.leftCompletable
  obtain ⟨position, output, hcandidate, hleftValue, hprivate⟩ :=
    privateCandidate_eq_of_addPending_privateStructuralHit candidate left hclean hhit
  subst candidate
  have hrightValue : right.state.values (.position position) = some output := by
    have hleftPosition : left.positionValue position = some output := by
      simp [DeferredContext.positionValue, hleftValue, hprivate]
    have hresolved : resolvedCompletionValue table right (.position position) = some output := by
      rw [← hcontext.view.valueEq]
      simpa [resolvedCompletionValue] using hleftPosition
    rw [hrightMaterialized] at hresolved
    cases hright : right.state.values (.position position) with
    | none =>
        simp [resolvedCompletionValue, directDeferredContext, directDeferredValues,
          DeferredContext.positionValue, hright] at hresolved
    | some existing =>
        have heq : existing = output := by
          simpa [resolvedCompletionValue, directDeferredContext, directDeferredValues,
            DeferredContext.positionValue, hright] using hresolved
        simpa [hright, heq]
  let observation := cleanProbeObservation right.state
    (.position position) (truncateHash output)
  have hobservation : observation.ExistingHiddenHit := by
    refine ⟨?_, output, ?_, ?_⟩
    · simp [observation, cleanProbeObservation, hhidden]
    · simpa [observation, cleanProbeObservation, hrightValue]
    · simp [observation, cleanProbeObservation]
  have hlength : observations.length < (observations ++ [observation]).length := by simp
  let selected : Fin (observations ++ [observation]).length :=
    ⟨observations.length, hlength⟩
  change FirstExistingHiddenHitAt
    (⟨right.state, 0, (), table, observations ++ [observation]⟩ :
      ObservedCleanRunResult Unit) observations.length
  refine ⟨selected, rfl, ?_, ?_⟩
  · simpa [ExistingHiddenHitAtOrdinal, selected, observation] using hobservation
  · intro earlier hearlier
    have hearlierLength : earlier.val < observations.length := by
      simpa [selected] using hearlier
    let before : Fin observations.length := ⟨earlier.val, hearlierLength⟩
    have hbefore := hnoEarlier (observations.get before) (List.get_mem _ _)
    simpa [ExistingHiddenHitAtOrdinal, selected, before, observation,
      List.getElem_append, hearlierLength] using hbefore

def SnapshotObservedSelectedStoppedRel
    (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (source : PrivateWitnessSnapshotOutput)
    (observed : Option (ObservedCleanRunResult (α × SplitHashCache))) : Prop :=
  observed = none ∨
    ∃ result, observed = some result ∧
      result.table = table ∧
      DoomedResolvedContext table (directDeferredContext result.state) ∧
      FirstExistingHiddenHitAt result ordinal ∧
      SelectedPrivateSnapshotHitAt source ordinal ∧
      SelectedSnapshotObservationAlignedAt table source result ordinal

theorem missingChainStartHit_of_doomed_direct_valid
    (table : OtsSecretIndex → HashOutput)
    (state : LazyRevealProbe.State Coordinate)
    (hdoomed : DoomedResolvedContext table (directDeferredContext state))
    (hvalid : (directDeferredContext state).Valid)
    (hcard : state.pending.card < Fintype.card Digest) :
    MissingChainStartHit table (directDeferredContext state) := by
  have hcauses := privateStructuralHit_or_missingChainStartHit_of_not_completable table
    (directDeferredContext state) hvalid hdoomed.2.1 hcard hdoomed.2.2
  exact hcauses.resolve_left (not_privateStructuralHit_of_directDeferredContext _ rfl)

def SnapshotObservedFirstStoppedRel
    (table : OtsSecretIndex → HashOutput)
    (source : PrivateWitnessSnapshotOutput)
    (observed : Option (ObservedCleanRunResult (α × SplitHashCache))) : Prop :=
  observed = none ∨
    (∃ result aligned, observed = some result ∧
      aligned <+: result.observations ∧
      SnapshotsObservedAt table source.2 aligned ∧
      (∀ observation ∈ result.observations, ¬observation.ExistingHiddenHit) ∧
      ∀ witness, source.1 = some witness →
        result.state.values (.position witness.position) = some witness.output) ∨
    (∃ result ordinal, observed = some result ∧
      result.table = table ∧
      DoomedResolvedContext table (directDeferredContext result.state) ∧
      FirstExistingHiddenHitAt result ordinal ∧
      SelectedPrivateSnapshotHitAt source ordinal ∧
      SelectedSnapshotObservationAlignedAt table source result ordinal) ∨
    ∃ result, observed = some result ∧
      result.table = table ∧
      DoomedResolvedContext table (directDeferredContext result.state) ∧
      ObservedStoppedCause table result

theorem SnapshotObservedSelectedStoppedRel.to_firstStopped
    {table : OtsSecretIndex → HashOutput} {ordinal : Nat}
    {source : PrivateWitnessSnapshotOutput}
    {observed : Option (ObservedCleanRunResult (α × SplitHashCache))}
    (hrelation : SnapshotObservedSelectedStoppedRel table ordinal source observed) :
    SnapshotObservedFirstStoppedRel table source observed := by
  rcases hrelation with hfailed |
    ⟨result, hresult, htable, hdoomed, hfirst, hselected, haligned⟩
  · exact Or.inl hfailed
  · exact Or.inr (Or.inr (Or.inl
      ⟨result, ordinal, hresult, htable, hdoomed, hfirst, hselected, haligned⟩))

set_option maxRecDepth 100000 in
theorem relTriple_source_observedMaterializedBoundary_selectedStopped
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (source : ProbComp PrivateWitnessSnapshotOutput)
    (snapshots : List PlannedProbeSnapshot)
    (candidate : Probe) (context : DeferredContext)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hsource : ∀ output ∈ support source,
      PrivateWitnessSnapshotExtends
        (snapshots ++ [(⟨candidate, context⟩ : PlannedProbeSnapshot)]) output)
    (hcompletable : DeferredCompletable table context)
    (hhidden : candidate.coordinate ∉ context.state.revealed)
    (havoid : ∀ position output,
      candidate = ⟨.position position, truncateHash output⟩ →
      context.state.values (.position position) = none →
      context.values position = some output →
      CandidatesAvoidRoot position (truncateHash output)
        (snapshots.map PlannedProbeSnapshot.toProbe))
    (hhit : PrivateStructuralHit
      ({ context with
        state := context.state.addPending candidate.coordinate candidate.candidate } :
        DeferredContext))
    (hfirst : FirstExistingHiddenHitAt
      (⟨state, fuel, (), table, observations⟩ : ObservedCleanRunResult Unit) snapshots.length)
    (hselectedAligned : ∀ output ∈ support source,
      SelectedSnapshotObservationAlignedAt table output
        (⟨state, fuel, (), table, observations⟩ : ObservedCleanRunResult Unit)
        snapshots.length)
    (hdoomed : DoomedResolvedContext table (directDeferredContext state)) :
    RelTriple source
      (observedMaterializedBoundary parameter root ftsSecret computation observations state fuel
        table cache)
      (SnapshotObservedSelectedStoppedRel table snapshots.length) := by
  have hbase := relTriple_true source
    (observedMaterializedBoundary parameter root ftsSecret computation observations state fuel
      table cache)
  have hleft :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun output => output ∈ support source) (fun output houtput => houtput)
  have hboth :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleft
  apply relTriple_post_mono hboth
  intro sourceOutput observed hrelation
  cases observed with
  | none => exact Or.inl rfl
  | some result =>
      right
      have hprefix := observations_prefix_of_mem_observedMaterializedBoundary parameter root
        ftsSecret computation observations state fuel table cache result hrelation.2
      have hdoomedResult := materializedDoomed_of_mem_observedMaterializedBoundary parameter root
        ftsSecret computation observations state fuel table cache result hdoomed hrelation.2
      refine ⟨result, rfl, hdoomedResult.1, hdoomedResult.2, ?_, ?_, ?_⟩
      exact hfirst.prefix hprefix
      exact selectedPrivateSnapshotHitAt_of_appended_privateStructuralHit snapshots candidate
        context sourceOutput (hsource sourceOutput hrelation.1.2) hcompletable hhidden havoid hhit
      exact (hselectedAligned sourceOutput hrelation.1.2).prefix hprefix

set_option maxRecDepth 100000 in
theorem relTriple_source_observedMaterializedBoundary_firstStopped_of_selected
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (source : ProbComp PrivateWitnessSnapshotOutput)
    (snapshots : List PlannedProbeSnapshot)
    (candidate : Probe) (context : DeferredContext)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hsource : ∀ output ∈ support source,
      PrivateWitnessSnapshotExtends
        (snapshots ++ [(⟨candidate, context⟩ : PlannedProbeSnapshot)]) output)
    (hcompletable : DeferredCompletable table context)
    (hhidden : candidate.coordinate ∉ context.state.revealed)
    (havoid : ∀ position output,
      candidate = ⟨.position position, truncateHash output⟩ →
      context.state.values (.position position) = none →
      context.values position = some output →
      CandidatesAvoidRoot position (truncateHash output)
        (snapshots.map PlannedProbeSnapshot.toProbe))
    (hhit : PrivateStructuralHit
      ({ context with
        state := context.state.addPending candidate.coordinate candidate.candidate } :
        DeferredContext))
    (hfirst : FirstExistingHiddenHitAt
      (⟨state, fuel, (), table, observations⟩ : ObservedCleanRunResult Unit) snapshots.length)
    (hselectedAligned : ∀ output ∈ support source,
      SelectedSnapshotObservationAlignedAt table output
        (⟨state, fuel, (), table, observations⟩ : ObservedCleanRunResult Unit)
        snapshots.length)
    (hdoomed : DoomedResolvedContext table (directDeferredContext state)) :
    RelTriple source
      (observedMaterializedBoundary parameter root ftsSecret computation observations state fuel
        table cache)
      (SnapshotObservedFirstStoppedRel table) := by
  apply relTriple_post_mono
    (relTriple_source_observedMaterializedBoundary_selectedStopped parameter root ftsSecret
      computation source snapshots candidate context observations state fuel table cache hsource
      hcompletable hhidden havoid hhit hfirst hselectedAligned hdoomed)
  intro sourceOutput observed hrelation
  exact hrelation.to_firstStopped

set_option maxRecDepth 100000 in
theorem relTriple_any_observedMaterializedBoundary_firstStopped_of_cause
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (source : ProbComp PrivateWitnessSnapshotOutput)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hdoomed : DoomedResolvedContext table (directDeferredContext state))
    (hcause : MissingChainStartHit table (directDeferredContext state) ∨
      FirstExistingHiddenChainStartHit observations) :
    RelTriple source
      (observedMaterializedBoundary parameter root ftsSecret computation observations state fuel
        table cache)
      (SnapshotObservedFirstStoppedRel table) := by
  have hbase := relTriple_true source
    (observedMaterializedBoundary parameter root ftsSecret computation observations state fuel
      table cache)
  have hboth :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hbase
  apply relTriple_post_mono hboth
  intro sourceOutput observed hrelation
  cases observed with
  | none => exact Or.inl rfl
  | some result =>
      right
      right
      right
      refine ⟨result, rfl, ?_, ?_, ?_⟩
      · exact (materializedDoomed_of_mem_observedMaterializedBoundary parameter root ftsSecret
          computation observations state fuel table cache result hdoomed hrelation.2).1
      · exact (materializedDoomed_of_mem_observedMaterializedBoundary parameter root ftsSecret
          computation observations state fuel table cache result hdoomed hrelation.2).2
      · exact observedStoppedCause_of_mem_observedMaterializedBoundary parameter root ftsSecret
          computation observations state fuel table cache result hcause hrelation.2

theorem SnapshotObservedFirstStoppedRel.selected_of_successful_firstRoot
    {table : OtsSecretIndex → HashOutput}
    {source : PrivateWitnessSnapshotOutput}
    {result : ObservedCleanRunResult (α × SplitHashCache)}
    (hrelation : SnapshotObservedFirstStoppedRel table source (some result))
    (finalResult : ObservedCleanRunResult (α × SplitHashCache))
    (hfinish : some finalResult ∈ support
      (finishObservedCleanRunFromTable (some result)))
    (ordinal : Nat)
    (hfirst : FirstExistingHiddenHitAt result ordinal)
    (hroot : ∀ selected : Fin result.observations.length,
      selected.val = ordinal →
        (result.observations.get selected).toProbe.IsLayerRoot) :
    SelectedPrivateSnapshotHitAt source ordinal := by
  rcases hrelation with hnone | haligned | hselected | hstopped
  · simp at hnone
  · obtain ⟨other, aligned, hresult, _hprefix, _hsnapshots, hnoHit, _hstored⟩ := haligned
    have heq : other = result := Option.some.inj hresult.symm
    subst other
    obtain ⟨selected, _hordinal, hhit, _hbefore⟩ := hfirst
    exact (hnoHit (result.observations.get selected) (List.get_mem _ _) hhit).elim
  · obtain ⟨other, selectedOrdinal, hresult, _htable, _hdoomed,
      hselectedFirst, hselected, _haligned⟩ := hselected
    have heq : other = result := Option.some.inj hresult.symm
    subst other
    obtain ⟨left, hleftOrdinal, hleftHit, hleftBefore⟩ := hselectedFirst
    obtain ⟨right, hrightOrdinal, hrightHit, hrightBefore⟩ := hfirst
    have hsame : left = right := firstExistingHiddenHit_selected_unique
      ⟨hleftHit, by
        intro earlier hearlier
        exact hleftBefore earlier (by omega)⟩
      ⟨hrightHit, by
        intro earlier hearlier
        exact hrightBefore earlier (by omega)⟩
    have hordinals : selectedOrdinal = ordinal := by
      have hvals := congrArg Fin.val hsame
      omega
    simpa [hordinals] using hselected
  · obtain ⟨other, hresult, htable, _hdoomed, hcause⟩ := hstopped
    have heq : other = result := Option.some.inj hresult.symm
    subst other
    rcases hcause with hmissing | hchain
    · rw [← htable] at hmissing
      exact (not_missingChainStartHit_of_mem_finishObservedCleanRunFromTable result finalResult
        hfinish hmissing).elim
    · obtain ⟨selected, hselected, _hhit⟩ := hchain.selected_eq hfirst
      exact (not_firstExistingHiddenRootHitAt_of_firstChainStart hchain hfirst selected hselected
        (hroot selected hselected)).elim

theorem SnapshotObservedFirstStoppedRel.selected_or_chain_of_successful_firstNonRoot
    {table : OtsSecretIndex → HashOutput}
    {source : PrivateWitnessSnapshotOutput}
    {result : ObservedCleanRunResult (α × SplitHashCache)}
    (hrelation : SnapshotObservedFirstStoppedRel table source (some result))
    (finalResult : ObservedCleanRunResult (α × SplitHashCache))
    (hfinish : some finalResult ∈ support
      (finishObservedCleanRunFromTable (some result)))
    (ordinal : Nat)
    (hfirst : FirstExistingHiddenHitAt result ordinal) :
    SelectedPrivateSnapshotHitAt source ordinal ∨
      FirstExistingHiddenChainStartHit result.observations := by
  rcases hrelation with hnone | haligned | hselected | hstopped
  · simp at hnone
  · obtain ⟨other, aligned, hresult, _hprefix, _hsnapshots, hnoHit, _hstored⟩ := haligned
    have heq : other = result := Option.some.inj hresult.symm
    subst other
    obtain ⟨selected, _hordinal, hhit, _hbefore⟩ := hfirst
    exact (hnoHit (result.observations.get selected) (List.get_mem _ _) hhit).elim
  · left
    obtain ⟨other, selectedOrdinal, hresult, _htable, _hdoomed,
      hselectedFirst, hselected, _haligned⟩ := hselected
    have heq : other = result := Option.some.inj hresult.symm
    subst other
    obtain ⟨left, hleftOrdinal, hleftHit, hleftBefore⟩ := hselectedFirst
    obtain ⟨right, hrightOrdinal, hrightHit, hrightBefore⟩ := hfirst
    have hsame : left = right := firstExistingHiddenHit_selected_unique
      ⟨hleftHit, by
        intro earlier hearlier
        exact hleftBefore earlier (by omega)⟩
      ⟨hrightHit, by
        intro earlier hearlier
        exact hrightBefore earlier (by omega)⟩
    have hordinals : selectedOrdinal = ordinal := by
      have hvals := congrArg Fin.val hsame
      omega
    simpa [hordinals] using hselected
  · obtain ⟨other, hresult, htable, _hdoomed, hcause⟩ := hstopped
    have heq : other = result := Option.some.inj hresult.symm
    subst other
    rcases hcause with hmissing | hchain
    · rw [← htable] at hmissing
      exact (not_missingChainStartHit_of_mem_finishObservedCleanRunFromTable result finalResult
        hfinish hmissing).elim
    · exact Or.inr hchain

theorem SnapshotObservedFirstStoppedRel.selectedAligned_or_chain_of_successful_firstHit
    {table : OtsSecretIndex → HashOutput}
    {source : PrivateWitnessSnapshotOutput}
    {result : ObservedCleanRunResult (α × SplitHashCache)}
    (hrelation : SnapshotObservedFirstStoppedRel table source (some result))
    (finalResult : ObservedCleanRunResult (α × SplitHashCache))
    (hfinish : some finalResult ∈ support
      (finishObservedCleanRunFromTable (some result)))
    (ordinal : Nat)
    (hfirst : FirstExistingHiddenHitAt result ordinal) :
    (SelectedPrivateSnapshotHitAt source ordinal ∧
      SelectedSnapshotObservationAlignedAt table source result ordinal) ∨
      FirstExistingHiddenChainStartHit result.observations := by
  rcases hrelation with hnone | haligned | hselected | hstopped
  · simp at hnone
  · obtain ⟨other, _aligned, hresult, _hprefix, _hsnapshots, hnoHit, _hstored⟩ :=
      haligned
    have heq : other = result := Option.some.inj hresult.symm
    subst other
    obtain ⟨selected, _hordinal, hhit, _hbefore⟩ := hfirst
    exact (hnoHit (result.observations.get selected) (List.get_mem _ _) hhit).elim
  · left
    obtain ⟨other, selectedOrdinal, hresult, _htable, _hdoomed,
      hselectedFirst, hselectedHit, hselectedAligned⟩ := hselected
    have heq : other = result := Option.some.inj hresult.symm
    subst other
    obtain ⟨left, _hleftOrdinal, hleftHit, hleftBefore⟩ := hselectedFirst
    obtain ⟨right, _hrightOrdinal, hrightHit, hrightBefore⟩ := hfirst
    have hsame : left = right := firstExistingHiddenHit_selected_unique
      ⟨hleftHit, by
        intro earlier hearlier
        exact hleftBefore earlier (by omega)⟩
      ⟨hrightHit, by
        intro earlier hearlier
        exact hrightBefore earlier (by omega)⟩
    have hordinals : selectedOrdinal = ordinal := by
      have hvals := congrArg Fin.val hsame
      omega
    simpa [hordinals] using And.intro hselectedHit hselectedAligned
  · obtain ⟨other, hresult, htable, _hdoomed, hcause⟩ := hstopped
    have heq : other = result := Option.some.inj hresult.symm
    subst other
    rcases hcause with hmissing | hchain
    · rw [← htable] at hmissing
      exact (not_missingChainStartHit_of_mem_finishObservedCleanRunFromTable result finalResult
        hfinish hmissing).elim
    · exact Or.inr hchain
