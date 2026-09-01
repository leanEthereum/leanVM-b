import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootDeferred

/-!
# Layer-root ordinal selection

The hidden ordinal risk is factored at the instant its candidate becomes available. The prefix
records that candidate together with the canonical deferred context, but does not inspect the
private structural output. The final equality test is therefore the only place where the selected
layer root is read.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

structure PrivateOrdinalSelection where
  candidate : Probe
  context : DeferredContext
  candidates : List Probe

noncomputable def selectedPrivateOrdinal?
    (ordinal : Nat) (candidates : List Probe) (context : DeferredContext) :
    Option PrivateOrdinalSelection :=
  if hselected : ordinal < candidates.length then
    some ⟨candidates.get ⟨ordinal, hselected⟩, context, candidates⟩
  else none

noncomputable def finishDirectPrivateOrdinalSelection
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp (Option PrivateOrdinalSelection))
    (candidates : List Probe) : DirectWitnessResult α →
      ProbComp (Option PrivateOrdinalSelection)
  | .stoppedFuel => pure none
  | .stoppedOrdinary => pure none
  | .stoppedPrivate _ => pure none
  | .done result => observe result.context result.remaining result.value candidates

noncomputable def canonicalizeDirectPrivateOrdinalSelection
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp (Option PrivateOrdinalSelection))
    (context : DeferredContext) (fuel : Nat) (value : α) (candidates : List Probe) :
    ProbComp (Option PrivateOrdinalSelection) := by
  classical
  let canonical := canonicalizeMaterializedValues table context
  exact if PrivateStructuralHit canonical then pure none
    else if PublishedValues context.state then
      if DeferredCompletable table canonical then
        observe canonical fuel value candidates
      else pure none
    else pure none

noncomputable def directDetailedBoundaryPrivateOrdinalSelection
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ProbComp (Option PrivateOrdinalSelection) := by
  classical
  exact OracleComp.construct
    (C := fun _ : OracleComp (OracleWorld + SigningSpec) α =>
      List Probe → DeferredContext → Nat → (OtsSecretIndex → HashOutput) →
        SplitHashCache → ProbComp (Option PrivateOrdinalSelection))
    (fun _value candidates context _fuel _table _cache =>
      pure (selectedPrivateOrdinal? ordinal candidates context))
    (fun query _next recursivelyRun candidates context fuel table cache =>
      if hselected : ordinal < candidates.length then
        pure (some ⟨candidates.get ⟨ordinal, hselected⟩, context, candidates⟩)
      else
        match query with
        | .inl (.inl n) =>
            runDirectResolvedWitnessFromTable context fuel table ((splitUniformImpl n).run cache) >>=
              finishDirectPrivateOrdinalSelection
                (canonicalizeDirectPrivateOrdinalSelection table
                  (fun nextContext remaining value laterCandidates =>
                    recursivelyRun value.1 laterCandidates nextContext remaining table value.2))
                candidates
        | .inl (.inr input) =>
            let plan := purePlanProbingHashQuery parameter input context.state
            let nextCandidates := appendPlannedCandidate candidates
              (rootAwarePlannedCandidate? parameter input context.state)
            if hnextSelected : ordinal < nextCandidates.length then
              pure (some ⟨nextCandidates.get ⟨ordinal, hnextSelected⟩, context,
                nextCandidates⟩)
            else
              runDirectResolvedWitnessFromTable context fuel table
                  ((probingHashQueryAfterPlan parameter input plan).run cache) >>=
                finishDirectPrivateOrdinalSelection
                  (canonicalizeDirectPrivateOrdinalSelection table
                    (fun nextContext remaining value laterCandidates =>
                      recursivelyRun value.1 laterCandidates nextContext remaining table value.2))
                  nextCandidates
        | .inr message =>
            runDirectResolvedWitnessFromTable context fuel table
                ((maskedSign parameter root ftsSecret message).run cache) >>=
              finishDirectPrivateOrdinalSelection
                (canonicalizeDirectPrivateOrdinalSelection table
                  (fun nextContext remaining value laterCandidates =>
                    recursivelyRun value.1 laterCandidates nextContext remaining table value.2))
                candidates)
    computation candidates context fuel table cache

noncomputable def privateOrdinalSelectionFire :
    Option PrivateOrdinalSelection → ProbComp Bool
  | none => pure false
  | some selection => hiddenPrivateCandidateFire selection.candidate selection.context

theorem directDetailedBoundaryPrivateOrdinalSelection_eq_selected
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hselected : ordinal < candidates.length) :
    directDetailedBoundaryPrivateOrdinalSelection ordinal parameter root ftsSecret computation
        candidates context fuel table cache =
      pure (some ⟨candidates.get ⟨ordinal, hselected⟩, context, candidates⟩) := by
  induction computation using OracleComp.inductionOn generalizing candidates context fuel cache with
  | pure value =>
      rw [directDetailedBoundaryPrivateOrdinalSelection, OracleComp.construct_pure]
      simp [selectedPrivateOrdinal?, hselected]
  | query_bind query next ih =>
      rw [directDetailedBoundaryPrivateOrdinalSelection, OracleComp.construct_query_bind]
      simp only [hselected, ↓reduceDIte]

def PrivateOrdinalSelectionExtends
    (initial : List Probe) : Option PrivateOrdinalSelection → Prop
  | none => True
  | some selection => initial.IsPrefix selection.candidates

theorem PrivateOrdinalSelectionExtends.mono
    {first second : List Probe} {selection : Option PrivateOrdinalSelection}
    (hprefix : first.IsPrefix second)
    (hextends : PrivateOrdinalSelectionExtends second selection) :
    PrivateOrdinalSelectionExtends first selection := by
  cases selection with
  | none => trivial
  | some selection => exact hprefix.trans hextends

theorem privateOrdinalSelectionExtends_selectedPrivateOrdinal
    (ordinal : Nat) (candidates : List Probe) (context : DeferredContext) :
    PrivateOrdinalSelectionExtends candidates
      (selectedPrivateOrdinal? ordinal candidates context) := by
  unfold selectedPrivateOrdinal?
  split <;> simp [PrivateOrdinalSelectionExtends]

theorem privateOrdinalSelectionExtends_of_mem_finish
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp (Option PrivateOrdinalSelection))
    (candidates : List Probe) (result : DirectWitnessResult α)
    (hobserve : ∀ resolved output,
      result = .done resolved →
      output ∈ support
        (observe resolved.context resolved.remaining resolved.value candidates) →
      PrivateOrdinalSelectionExtends candidates output)
    (output : Option PrivateOrdinalSelection)
    (houtput : output ∈ support
      (finishDirectPrivateOrdinalSelection observe candidates result)) :
    PrivateOrdinalSelectionExtends candidates output := by
  cases result with
  | stoppedFuel => simp [finishDirectPrivateOrdinalSelection] at houtput; subst output; trivial
  | stoppedOrdinary => simp [finishDirectPrivateOrdinalSelection] at houtput; subst output; trivial
  | stoppedPrivate witness =>
      simp [finishDirectPrivateOrdinalSelection] at houtput
      subst output
      trivial
  | done resolved =>
      exact hobserve resolved output rfl houtput

theorem privateOrdinalSelectionExtends_of_mem_canonicalize
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp (Option PrivateOrdinalSelection))
    (context : DeferredContext) (fuel : Nat) (value : α)
    (candidates : List Probe)
    (hobserve : ∀ nextContext output,
      output ∈ support (observe nextContext fuel value candidates) →
      PrivateOrdinalSelectionExtends candidates output)
    (output : Option PrivateOrdinalSelection)
    (houtput : output ∈ support
      (canonicalizeDirectPrivateOrdinalSelection table observe context fuel value candidates)) :
    PrivateOrdinalSelectionExtends candidates output := by
  classical
  unfold canonicalizeDirectPrivateOrdinalSelection at houtput
  let canonical := canonicalizeMaterializedValues table context
  by_cases hhit : PrivateStructuralHit canonical
  · simp [canonical, hhit] at houtput
    subst output
    trivial
  · simp only [canonical, hhit, ↓reduceIte] at houtput
    by_cases hpublished : PublishedValues context.state
    · simp only [hpublished, ↓reduceIte] at houtput
      by_cases hcompletable : DeferredCompletable table canonical
      · change DeferredCompletable table (canonicalizeMaterializedValues table context)
          at hcompletable
        rw [if_pos hcompletable] at houtput
        exact hobserve canonical output houtput
      · change ¬DeferredCompletable table (canonicalizeMaterializedValues table context)
          at hcompletable
        rw [if_neg hcompletable] at houtput
        simp only [support_pure, Set.mem_singleton_iff] at houtput
        subst output
        trivial
    · simp [hpublished] at houtput
      subst output
      trivial

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem privateOrdinalSelectionExtends_of_mem_direct
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (output : Option PrivateOrdinalSelection)
    (houtput : output ∈ support
      (directDetailedBoundaryPrivateOrdinalSelection ordinal parameter root ftsSecret computation
        candidates context fuel table cache)) :
    PrivateOrdinalSelectionExtends candidates output := by
  induction computation using OracleComp.inductionOn generalizing
      candidates context fuel cache output with
  | pure value =>
      rw [directDetailedBoundaryPrivateOrdinalSelection, OracleComp.construct_pure] at houtput
      simp only [support_pure, Set.mem_singleton_iff] at houtput
      subst output
      exact privateOrdinalSelectionExtends_selectedPrivateOrdinal ordinal candidates context
  | query_bind query next ih =>
      rw [directDetailedBoundaryPrivateOrdinalSelection,
        OracleComp.construct_query_bind] at houtput
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte, support_pure, Set.mem_singleton_iff] at houtput
        subst output
        simp [PrivateOrdinalSelectionExtends]
      · simp only [hselected, ↓reduceDIte] at houtput
        cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                rw [mem_support_bind_iff] at houtput
                obtain ⟨result, hresult, hfinish⟩ := houtput
                apply privateOrdinalSelectionExtends_of_mem_finish _ candidates result
                  (output := output) (houtput := hfinish)
                intro resolved nextOutput heq hnextOutput
                subst result
                apply privateOrdinalSelectionExtends_of_mem_canonicalize table _
                  resolved.context resolved.remaining resolved.value candidates
                  (output := nextOutput) (houtput := hnextOutput)
                intro nextContext finalOutput hfinalOutput
                exact ih resolved.value.1 candidates nextContext resolved.remaining
                  resolved.value.2 finalOutput hfinalOutput
            | inr input =>
                let publicContext := context
                let plan := purePlanProbingHashQuery parameter input context.state
                let nextCandidates := appendPlannedCandidate candidates
                  (rootAwarePlannedCandidate? parameter input context.state)
                by_cases hnextSelected : ordinal < nextCandidates.length
                · have hactual : ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwarePlannedCandidate? parameter input context.state)).length := by
                    simpa [nextCandidates] using hnextSelected
                  simp only [hactual, ↓reduceDIte, support_pure,
                    Set.mem_singleton_iff] at houtput
                  subst output
                  have hprefix : candidates.IsPrefix nextCandidates := by
                    unfold nextCandidates appendPlannedCandidate
                    cases rootAwarePlannedCandidate? parameter input context.state <;> simp
                  exact hprefix
                · have hactual : ¬ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwarePlannedCandidate? parameter input context.state)).length := by
                    simpa [nextCandidates] using hnextSelected
                  simp only [hactual, ↓reduceDIte] at houtput
                  rw [mem_support_bind_iff] at houtput
                  obtain ⟨result, hresult, hfinish⟩ := houtput
                  have hprefix : candidates.IsPrefix nextCandidates := by
                    unfold nextCandidates appendPlannedCandidate
                    cases rootAwarePlannedCandidate? parameter input context.state <;> simp
                  apply PrivateOrdinalSelectionExtends.mono hprefix
                  apply privateOrdinalSelectionExtends_of_mem_finish _ nextCandidates result
                    (output := output) (houtput := hfinish)
                  intro resolved nextOutput heq hnextOutput
                  subst result
                  apply privateOrdinalSelectionExtends_of_mem_canonicalize table _
                    resolved.context resolved.remaining resolved.value nextCandidates
                    (output := nextOutput) (houtput := hnextOutput)
                  intro nextContext finalOutput hfinalOutput
                  exact ih resolved.value.1 nextCandidates nextContext resolved.remaining
                    resolved.value.2 finalOutput hfinalOutput
        | inr message =>
            rw [mem_support_bind_iff] at houtput
            obtain ⟨result, hresult, hfinish⟩ := houtput
            apply privateOrdinalSelectionExtends_of_mem_finish _ candidates result
              (output := output) (houtput := hfinish)
            intro resolved nextOutput heq hnextOutput
            subst result
            apply privateOrdinalSelectionExtends_of_mem_canonicalize table _
              resolved.context resolved.remaining resolved.value candidates
              (output := nextOutput) (houtput := hnextOutput)
            intro nextContext finalOutput hfinalOutput
            exact ih resolved.value.1 candidates nextContext resolved.remaining
              resolved.value.2 finalOutput hfinalOutput

def PrivateOrdinalSelectionPendingCovered
    (ordinal : Nat) : Option PrivateOrdinalSelection → Prop
  | none => True
  | some selection =>
      PendingCoveredBy (selection.candidates.take ordinal) selection.context

theorem privateOrdinalSelectionPendingCovered_of_mem_finish
    (ordinal : Nat)
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp (Option PrivateOrdinalSelection))
    (candidates : List Probe) (result : DirectWitnessResult α)
    (hobserve : ∀ resolved output,
      result = .done resolved →
      output ∈ support
        (observe resolved.context resolved.remaining resolved.value candidates) →
      PrivateOrdinalSelectionPendingCovered ordinal output)
    (output : Option PrivateOrdinalSelection)
    (houtput : output ∈ support
      (finishDirectPrivateOrdinalSelection observe candidates result)) :
    PrivateOrdinalSelectionPendingCovered ordinal output := by
  cases result with
  | stoppedFuel => simp [finishDirectPrivateOrdinalSelection] at houtput; subst output; trivial
  | stoppedOrdinary => simp [finishDirectPrivateOrdinalSelection] at houtput; subst output; trivial
  | stoppedPrivate witness =>
      simp [finishDirectPrivateOrdinalSelection] at houtput
      subst output
      trivial
  | done resolved => exact hobserve resolved output rfl houtput

theorem privateOrdinalSelectionPendingCovered_of_mem_canonicalize
    (ordinal : Nat) (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp (Option PrivateOrdinalSelection))
    (context : DeferredContext) (fuel : Nat) (value : α)
    (candidates : List Probe)
    (hobserve : ∀ nextContext output,
      PendingCoveredBy candidates nextContext →
      output ∈ support (observe nextContext fuel value candidates) →
      PrivateOrdinalSelectionPendingCovered ordinal output)
    (hcovered : PendingCoveredBy candidates context)
    (output : Option PrivateOrdinalSelection)
    (houtput : output ∈ support
      (canonicalizeDirectPrivateOrdinalSelection table observe context fuel value candidates)) :
    PrivateOrdinalSelectionPendingCovered ordinal output := by
  classical
  unfold canonicalizeDirectPrivateOrdinalSelection at houtput
  let canonical := canonicalizeMaterializedValues table context
  by_cases hhit : PrivateStructuralHit canonical
  · simp [canonical, hhit] at houtput
    subst output
    trivial
  · simp only [canonical, hhit, ↓reduceIte] at houtput
    by_cases hpublished : PublishedValues context.state
    · simp only [hpublished, ↓reduceIte] at houtput
      by_cases hcompletable : DeferredCompletable table canonical
      · rw [if_pos hcompletable] at houtput
        apply hobserve canonical output
        · exact (pendingCoveredBy_canonicalize_iff table candidates context).2 hcovered
        · exact houtput
      · rw [if_neg hcompletable] at houtput
        simp only [support_pure, Set.mem_singleton_iff] at houtput
        subst output
        trivial
    · simp [hpublished] at houtput
      subst output
      trivial

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem privateOrdinalSelectionPendingCovered_of_mem_direct
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hcovered : PendingCoveredBy candidates context)
    (hlength : candidates.length ≤ ordinal)
    (output : Option PrivateOrdinalSelection)
    (houtput : output ∈ support
      (directDetailedBoundaryPrivateOrdinalSelection ordinal parameter root ftsSecret computation
        candidates context fuel table cache)) :
    PrivateOrdinalSelectionPendingCovered ordinal output := by
  induction computation using OracleComp.inductionOn generalizing
      candidates context fuel cache output with
  | pure value =>
      rw [directDetailedBoundaryPrivateOrdinalSelection, OracleComp.construct_pure] at houtput
      have hnotSelected : ¬ordinal < candidates.length := by omega
      simp [selectedPrivateOrdinal?, hnotSelected] at houtput
      subst output
      trivial
  | query_bind query next ih =>
      rw [directDetailedBoundaryPrivateOrdinalSelection,
        OracleComp.construct_query_bind] at houtput
      have hnotSelected : ¬ordinal < candidates.length := by omega
      simp only [hnotSelected, ↓reduceDIte] at houtput
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              rw [mem_support_bind_iff] at houtput
              obtain ⟨result, hresult, hfinish⟩ := houtput
              apply privateOrdinalSelectionPendingCovered_of_mem_finish ordinal _ candidates result
                (output := output) (houtput := hfinish)
              intro resolved nextOutput heq hnextOutput
              subst result
              have hdetailed : DirectDetailedResult.done resolved ∈ support
                  (runDirectResolvedDetailedFromTable context fuel table
                    ((splitUniformImpl n).run cache)) := by
                rw [← map_erase_runDirectResolvedWitnessFromTable
                  ((splitUniformImpl n).run cache) context fuel table, support_map]
                exact ⟨DirectWitnessResult.done resolved, hresult, rfl⟩
              have hprobeBound : ((splitUniformImpl n).run cache).IsQueryBoundP
                  (IsUncoveredProbe candidates) 0 :=
                OracleComp.IsQueryBoundP.of_imp (isUncoveredProbe_imp_isProbe candidates)
                  (splitUniformImpl_probeFree n cache)
              have hnextCovered := pendingCoveredBy_of_done_runDirectResolvedDetailedFromTable
                candidates ((splitUniformImpl n).run cache) context fuel table resolved hcovered
                  hprobeBound hdetailed
              apply privateOrdinalSelectionPendingCovered_of_mem_canonicalize ordinal table _
                resolved.context resolved.remaining resolved.value candidates _ hnextCovered
                nextOutput hnextOutput
              intro nextContext finalOutput hfinalCovered hfinalOutput
              exact ih resolved.value.1 candidates nextContext resolved.remaining resolved.value.2
                hfinalCovered hlength finalOutput hfinalOutput
          | inr input =>
              let plan := purePlanProbingHashQuery parameter input context.state
              let candidate? := rootAwarePlannedCandidate? parameter input context.state
              let nextCandidates := appendPlannedCandidate candidates candidate?
              by_cases hnextSelected : ordinal < nextCandidates.length
              · have hactual : ordinal <
                    (appendPlannedCandidate candidates
                      (rootAwarePlannedCandidate? parameter input context.state)).length := by
                  simpa [candidate?, nextCandidates] using hnextSelected
                simp only [hactual, ↓reduceDIte, support_pure,
                  Set.mem_singleton_iff] at houtput
                subst output
                change PendingCoveredBy (nextCandidates.take ordinal) context
                cases hcandidate : candidate? with
                | none =>
                    have hnextEq : nextCandidates = candidates := by
                      simp [nextCandidates, appendPlannedCandidate, hcandidate]
                    exfalso
                    rw [hnextEq] at hnextSelected
                    omega
                | some candidate =>
                    have hlengthEq : candidates.length = ordinal := by
                      have hnextLength : nextCandidates.length = candidates.length + 1 := by
                        simp [nextCandidates, appendPlannedCandidate, hcandidate]
                      omega
                    have htake : nextCandidates.take ordinal = candidates := by
                      simp [nextCandidates, appendPlannedCandidate, hcandidate, hlengthEq]
                    rwa [htake]
              · have hactual : ¬ordinal <
                    (appendPlannedCandidate candidates
                      (rootAwarePlannedCandidate? parameter input context.state)).length := by
                  simpa [candidate?, nextCandidates] using hnextSelected
                simp only [hactual, ↓reduceDIte] at houtput
                rw [mem_support_bind_iff] at houtput
                obtain ⟨result, hresult, hfinish⟩ := houtput
                have hnextLength : nextCandidates.length ≤ ordinal := by omega
                have hnextCoveredAtStart : PendingCoveredBy nextCandidates context := by
                  apply hcovered.mono_candidates
                  unfold nextCandidates candidate? appendPlannedCandidate
                  cases rootAwarePlannedCandidate? parameter input context.state <;> simp
                apply privateOrdinalSelectionPendingCovered_of_mem_finish ordinal _ nextCandidates
                  result (output := output) (houtput := hfinish)
                intro resolved nextOutput heq hnextOutput
                subst result
                have hplanMem : ∀ candidate, plan.candidate? = some candidate →
                    candidate ∈ nextCandidates := by
                  intro candidate hcandidate
                  have hrecorded := rootAwarePlannedCandidate?_eq_of_plan_some hcandidate
                  simp [nextCandidates, candidate?, appendPlannedCandidate, hrecorded]
                have hprobeBound := probingHashQueryAfterPlan_probeBound parameter input plan
                  nextCandidates hplanMem cache
                have hdetailed : DirectDetailedResult.done resolved ∈ support
                    (runDirectResolvedDetailedFromTable context fuel table
                      ((probingHashQueryAfterPlan parameter input plan).run cache)) := by
                  rw [← map_erase_runDirectResolvedWitnessFromTable
                    ((probingHashQueryAfterPlan parameter input plan).run cache) context fuel table,
                    support_map]
                  exact ⟨DirectWitnessResult.done resolved, hresult, rfl⟩
                have hnextCovered := pendingCoveredBy_of_done_runDirectResolvedDetailedFromTable
                  nextCandidates ((probingHashQueryAfterPlan parameter input plan).run cache)
                    context fuel table resolved hnextCoveredAtStart hprobeBound hdetailed
                apply privateOrdinalSelectionPendingCovered_of_mem_canonicalize ordinal table _
                  resolved.context resolved.remaining resolved.value nextCandidates _ hnextCovered
                  nextOutput hnextOutput
                intro nextContext finalOutput hfinalCovered hfinalOutput
                exact ih resolved.value.1 nextCandidates nextContext resolved.remaining
                  resolved.value.2 hfinalCovered hnextLength finalOutput hfinalOutput
      | inr message =>
          rw [mem_support_bind_iff] at houtput
          obtain ⟨result, hresult, hfinish⟩ := houtput
          apply privateOrdinalSelectionPendingCovered_of_mem_finish ordinal _ candidates result
            (output := output) (houtput := hfinish)
          intro resolved nextOutput heq hnextOutput
          subst result
          have hprobeBound : ((maskedSign parameter root ftsSecret message).run cache).IsQueryBoundP
              (IsUncoveredProbe candidates) 0 :=
            OracleComp.IsQueryBoundP.of_imp (isUncoveredProbe_imp_isProbe candidates)
              (maskedSign_probeFree parameter root ftsSecret message cache)
          have hdetailed : DirectDetailedResult.done resolved ∈ support
              (runDirectResolvedDetailedFromTable context fuel table
                ((maskedSign parameter root ftsSecret message).run cache)) := by
            rw [← map_erase_runDirectResolvedWitnessFromTable
              ((maskedSign parameter root ftsSecret message).run cache) context fuel table,
              support_map]
            exact ⟨DirectWitnessResult.done resolved, hresult, rfl⟩
          have hnextCovered := pendingCoveredBy_of_done_runDirectResolvedDetailedFromTable
            candidates ((maskedSign parameter root ftsSecret message).run cache) context fuel table
              resolved hcovered hprobeBound hdetailed
          apply privateOrdinalSelectionPendingCovered_of_mem_canonicalize ordinal table _
            resolved.context resolved.remaining resolved.value candidates _ hnextCovered
            nextOutput hnextOutput
          intro nextContext finalOutput hfinalCovered hfinalOutput
          exact ih resolved.value.1 candidates nextContext resolved.remaining resolved.value.2
            hfinalCovered hlength finalOutput hfinalOutput

theorem finishDirectPrivateOrdinalSelection_bind_fire
    (selectionObserve : DeferredContext → Nat → α → List Probe →
      ProbComp (Option PrivateOrdinalSelection))
    (riskObserve : DeferredContext → Nat → α → List Probe → ProbComp Bool)
    (candidates : List Probe) (result : DirectWitnessResult α)
    (hobserve : ∀ context fuel value laterCandidates,
      selectionObserve context fuel value laterCandidates >>= privateOrdinalSelectionFire =
        riskObserve context fuel value laterCandidates) :
    finishDirectPrivateOrdinalSelection selectionObserve candidates result >>=
        privateOrdinalSelectionFire =
      finishDirectWitnessOrdinalRisk riskObserve candidates result := by
  cases result with
  | stoppedFuel => simp [finishDirectPrivateOrdinalSelection,
      finishDirectWitnessOrdinalRisk, privateOrdinalSelectionFire]
  | stoppedOrdinary => simp [finishDirectPrivateOrdinalSelection,
      finishDirectWitnessOrdinalRisk, privateOrdinalSelectionFire]
  | stoppedPrivate witness => simp [finishDirectPrivateOrdinalSelection,
      finishDirectWitnessOrdinalRisk, privateOrdinalSelectionFire]
  | done result =>
      simpa [finishDirectPrivateOrdinalSelection, finishDirectWitnessOrdinalRisk] using
        hobserve result.context result.remaining result.value candidates

theorem canonicalizeDirectPrivateOrdinalSelection_bind_fire
    (table : OtsSecretIndex → HashOutput)
    (selectionObserve : DeferredContext → Nat → α → List Probe →
      ProbComp (Option PrivateOrdinalSelection))
    (riskObserve : DeferredContext → Nat → α → List Probe → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (value : α) (candidates : List Probe)
    (hobserve : ∀ nextContext remaining nextValue laterCandidates,
      selectionObserve nextContext remaining nextValue laterCandidates >>=
          privateOrdinalSelectionFire =
        riskObserve nextContext remaining nextValue laterCandidates) :
    canonicalizeDirectPrivateOrdinalSelection table selectionObserve context fuel value
          candidates >>=
        privateOrdinalSelectionFire =
      canonicalizeDirectWitnessOrdinalRisk table riskObserve context fuel value candidates := by
  classical
  unfold canonicalizeDirectPrivateOrdinalSelection canonicalizeDirectWitnessOrdinalRisk
  let canonical := canonicalizeMaterializedValues table context
  by_cases hhit : PrivateStructuralHit canonical
  · simp [canonical, hhit, privateOrdinalSelectionFire]
  · simp only [canonical, hhit, ↓reduceIte]
    by_cases hpublished : PublishedValues context.state
    · simp only [hpublished, ↓reduceIte]
      by_cases hcompletable : DeferredCompletable table canonical
      · simpa [canonical, hcompletable] using
          (hobserve canonical fuel value candidates)
      · simp [canonical, hcompletable, privateOrdinalSelectionFire]
    · simp [hpublished, privateOrdinalSelectionFire]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem directDetailedBoundaryPrivateOrdinalHiddenRisk_eq_selection_bind_fire
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    directDetailedBoundaryPrivateOrdinalSelection ordinal parameter root ftsSecret computation
          candidates context fuel table cache >>=
        privateOrdinalSelectionFire =
      directDetailedBoundaryPrivateOrdinalHiddenRisk ordinal parameter root ftsSecret computation
        candidates context fuel table cache := by
  induction computation using OracleComp.inductionOn generalizing
      candidates context fuel cache with
  | pure value =>
      rw [directDetailedBoundaryPrivateOrdinalSelection, OracleComp.construct_pure,
        directDetailedBoundaryPrivateOrdinalHiddenRisk, OracleComp.construct_pure]
      by_cases hselected : ordinal < candidates.length
      · simp [selectedPrivateOrdinal?, hselected, privateOrdinalSelectionFire]
      · simp [selectedPrivateOrdinal?, hselected, privateOrdinalSelectionFire]
  | query_bind query next ih =>
      rw [directDetailedBoundaryPrivateOrdinalSelection, OracleComp.construct_query_bind,
        directDetailedBoundaryPrivateOrdinalHiddenRisk, OracleComp.construct_query_bind]
      by_cases hselected : ordinal < candidates.length
      · simp [hselected, privateOrdinalSelectionFire]
      · simp only [hselected, ↓reduceDIte]
        cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                rw [bind_assoc]
                apply bind_congr
                intro result
                apply finishDirectPrivateOrdinalSelection_bind_fire
                intro nextContext remaining value laterCandidates
                apply canonicalizeDirectPrivateOrdinalSelection_bind_fire
                intro finalContext finalRemaining finalValue finalCandidates
                exact ih finalValue.1 finalCandidates finalContext finalRemaining finalValue.2
            | inr input =>
                let plan := purePlanProbingHashQuery parameter input context.state
                let nextCandidates := appendPlannedCandidate candidates
                  (rootAwarePlannedCandidate? parameter input context.state)
                by_cases hnextSelected : ordinal < nextCandidates.length
                · have hactual : ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwarePlannedCandidate? parameter input context.state)).length := by
                    simpa [nextCandidates] using hnextSelected
                  simp [hactual, privateOrdinalSelectionFire]
                · have hactual : ¬ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwarePlannedCandidate? parameter input context.state)).length := by
                    simpa [nextCandidates] using hnextSelected
                  simp only [hactual, ↓reduceDIte]
                  rw [bind_assoc]
                  apply bind_congr
                  intro result
                  apply finishDirectPrivateOrdinalSelection_bind_fire
                  intro nextContext remaining value laterCandidates
                  apply canonicalizeDirectPrivateOrdinalSelection_bind_fire
                  intro finalContext finalRemaining finalValue finalCandidates
                  exact ih finalValue.1 finalCandidates finalContext finalRemaining finalValue.2
        | inr message =>
            rw [bind_assoc]
            apply bind_congr
            intro result
            apply finishDirectPrivateOrdinalSelection_bind_fire
            intro nextContext remaining value laterCandidates
            apply canonicalizeDirectPrivateOrdinalSelection_bind_fire
            intro finalContext finalRemaining finalValue finalCandidates
            exact ih finalValue.1 finalCandidates finalContext finalRemaining finalValue.2

end SphincsSecurity.Concrete.OtsProbeSimulation
