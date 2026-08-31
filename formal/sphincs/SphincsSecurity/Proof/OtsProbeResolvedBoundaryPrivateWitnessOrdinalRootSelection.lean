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

noncomputable def selectedPrivateOrdinal?
    (ordinal : Nat) (candidates : List Probe) (context : DeferredContext) :
    Option PrivateOrdinalSelection :=
  if hselected : ordinal < candidates.length then
    some ⟨candidates.get ⟨ordinal, hselected⟩, context⟩
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
        pure (some ⟨candidates.get ⟨ordinal, hselected⟩, context⟩)
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
              pure (some ⟨nextCandidates.get ⟨ordinal, hnextSelected⟩, context⟩)
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
      pure (some ⟨candidates.get ⟨ordinal, hselected⟩, context⟩) := by
  induction computation using OracleComp.inductionOn generalizing candidates context fuel cache with
  | pure value =>
      rw [directDetailedBoundaryPrivateOrdinalSelection, OracleComp.construct_pure]
      simp [selectedPrivateOrdinal?, hselected]
  | query_bind query next ih =>
      rw [directDetailedBoundaryPrivateOrdinalSelection, OracleComp.construct_query_bind]
      simp only [hselected, ↓reduceDIte]

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
