import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalPrefix

/-!
# Ordinal prefix risk

The prefix-risk computation follows the normalized execution until one fixed candidate ordinal is
selected. It then stops before executing that hash-query suffix and tests the selected candidate
against the current deferred structural output. Earlier stops and a computation that ends before
the ordinal is selected contribute zero.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable

noncomputable def finishDirectWitnessOrdinalRisk
    (observe : DeferredContext → Nat → α → List Probe → ProbComp Bool)
    (candidates : List Probe) : DirectWitnessResult α → ProbComp Bool
  | .stoppedFuel => pure false
  | .stoppedOrdinary => pure false
  | .stoppedPrivate _ => pure false
  | .done result => observe result.context result.remaining result.value candidates

noncomputable def canonicalizeDirectWitnessOrdinalRisk
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List Probe → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (value : α) (candidates : List Probe) :
    ProbComp Bool := by
  classical
  let canonical := canonicalizeMaterializedValues table context
  exact if PrivateStructuralHit canonical then
    pure false
  else if PublishedValues context.state then
    if DeferredCompletable table canonical then
      observe canonical fuel value candidates
    else
      pure false
  else
    pure false

noncomputable def directDetailedBoundaryPrivateOrdinalRisk
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) : ProbComp Bool := by
  classical
  exact OracleComp.construct
    (C := fun _ : OracleComp (OracleWorld + SigningSpec) α =>
      List Probe → DeferredContext → Nat → (OtsSecretIndex → HashOutput) →
        SplitHashCache → ProbComp Bool)
    (fun _value candidates context _fuel _table _cache =>
      if hselected : ordinal < candidates.length then
        privateCandidateFire (candidates.get ⟨ordinal, hselected⟩) context
      else
        pure false)
    (fun query _next recursivelyRun candidates context fuel table cache =>
      if hselected : ordinal < candidates.length then
        privateCandidateFire (candidates.get ⟨ordinal, hselected⟩) context
      else
        match query with
        | .inl (.inl n) =>
            runDirectResolvedWitnessFromTable context fuel table ((splitUniformImpl n).run cache) >>=
              finishDirectWitnessOrdinalRisk
                (canonicalizeDirectWitnessOrdinalRisk table
                  (fun nextContext remaining value laterCandidates =>
                    recursivelyRun value.1 laterCandidates nextContext remaining table value.2))
                candidates
        | .inl (.inr input) =>
            let plan := purePlanProbingHashQuery parameter input context.state
            let nextCandidates := appendPlannedCandidate candidates plan.candidate?
            if hnextSelected : ordinal < nextCandidates.length then
              privateCandidateFire (nextCandidates.get ⟨ordinal, hnextSelected⟩) context
            else
              runDirectResolvedWitnessFromTable context fuel table
                  ((probingHashQueryAfterPlan parameter input plan).run cache) >>=
                finishDirectWitnessOrdinalRisk
                  (canonicalizeDirectWitnessOrdinalRisk table
                    (fun nextContext remaining value laterCandidates =>
                      recursivelyRun value.1 laterCandidates nextContext remaining table value.2))
                  nextCandidates
        | .inr message =>
            runDirectResolvedWitnessFromTable context fuel table
                ((maskedSign parameter root ftsSecret message).run cache) >>=
              finishDirectWitnessOrdinalRisk
                (canonicalizeDirectWitnessOrdinalRisk table
                  (fun nextContext remaining value laterCandidates =>
                    recursivelyRun value.1 laterCandidates nextContext remaining table value.2))
                candidates)
    computation candidates context fuel table cache

noncomputable def granularDetailedRetainedRestPrivateOrdinalRisk
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (ordinal : Nat) (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (candidates : List Probe) : ProbComp Bool :=
  directDetailedBoundaryPrivateOrdinalRisk ordinal parameter value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
    candidates context fuel table value.2

theorem directDetailedBoundaryPrivateOrdinalRisk_eq_fire_of_selected
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hselected : ordinal < candidates.length) :
    directDetailedBoundaryPrivateOrdinalRisk ordinal parameter root ftsSecret computation
        candidates context fuel table cache =
      privateCandidateFire (candidates.get ⟨ordinal, hselected⟩) context := by
  induction computation using OracleComp.inductionOn generalizing candidates context fuel cache with
  | pure value =>
      rw [directDetailedBoundaryPrivateOrdinalRisk, OracleComp.construct_pure]
      simp only [hselected, ↓reduceDIte]
  | query_bind query next ih =>
      rw [directDetailedBoundaryPrivateOrdinalRisk, OracleComp.construct_query_bind]
      simp only [hselected, ↓reduceDIte]

theorem directDetailedBoundaryPrivateOrdinalRisk_pure_eq_false_of_not_selected
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (value : α) (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hnotSelected : ¬ordinal < candidates.length) :
    directDetailedBoundaryPrivateOrdinalRisk ordinal parameter root ftsSecret
        (pure value : OracleComp (OracleWorld + SigningSpec) α)
        candidates context fuel table cache = pure false := by
  rw [directDetailedBoundaryPrivateOrdinalRisk, OracleComp.construct_pure]
  simp only [hnotSelected, ↓reduceDIte]

theorem not_witnessUsesOrdinal_of_not_lt_length
    (ordinal : Nat) (output : PrivateWitnessPlanOutput)
    (hnot : ¬ordinal < output.2.length) :
    ¬WitnessUsesOrdinal ordinal output := by
  rintro ⟨witness, sourceOrdinal, _hwitness, hordinal, _hsource⟩
  exact hnot (hordinal ▸ sourceOrdinal.isLt)

theorem probEvent_finishDirectWitnessPlanUsesOrdinal_le_risk
    (ordinal : Nat)
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (riskObserve : DeferredContext → Nat → α → List Probe → ProbComp Bool)
    (candidates : List Probe) (result : DirectWitnessResult α)
    (hnotSelected : ¬ordinal < candidates.length)
    (hcontinuation : ∀ resolved : ResolvedRunResult α,
      result = .done resolved →
      Pr[WitnessUsesOrdinal ordinal |
          observe resolved.context resolved.remaining resolved.value candidates] ≤
        Pr[fun hit : Bool => hit = true |
          riskObserve resolved.context resolved.remaining resolved.value candidates]) :
    Pr[WitnessUsesOrdinal ordinal |
        finishDirectWitnessPlanObserve observe candidates result] ≤
      Pr[fun hit : Bool => hit = true |
        finishDirectWitnessOrdinalRisk riskObserve candidates result] := by
  cases result with
  | stoppedFuel =>
    simp [finishDirectWitnessPlanObserve, finishDirectWitnessOrdinalRisk,
        WitnessUsesOrdinal]
  | stoppedOrdinary =>
    simp [finishDirectWitnessPlanObserve, finishDirectWitnessOrdinalRisk,
        WitnessUsesOrdinal]
  | stoppedPrivate witness =>
      have hnone : ¬WitnessUsesOrdinal ordinal (some witness, candidates) :=
        not_witnessUsesOrdinal_of_not_lt_length ordinal (some witness, candidates) hnotSelected
      simp [finishDirectWitnessPlanObserve, finishDirectWitnessOrdinalRisk, hnone]
  | done resolved =>
      simpa [finishDirectWitnessPlanObserve, finishDirectWitnessOrdinalRisk] using
        hcontinuation resolved rfl

theorem probEvent_runDirectWitnessPlanUsesOrdinal_le_risk
    (ordinal : Nat)
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (riskObserve : DeferredContext → Nat → α → List Probe → ProbComp Bool)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hnotSelected : ¬ordinal < candidates.length)
    (hcontinuation : ∀ result : ResolvedRunResult α,
      DirectWitnessResult.done result ∈ support
        (runDirectResolvedWitnessFromTable context fuel table computation) →
      Pr[WitnessUsesOrdinal ordinal |
          observe result.context result.remaining result.value candidates] ≤
        Pr[fun hit : Bool => hit = true |
          riskObserve result.context result.remaining result.value candidates]) :
    Pr[WitnessUsesOrdinal ordinal |
        runDirectWitnessPlanObserve observe candidates context fuel table computation] ≤
      Pr[fun hit : Bool => hit = true |
        runDirectResolvedWitnessFromTable context fuel table computation >>=
          finishDirectWitnessOrdinalRisk riskObserve candidates] := by
  unfold runDirectWitnessPlanObserve
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hresult : result ∈ support
      (runDirectResolvedWitnessFromTable context fuel table computation)
  · exact mul_le_mul' le_rfl
      (probEvent_finishDirectWitnessPlanUsesOrdinal_le_risk ordinal observe riskObserve candidates
        result hnotSelected (by
          intro resolved heq
          subst result
          exact hcontinuation resolved hresult))
  · rw [probOutput_eq_zero_of_not_mem_support hresult]
    simp

theorem probEvent_canonicalizeWitnessPlanUsesOrdinal_le_risk
    (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (riskObserve : DeferredContext → Nat → α → List Probe → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (value : α) (candidates : List Probe)
    (hnotSelected : ¬ordinal < candidates.length)
    (hcontinuation :
      let canonical := canonicalizeMaterializedValues table context
      ¬PrivateStructuralHit canonical → PublishedValues context.state →
      DeferredCompletable table canonical →
      Pr[WitnessUsesOrdinal ordinal | observe canonical fuel value candidates] ≤
        Pr[fun hit : Bool => hit = true |
          riskObserve canonical fuel value candidates]) :
    Pr[WitnessUsesOrdinal ordinal |
        canonicalizeDirectWitnessPlanObserve table observe context fuel value candidates] ≤
      Pr[fun hit : Bool => hit = true |
        canonicalizeDirectWitnessOrdinalRisk table riskObserve context fuel value candidates] := by
  let canonical := canonicalizeMaterializedValues table context
  unfold canonicalizeDirectWitnessPlanObserve canonicalizeDirectWitnessOrdinalRisk
  by_cases hhit : PrivateStructuralHit canonical
  · simp only [canonical, hhit, ↓reduceDIte, if_pos]
    rw [probEvent_pure, probEvent_pure]
    simp only [Bool.false_eq_true, if_false]
    rw [if_neg (not_witnessUsesOrdinal_of_not_lt_length ordinal _ hnotSelected)]
  · simp only [canonical, hhit, ↓reduceDIte]
    by_cases hpublished : PublishedValues context.state
    · simp only [hpublished, ↓reduceIte]
      unfold classifyDirectWitnessPlanObserve
      change ¬PrivateStructuralHit (canonicalizeMaterializedValues table context) at hhit
      simp only [hhit, ↓reduceDIte]
      by_cases hcompletable : DeferredCompletable table canonical
      · change DeferredCompletable table (canonicalizeMaterializedValues table context)
            at hcompletable
        simp only [hcompletable, ↓reduceIte]
        exact hcontinuation hhit hpublished hcompletable
      · change ¬DeferredCompletable table (canonicalizeMaterializedValues table context)
            at hcompletable
        simp only [hcompletable, ↓reduceIte, probEvent_pure, Bool.false_eq_true]
        have hnone : ¬WitnessUsesOrdinal ordinal
            ((none, candidates) : PrivateWitnessPlanOutput) :=
          not_witnessUsesOrdinal_of_not_lt_length ordinal _ hnotSelected
        rw [if_neg hnone]
    · simp only [hpublished, ↓reduceIte, probEvent_pure, Bool.false_eq_true]
      have hnone : ¬WitnessUsesOrdinal ordinal
          ((none, candidates) : PrivateWitnessPlanOutput) :=
        not_witnessUsesOrdinal_of_not_lt_length ordinal _ hnotSelected
      rw [if_neg hnone]

end SphincsSecurity.Concrete.OtsProbeSimulation
