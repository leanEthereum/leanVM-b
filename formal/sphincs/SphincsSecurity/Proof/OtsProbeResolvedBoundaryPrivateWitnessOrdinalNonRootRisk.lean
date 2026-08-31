import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalHiddenFreshSigner

/-!
# Non-root ordinal risk

The least selected ordinal is split by whether its candidate names a layer root. This risk is the
existing hidden prefix risk with root candidates gated to false. The weakened freshness invariant
is therefore sufficient through the concrete signer.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable

noncomputable def nonRootHiddenPrivateCandidateFire
    (candidate : Probe) (context : DeferredContext) : ProbComp Bool :=
  if candidate.IsLayerRoot then pure false else hiddenPrivateCandidateFire candidate context

theorem probEvent_nonRootHiddenPrivateCandidateFire_le
    (candidate : Probe) (context : DeferredContext)
    (hparent : candidate.HasStructuralParent)
    (hfresh : CandidatePositionsFreshExceptLayerRoots context) :
    Pr[fun hit : Bool => hit = true |
        nonRootHiddenPrivateCandidateFire candidate context] ≤
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  by_cases hroot : candidate.IsLayerRoot
  · simp [nonRootHiddenPrivateCandidateFire, hroot]
  · rw [nonRootHiddenPrivateCandidateFire, if_neg hroot]
    rw [probEvent_eq_eq_probOutput]
    exact probEvent_hiddenPrivateCandidateFire_le_of_freshExceptLayerRoots candidate context
      hparent hroot hfresh

noncomputable def directDetailedBoundaryPrivateOrdinalNonRootRisk
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
        nonRootHiddenPrivateCandidateFire (candidates.get ⟨ordinal, hselected⟩) context
      else pure false)
    (fun query _next recursivelyRun candidates context fuel table cache =>
      if hselected : ordinal < candidates.length then
        nonRootHiddenPrivateCandidateFire (candidates.get ⟨ordinal, hselected⟩) context
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
            let nextCandidates := appendPlannedCandidate candidates
              (rootAwarePlannedCandidate? parameter input context.state)
            if hnextSelected : ordinal < nextCandidates.length then
              nonRootHiddenPrivateCandidateFire
                (nextCandidates.get ⟨ordinal, hnextSelected⟩) context
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

theorem directDetailedBoundaryPrivateOrdinalNonRootRisk_eq_fire_of_selected
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hselected : ordinal < candidates.length) :
    directDetailedBoundaryPrivateOrdinalNonRootRisk ordinal parameter root ftsSecret computation
        candidates context fuel table cache =
      nonRootHiddenPrivateCandidateFire
        (candidates.get ⟨ordinal, hselected⟩) context := by
  induction computation using OracleComp.inductionOn generalizing candidates context fuel cache with
  | pure value =>
      rw [directDetailedBoundaryPrivateOrdinalNonRootRisk, OracleComp.construct_pure]
      simp only [hselected, ↓reduceDIte]
  | query_bind query next ih =>
      rw [directDetailedBoundaryPrivateOrdinalNonRootRisk, OracleComp.construct_query_bind]
      simp only [hselected, ↓reduceDIte]

theorem not_witnessFirstUsesNonLayerRootOrdinal_of_not_lt_length
    (ordinal : Nat) (output : PrivateWitnessPlanOutput)
    (hnot : ¬ordinal < output.2.length) :
    ¬WitnessFirstUsesNonLayerRootOrdinal ordinal output := by
  intro hfirst
  exact (not_witnessUsesOrdinal_of_not_lt_length ordinal output hnot)
    (witnessUsesOrdinal_of_witnessFirstUsesNonLayerRootOrdinal hfirst)

theorem probEvent_finishDirectWitnessPlanFirstUsesNonRootOrdinal_le_risk
    (ordinal : Nat)
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (riskObserve : DeferredContext → Nat → α → List Probe → ProbComp Bool)
    (candidates : List Probe) (result : DirectWitnessResult α)
    (hnotSelected : ¬ordinal < candidates.length)
    (hcontinuation : ∀ resolved : ResolvedRunResult α,
      result = .done resolved →
      Pr[WitnessFirstUsesNonLayerRootOrdinal ordinal |
          observe resolved.context resolved.remaining resolved.value candidates] ≤
        Pr[fun hit : Bool => hit = true |
          riskObserve resolved.context resolved.remaining resolved.value candidates]) :
    Pr[WitnessFirstUsesNonLayerRootOrdinal ordinal |
        finishDirectWitnessPlanObserve observe candidates result] ≤
      Pr[fun hit : Bool => hit = true |
        finishDirectWitnessOrdinalRisk riskObserve candidates result] := by
  cases result with
  | stoppedFuel =>
      simp [finishDirectWitnessPlanObserve, finishDirectWitnessOrdinalRisk,
        WitnessFirstUsesNonLayerRootOrdinal]
  | stoppedOrdinary =>
      simp [finishDirectWitnessPlanObserve, finishDirectWitnessOrdinalRisk,
        WitnessFirstUsesNonLayerRootOrdinal]
  | stoppedPrivate witness =>
      have hnone : ¬WitnessFirstUsesNonLayerRootOrdinal ordinal (some witness, candidates) :=
        not_witnessFirstUsesNonLayerRootOrdinal_of_not_lt_length ordinal
          (some witness, candidates) hnotSelected
      simp [finishDirectWitnessPlanObserve, finishDirectWitnessOrdinalRisk, hnone]
  | done resolved =>
      simpa [finishDirectWitnessPlanObserve, finishDirectWitnessOrdinalRisk] using
        hcontinuation resolved rfl

theorem probEvent_runDirectWitnessPlanFirstUsesNonRootOrdinal_le_risk
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
      Pr[WitnessFirstUsesNonLayerRootOrdinal ordinal |
          observe result.context result.remaining result.value candidates] ≤
        Pr[fun hit : Bool => hit = true |
          riskObserve result.context result.remaining result.value candidates]) :
    Pr[WitnessFirstUsesNonLayerRootOrdinal ordinal |
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
      (probEvent_finishDirectWitnessPlanFirstUsesNonRootOrdinal_le_risk ordinal observe riskObserve
        candidates result hnotSelected (by
          intro resolved heq
          subst result
          exact hcontinuation resolved hresult))
  · rw [probOutput_eq_zero_of_not_mem_support hresult]
    simp

theorem probEvent_canonicalizeWitnessPlanFirstUsesNonRootOrdinal_le_risk
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
      Pr[WitnessFirstUsesNonLayerRootOrdinal ordinal |
          observe canonical fuel value candidates] ≤
        Pr[fun hit : Bool => hit = true |
          riskObserve canonical fuel value candidates]) :
    Pr[WitnessFirstUsesNonLayerRootOrdinal ordinal |
        canonicalizeDirectWitnessPlanObserve table observe context fuel value candidates] ≤
      Pr[fun hit : Bool => hit = true |
        canonicalizeDirectWitnessOrdinalRisk table riskObserve context fuel value candidates] := by
  let canonical := canonicalizeMaterializedValues table context
  unfold canonicalizeDirectWitnessPlanObserve canonicalizeDirectWitnessOrdinalRisk
  by_cases hhit : PrivateStructuralHit canonical
  · simp only [canonical, hhit, ↓reduceDIte, if_pos]
    rw [probEvent_pure, probEvent_pure]
    simp only [Bool.false_eq_true, if_false]
    rw [if_neg
      (not_witnessFirstUsesNonLayerRootOrdinal_of_not_lt_length ordinal _ hnotSelected)]
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
        have hnone : ¬WitnessFirstUsesNonLayerRootOrdinal ordinal
            ((none, candidates) : PrivateWitnessPlanOutput) :=
          not_witnessFirstUsesNonLayerRootOrdinal_of_not_lt_length ordinal _ hnotSelected
        rw [if_neg hnone]
    · simp only [hpublished, ↓reduceIte, probEvent_pure, Bool.false_eq_true]
      have hnone : ¬WitnessFirstUsesNonLayerRootOrdinal ordinal
          ((none, candidates) : PrivateWitnessPlanOutput) :=
        not_witnessFirstUsesNonLayerRootOrdinal_of_not_lt_length ordinal _ hnotSelected
      rw [if_neg hnone]

theorem probEvent_unselectedDirectWitnessStepFirstUsesNonRootOrdinal_le_risk
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
      Pr[WitnessFirstUsesNonLayerRootOrdinal ordinal |
          observe (canonicalizeMaterializedValues table result.context)
            result.remaining result.value candidates] ≤
        Pr[fun hit : Bool => hit = true |
          riskObserve (canonicalizeMaterializedValues table result.context)
            result.remaining result.value candidates]) :
    Pr[WitnessFirstUsesNonLayerRootOrdinal ordinal |
        runDirectWitnessPlanObserve
          (canonicalizeDirectWitnessPlanObserve table observe)
          candidates context fuel table computation] ≤
      Pr[fun hit : Bool => hit = true |
        runDirectResolvedWitnessFromTable context fuel table computation >>=
          finishDirectWitnessOrdinalRisk
            (canonicalizeDirectWitnessOrdinalRisk table riskObserve) candidates] := by
  apply probEvent_runDirectWitnessPlanFirstUsesNonRootOrdinal_le_risk ordinal _ _ candidates
    context fuel table computation hnotSelected
  intro result hresult
  apply probEvent_canonicalizeWitnessPlanFirstUsesNonRootOrdinal_le_risk table ordinal _ _
    result.context result.remaining result.value candidates hnotSelected
  dsimp only
  intro _hprivate _hpublished _hcompletable
  exact hcontinuation result hresult

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_directDetailedBoundaryWitnessFirstUsesNonRootOrdinal_le_of_selected
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) →
      List Probe → ProbComp PrivateWitnessPlanOutput)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hselected : ordinal < candidates.length)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hpublished : PublishedValues context.state)
    (hterminal : ∀ nextContext remaining value nextCandidates,
      nextContext.ValuesConsistent → StartTableAgrees nextContext.state table →
      PublishedValues nextContext.state →
      Pr[PrivateWitnessPlanMatchesCandidate (candidates.get ⟨ordinal, hselected⟩) |
          observe nextContext remaining value nextCandidates] ≤
        Pr[fun hit : Bool => hit = true |
          hiddenPrivateCandidateFire (candidates.get ⟨ordinal, hselected⟩) nextContext])
    (hobservePrefix : ∀ nextContext remaining value nextCandidates output,
      output ∈ support (observe nextContext remaining value nextCandidates) →
      PrivateWitnessPlanExtends nextCandidates output) :
    Pr[WitnessFirstUsesNonLayerRootOrdinal ordinal |
        directDetailedBoundaryNormalizedPrivateWitnessPlanObserve parameter root ftsSecret
          computation observe candidates context fuel table cache] ≤
      Pr[fun hit : Bool => hit = true |
        nonRootHiddenPrivateCandidateFire
          (candidates.get ⟨ordinal, hselected⟩) context] := by
  let candidate := candidates.get ⟨ordinal, hselected⟩
  by_cases hroot : candidate.IsLayerRoot
  · have hzero : Pr[WitnessFirstUsesNonLayerRootOrdinal ordinal |
        directDetailedBoundaryNormalizedPrivateWitnessPlanObserve parameter root ftsSecret
          computation observe candidates context fuel table cache] = 0 := by
      apply probEvent_eq_zero
      intro output houtput hfirst
      exact not_witnessFirstUsesNonLayerRootOrdinal_of_prefix_of_root candidates output ordinal
        hselected
        (privateWitnessPlanExtends_of_mem_directDetailedBoundaryNormalizedPrivateWitnessPlanObserve
          parameter root ftsSecret computation observe candidates context fuel table cache
          hobservePrefix output houtput)
        hroot hfirst
    rw [hzero]
    have hroot' : (candidates.get ⟨ordinal, hselected⟩).IsLayerRoot := by
      simpa [candidate] using hroot
    unfold nonRootHiddenPrivateCandidateFire
    rw [if_pos hroot']
    simp
  · calc
      _ ≤ Pr[PrivateWitnessPlanMatchesCandidate candidate |
          directDetailedBoundaryNormalizedPrivateWitnessPlanObserve parameter root ftsSecret
            computation observe candidates context fuel table cache] := by
        apply probEvent_mono
        intro output houtput hfirst
        apply privateWitnessPlanMatchesCandidate_of_usesOrdinal_of_prefix candidates output
          ordinal hselected
        · exact privateWitnessPlanExtends_of_mem_directDetailedBoundaryNormalizedPrivateWitnessPlanObserve
            parameter root ftsSecret computation observe candidates context fuel table cache
            hobservePrefix output houtput
        · exact witnessUsesOrdinal_of_witnessFirstUsesNonLayerRootOrdinal hfirst
      _ ≤ Pr[fun hit : Bool => hit = true |
          hiddenPrivateCandidateFire candidate context] := by
        exact probEvent_directDetailedBoundaryNormalizedPrivateWitnessPlanMatchesCandidate_le_hidden
          candidate parameter root ftsSecret computation observe candidates context fuel table
          cache hconsistent hstarts hpublished (by
            intro nextContext remaining value nextCandidates hnextConsistent hnextStarts
              hnextPublished
            exact hterminal nextContext remaining value nextCandidates hnextConsistent hnextStarts
              hnextPublished)
      _ = _ := by
        have hroot' : ¬(candidates.get ⟨ordinal, hselected⟩).IsLayerRoot := by
          simpa [candidate] using hroot
        unfold nonRootHiddenPrivateCandidateFire
        rw [if_neg hroot']

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_hashBranchWitnessFirstUsesNonRootOrdinal_le_nonRootRisk
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : HashInput)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) →
      List Probe → ProbComp PrivateWitnessPlanOutput)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hnotSelected : ¬ordinal < candidates.length)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hpublished : PublishedValues context.state)
    (hrecursive : ∀ output nextCandidates nextContext remaining nextCache,
      ¬ordinal < nextCandidates.length →
      nextContext.ValuesConsistent → StartTableAgrees nextContext.state table →
      PublishedValues nextContext.state →
      Pr[WitnessFirstUsesNonLayerRootOrdinal ordinal |
          directDetailedBoundaryNormalizedPrivateWitnessPlanObserve parameter root ftsSecret
            (next output) observe nextCandidates nextContext remaining table nextCache] ≤
        Pr[fun hit : Bool => hit = true |
          directDetailedBoundaryPrivateOrdinalNonRootRisk ordinal parameter root ftsSecret
            (next output) nextCandidates nextContext remaining table nextCache])
    (hterminalMatch : ∀ candidate nextContext remaining value nextCandidates,
      nextContext.ValuesConsistent → StartTableAgrees nextContext.state table →
      PublishedValues nextContext.state →
      Pr[PrivateWitnessPlanMatchesCandidate candidate |
          observe nextContext remaining value nextCandidates] ≤
        Pr[fun hit : Bool => hit = true |
          hiddenPrivateCandidateFire candidate nextContext])
    (hterminalPrefix : ∀ nextContext remaining value nextCandidates output,
      output ∈ support (observe nextContext remaining value nextCandidates) →
      PrivateWitnessPlanExtends nextCandidates output) :
    let plan := purePlanProbingHashQuery parameter input context.state
    let nextCandidates := appendPlannedCandidate candidates
      (rootAwarePlannedCandidate? parameter input context.state)
    Pr[WitnessFirstUsesNonLayerRootOrdinal ordinal |
        runDirectWitnessPlanObserve
          (canonicalizeDirectWitnessPlanObserve table
            (fun nextContext remaining value laterCandidates =>
              directDetailedBoundaryNormalizedPrivateWitnessPlanObserve parameter root ftsSecret
                (next value.1) observe laterCandidates nextContext remaining table value.2))
          nextCandidates context fuel table
            ((probingHashQueryAfterPlan parameter input plan).run cache)] ≤
      Pr[fun hit : Bool => hit = true |
        if hselected : ordinal < nextCandidates.length then
          nonRootHiddenPrivateCandidateFire
            (nextCandidates.get ⟨ordinal, hselected⟩) context
        else
          runDirectResolvedWitnessFromTable context fuel table
              ((probingHashQueryAfterPlan parameter input plan).run cache) >>=
            finishDirectWitnessOrdinalRisk
              (canonicalizeDirectWitnessOrdinalRisk table
                (fun nextContext remaining value laterCandidates =>
                  directDetailedBoundaryPrivateOrdinalNonRootRisk ordinal parameter root ftsSecret
                    (next value.1) laterCandidates nextContext remaining table value.2))
              nextCandidates] := by
  dsimp only
  let plan := purePlanProbingHashQuery parameter input context.state
  let nextCandidates := appendPlannedCandidate candidates
    (rootAwarePlannedCandidate? parameter input context.state)
  by_cases hnextSelected : ordinal < nextCandidates.length
  · rw [dif_pos hnextSelected]
    have hexists : ∃ candidate,
        rootAwarePlannedCandidate? parameter input context.state = some candidate := by
      cases hcandidate : rootAwarePlannedCandidate? parameter input context.state with
      | none =>
          have hsame : nextCandidates = candidates := by
            simp [nextCandidates, appendPlannedCandidate, hcandidate]
          exact (hnotSelected (hsame ▸ hnextSelected)).elim
      | some candidate => exact ⟨candidate, rfl⟩
    obtain ⟨candidate, hcandidate⟩ := hexists
    have hordinal : ordinal = candidates.length := by
      have hlength : nextCandidates.length = candidates.length + 1 := by
        simp [nextCandidates, appendPlannedCandidate, hcandidate]
      omega
    subst ordinal
    have hget : nextCandidates.get ⟨candidates.length, hnextSelected⟩ = candidate := by
      simp [nextCandidates, appendPlannedCandidate, hcandidate, List.get_eq_getElem]
    rw [hget]
    by_cases hroot : candidate.IsLayerRoot
    · have hzero : Pr[WitnessFirstUsesNonLayerRootOrdinal candidates.length |
          runDirectWitnessPlanObserve
            (canonicalizeDirectWitnessPlanObserve table
              (fun nextContext remaining value laterCandidates =>
                directDetailedBoundaryNormalizedPrivateWitnessPlanObserve parameter root ftsSecret
                  (next value.1) observe laterCandidates nextContext remaining table value.2))
            nextCandidates context fuel table
              ((probingHashQueryAfterPlan parameter input plan).run cache)] = 0 := by
        apply probEvent_eq_zero
        intro output houtput hfirst
        apply not_witnessFirstUsesNonLayerRootOrdinal_of_prefix_of_root nextCandidates output
          candidates.length hnextSelected
        · apply privateWitnessPlanExtends_of_mem_runDirectWitnessPlanObserve _ nextCandidates
            context fuel table ((probingHashQueryAfterPlan parameter input plan).run cache)
            (output := output) (houtput := houtput)
          intro result _hresult nextOutput hnextOutput
          apply privateWitnessPlanExtends_of_mem_canonicalizeDirectWitnessPlanObserve table _
            result.context result.remaining result.value nextCandidates
            (output := nextOutput) (houtput := hnextOutput)
          intro finalOutput hfinalOutput
          exact privateWitnessPlanExtends_of_mem_directDetailedBoundaryNormalizedPrivateWitnessPlanObserve
            parameter root ftsSecret (next result.value.1) observe nextCandidates
            (canonicalizeMaterializedValues table result.context) result.remaining table
            result.value.2 hterminalPrefix finalOutput hfinalOutput
        · rw [hget]
          exact hroot
        · exact hfirst
      rw [hzero]
      simp [nonRootHiddenPrivateCandidateFire, hroot]
    · have hbound := probEvent_selectedHashPlanWitnessUsesOrdinal_le_hidden parameter root
        ftsSecret input next observe candidates context fuel table cache candidate hconsistent
        hstarts hpublished
        (by
          intro nextContext remaining value laterCandidates hnextConsistent hnextStarts
            hnextPublished
          exact hterminalMatch candidate nextContext remaining value laterCandidates
            hnextConsistent hnextStarts hnextPublished)
        hterminalPrefix
      calc
        _ ≤ Pr[WitnessUsesOrdinal candidates.length |
            runDirectWitnessPlanObserve
              (canonicalizeDirectWitnessPlanObserve table
                (fun nextContext remaining value laterCandidates =>
                  directDetailedBoundaryNormalizedPrivateWitnessPlanObserve parameter root
                    ftsSecret (next value.1) observe laterCandidates nextContext remaining table
                    value.2))
              nextCandidates context fuel table
                ((probingHashQueryAfterPlan parameter input plan).run cache)] := by
          apply probEvent_mono
          intro output _houtput hfirst
          exact witnessUsesOrdinal_of_witnessFirstUsesNonLayerRootOrdinal hfirst
        _ ≤ Pr[fun hit : Bool => hit = true |
            hiddenPrivateCandidateFire candidate context] := by
          simpa only [nextCandidates, hcandidate, appendPlannedCandidate, plan] using hbound
        _ = _ := by
          unfold nonRootHiddenPrivateCandidateFire
          rw [if_neg hroot]
  · rw [dif_neg hnextSelected]
    apply probEvent_unselectedDirectWitnessStepFirstUsesNonRootOrdinal_le_risk ordinal _ _
      nextCandidates context fuel table
      ((probingHashQueryAfterPlan parameter input plan).run cache) hnextSelected
    intro result hresult
    let inner := (probingHashQueryAfterPlan parameter input plan).run cache
    have hdetailed : DirectDetailedResult.done result ∈ support
        (runDirectResolvedDetailedFromTable context fuel table inner) := by
      rw [← map_erase_runDirectResolvedWitnessFromTable inner context fuel table, support_map]
      exact ⟨DirectWitnessResult.done result, hresult, rfl⟩
    have hcore := resolvedCore_of_done_mem_runDirectResolvedWitnessFromTable inner context fuel
      table result hconsistent hstarts hresult
    have hnextPublished := publishedValues_of_done_runDirectResolvedDetailedFromTable
      (probingHashQueryAfterPlan parameter input plan)
      (preservesPublishedValues_probingHashQueryAfterPlan parameter input plan)
      context fuel table cache result hpublished hdetailed
    exact hrecursive result.value.1 nextCandidates
      (canonicalizeMaterializedValues table result.context) result.remaining result.value.2
      hnextSelected
      (canonicalizeMaterializedValues_valuesConsistent table result.context hcore.2.1)
      (canonicalizeMaterializedValues_startTableAgrees table result.context)
      hnextPublished.to_canonicalizedMaterializedValues

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_directDetailedBoundaryWitnessFirstUsesNonRootOrdinal_le_nonRootRisk
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) →
      List Probe → ProbComp PrivateWitnessPlanOutput)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hnotSelected : ¬ordinal < candidates.length)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hpublished : PublishedValues context.state)
    (hterminalZero : ∀ nextContext remaining value nextCandidates,
      ¬ordinal < nextCandidates.length →
      Pr[WitnessFirstUsesNonLayerRootOrdinal ordinal |
          observe nextContext remaining value nextCandidates] ≤ 0)
    (hterminalMatch : ∀ candidate nextContext remaining value nextCandidates,
      nextContext.ValuesConsistent → StartTableAgrees nextContext.state table →
      PublishedValues nextContext.state →
      Pr[PrivateWitnessPlanMatchesCandidate candidate |
          observe nextContext remaining value nextCandidates] ≤
        Pr[fun hit : Bool => hit = true |
          hiddenPrivateCandidateFire candidate nextContext])
    (hterminalPrefix : ∀ nextContext remaining value nextCandidates output,
      output ∈ support (observe nextContext remaining value nextCandidates) →
      PrivateWitnessPlanExtends nextCandidates output) :
    Pr[WitnessFirstUsesNonLayerRootOrdinal ordinal |
        directDetailedBoundaryNormalizedPrivateWitnessPlanObserve parameter root ftsSecret
          computation observe candidates context fuel table cache] ≤
      Pr[fun hit : Bool => hit = true |
        directDetailedBoundaryPrivateOrdinalNonRootRisk ordinal parameter root ftsSecret
          computation candidates context fuel table cache] := by
  induction computation using OracleComp.inductionOn generalizing
      candidates context fuel cache with
  | pure value =>
      rw [directDetailedBoundaryNormalizedPrivateWitnessPlanObserve,
        OracleComp.construct_pure, directDetailedBoundaryPrivateOrdinalNonRootRisk,
        OracleComp.construct_pure]
      simp only [hnotSelected, ↓reduceDIte]
      simpa using hterminalZero context fuel (value, cache) candidates hnotSelected
  | query_bind query next ih =>
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              rw [directDetailedBoundaryNormalizedPrivateWitnessPlanObserve,
                OracleComp.construct_query_bind,
                directDetailedBoundaryPrivateOrdinalNonRootRisk,
                OracleComp.construct_query_bind]
              simp only [hnotSelected, ↓reduceDIte]
              let inner := (splitUniformImpl n).run cache
              apply probEvent_unselectedDirectWitnessStepFirstUsesNonRootOrdinal_le_risk ordinal
                _ _ candidates context fuel table inner hnotSelected
              intro result hresult
              have hdetailed : DirectDetailedResult.done result ∈ support
                  (runDirectResolvedDetailedFromTable context fuel table inner) := by
                rw [← map_erase_runDirectResolvedWitnessFromTable inner context fuel table,
                  support_map]
                exact ⟨DirectWitnessResult.done result, hresult, rfl⟩
              have hcore := resolvedCore_of_done_mem_runDirectResolvedWitnessFromTable inner
                context fuel table result hconsistent hstarts hresult
              have hnextPublished := publishedValues_of_done_runDirectResolvedDetailedFromTable
                (splitUniformImpl n) (preservesPublishedValuesImpl_splitUniformImpl n)
                context fuel table cache result hpublished hdetailed
              exact ih result.value.1 candidates
                (canonicalizeMaterializedValues table result.context) result.remaining
                result.value.2 hnotSelected
                (canonicalizeMaterializedValues_valuesConsistent table result.context hcore.2.1)
                (canonicalizeMaterializedValues_startTableAgrees table result.context)
                hnextPublished.to_canonicalizedMaterializedValues
          | inr input =>
              rw [directDetailedBoundaryNormalizedPrivateWitnessPlanObserve,
                OracleComp.construct_query_bind,
                directDetailedBoundaryPrivateOrdinalNonRootRisk,
                OracleComp.construct_query_bind]
              simp only [hnotSelected, ↓reduceDIte]
              apply probEvent_hashBranchWitnessFirstUsesNonRootOrdinal_le_nonRootRisk ordinal
                parameter root ftsSecret input next observe candidates context fuel table cache
                hnotSelected hconsistent hstarts hpublished
              · intro output nextCandidates nextContext remaining nextCache hnextNotSelected
                  hnextConsistent hnextStarts hnextPublished
                exact ih output nextCandidates nextContext remaining nextCache hnextNotSelected
                  hnextConsistent hnextStarts hnextPublished
              · exact hterminalMatch
              · exact hterminalPrefix
      | inr message =>
          rw [directDetailedBoundaryNormalizedPrivateWitnessPlanObserve,
            OracleComp.construct_query_bind,
            directDetailedBoundaryPrivateOrdinalNonRootRisk,
            OracleComp.construct_query_bind]
          simp only [hnotSelected, ↓reduceDIte]
          let inner := (maskedSign parameter root ftsSecret message).run cache
          apply probEvent_unselectedDirectWitnessStepFirstUsesNonRootOrdinal_le_risk ordinal _ _
            candidates context fuel table inner hnotSelected
          intro result hresult
          have hdetailed : DirectDetailedResult.done result ∈ support
              (runDirectResolvedDetailedFromTable context fuel table inner) := by
            rw [← map_erase_runDirectResolvedWitnessFromTable inner context fuel table,
              support_map]
            exact ⟨DirectWitnessResult.done result, hresult, rfl⟩
          have hcore := resolvedCore_of_done_mem_runDirectResolvedWitnessFromTable inner context
            fuel table result hconsistent hstarts hresult
          have hnextPublished := publishedValues_of_done_runDirectResolvedDetailedFromTable
            (maskedSign parameter root ftsSecret message)
            (preservesPublishedValues_maskedSign parameter root ftsSecret message)
            context fuel table cache result hpublished hdetailed
          exact ih result.value.1 candidates
            (canonicalizeMaterializedValues table result.context) result.remaining
            result.value.2 hnotSelected
            (canonicalizeMaterializedValues_valuesConsistent table result.context hcore.2.1)
            (canonicalizeMaterializedValues_startTableAgrees table result.context)
            hnextPublished.to_canonicalizedMaterializedValues

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_granularDetailedRetainedRestWitnessFirstUsesNonRootOrdinal_le_nonRootRisk
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (ordinal : Nat) (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (candidates : List Probe)
    (hnotSelected : ¬ordinal < candidates.length)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hpublished : PublishedValues context.state) :
    Pr[WitnessFirstUsesNonLayerRootOrdinal ordinal |
        granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve adversary parameter table
          ftsSecret context fuel value candidates] ≤
      Pr[fun hit : Bool => hit = true |
        directDetailedBoundaryPrivateOrdinalNonRootRisk ordinal parameter value.1 ftsSecret
          (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
          candidates context fuel table value.2] := by
  unfold granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve
  apply probEvent_directDetailedBoundaryWitnessFirstUsesNonRootOrdinal_le_nonRootRisk ordinal
    parameter value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
    (retainedResolvedFinalizationPrivateWitnessPlanObserve table value.1)
    candidates context fuel table value.2 hnotSelected hconsistent hstarts hpublished
  · intro nextContext remaining nextValue nextCandidates hnextNotSelected
    calc
      _ ≤ Pr[WitnessUsesOrdinal ordinal |
          retainedResolvedFinalizationPrivateWitnessPlanObserve table value.1 nextContext
            remaining nextValue nextCandidates] := by
        apply probEvent_mono
        intro output _houtput hfirst
        exact witnessUsesOrdinal_of_witnessFirstUsesNonLayerRootOrdinal hfirst
      _ ≤ 0 := probEvent_retainedFinalizationWitnessUsesOrdinal_le_zero table value.1 nextContext
        remaining nextValue nextCandidates ordinal hnextNotSelected
  · intro candidate nextContext remaining nextValue nextCandidates _hnextConsistent
      _hnextStarts hnextPublished
    exact probEvent_retainedResolvedFinalizationPrivateWitnessPlanMatchesCandidate_le_hidden table
      value.1 candidate nextContext remaining nextValue nextCandidates hnextPublished
  · intro nextContext remaining nextValue nextCandidates output houtput
    exact privateWitnessPlanExtends_of_mem_retainedResolvedFinalizationPrivateWitnessPlanObserve
      table value.1 nextContext remaining nextValue nextCandidates output houtput

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_directDetailedBoundaryPrivateOrdinalNonRootRisk_le
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hparents : CandidatesHaveStructuralParent candidates)
    (hfresh : CandidatePositionsFreshExceptLayerRoots context)
    (hpublishedContext : PublishedValues context.state) :
    Pr[fun hit : Bool => hit = true |
        directDetailedBoundaryPrivateOrdinalNonRootRisk ordinal parameter root ftsSecret
          computation candidates context fuel table cache] ≤
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  induction computation using OracleComp.inductionOn generalizing candidates context fuel cache with
  | pure value =>
      rw [directDetailedBoundaryPrivateOrdinalNonRootRisk, OracleComp.construct_pure]
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte]
        exact probEvent_nonRootHiddenPrivateCandidateFire_le
          (candidates.get ⟨ordinal, hselected⟩) context
          (candidateHasStructuralParent_get hparents ordinal hselected) hfresh
      · simp [hselected]
  | query_bind query next ih =>
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              rw [directDetailedBoundaryPrivateOrdinalNonRootRisk,
                OracleComp.construct_query_bind]
              by_cases hselected : ordinal < candidates.length
              · simp only [hselected, ↓reduceDIte]
                exact probEvent_nonRootHiddenPrivateCandidateFire_le
                  (candidates.get ⟨ordinal, hselected⟩) context
                  (candidateHasStructuralParent_get hparents ordinal hselected) hfresh
              · simp only [hselected, ↓reduceDIte]
                apply probEvent_bind_le_of_forall_le
                intro result hresult
                apply probEvent_finishDirectWitnessOrdinalRisk_le table _ candidates result _
                intro resolved heq hpublished hcompletable
                subst result
                exact ih resolved.value.1 candidates
                  (canonicalizeMaterializedValues table resolved.context) resolved.remaining
                  resolved.value.2 hparents
                  (candidatePositionsFreshExceptLayerRoots_uniformStep n context fuel table cache
                    resolved hfresh hresult)
                  hpublished.to_canonicalizedMaterializedValues
          | inr input =>
              rw [directDetailedBoundaryPrivateOrdinalNonRootRisk,
                OracleComp.construct_query_bind]
              by_cases hselected : ordinal < candidates.length
              · simp only [hselected, ↓reduceDIte]
                exact probEvent_nonRootHiddenPrivateCandidateFire_le
                  (candidates.get ⟨ordinal, hselected⟩) context
                  (candidateHasStructuralParent_get hparents ordinal hselected) hfresh
              · simp only [hselected, ↓reduceDIte]
                let plan := purePlanProbingHashQuery parameter input context.state
                let nextCandidates := appendPlannedCandidate candidates
                  (rootAwarePlannedCandidate? parameter input context.state)
                have hnextParents : CandidatesHaveStructuralParent nextCandidates := by
                  apply hparents.appendPlanned
                    (rootAwarePlannedCandidate? parameter input context.state)
                  intro candidate hcandidate
                  exact rootAwarePlannedCandidate?_hasStructuralParent hcandidate
                by_cases hnextSelected : ordinal < nextCandidates.length
                · have hactual : ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwarePlannedCandidate? parameter input context.state)).length := by
                    simpa [nextCandidates, plan] using hnextSelected
                  rw [dif_pos hactual]
                  simpa [nextCandidates, plan] using
                    (probEvent_nonRootHiddenPrivateCandidateFire_le
                      (nextCandidates.get ⟨ordinal, hnextSelected⟩) context
                      (candidateHasStructuralParent_get hnextParents ordinal hnextSelected) hfresh)
                · have hactual : ¬ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwarePlannedCandidate? parameter input context.state)).length := by
                    simpa [nextCandidates, plan] using hnextSelected
                  rw [dif_neg hactual]
                  apply probEvent_bind_le_of_forall_le
                  intro result hresult
                  apply probEvent_finishDirectWitnessOrdinalRisk_le table _ nextCandidates result _
                  intro resolved heq hpublished hcompletable
                  subst result
                  exact ih resolved.value.1 nextCandidates
                    (canonicalizeMaterializedValues table resolved.context) resolved.remaining
                    resolved.value.2 hnextParents
                    (candidatePositionsFreshExceptLayerRoots_hashStep parameter input plan context
                      fuel table cache resolved hfresh hpublishedContext hresult)
                    hpublished.to_canonicalizedMaterializedValues
      | inr message =>
          rw [directDetailedBoundaryPrivateOrdinalNonRootRisk,
            OracleComp.construct_query_bind]
          by_cases hselected : ordinal < candidates.length
          · simp only [hselected, ↓reduceDIte]
            exact probEvent_nonRootHiddenPrivateCandidateFire_le
              (candidates.get ⟨ordinal, hselected⟩) context
              (candidateHasStructuralParent_get hparents ordinal hselected) hfresh
          · simp only [hselected, ↓reduceDIte]
            apply probEvent_bind_le_of_forall_le
            intro result hresult
            apply probEvent_finishDirectWitnessOrdinalRisk_le table _ candidates result _
            intro resolved heq hpublished hcompletable
            subst result
            exact ih resolved.value.1 candidates
              (canonicalizeMaterializedValues table resolved.context) resolved.remaining
              resolved.value.2 hparents
              (candidatePositionsFreshExceptLayerRoots_signStep parameter root ftsSecret message
                context fuel table cache resolved hfresh hpublishedContext hresult)
              hpublished.to_canonicalizedMaterializedValues

theorem probEvent_granularDetailedRetainedRestWitnessFirstUsesNonRootOrdinal_le
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (ordinal : Nat) (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (candidates : List Probe)
    (hnotSelected : ¬ordinal < candidates.length)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hpublished : PublishedValues context.state)
    (hparents : CandidatesHaveStructuralParent candidates)
    (hfresh : CandidatePositionsFreshExceptLayerRoots context) :
    Pr[WitnessFirstUsesNonLayerRootOrdinal ordinal |
        granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve adversary parameter table
          ftsSecret context fuel value candidates] ≤
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  calc
    _ ≤ Pr[fun hit : Bool => hit = true |
        directDetailedBoundaryPrivateOrdinalNonRootRisk ordinal parameter value.1 ftsSecret
          (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
          candidates context fuel table value.2] :=
      probEvent_granularDetailedRetainedRestWitnessFirstUsesNonRootOrdinal_le_nonRootRisk
        adversary parameter table ftsSecret ordinal context fuel value candidates hnotSelected
        hconsistent hstarts hpublished
    _ ≤ _ := probEvent_directDetailedBoundaryPrivateOrdinalNonRootRisk_le ordinal parameter
      value.1 ftsSecret (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
      candidates context fuel table value.2 hparents hfresh hpublished

end SphincsSecurity.Concrete.OtsProbeSimulation
