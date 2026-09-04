import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRisk

/-!
# Ordinal witness to prefix-risk lift

The normalized witness event is bounded by the prefix-risk computation one outer query at a time.
The common unselected step is kept separate from the dependent outer query match.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable

theorem probEvent_unselectedDirectWitnessStep_le_ordinalRisk
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
          observe (canonicalizeMaterializedValues table result.context)
            result.remaining result.value candidates] ≤
        Pr[fun hit : Bool => hit = true |
          riskObserve (canonicalizeMaterializedValues table result.context)
            result.remaining result.value candidates]) :
    Pr[WitnessUsesOrdinal ordinal |
        runDirectWitnessPlanObserve
          (canonicalizeDirectWitnessPlanObserve table observe)
          candidates context fuel table computation] ≤
      Pr[fun hit : Bool => hit = true |
        runDirectResolvedWitnessFromTable context fuel table computation >>=
          finishDirectWitnessOrdinalRisk
            (canonicalizeDirectWitnessOrdinalRisk table riskObserve) candidates] := by
  apply probEvent_runDirectWitnessPlanUsesOrdinal_le_risk ordinal _ _ candidates context fuel
    table computation hnotSelected
  intro result hresult
  apply probEvent_canonicalizeWitnessPlanUsesOrdinal_le_risk table ordinal _ _
    result.context result.remaining result.value candidates hnotSelected
  dsimp only
  intro _hprivate _hpublished _hcompletable
  exact hcontinuation result hresult

theorem resolvedCore_of_done_mem_runDirectResolvedWitnessFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult α)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hresult : DirectWitnessResult.done result ∈ support
      (runDirectResolvedWitnessFromTable context fuel table computation)) :
    result.table = table ∧ result.context.ValuesConsistent ∧
      StartTableAgrees result.context.state table := by
  have hdetailed : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table computation) := by
    rw [← map_erase_runDirectResolvedWitnessFromTable computation context fuel table,
      support_map]
    exact ⟨DirectWitnessResult.done result, hresult, rfl⟩
  exact resolvedCore_of_mem_runDirectResolvedFromTable computation context fuel table result
    hconsistent hstarts
    (mem_support_runDirectResolvedFromTable_of_done_detailed computation context fuel table result
      hdetailed)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_hashBranchWitnessUsesOrdinal_le_ordinalRisk
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
    (hrecursive : ∀ output nextCandidates nextContext remaining nextCache,
      ¬ordinal < nextCandidates.length →
      nextContext.ValuesConsistent → StartTableAgrees nextContext.state table →
      Pr[WitnessUsesOrdinal ordinal |
          directDetailedBoundaryNormalizedPrivateWitnessPlanObserve parameter root ftsSecret
            (next output) observe nextCandidates nextContext remaining table nextCache] ≤
        Pr[fun hit : Bool => hit = true |
          directDetailedBoundaryPrivateOrdinalRisk ordinal parameter root ftsSecret
            (next output) nextCandidates nextContext remaining table nextCache])
    (hterminalMatch : ∀ candidate nextContext remaining value nextCandidates,
      nextContext.ValuesConsistent → StartTableAgrees nextContext.state table →
      Pr[PrivateWitnessPlanMatchesCandidate candidate |
          observe nextContext remaining value nextCandidates] ≤
        Pr[fun hit : Bool => hit = true | privateCandidateFire candidate nextContext])
    (hterminalPrefix : ∀ nextContext remaining value nextCandidates output,
      output ∈ support (observe nextContext remaining value nextCandidates) →
      PrivateWitnessPlanExtends nextCandidates output) :
    let plan := purePlanProbingHashQuery parameter input context.state
    let nextCandidates := appendPlannedCandidate candidates
      (rootAwarePlannedCandidate? parameter input context.state)
    Pr[WitnessUsesOrdinal ordinal |
        runDirectWitnessPlanObserve
          (canonicalizeDirectWitnessPlanObserve table
            (fun nextContext remaining value laterCandidates =>
              directDetailedBoundaryNormalizedPrivateWitnessPlanObserve parameter root ftsSecret
                (next value.1) observe laterCandidates nextContext remaining table value.2))
          nextCandidates context fuel table
            ((probingHashQueryAfterPlan parameter input plan).run cache)] ≤
      Pr[fun hit : Bool => hit = true |
        if hselected : ordinal < nextCandidates.length then
          privateCandidateFire (nextCandidates.get ⟨ordinal, hselected⟩) context
        else
          runDirectResolvedWitnessFromTable context fuel table
              ((probingHashQueryAfterPlan parameter input plan).run cache) >>=
            finishDirectWitnessOrdinalRisk
              (canonicalizeDirectWitnessOrdinalRisk table
                (fun nextContext remaining value laterCandidates =>
                  directDetailedBoundaryPrivateOrdinalRisk ordinal parameter root ftsSecret
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
    have hbound := probEvent_selectedHashPlanWitnessUsesOrdinal_le parameter root ftsSecret input
      next observe candidates context fuel table cache candidate hconsistent hstarts
      (by
        intro nextContext remaining value laterCandidates hnextConsistent hnextStarts
        exact hterminalMatch candidate nextContext remaining value laterCandidates
          hnextConsistent hnextStarts)
      hterminalPrefix
    simpa only [nextCandidates, hcandidate, appendPlannedCandidate, plan] using hbound
  · rw [dif_neg hnextSelected]
    apply probEvent_unselectedDirectWitnessStep_le_ordinalRisk ordinal _ _ nextCandidates
      context fuel table ((probingHashQueryAfterPlan parameter input plan).run cache)
      hnextSelected
    intro result hresult
    have hcore := resolvedCore_of_done_mem_runDirectResolvedWitnessFromTable
      ((probingHashQueryAfterPlan parameter input plan).run cache) context fuel table result
      hconsistent hstarts hresult
    exact hrecursive result.value.1 nextCandidates
      (canonicalizeMaterializedValues table result.context) result.remaining result.value.2
      hnextSelected
      (canonicalizeMaterializedValues_valuesConsistent table result.context hcore.2.1)
      (canonicalizeMaterializedValues_startTableAgrees table result.context)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_directDetailedBoundaryWitnessUsesOrdinal_le_ordinalRisk
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
    (hterminalZero : ∀ nextContext remaining value nextCandidates,
      ¬ordinal < nextCandidates.length →
      Pr[WitnessUsesOrdinal ordinal |
          observe nextContext remaining value nextCandidates] ≤ 0)
    (hterminalMatch : ∀ candidate nextContext remaining value nextCandidates,
      nextContext.ValuesConsistent → StartTableAgrees nextContext.state table →
      Pr[PrivateWitnessPlanMatchesCandidate candidate |
          observe nextContext remaining value nextCandidates] ≤
        Pr[fun hit : Bool => hit = true | privateCandidateFire candidate nextContext])
    (hterminalPrefix : ∀ nextContext remaining value nextCandidates output,
      output ∈ support (observe nextContext remaining value nextCandidates) →
      PrivateWitnessPlanExtends nextCandidates output) :
    Pr[WitnessUsesOrdinal ordinal |
        directDetailedBoundaryNormalizedPrivateWitnessPlanObserve parameter root ftsSecret
          computation observe candidates context fuel table cache] ≤
      Pr[fun hit : Bool => hit = true |
        directDetailedBoundaryPrivateOrdinalRisk ordinal parameter root ftsSecret computation
          candidates context fuel table cache] := by
  induction computation using OracleComp.inductionOn generalizing
      candidates context fuel cache with
  | pure value =>
      rw [directDetailedBoundaryNormalizedPrivateWitnessPlanObserve,
        OracleComp.construct_pure, directDetailedBoundaryPrivateOrdinalRisk,
        OracleComp.construct_pure]
      simp only [hnotSelected, ↓reduceDIte]
      simpa using hterminalZero context fuel (value, cache) candidates hnotSelected
  | query_bind query next ih =>
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              rw [directDetailedBoundaryNormalizedPrivateWitnessPlanObserve,
                OracleComp.construct_query_bind, directDetailedBoundaryPrivateOrdinalRisk,
                OracleComp.construct_query_bind]
              simp only [hnotSelected, ↓reduceDIte]
              apply probEvent_unselectedDirectWitnessStep_le_ordinalRisk ordinal _ _ candidates
                context fuel table ((splitUniformImpl n).run cache) hnotSelected
              intro result hresult
              have hcore := resolvedCore_of_done_mem_runDirectResolvedWitnessFromTable
                ((splitUniformImpl n).run cache) context fuel table result hconsistent hstarts
                hresult
              exact ih result.value.1 candidates
                (canonicalizeMaterializedValues table result.context) result.remaining
                result.value.2 hnotSelected
                (canonicalizeMaterializedValues_valuesConsistent table result.context hcore.2.1)
                (canonicalizeMaterializedValues_startTableAgrees table result.context)
          | inr input =>
              rw [directDetailedBoundaryNormalizedPrivateWitnessPlanObserve,
                OracleComp.construct_query_bind, directDetailedBoundaryPrivateOrdinalRisk,
                OracleComp.construct_query_bind]
              simp only [hnotSelected, ↓reduceDIte]
              apply probEvent_hashBranchWitnessUsesOrdinal_le_ordinalRisk ordinal parameter root
                ftsSecret input next observe candidates context fuel table cache hnotSelected
                hconsistent hstarts
              · intro output nextCandidates nextContext remaining nextCache hnextNotSelected
                  hnextConsistent hnextStarts
                exact ih output nextCandidates nextContext remaining nextCache hnextNotSelected
                  hnextConsistent hnextStarts
              · exact hterminalMatch
              · exact hterminalPrefix
      | inr message =>
          rw [directDetailedBoundaryNormalizedPrivateWitnessPlanObserve,
            OracleComp.construct_query_bind, directDetailedBoundaryPrivateOrdinalRisk,
            OracleComp.construct_query_bind]
          simp only [hnotSelected, ↓reduceDIte]
          apply probEvent_unselectedDirectWitnessStep_le_ordinalRisk ordinal _ _ candidates
            context fuel table ((maskedSign parameter root ftsSecret message).run cache)
            hnotSelected
          intro result hresult
          have hcore := resolvedCore_of_done_mem_runDirectResolvedWitnessFromTable
            ((maskedSign parameter root ftsSecret message).run cache)
            context fuel table result hconsistent hstarts hresult
          exact ih result.value.1 candidates
            (canonicalizeMaterializedValues table result.context) result.remaining
            result.value.2 hnotSelected
            (canonicalizeMaterializedValues_valuesConsistent table result.context hcore.2.1)
            (canonicalizeMaterializedValues_startTableAgrees table result.context)

theorem probEvent_retainedFinalizationWitnessUsesOrdinal_le_zero
    (table : OtsSecretIndex → HashOutput) (root : Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : RetainedRestResult × SplitHashCache) (candidates : List Probe)
    (ordinal : Nat) (hnotSelected : ¬ordinal < candidates.length) :
    Pr[WitnessUsesOrdinal ordinal |
        retainedResolvedFinalizationPrivateWitnessPlanObserve table root context fuel value
          candidates] ≤ 0 := by
  unfold retainedResolvedFinalizationPrivateWitnessPlanObserve
  by_cases hhit : PrivateStructuralHit context
  · simp only [hhit, ↓reduceDIte]
    have hnone : ¬WitnessUsesOrdinal ordinal
        (some (privateHitWitnessOf context hhit), candidates) :=
      not_witnessUsesOrdinal_of_not_lt_length ordinal _ hnotSelected
    simp [hnone]
  · simp only [hhit, ↓reduceDIte]
    have hnone : ¬WitnessUsesOrdinal ordinal
        ((none, candidates) : PrivateWitnessPlanOutput) :=
      not_witnessUsesOrdinal_of_not_lt_length ordinal _ hnotSelected
    simp [hnone]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_granularDetailedRetainedRestWitnessUsesOrdinal_le_ordinalRisk
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (ordinal : Nat) (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (candidates : List Probe)
    (hnotSelected : ¬ordinal < candidates.length)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table) :
    Pr[WitnessUsesOrdinal ordinal |
        granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve adversary parameter table
          ftsSecret context fuel value candidates] ≤
      Pr[fun hit : Bool => hit = true |
        granularDetailedRetainedRestPrivateOrdinalRisk adversary parameter table ftsSecret
          ordinal context fuel value candidates] := by
  unfold granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve
    granularDetailedRetainedRestPrivateOrdinalRisk
  apply probEvent_directDetailedBoundaryWitnessUsesOrdinal_le_ordinalRisk ordinal parameter
    value.1 ftsSecret (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
    (retainedResolvedFinalizationPrivateWitnessPlanObserve table value.1)
    candidates context fuel table value.2 hnotSelected hconsistent hstarts
  · intro nextContext remaining nextValue nextCandidates hnextNotSelected
    exact probEvent_retainedFinalizationWitnessUsesOrdinal_le_zero table value.1 nextContext
      remaining nextValue nextCandidates ordinal hnextNotSelected
  · intro candidate nextContext remaining nextValue nextCandidates _hnextConsistent
      _hnextStarts
    exact probEvent_retainedResolvedFinalizationPrivateWitnessPlanMatchesCandidate_le table
      value.1 candidate nextContext remaining nextValue nextCandidates
  · intro nextContext remaining nextValue nextCandidates output houtput
    exact privateWitnessPlanExtends_of_mem_retainedResolvedFinalizationPrivateWitnessPlanObserve
      table value.1 nextContext remaining nextValue nextCandidates output houtput

end SphincsSecurity.Concrete.OtsProbeSimulation
