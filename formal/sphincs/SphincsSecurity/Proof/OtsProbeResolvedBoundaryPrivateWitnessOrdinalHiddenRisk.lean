import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalHiddenPrefix

/-!
# Hidden ordinal prefix risk

This is the sound prefix endpoint. It follows the normalized execution until a fixed ordinal is
selected and then tests only the hidden candidate risk. Earlier stops and termination before the
ordinal contribute zero.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable

noncomputable def directDetailedBoundaryPrivateOrdinalHiddenRisk
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
        hiddenPrivateCandidateFire (candidates.get ⟨ordinal, hselected⟩) context
      else
        pure false)
    (fun query _next recursivelyRun candidates context fuel table cache =>
      if hselected : ordinal < candidates.length then
        hiddenPrivateCandidateFire (candidates.get ⟨ordinal, hselected⟩) context
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
              hiddenPrivateCandidateFire
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

noncomputable def granularDetailedRetainedRestPrivateOrdinalHiddenRisk
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (ordinal : Nat) (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (candidates : List Probe) : ProbComp Bool :=
  directDetailedBoundaryPrivateOrdinalHiddenRisk ordinal parameter value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
    candidates context fuel table value.2

theorem directDetailedBoundaryPrivateOrdinalHiddenRisk_eq_fire_of_selected
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hselected : ordinal < candidates.length) :
    directDetailedBoundaryPrivateOrdinalHiddenRisk ordinal parameter root ftsSecret computation
        candidates context fuel table cache =
      hiddenPrivateCandidateFire (candidates.get ⟨ordinal, hselected⟩) context := by
  induction computation using OracleComp.inductionOn generalizing candidates context fuel cache with
  | pure value =>
      rw [directDetailedBoundaryPrivateOrdinalHiddenRisk, OracleComp.construct_pure]
      simp only [hselected, ↓reduceDIte]
  | query_bind query next ih =>
      rw [directDetailedBoundaryPrivateOrdinalHiddenRisk, OracleComp.construct_query_bind]
      simp only [hselected, ↓reduceDIte]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_hashBranchWitnessUsesOrdinal_le_hiddenRisk
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
      Pr[WitnessUsesOrdinal ordinal |
          directDetailedBoundaryNormalizedPrivateWitnessPlanObserve parameter root ftsSecret
            (next output) observe nextCandidates nextContext remaining table nextCache] ≤
        Pr[fun hit : Bool => hit = true |
          directDetailedBoundaryPrivateOrdinalHiddenRisk ordinal parameter root ftsSecret
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
          hiddenPrivateCandidateFire (nextCandidates.get ⟨ordinal, hselected⟩) context
        else
          runDirectResolvedWitnessFromTable context fuel table
              ((probingHashQueryAfterPlan parameter input plan).run cache) >>=
            finishDirectWitnessOrdinalRisk
              (canonicalizeDirectWitnessOrdinalRisk table
                (fun nextContext remaining value laterCandidates =>
                  directDetailedBoundaryPrivateOrdinalHiddenRisk ordinal parameter root ftsSecret
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
    have hbound := probEvent_selectedHashPlanWitnessUsesOrdinal_le_hidden parameter root ftsSecret
      input next observe candidates context fuel table cache candidate hconsistent hstarts
      hpublished
      (by
        intro nextContext remaining value laterCandidates hnextConsistent hnextStarts
          hnextPublished
        exact hterminalMatch candidate nextContext remaining value laterCandidates hnextConsistent
          hnextStarts hnextPublished)
      hterminalPrefix
    simpa only [nextCandidates, hcandidate, appendPlannedCandidate, plan] using hbound
  · rw [dif_neg hnextSelected]
    apply probEvent_unselectedDirectWitnessStep_le_ordinalRisk ordinal _ _ nextCandidates
      context fuel table ((probingHashQueryAfterPlan parameter input plan).run cache)
      hnextSelected
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
theorem probEvent_directDetailedBoundaryWitnessUsesOrdinal_le_hiddenRisk
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
      Pr[WitnessUsesOrdinal ordinal |
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
    Pr[WitnessUsesOrdinal ordinal |
        directDetailedBoundaryNormalizedPrivateWitnessPlanObserve parameter root ftsSecret
          computation observe candidates context fuel table cache] ≤
      Pr[fun hit : Bool => hit = true |
        directDetailedBoundaryPrivateOrdinalHiddenRisk ordinal parameter root ftsSecret computation
          candidates context fuel table cache] := by
  induction computation using OracleComp.inductionOn generalizing
      candidates context fuel cache with
  | pure value =>
      rw [directDetailedBoundaryNormalizedPrivateWitnessPlanObserve,
        OracleComp.construct_pure, directDetailedBoundaryPrivateOrdinalHiddenRisk,
        OracleComp.construct_pure]
      simp only [hnotSelected, ↓reduceDIte]
      simpa using hterminalZero context fuel (value, cache) candidates hnotSelected
  | query_bind query next ih =>
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              rw [directDetailedBoundaryNormalizedPrivateWitnessPlanObserve,
                OracleComp.construct_query_bind, directDetailedBoundaryPrivateOrdinalHiddenRisk,
                OracleComp.construct_query_bind]
              simp only [hnotSelected, ↓reduceDIte]
              let inner := (splitUniformImpl n).run cache
              apply probEvent_unselectedDirectWitnessStep_le_ordinalRisk ordinal _ _ candidates
                context fuel table inner hnotSelected
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
                OracleComp.construct_query_bind, directDetailedBoundaryPrivateOrdinalHiddenRisk,
                OracleComp.construct_query_bind]
              simp only [hnotSelected, ↓reduceDIte]
              apply probEvent_hashBranchWitnessUsesOrdinal_le_hiddenRisk ordinal parameter root
                ftsSecret input next observe candidates context fuel table cache hnotSelected
                hconsistent hstarts hpublished
              · intro output nextCandidates nextContext remaining nextCache hnextNotSelected
                  hnextConsistent hnextStarts hnextPublished
                exact ih output nextCandidates nextContext remaining nextCache hnextNotSelected
                  hnextConsistent hnextStarts hnextPublished
              · exact hterminalMatch
              · exact hterminalPrefix
      | inr message =>
          rw [directDetailedBoundaryNormalizedPrivateWitnessPlanObserve,
            OracleComp.construct_query_bind, directDetailedBoundaryPrivateOrdinalHiddenRisk,
            OracleComp.construct_query_bind]
          simp only [hnotSelected, ↓reduceDIte]
          let inner := (maskedSign parameter root ftsSecret message).run cache
          apply probEvent_unselectedDirectWitnessStep_le_ordinalRisk ordinal _ _ candidates
            context fuel table inner hnotSelected
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
theorem probEvent_granularDetailedRetainedRestWitnessUsesOrdinal_le_hiddenRisk
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (ordinal : Nat) (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (candidates : List Probe)
    (hnotSelected : ¬ordinal < candidates.length)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hpublished : PublishedValues context.state) :
    Pr[WitnessUsesOrdinal ordinal |
        granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve adversary parameter table
          ftsSecret context fuel value candidates] ≤
      Pr[fun hit : Bool => hit = true |
        granularDetailedRetainedRestPrivateOrdinalHiddenRisk adversary parameter table ftsSecret
          ordinal context fuel value candidates] := by
  unfold granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve
    granularDetailedRetainedRestPrivateOrdinalHiddenRisk
  apply probEvent_directDetailedBoundaryWitnessUsesOrdinal_le_hiddenRisk ordinal parameter value.1
    ftsSecret (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
    (retainedResolvedFinalizationPrivateWitnessPlanObserve table value.1)
    candidates context fuel table value.2 hnotSelected hconsistent hstarts hpublished
  · intro nextContext remaining nextValue nextCandidates hnextNotSelected
    exact probEvent_retainedFinalizationWitnessUsesOrdinal_le_zero table value.1 nextContext
      remaining nextValue nextCandidates ordinal hnextNotSelected
  · intro candidate nextContext remaining nextValue nextCandidates _hnextConsistent
      _hnextStarts hnextPublished
    exact probEvent_retainedResolvedFinalizationPrivateWitnessPlanMatchesCandidate_le_hidden table
      value.1 candidate nextContext remaining nextValue nextCandidates hnextPublished
  · intro nextContext remaining nextValue nextCandidates output houtput
    exact privateWitnessPlanExtends_of_mem_retainedResolvedFinalizationPrivateWitnessPlanObserve
      table value.1 nextContext remaining nextValue nextCandidates output houtput

end SphincsSecurity.Concrete.OtsProbeSimulation
