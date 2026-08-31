import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateHindsight

/-!
# Fixed-list outer induction

Incompatible candidate prefixes have zero gated risk without state invariants. Compatible prefixes are dominated by guarded preparation.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable

theorem probEvent_decide_planHit_eq
    (finalCandidates : List Probe) (run : ProbComp (Bool × List Probe)) :
    Pr[fun output => decide (PlanHitAt finalCandidates output) = true | run] =
      Pr[PlanHitAt finalCandidates | run] :=
  OracleComp.probEvent_congr' (fun output _ => by simp) rfl

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_directDetailedBoundaryNormalizedPlanHitObserve_eq_zero_of_not_prefix
    (finalCandidates : List Probe)
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) →
      List Probe → ProbComp (Bool × List Probe))
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hnotPrefix : ¬candidates.IsPrefix finalCandidates)
    (hterminalZero : ∀ nextContext remaining value currentCandidates,
      ¬currentCandidates.IsPrefix finalCandidates →
      Pr[PlanHitAt finalCandidates |
          observe nextContext remaining value currentCandidates] = 0) :
    Pr[= true | directDetailedBoundaryNormalizedPlanHitObserve finalCandidates parameter root
      ftsSecret computation observe candidates context fuel table cache] = 0 := by
  induction computation using OracleComp.inductionOn generalizing candidates context fuel cache with
  | pure value =>
      rw [directDetailedBoundaryNormalizedPlanHitObserve, OracleComp.construct_pure,
        ← probEvent_eq_eq_probOutput, probEvent_map]
      change Pr[fun output => decide (PlanHitAt finalCandidates output) = true |
          observe context fuel (value, cache) candidates] = 0
      rw [probEvent_decide_planHit_eq]
      exact hterminalZero context fuel (value, cache) candidates hnotPrefix
  | query_bind query next ih =>
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              rw [directDetailedBoundaryNormalizedPlanHitObserve,
                OracleComp.construct_query_bind]
              apply probEvent_runDirectDetailedPlanHitObserve_eq_zero finalCandidates candidates
              · exact fun heq => hnotPrefix (heq ▸ by simp)
              · intro result _hresult
                apply probEvent_canonicalizeDirectDetailedPlanHitObserve_eq_zero table
                  finalCandidates candidates
                · exact fun heq => hnotPrefix (heq ▸ by simp)
                · dsimp only
                  intro _hprivate _hcompletable
                  exact ih result.value.1 candidates
                    (canonicalizeMaterializedValues table result.context) result.remaining
                    result.value.2 hnotPrefix
          | inr input =>
              rw [directDetailedBoundaryNormalizedPlanHitObserve,
                OracleComp.construct_query_bind]
              let plan := purePlanProbingHashQuery parameter input context.state
              let nextCandidates := appendPlannedCandidate candidates plan.candidate?
              have hcurrentPrefix : candidates.IsPrefix nextCandidates := by
                unfold nextCandidates appendPlannedCandidate
                cases plan.candidate? <;> simp
              have hnextNotPrefix : ¬nextCandidates.IsPrefix finalCandidates := fun hnext =>
                hnotPrefix (hcurrentPrefix.trans hnext)
              apply probEvent_runDirectDetailedPlanHitObserve_eq_zero finalCandidates
                nextCandidates
              · exact fun heq => hnextNotPrefix (heq ▸ by simp)
              · intro result _hresult
                apply probEvent_canonicalizeDirectDetailedPlanHitObserve_eq_zero table
                  finalCandidates nextCandidates
                · exact fun heq => hnextNotPrefix (heq ▸ by simp)
                · dsimp only
                  intro _hprivate _hcompletable
                  exact ih result.value.1 nextCandidates
                    (canonicalizeMaterializedValues table result.context) result.remaining
                    result.value.2 hnextNotPrefix
      | inr message =>
          rw [directDetailedBoundaryNormalizedPlanHitObserve,
            OracleComp.construct_query_bind]
          apply probEvent_runDirectDetailedPlanHitObserve_eq_zero finalCandidates candidates
          · exact fun heq => hnotPrefix (heq ▸ by simp)
          · intro result _hresult
            apply probEvent_canonicalizeDirectDetailedPlanHitObserve_eq_zero table
              finalCandidates candidates
            · exact fun heq => hnotPrefix (heq ▸ by simp)
            · dsimp only
              intro _hprivate _hcompletable
              exact ih result.value.1 candidates
                (canonicalizeMaterializedValues table result.context) result.remaining
                result.value.2 hnotPrefix

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem probEvent_directDetailedBoundaryNormalizedPlanHitObserve_le_guarded
    (finalCandidates : List Probe)
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) →
      List Probe → ProbComp (Bool × List Probe))
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hprefix : candidates.IsPrefix finalCandidates)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hpublished : PublishedValues context.state)
    (hcovered : PendingCoveredBy finalCandidates context)
    (hterminalLe : ∀ nextContext remaining value currentCandidates,
      currentCandidates.IsPrefix finalCandidates → nextContext.ValuesConsistent →
      StartTableAgrees nextContext.state table → PublishedValues nextContext.state →
      PendingCoveredBy finalCandidates nextContext →
      Pr[PlanHitAt finalCandidates |
          observe nextContext remaining value currentCandidates] ≤
        Pr[= true | guardedPreparationObserve finalCandidates nextContext])
    (hterminalZero : ∀ nextContext remaining value currentCandidates,
      ¬currentCandidates.IsPrefix finalCandidates →
      Pr[PlanHitAt finalCandidates |
          observe nextContext remaining value currentCandidates] = 0) :
    Pr[= true | directDetailedBoundaryNormalizedPlanHitObserve finalCandidates parameter root
      ftsSecret computation observe candidates context fuel table cache] ≤
      Pr[= true | guardedPreparationObserve finalCandidates context] := by
  induction computation using OracleComp.inductionOn generalizing candidates context fuel cache with
  | pure value =>
      rw [directDetailedBoundaryNormalizedPlanHitObserve, OracleComp.construct_pure,
        ← probEvent_eq_eq_probOutput, probEvent_map]
      change Pr[fun output => decide (PlanHitAt finalCandidates output) = true |
          observe context fuel (value, cache) candidates] ≤ _
      rw [probEvent_decide_planHit_eq]
      exact hterminalLe context fuel (value, cache) candidates hprefix hconsistent hstarts
        hpublished hcovered
  | query_bind query next ih =>
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              rw [directDetailedBoundaryNormalizedPlanHitObserve,
                OracleComp.construct_query_bind]
              let inner := (splitUniformImpl n).run cache
              have hprobeBound : inner.IsQueryBoundP (IsUncoveredProbe finalCandidates) 0 :=
                OracleComp.IsQueryBoundP.of_imp (isUncoveredProbe_imp_isProbe finalCandidates)
                  (splitUniformImpl_probeFree n cache)
              apply probEvent_runDirectDetailedPlanHitObserve_le_guarded finalCandidates
                candidates _ context fuel table inner hcovered hprobeBound
              intro result hresult
              have hdirect := mem_support_runDirectResolvedFromTable_of_done_detailed inner
                context fuel table result hresult
              have hcore := resolvedCore_of_mem_runDirectResolvedFromTable inner context fuel table
                result hconsistent hstarts hdirect
              have hnextPublished := publishedValues_of_done_runDirectResolvedDetailedFromTable
                (splitUniformImpl n) (preservesPublishedValuesImpl_splitUniformImpl n)
                context fuel table cache result hpublished hresult
              have hnextCovered := pendingCoveredBy_of_done_runDirectResolvedDetailedFromTable
                finalCandidates inner context fuel table result hcovered hprobeBound hresult
              apply probEvent_canonicalizeDirectDetailedPlanHitObserve_le_guarded table
                finalCandidates candidates
                (observe := fun nextContext remaining value =>
                  directDetailedBoundaryNormalizedPlanHitObserve finalCandidates parameter root
                    ftsSecret (next value.1) observe candidates nextContext remaining table value.2)
                result.context result.remaining result.value hcore.2.1 hnextPublished hnextCovered
              dsimp only
              intro _hprivate _hcompletable
              exact ih result.value.1 candidates
                (canonicalizeMaterializedValues table result.context) result.remaining
                result.value.2 hprefix
                (canonicalizeMaterializedValues_valuesConsistent table result.context hcore.2.1)
                (canonicalizeMaterializedValues_startTableAgrees table result.context)
                hnextPublished.to_canonicalizedMaterializedValues
                ((pendingCoveredBy_canonicalize_iff table finalCandidates result.context).2
                  hnextCovered)
          | inr input =>
              rw [directDetailedBoundaryNormalizedPlanHitObserve,
                OracleComp.construct_query_bind]
              let plan := purePlanProbingHashQuery parameter input context.state
              let nextCandidates := appendPlannedCandidate candidates plan.candidate?
              by_cases hnextPrefix : nextCandidates.IsPrefix finalCandidates
              · have hplanMem : ∀ candidate, plan.candidate? = some candidate →
                    candidate ∈ finalCandidates := by
                  intro candidate hcandidate
                  apply hnextPrefix.subset
                  simp [nextCandidates, appendPlannedCandidate, hcandidate]
                let inner := (probingHashQueryAfterPlan parameter input plan).run cache
                have hprobeBound := probingHashQueryAfterPlan_probeBound parameter input plan
                  finalCandidates hplanMem cache
                apply probEvent_runDirectDetailedPlanHitObserve_le_guarded finalCandidates
                  nextCandidates _ context fuel table inner hcovered hprobeBound
                intro result hresult
                have hdirect := mem_support_runDirectResolvedFromTable_of_done_detailed inner
                  context fuel table result hresult
                have hcore := resolvedCore_of_mem_runDirectResolvedFromTable inner context fuel table
                  result hconsistent hstarts hdirect
                have hnextPublished := publishedValues_of_done_runDirectResolvedDetailedFromTable
                  (probingHashQueryAfterPlan parameter input plan)
                  (preservesPublishedValues_probingHashQueryAfterPlan parameter input plan)
                  context fuel table cache result hpublished hresult
                have hnextCovered := pendingCoveredBy_of_done_runDirectResolvedDetailedFromTable
                  finalCandidates inner context fuel table result hcovered hprobeBound hresult
                apply probEvent_canonicalizeDirectDetailedPlanHitObserve_le_guarded table
                  finalCandidates nextCandidates
                  (observe := fun nextContext remaining value =>
                    directDetailedBoundaryNormalizedPlanHitObserve finalCandidates parameter root
                      ftsSecret (next value.1) observe nextCandidates nextContext remaining table
                        value.2)
                  result.context result.remaining result.value hcore.2.1 hnextPublished hnextCovered
                dsimp only
                intro _hprivate _hcompletable
                exact ih result.value.1 nextCandidates
                  (canonicalizeMaterializedValues table result.context) result.remaining
                  result.value.2 hnextPrefix
                  (canonicalizeMaterializedValues_valuesConsistent table result.context hcore.2.1)
                  (canonicalizeMaterializedValues_startTableAgrees table result.context)
                  hnextPublished.to_canonicalizedMaterializedValues
                  ((pendingCoveredBy_canonicalize_iff table finalCandidates result.context).2
                    hnextCovered)
              · have hzero :=
                  probEvent_runDirectDetailedPlanHitObserve_eq_zero finalCandidates nextCandidates
                    (fun nextContext remaining value =>
                      canonicalizeDirectDetailedPlanHitObserve table finalCandidates nextCandidates
                        (fun finalContext finalRemaining finalValue =>
                          directDetailedBoundaryNormalizedPlanHitObserve finalCandidates parameter
                            root ftsSecret (next finalValue.1) observe nextCandidates finalContext
                            finalRemaining table finalValue.2)
                        nextContext remaining value)
                    context fuel table ((probingHashQueryAfterPlan parameter input plan).run cache)
                    (fun heq => hnextPrefix (heq ▸ by simp)) (by
                      intro result _hresult
                      apply probEvent_canonicalizeDirectDetailedPlanHitObserve_eq_zero table
                        finalCandidates nextCandidates
                      · exact fun heq => hnextPrefix (heq ▸ by simp)
                      · dsimp only
                        intro _hprivate _hcompletable
                        exact probEvent_directDetailedBoundaryNormalizedPlanHitObserve_eq_zero_of_not_prefix
                          finalCandidates parameter root ftsSecret (next result.value.1) observe
                          nextCandidates (canonicalizeMaterializedValues table result.context)
                          result.remaining table result.value.2 hnextPrefix hterminalZero)
                exact hzero.le.trans zero_le
      | inr message =>
          rw [directDetailedBoundaryNormalizedPlanHitObserve,
            OracleComp.construct_query_bind]
          let inner := (maskedSign parameter root ftsSecret message).run cache
          have hprobeBound : inner.IsQueryBoundP (IsUncoveredProbe finalCandidates) 0 :=
            OracleComp.IsQueryBoundP.of_imp (isUncoveredProbe_imp_isProbe finalCandidates)
              (maskedSign_probeFree parameter root ftsSecret message cache)
          apply probEvent_runDirectDetailedPlanHitObserve_le_guarded finalCandidates candidates _
            context fuel table inner hcovered hprobeBound
          intro result hresult
          have hdirect := mem_support_runDirectResolvedFromTable_of_done_detailed inner context
            fuel table result hresult
          have hcore := resolvedCore_of_mem_runDirectResolvedFromTable inner context fuel table
            result hconsistent hstarts hdirect
          have hnextPublished := publishedValues_of_done_runDirectResolvedDetailedFromTable
            (maskedSign parameter root ftsSecret message)
            (preservesPublishedValues_maskedSign parameter root ftsSecret message)
            context fuel table cache result hpublished hresult
          have hnextCovered := pendingCoveredBy_of_done_runDirectResolvedDetailedFromTable
            finalCandidates inner context fuel table result hcovered hprobeBound hresult
          apply probEvent_canonicalizeDirectDetailedPlanHitObserve_le_guarded table
            finalCandidates candidates
            (observe := fun nextContext remaining value =>
              directDetailedBoundaryNormalizedPlanHitObserve finalCandidates parameter root
                ftsSecret (next value.1) observe candidates nextContext remaining table value.2)
            result.context result.remaining result.value hcore.2.1 hnextPublished hnextCovered
          dsimp only
          intro _hprivate _hcompletable
          exact ih result.value.1 candidates
            (canonicalizeMaterializedValues table result.context) result.remaining result.value.2
            hprefix (canonicalizeMaterializedValues_valuesConsistent table result.context hcore.2.1)
            (canonicalizeMaterializedValues_startTableAgrees table result.context)
            hnextPublished.to_canonicalizedMaterializedValues
            ((pendingCoveredBy_canonicalize_iff table finalCandidates result.context).2
              hnextCovered)

theorem probEvent_retainedResolvedFinalizationPrivatePlanObserve_planHit_le_guarded
    (table : OtsSecretIndex → HashOutput) (root : Digest)
    (finalCandidates currentCandidates : List Probe)
    (context : DeferredContext) (fuel : Nat)
    (value : RetainedRestResult × SplitHashCache)
    (hprefix : currentCandidates.IsPrefix finalCandidates)
    (hcovered : PendingCoveredBy finalCandidates context) :
    Pr[PlanHitAt finalCandidates |
        retainedResolvedFinalizationPrivatePlanObserve table root context fuel value
          currentCandidates] ≤
      Pr[= true | guardedPreparationObserve finalCandidates context] := by
  by_cases heq : currentCandidates = finalCandidates
  · subst currentCandidates
    by_cases hprivate : PrivateStructuralHit context
    · unfold retainedResolvedFinalizationPrivatePlanObserve
        retainedResolvedFinalizationPrivateObserve classifyDirectPrivateObserve
      simp only [hprivate, ↓reduceIte, pure_bind, probEvent_pure, PlanHitAt, and_self,
        ]
      have htrue := evalDist_guardedPreparationObserve_eq_true_of_privateStructuralHit
        finalCandidates context hcovered hprivate
      have hrawTrue : evalDist (guardedPreparationObserve finalCandidates context) =
          evalDist (pure true : ProbComp Bool) := htrue
      apply le_of_eq
      calc
        (1 : ℝ≥0∞) = Pr[= true | (pure true : ProbComp Bool)] := by simp
        _ = _ := OracleComp.probOutput_congr rfl hrawTrue.symm
    · simp [retainedResolvedFinalizationPrivatePlanObserve,
        retainedResolvedFinalizationPrivateObserve, classifyDirectPrivateObserve,
        hprivate, PlanHitAt]
  · unfold retainedResolvedFinalizationPrivatePlanObserve
      retainedResolvedFinalizationPrivateObserve classifyDirectPrivateObserve
    by_cases hprivate : PrivateStructuralHit context <;>
      simp [hprivate, PlanHitAt, heq]

theorem probEvent_retainedResolvedFinalizationPrivatePlanObserve_planHit_eq_zero
    (table : OtsSecretIndex → HashOutput) (root : Digest)
    (finalCandidates currentCandidates : List Probe)
    (context : DeferredContext) (fuel : Nat)
    (value : RetainedRestResult × SplitHashCache)
    (hnotPrefix : ¬currentCandidates.IsPrefix finalCandidates) :
    Pr[PlanHitAt finalCandidates |
        retainedResolvedFinalizationPrivatePlanObserve table root context fuel value
          currentCandidates] = 0 := by
  have hne : currentCandidates ≠ finalCandidates := fun heq =>
    hnotPrefix (heq ▸ by simp)
  unfold retainedResolvedFinalizationPrivatePlanObserve
    retainedResolvedFinalizationPrivateObserve classifyDirectPrivateObserve
  by_cases hprivate : PrivateStructuralHit context <;>
    simp [hprivate, PlanHitAt, hne]

theorem probEvent_granularDetailedRetainedRestNormalizedPlanHitObserve_le_guarded
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (finalCandidates currentCandidates : List Probe)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache)
    (hprefix : currentCandidates.IsPrefix finalCandidates)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hpublished : PublishedValues context.state)
    (hcovered : PendingCoveredBy finalCandidates context) :
    Pr[= true | directDetailedBoundaryNormalizedPlanHitObserve finalCandidates parameter
        value.1 ftsSecret (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
        (retainedResolvedFinalizationPrivatePlanObserve table value.1)
        currentCandidates context fuel table value.2] ≤
      Pr[= true | guardedPreparationObserve finalCandidates context] := by
  apply probEvent_directDetailedBoundaryNormalizedPlanHitObserve_le_guarded finalCandidates
    parameter value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
    (retainedResolvedFinalizationPrivatePlanObserve table value.1)
    currentCandidates context fuel table value.2 hprefix hconsistent hstarts hpublished hcovered
  · intro nextContext remaining nextValue nextCandidates hnextPrefix _hnextConsistent
      _hnextStarts _hnextPublished hnextCovered
    exact probEvent_retainedResolvedFinalizationPrivatePlanObserve_planHit_le_guarded table
      value.1 finalCandidates nextCandidates nextContext remaining nextValue hnextPrefix
      hnextCovered
  · intro nextContext remaining nextValue nextCandidates hnextNotPrefix
    exact probEvent_retainedResolvedFinalizationPrivatePlanObserve_planHit_eq_zero table value.1
      finalCandidates nextCandidates nextContext remaining nextValue hnextNotPrefix

theorem probEvent_granularDetailedRetainedRestNormalized_planHit_le_guarded
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (finalCandidates currentCandidates : List Probe)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache)
    (hprefix : currentCandidates.IsPrefix finalCandidates)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hpublished : PublishedValues context.state)
    (hcovered : PendingCoveredBy finalCandidates context) :
    Pr[PlanHitAt finalCandidates |
        granularDetailedRetainedRestNormalizedPrivatePlanObserve adversary parameter table
          ftsSecret context fuel value currentCandidates] ≤
      Pr[= true | guardedPreparationObserve finalCandidates context] := by
  unfold granularDetailedRetainedRestNormalizedPrivatePlanObserve
  calc
    _ = Pr[= true | directDetailedBoundaryNormalizedPlanHitObserve finalCandidates parameter
          value.1 ftsSecret (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
          (retainedResolvedFinalizationPrivatePlanObserve table value.1)
          currentCandidates context fuel table value.2] :=
      probEvent_planHit_directDetailedBoundaryNormalizedPrivatePlanObserve_eq finalCandidates
        parameter value.1 ftsSecret
        (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
        (retainedResolvedFinalizationPrivatePlanObserve table value.1)
        currentCandidates context fuel table value.2
    _ ≤ _ := probEvent_granularDetailedRetainedRestNormalizedPlanHitObserve_le_guarded
      adversary parameter table ftsSecret finalCandidates currentCandidates context fuel value
      hprefix hconsistent hstarts hpublished hcovered

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem preservesPublishedValues_maskedPublishedTreeRoot :
    PreservesPublishedValues maskedPublishedTreeRoot := by
  unfold maskedPublishedTreeRoot
  apply (preservesPublishedValues_ensureTreeNode topLayer rootTree
    (layerHeight topLayer) 0).bind
  intro _
  exact preservesPublishedValues_revealPublishedCoordinate
    (.position (.node topLayer rootTree
      ⟨layerHeight topLayer - 1, by norm_num [layerHeight, topLayer, maxLayerHeight]⟩ 0))

end SphincsSecurity.Concrete.OtsProbeSimulation
