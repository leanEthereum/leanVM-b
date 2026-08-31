import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalHiddenMatchLift

/-!
# Hidden fixed-candidate outer continuation

The hidden matching observer is lifted through every normalized outer query. Completed direct
steps preserve publication, so canonicalization may recurse with the same hidden gate.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_directDetailedBoundaryNormalizedPrivateWitnessPlanMatchesCandidate_le_hidden
    (candidate : Probe) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) →
      List Probe → ProbComp PrivateWitnessPlanOutput)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hpublished : PublishedValues context.state)
    (hterminal : ∀ nextContext remaining value nextCandidates,
      nextContext.ValuesConsistent → StartTableAgrees nextContext.state table →
      PublishedValues nextContext.state →
      Pr[PrivateWitnessPlanMatchesCandidate candidate |
          observe nextContext remaining value nextCandidates] ≤
        Pr[fun hit : Bool => hit = true |
          hiddenPrivateCandidateFire candidate nextContext]) :
    Pr[PrivateWitnessPlanMatchesCandidate candidate |
        directDetailedBoundaryNormalizedPrivateWitnessPlanObserve parameter root ftsSecret
          computation observe candidates context fuel table cache] ≤
      Pr[fun hit : Bool => hit = true |
        hiddenPrivateCandidateFire candidate context] := by
  induction computation using OracleComp.inductionOn generalizing candidates context fuel cache with
  | pure value =>
      rw [directDetailedBoundaryNormalizedPrivateWitnessPlanObserve,
        OracleComp.construct_pure]
      exact hterminal context fuel (value, cache) candidates hconsistent hstarts hpublished
  | query_bind query next ih =>
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              rw [directDetailedBoundaryNormalizedPrivateWitnessPlanObserve,
                OracleComp.construct_query_bind]
              let inner := (splitUniformImpl n).run cache
              apply probEvent_runDirectWitnessPlanMatchesCandidate_le_hidden candidate _
                candidates context fuel table inner hpublished
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
              apply probEvent_canonicalizeDirectWitnessPlanMatchesCandidate_le_hidden table
                candidate _ result.context result.remaining result.value candidates hcore.2.1
                hnextPublished
              dsimp only
              intro _hprivate _hcompletable
              exact ih result.value.1 candidates
                (canonicalizeMaterializedValues table result.context) result.remaining
                result.value.2
                (canonicalizeMaterializedValues_valuesConsistent table result.context hcore.2.1)
                (canonicalizeMaterializedValues_startTableAgrees table result.context)
                hnextPublished.to_canonicalizedMaterializedValues
          | inr input =>
              rw [directDetailedBoundaryNormalizedPrivateWitnessPlanObserve,
                OracleComp.construct_query_bind]
              let plan := purePlanProbingHashQuery parameter input context.state
              let nextCandidates := appendPlannedCandidate candidates plan.candidate?
              let inner := (probingHashQueryAfterPlan parameter input plan).run cache
              apply probEvent_runDirectWitnessPlanMatchesCandidate_le_hidden candidate _
                nextCandidates context fuel table inner hpublished
              intro result hresult
              have hdetailed : DirectDetailedResult.done result ∈ support
                  (runDirectResolvedDetailedFromTable context fuel table inner) := by
                rw [← map_erase_runDirectResolvedWitnessFromTable inner context fuel table,
                  support_map]
                exact ⟨DirectWitnessResult.done result, hresult, rfl⟩
              have hcore := resolvedCore_of_done_mem_runDirectResolvedWitnessFromTable inner
                context fuel table result hconsistent hstarts hresult
              have hnextPublished := publishedValues_of_done_runDirectResolvedDetailedFromTable
                (probingHashQueryAfterPlan parameter input plan)
                (preservesPublishedValues_probingHashQueryAfterPlan parameter input plan)
                context fuel table cache result hpublished hdetailed
              apply probEvent_canonicalizeDirectWitnessPlanMatchesCandidate_le_hidden table
                candidate _ result.context result.remaining result.value nextCandidates hcore.2.1
                hnextPublished
              dsimp only
              intro _hprivate _hcompletable
              exact ih result.value.1 nextCandidates
                (canonicalizeMaterializedValues table result.context) result.remaining
                result.value.2
                (canonicalizeMaterializedValues_valuesConsistent table result.context hcore.2.1)
                (canonicalizeMaterializedValues_startTableAgrees table result.context)
                hnextPublished.to_canonicalizedMaterializedValues
      | inr message =>
          rw [directDetailedBoundaryNormalizedPrivateWitnessPlanObserve,
            OracleComp.construct_query_bind]
          let inner := (maskedSign parameter root ftsSecret message).run cache
          apply probEvent_runDirectWitnessPlanMatchesCandidate_le_hidden candidate _ candidates
            context fuel table inner hpublished
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
          apply probEvent_canonicalizeDirectWitnessPlanMatchesCandidate_le_hidden table candidate _
            result.context result.remaining result.value candidates hcore.2.1 hnextPublished
          dsimp only
          intro _hprivate _hcompletable
          exact ih result.value.1 candidates
            (canonicalizeMaterializedValues table result.context) result.remaining result.value.2
            (canonicalizeMaterializedValues_valuesConsistent table result.context hcore.2.1)
            (canonicalizeMaterializedValues_startTableAgrees table result.context)
            hnextPublished.to_canonicalizedMaterializedValues

end SphincsSecurity.Concrete.OtsProbeSimulation
