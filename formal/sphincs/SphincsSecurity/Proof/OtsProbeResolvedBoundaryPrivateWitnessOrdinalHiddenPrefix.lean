import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalHiddenMatchOuter

/-!
# Hidden selected-ordinal step

The exact hash query that appends an ordinal is bounded by the hidden candidate observer. The
retained finalizer satisfies the hidden terminal condition because a published coordinate cannot
be the position of a private witness.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable

theorem probEvent_retainedResolvedFinalizationPrivateWitnessPlanMatchesCandidate_le_hidden
    (table : OtsSecretIndex → HashOutput) (root : Digest) (candidate : Probe)
    (context : DeferredContext) (fuel : Nat)
    (value : RetainedRestResult × SplitHashCache) (candidates : List Probe)
    (hpublished : PublishedValues context.state) :
    Pr[PrivateWitnessPlanMatchesCandidate candidate |
        retainedResolvedFinalizationPrivateWitnessPlanObserve table root context fuel value
          candidates] ≤
      Pr[fun hit : Bool => hit = true |
        hiddenPrivateCandidateFire candidate context] := by
  by_cases hrevealed : candidate.coordinate ∈ context.state.revealed
  · rw [hiddenPrivateCandidateFire_of_revealed candidate context hrevealed]
    unfold retainedResolvedFinalizationPrivateWitnessPlanObserve
    by_cases hhit : PrivateStructuralHit context
    · simp only [hhit, ↓reduceDIte]
      have hspec := privateHitWitnessOf_spec context hhit
      have hnotMatch :
          ¬(privateHitWitnessOf context hhit).MatchesCandidate candidate := by
        intro hmatch
        have hknown := hpublished candidate.coordinate hrevealed
        rw [hmatch.1] at hknown
        exact hknown hspec.1
      simp [PrivateWitnessPlanMatchesCandidate, hnotMatch]
    · simp [hhit, PrivateWitnessPlanMatchesCandidate]
  · rw [hiddenPrivateCandidateFire_of_not_revealed candidate context hrevealed]
    exact probEvent_retainedResolvedFinalizationPrivateWitnessPlanMatchesCandidate_le table root
      candidate context fuel value candidates

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_selectedHashPlanWitnessUsesOrdinal_le_hidden
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : HashInput)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) →
      List Probe → ProbComp PrivateWitnessPlanOutput)
    (current : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (candidate : Probe)
    (_hplan : (purePlanProbingHashQuery parameter input context.state).candidate? =
      some candidate)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hpublished : PublishedValues context.state)
    (hterminal : ∀ nextContext remaining value nextCandidates,
      nextContext.ValuesConsistent → StartTableAgrees nextContext.state table →
      PublishedValues nextContext.state →
      Pr[PrivateWitnessPlanMatchesCandidate candidate |
          observe nextContext remaining value nextCandidates] ≤
        Pr[fun hit : Bool => hit = true |
          hiddenPrivateCandidateFire candidate nextContext])
    (hobservePrefix : ∀ nextContext remaining value nextCandidates output,
      output ∈ support (observe nextContext remaining value nextCandidates) →
      PrivateWitnessPlanExtends nextCandidates output) :
    Pr[WitnessUsesOrdinal current.length |
        runDirectWitnessPlanObserve
          (canonicalizeDirectWitnessPlanObserve table
            (fun nextContext remaining value laterCandidates =>
              directDetailedBoundaryNormalizedPrivateWitnessPlanObserve parameter root ftsSecret
                (next value.1) observe laterCandidates nextContext remaining table value.2))
          (current ++ [candidate]) context fuel table
            ((probingHashQueryAfterPlan parameter input
              (purePlanProbingHashQuery parameter input context.state)).run cache)] ≤
      Pr[fun hit : Bool => hit = true |
        hiddenPrivateCandidateFire candidate context] := by
  let plan := purePlanProbingHashQuery parameter input context.state
  let branch := runDirectWitnessPlanObserve
    (canonicalizeDirectWitnessPlanObserve table
      (fun nextContext remaining value laterCandidates =>
        directDetailedBoundaryNormalizedPrivateWitnessPlanObserve parameter root ftsSecret
          (next value.1) observe laterCandidates nextContext remaining table value.2))
    (current ++ [candidate]) context fuel table
      ((probingHashQueryAfterPlan parameter input plan).run cache)
  apply probEvent_witnessUses_newlyAppendedOrdinal_le branch current candidate _
  · intro output houtput
    unfold branch at houtput
    apply privateWitnessPlanExtends_of_mem_runDirectWitnessPlanObserve _
      (current ++ [candidate]) context fuel table
      ((probingHashQueryAfterPlan parameter input plan).run cache) (output := output)
      (houtput := houtput)
    intro result _hresult nextOutput hnextOutput
    apply privateWitnessPlanExtends_of_mem_canonicalizeDirectWitnessPlanObserve table _
      result.context result.remaining result.value (current ++ [candidate])
      (output := nextOutput) (houtput := hnextOutput)
    intro finalOutput hfinalOutput
    exact privateWitnessPlanExtends_of_mem_directDetailedBoundaryNormalizedPrivateWitnessPlanObserve
      parameter root ftsSecret (next result.value.1) observe (current ++ [candidate])
      (canonicalizeMaterializedValues table result.context) result.remaining table result.value.2
      hobservePrefix finalOutput hfinalOutput
  · unfold branch
    apply probEvent_runDirectWitnessPlanMatchesCandidate_le_hidden candidate _
      (current ++ [candidate]) context fuel table
      ((probingHashQueryAfterPlan parameter input plan).run cache) hpublished
    intro result hresult
    let inner := (probingHashQueryAfterPlan parameter input plan).run cache
    have hdetailed : DirectDetailedResult.done result ∈ support
        (runDirectResolvedDetailedFromTable context fuel table inner) := by
      rw [← map_erase_runDirectResolvedWitnessFromTable inner context fuel table, support_map]
      exact ⟨DirectWitnessResult.done result, hresult, rfl⟩
    have hcore := resolvedCore_of_mem_runDirectResolvedFromTable inner context fuel table result
      hconsistent hstarts
      (mem_support_runDirectResolvedFromTable_of_done_detailed inner context fuel table result
        hdetailed)
    have hnextPublished := publishedValues_of_done_runDirectResolvedDetailedFromTable
      (probingHashQueryAfterPlan parameter input plan)
      (preservesPublishedValues_probingHashQueryAfterPlan parameter input plan)
      context fuel table cache result hpublished hdetailed
    apply probEvent_canonicalizeDirectWitnessPlanMatchesCandidate_le_hidden table candidate _
      result.context result.remaining result.value (current ++ [candidate]) hcore.2.1
      hnextPublished
    dsimp only
    intro _hprivate _hcompletable
    exact probEvent_directDetailedBoundaryNormalizedPrivateWitnessPlanMatchesCandidate_le_hidden
      candidate parameter root ftsSecret (next result.value.1) observe (current ++ [candidate])
      (canonicalizeMaterializedValues table result.context) result.remaining table result.value.2
      (canonicalizeMaterializedValues_valuesConsistent table result.context hcore.2.1)
      (canonicalizeMaterializedValues_startTableAgrees table result.context)
      hnextPublished.to_canonicalizedMaterializedValues hterminal

end SphincsSecurity.Concrete.OtsProbeSimulation
