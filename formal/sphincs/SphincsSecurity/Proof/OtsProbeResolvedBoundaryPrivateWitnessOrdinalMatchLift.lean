import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalMatch

/-!
# Fixed-candidate outer continuation

The witness event after a candidate is fixed is lifted through direct runs and canonical query
boundaries. Candidate-list bookkeeping is irrelevant here; only the retained position and output
are compared with the selected candidate.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable

def PrivateWitnessPlanMatchesCandidate
    (candidate : Probe) (output : PrivateWitnessPlanOutput) : Prop :=
  ∃ witness, output.1 = some witness ∧ witness.MatchesCandidate candidate

theorem probEvent_finishDirectWitnessPlanMatchesCandidate_le
    (candidate : Probe)
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (candidates : List Probe) (result : DirectWitnessResult α)
    (hobserve : ∀ resolved : ResolvedRunResult α,
      result = .done resolved →
      Pr[PrivateWitnessPlanMatchesCandidate candidate |
          observe resolved.context resolved.remaining resolved.value candidates] ≤
        Pr[fun hit : Bool => hit = true |
          privateCandidateFire candidate resolved.context]) :
    Pr[PrivateWitnessPlanMatchesCandidate candidate |
        finishDirectWitnessPlanObserve observe candidates result] ≤
      Pr[fun hit : Bool => hit = true |
        finishDirectWitnessPrivateCandidateMatch candidate result] := by
  cases result with
  | stoppedFuel => simp [finishDirectWitnessPlanObserve,
      finishDirectWitnessPrivateCandidateMatch, PrivateWitnessPlanMatchesCandidate]
  | stoppedOrdinary => simp [finishDirectWitnessPlanObserve,
      finishDirectWitnessPrivateCandidateMatch, PrivateWitnessPlanMatchesCandidate]
  | stoppedPrivate witness =>
      simp [finishDirectWitnessPlanObserve, finishDirectWitnessPrivateCandidateMatch,
        PrivateWitnessPlanMatchesCandidate]
  | done resolved =>
      simpa [finishDirectWitnessPlanObserve, finishDirectWitnessPrivateCandidateMatch] using
        hobserve resolved rfl

set_option maxRecDepth 100000 in
theorem probEvent_runDirectWitnessPlanMatchesCandidate_le
    (candidate : Probe)
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hobserve : ∀ result : ResolvedRunResult α,
      DirectWitnessResult.done result ∈ support
        (runDirectResolvedWitnessFromTable context fuel table computation) →
      Pr[PrivateWitnessPlanMatchesCandidate candidate |
          observe result.context result.remaining result.value candidates] ≤
        Pr[fun hit : Bool => hit = true |
          privateCandidateFire candidate result.context]) :
    Pr[PrivateWitnessPlanMatchesCandidate candidate |
        runDirectWitnessPlanObserve observe candidates context fuel table computation] ≤
      Pr[fun hit : Bool => hit = true | privateCandidateFire candidate context] := by
  unfold runDirectWitnessPlanObserve
  calc
    _ ≤ Pr[fun hit : Bool => hit = true |
        runDirectResolvedWitnessFromTable context fuel table computation >>=
          finishDirectWitnessPrivateCandidateMatch candidate] := by
      rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hresult : result ∈ support
          (runDirectResolvedWitnessFromTable context fuel table computation)
      · exact mul_le_mul' le_rfl
          (probEvent_finishDirectWitnessPlanMatchesCandidate_le candidate observe candidates
            result (by
              intro resolved heq
              subst result
              exact hobserve resolved hresult))
      · rw [probOutput_eq_zero_of_not_mem_support hresult]
        simp
    _ ≤ _ := probEvent_runDirectWitnessPrivateCandidateMatch_le candidate context fuel table
      computation

theorem probEvent_classifyDirectWitnessPlanMatchesCandidate_le
    (table : OtsSecretIndex → HashOutput) (candidate : Probe)
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (context : DeferredContext) (fuel : Nat) (value : α) (candidates : List Probe)
    (hcontinuation : ¬PrivateStructuralHit context → DeferredCompletable table context →
      Pr[PrivateWitnessPlanMatchesCandidate candidate |
          observe context fuel value candidates] ≤
        Pr[fun hit : Bool => hit = true | privateCandidateFire candidate context]) :
    Pr[PrivateWitnessPlanMatchesCandidate candidate |
        classifyDirectWitnessPlanObserve table observe context fuel value candidates] ≤
      Pr[fun hit : Bool => hit = true | privateCandidateFire candidate context] := by
  unfold classifyDirectWitnessPlanObserve
  by_cases hhit : PrivateStructuralHit context
  · simp only [hhit, ↓reduceDIte]
    have hspec := privateHitWitnessOf_spec context hhit
    have hmatch := probEvent_privateWitnessMatch_le_privateCandidateFire_of_privateValue
      candidate context (privateHitWitnessOf context hhit).position
      (privateHitWitnessOf context hhit).output hspec.1 hspec.2.1
    simpa [PrivateWitnessPlanMatchesCandidate] using hmatch
  · simp only [hhit, ↓reduceDIte]
    by_cases hcompletable : DeferredCompletable table context
    · simp only [hcompletable, ↓reduceIte]
      exact hcontinuation hhit hcompletable
    · simp [hcompletable, PrivateWitnessPlanMatchesCandidate]

theorem probEvent_canonicalizeDirectWitnessPlanMatchesCandidate_le
    (table : OtsSecretIndex → HashOutput) (candidate : Probe)
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (context : DeferredContext) (fuel : Nat) (value : α) (candidates : List Probe)
    (hconsistent : context.ValuesConsistent)
    (hcontinuation :
      let canonical := canonicalizeMaterializedValues table context
      ¬PrivateStructuralHit canonical → DeferredCompletable table canonical →
      Pr[PrivateWitnessPlanMatchesCandidate candidate |
          observe canonical fuel value candidates] ≤
        Pr[fun hit : Bool => hit = true | privateCandidateFire candidate canonical]) :
    Pr[PrivateWitnessPlanMatchesCandidate candidate |
        canonicalizeDirectWitnessPlanObserve table observe context fuel value candidates] ≤
      Pr[fun hit : Bool => hit = true | privateCandidateFire candidate context] := by
  let canonical := canonicalizeMaterializedValues table context
  have hfire := privateCandidateFire_canonicalize table candidate context hconsistent
  have hfireProb :
      Pr[fun hit : Bool => hit = true | privateCandidateFire candidate canonical] =
        Pr[fun hit : Bool => hit = true | privateCandidateFire candidate context] := by
    rw [probEvent_eq_eq_probOutput, probEvent_eq_eq_probOutput]
    exact OracleComp.probOutput_congr rfl (congrArg evalDist hfire)
  have hclassify :
      Pr[PrivateWitnessPlanMatchesCandidate candidate |
          classifyDirectWitnessPlanObserve table observe canonical fuel value candidates] ≤
        Pr[fun hit : Bool => hit = true | privateCandidateFire candidate canonical] :=
    probEvent_classifyDirectWitnessPlanMatchesCandidate_le table candidate observe canonical fuel
      value candidates hcontinuation
  unfold canonicalizeDirectWitnessPlanObserve
  by_cases hhit : PrivateStructuralHit canonical
  · simp only [canonical, hhit, ↓reduceDIte]
    have hspec := privateHitWitnessOf_spec canonical hhit
    have hmatch := probEvent_privateWitnessMatch_le_privateCandidateFire_of_privateValue
      candidate canonical (privateHitWitnessOf canonical hhit).position
      (privateHitWitnessOf canonical hhit).output hspec.1 hspec.2.1
    have hmatchEvent :
        Pr[PrivateWitnessPlanMatchesCandidate candidate |
            (pure (some (privateHitWitnessOf canonical hhit), candidates) :
              ProbComp PrivateWitnessPlanOutput)] ≤
          Pr[fun hit : Bool => hit = true |
            privateCandidateFire candidate canonical] := by
      rw [probEvent_eq_eq_probOutput]
      simpa [PrivateWitnessPlanMatchesCandidate] using hmatch
    exact hmatchEvent.trans (le_of_eq hfireProb)
  · simp only [canonical, hhit, ↓reduceDIte]
    by_cases hpublished : PublishedValues context.state
    · simp only [hpublished, ↓reduceIte]
      exact hclassify.trans (le_of_eq hfireProb)
    · simp [hpublished, PrivateWitnessPlanMatchesCandidate]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_directDetailedBoundaryNormalizedPrivateWitnessPlanMatchesCandidate_le
    (candidate : Probe) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) →
      List Probe → ProbComp PrivateWitnessPlanOutput)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hterminal : ∀ nextContext remaining value nextCandidates,
      nextContext.ValuesConsistent → StartTableAgrees nextContext.state table →
      Pr[PrivateWitnessPlanMatchesCandidate candidate |
          observe nextContext remaining value nextCandidates] ≤
        Pr[fun hit : Bool => hit = true |
          privateCandidateFire candidate nextContext]) :
    Pr[PrivateWitnessPlanMatchesCandidate candidate |
        directDetailedBoundaryNormalizedPrivateWitnessPlanObserve parameter root ftsSecret
          computation observe candidates context fuel table cache] ≤
      Pr[fun hit : Bool => hit = true | privateCandidateFire candidate context] := by
  induction computation using OracleComp.inductionOn generalizing candidates context fuel cache with
  | pure value =>
      rw [directDetailedBoundaryNormalizedPrivateWitnessPlanObserve,
        OracleComp.construct_pure]
      exact hterminal context fuel (value, cache) candidates hconsistent hstarts
  | query_bind query next ih =>
      rw [directDetailedBoundaryNormalizedPrivateWitnessPlanObserve,
        OracleComp.construct_query_bind]
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              let inner := (splitUniformImpl n).run cache
              apply probEvent_runDirectWitnessPlanMatchesCandidate_le candidate _ candidates
                context fuel table inner
              intro result hresult
              have hdetailed : DirectDetailedResult.done result ∈ support
                  (runDirectResolvedDetailedFromTable context fuel table inner) := by
                rw [← map_erase_runDirectResolvedWitnessFromTable inner context fuel table,
                  support_map]
                exact ⟨DirectWitnessResult.done result, hresult, rfl⟩
              have hcore := resolvedCore_of_mem_runDirectResolvedFromTable inner context fuel table
                result hconsistent hstarts
                (mem_support_runDirectResolvedFromTable_of_done_detailed inner context fuel table
                  result hdetailed)
              apply probEvent_canonicalizeDirectWitnessPlanMatchesCandidate_le table candidate _
                result.context result.remaining result.value candidates hcore.2.1
              dsimp only
              intro _hprivate _hcompletable
              exact ih result.value.1 candidates
                (canonicalizeMaterializedValues table result.context) result.remaining
                result.value.2
                (canonicalizeMaterializedValues_valuesConsistent table result.context hcore.2.1)
                (canonicalizeMaterializedValues_startTableAgrees table result.context)
          | inr input =>
              let plan := purePlanProbingHashQuery parameter input context.state
              let nextCandidates := appendPlannedCandidate candidates
                (rootAwarePlannedCandidate? parameter input context.state)
              let inner := (probingHashQueryAfterPlan parameter input plan).run cache
              apply probEvent_runDirectWitnessPlanMatchesCandidate_le candidate _ nextCandidates
                context fuel table inner
              intro result hresult
              have hdetailed : DirectDetailedResult.done result ∈ support
                  (runDirectResolvedDetailedFromTable context fuel table inner) := by
                rw [← map_erase_runDirectResolvedWitnessFromTable inner context fuel table,
                  support_map]
                exact ⟨DirectWitnessResult.done result, hresult, rfl⟩
              have hcore := resolvedCore_of_mem_runDirectResolvedFromTable inner context fuel table
                result hconsistent hstarts
                (mem_support_runDirectResolvedFromTable_of_done_detailed inner context fuel table
                  result hdetailed)
              apply probEvent_canonicalizeDirectWitnessPlanMatchesCandidate_le table candidate _
                result.context result.remaining result.value nextCandidates hcore.2.1
              dsimp only
              intro _hprivate _hcompletable
              exact ih result.value.1 nextCandidates
                (canonicalizeMaterializedValues table result.context) result.remaining
                result.value.2
                (canonicalizeMaterializedValues_valuesConsistent table result.context hcore.2.1)
                (canonicalizeMaterializedValues_startTableAgrees table result.context)
      | inr message =>
          let inner := (maskedSign parameter root ftsSecret message).run cache
          apply probEvent_runDirectWitnessPlanMatchesCandidate_le candidate _ candidates context
            fuel table inner
          intro result hresult
          have hdetailed : DirectDetailedResult.done result ∈ support
              (runDirectResolvedDetailedFromTable context fuel table inner) := by
            rw [← map_erase_runDirectResolvedWitnessFromTable inner context fuel table,
              support_map]
            exact ⟨DirectWitnessResult.done result, hresult, rfl⟩
          have hcore := resolvedCore_of_mem_runDirectResolvedFromTable inner context fuel table
            result hconsistent hstarts
            (mem_support_runDirectResolvedFromTable_of_done_detailed inner context fuel table result
              hdetailed)
          apply probEvent_canonicalizeDirectWitnessPlanMatchesCandidate_le table candidate _
            result.context result.remaining result.value candidates hcore.2.1
          dsimp only
          intro _hprivate _hcompletable
          exact ih result.value.1 candidates
            (canonicalizeMaterializedValues table result.context) result.remaining result.value.2
            (canonicalizeMaterializedValues_valuesConsistent table result.context hcore.2.1)
            (canonicalizeMaterializedValues_startTableAgrees table result.context)

theorem probEvent_retainedResolvedFinalizationPrivateWitnessPlanMatchesCandidate_le
    (table : OtsSecretIndex → HashOutput) (root : Digest) (candidate : Probe)
    (context : DeferredContext) (fuel : Nat)
    (value : RetainedRestResult × SplitHashCache) (candidates : List Probe) :
    Pr[PrivateWitnessPlanMatchesCandidate candidate |
        retainedResolvedFinalizationPrivateWitnessPlanObserve table root context fuel value
          candidates] ≤
      Pr[fun hit : Bool => hit = true | privateCandidateFire candidate context] := by
  unfold retainedResolvedFinalizationPrivateWitnessPlanObserve
  by_cases hhit : PrivateStructuralHit context
  · simp only [hhit, ↓reduceDIte]
    have hspec := privateHitWitnessOf_spec context hhit
    have hmatch := probEvent_privateWitnessMatch_le_privateCandidateFire_of_privateValue
      candidate context (privateHitWitnessOf context hhit).position
      (privateHitWitnessOf context hhit).output hspec.1 hspec.2.1
    have hmatchEvent :
        Pr[PrivateWitnessPlanMatchesCandidate candidate |
            (pure (some (privateHitWitnessOf context hhit), candidates) :
              ProbComp PrivateWitnessPlanOutput)] ≤
          Pr[fun hit : Bool => hit = true | privateCandidateFire candidate context] := by
      rw [probEvent_eq_eq_probOutput]
      simpa [PrivateWitnessPlanMatchesCandidate] using hmatch
    exact hmatchEvent
  · simp [hhit, PrivateWitnessPlanMatchesCandidate]

theorem probEvent_granularDetailedRetainedRestNormalizedWitnessMatchesCandidate_le
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (candidate : Probe) (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (candidates : List Probe)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table) :
    Pr[PrivateWitnessPlanMatchesCandidate candidate |
        granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve adversary parameter table
          ftsSecret context fuel value candidates] ≤
      Pr[fun hit : Bool => hit = true | privateCandidateFire candidate context] := by
  unfold granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve
  apply probEvent_directDetailedBoundaryNormalizedPrivateWitnessPlanMatchesCandidate_le candidate
    parameter value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
    (retainedResolvedFinalizationPrivateWitnessPlanObserve table value.1)
    candidates context fuel table value.2 hconsistent hstarts
  intro nextContext remaining nextValue nextCandidates _hnextConsistent _hnextStarts
  exact probEvent_retainedResolvedFinalizationPrivateWitnessPlanMatchesCandidate_le table value.1
    candidate nextContext remaining nextValue nextCandidates

end SphincsSecurity.Concrete.OtsProbeSimulation
