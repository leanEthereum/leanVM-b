import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalMatchLift

/-!
# Monotone witness plan prefixes

The normalized witness trace only appends candidates. A candidate already selected at one ordinal
therefore remains at that ordinal in every later output.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

def PrivateWitnessPlanExtends
    (candidates : List Probe) (output : PrivateWitnessPlanOutput) : Prop :=
  candidates.IsPrefix output.2

theorem privateWitnessPlanExtends_of_mem_finishDirectWitnessPlanObserve
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (candidates : List Probe) (result : DirectWitnessResult α)
    (hobserve : ∀ resolved : ResolvedRunResult α,
      result = .done resolved →
      ∀ output ∈ support
        (observe resolved.context resolved.remaining resolved.value candidates),
        PrivateWitnessPlanExtends candidates output)
    (output : PrivateWitnessPlanOutput)
    (houtput : output ∈ support
      (finishDirectWitnessPlanObserve observe candidates result)) :
    PrivateWitnessPlanExtends candidates output := by
  cases result with
  | stoppedFuel =>
      simp [finishDirectWitnessPlanObserve] at houtput
      subst output
      simp [PrivateWitnessPlanExtends]
  | stoppedOrdinary =>
      simp [finishDirectWitnessPlanObserve] at houtput
      subst output
      simp [PrivateWitnessPlanExtends]
  | stoppedPrivate witness =>
      simp [finishDirectWitnessPlanObserve] at houtput
      subst output
      simp [PrivateWitnessPlanExtends]
  | done resolved => exact hobserve resolved rfl output houtput

theorem privateWitnessPlanExtends_of_mem_runDirectWitnessPlanObserve
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hobserve : ∀ result : ResolvedRunResult α,
      DirectWitnessResult.done result ∈ support
        (runDirectResolvedWitnessFromTable context fuel table computation) →
      ∀ output ∈ support
        (observe result.context result.remaining result.value candidates),
        PrivateWitnessPlanExtends candidates output)
    (output : PrivateWitnessPlanOutput)
    (houtput : output ∈ support
      (runDirectWitnessPlanObserve observe candidates context fuel table computation)) :
    PrivateWitnessPlanExtends candidates output := by
  unfold runDirectWitnessPlanObserve at houtput
  rw [mem_support_bind_iff] at houtput
  obtain ⟨result, hresult, hfinish⟩ := houtput
  exact privateWitnessPlanExtends_of_mem_finishDirectWitnessPlanObserve observe candidates result
    (by
      intro resolved heq
      subst result
      exact hobserve resolved hresult)
    output hfinish

theorem privateWitnessPlanExtends_of_mem_classifyDirectWitnessPlanObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (context : DeferredContext) (fuel : Nat) (value : α) (candidates : List Probe)
    (hobserve : ∀ output ∈ support (observe context fuel value candidates),
      PrivateWitnessPlanExtends candidates output)
    (output : PrivateWitnessPlanOutput)
    (houtput : output ∈ support
      (classifyDirectWitnessPlanObserve table observe context fuel value candidates)) :
    PrivateWitnessPlanExtends candidates output := by
  unfold classifyDirectWitnessPlanObserve at houtput
  by_cases hhit : PrivateStructuralHit context
  · simp [hhit] at houtput
    subst output
    simp [PrivateWitnessPlanExtends]
  · simp only [hhit, ↓reduceDIte] at houtput
    by_cases hcompletable : DeferredCompletable table context
    · simp only [hcompletable, ↓reduceIte] at houtput
      exact hobserve output houtput
    · simp [hcompletable] at houtput
      subst output
      simp [PrivateWitnessPlanExtends]

theorem privateWitnessPlanExtends_of_mem_canonicalizeDirectWitnessPlanObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (context : DeferredContext) (fuel : Nat) (value : α) (candidates : List Probe)
    (hobserve : ∀ output ∈ support
      (observe (canonicalizeMaterializedValues table context) fuel value candidates),
      PrivateWitnessPlanExtends candidates output)
    (output : PrivateWitnessPlanOutput)
    (houtput : output ∈ support
      (canonicalizeDirectWitnessPlanObserve table observe context fuel value candidates)) :
    PrivateWitnessPlanExtends candidates output := by
  unfold canonicalizeDirectWitnessPlanObserve at houtput
  let canonical := canonicalizeMaterializedValues table context
  by_cases hhit : PrivateStructuralHit canonical
  · simp [canonical, hhit] at houtput
    subst output
    simp [PrivateWitnessPlanExtends]
  · simp only [canonical, hhit, ↓reduceDIte] at houtput
    by_cases hpublished : PublishedValues context.state
    · simp only [hpublished, ↓reduceIte] at houtput
      exact privateWitnessPlanExtends_of_mem_classifyDirectWitnessPlanObserve table observe
        canonical fuel value candidates hobserve output houtput
    · simp [hpublished] at houtput
      subst output
      simp [PrivateWitnessPlanExtends]

set_option maxRecDepth 100000 in
theorem privateWitnessPlanExtends_of_mem_directDetailedBoundaryNormalizedPrivateWitnessPlanObserve
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) →
      List Probe → ProbComp PrivateWitnessPlanOutput)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hobserve : ∀ nextContext remaining value nextCandidates output,
      output ∈ support (observe nextContext remaining value nextCandidates) →
      PrivateWitnessPlanExtends nextCandidates output)
    (output : PrivateWitnessPlanOutput)
    (houtput : output ∈ support
      (directDetailedBoundaryNormalizedPrivateWitnessPlanObserve parameter root ftsSecret
        computation observe candidates context fuel table cache)) :
    PrivateWitnessPlanExtends candidates output := by
  induction computation using OracleComp.inductionOn generalizing candidates context fuel cache output with
  | pure value =>
      rw [directDetailedBoundaryNormalizedPrivateWitnessPlanObserve,
        OracleComp.construct_pure] at houtput
      exact hobserve context fuel (value, cache) candidates output houtput
  | query_bind query next ih =>
      rw [directDetailedBoundaryNormalizedPrivateWitnessPlanObserve,
        OracleComp.construct_query_bind] at houtput
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              apply privateWitnessPlanExtends_of_mem_runDirectWitnessPlanObserve _ candidates
                context fuel table ((splitUniformImpl n).run cache) (output := output)
                (houtput := houtput)
              intro result _hresult nextOutput hnextOutput
              apply privateWitnessPlanExtends_of_mem_canonicalizeDirectWitnessPlanObserve table _
                result.context result.remaining result.value candidates (output := nextOutput)
                (houtput := hnextOutput)
              intro finalOutput hfinalOutput
              exact ih result.value.1 candidates
                (canonicalizeMaterializedValues table result.context) result.remaining
                result.value.2 finalOutput hfinalOutput
          | inr input =>
              let plan := purePlanProbingHashQuery parameter input context.state
              let nextCandidates := appendPlannedCandidate candidates plan.candidate?
              have hprefix : candidates.IsPrefix nextCandidates := by
                cases hcandidate : plan.candidate? <;>
                  simp [nextCandidates, appendPlannedCandidate, hcandidate]
              have hnext : PrivateWitnessPlanExtends nextCandidates output := by
                apply privateWitnessPlanExtends_of_mem_runDirectWitnessPlanObserve _ nextCandidates
                  context fuel table ((probingHashQueryAfterPlan parameter input plan).run cache)
                  (output := output) (houtput := houtput)
                intro result _hresult nextOutput hnextOutput
                apply privateWitnessPlanExtends_of_mem_canonicalizeDirectWitnessPlanObserve table _
                  result.context result.remaining result.value nextCandidates
                  (output := nextOutput) (houtput := hnextOutput)
                intro finalOutput hfinalOutput
                exact ih result.value.1 nextCandidates
                  (canonicalizeMaterializedValues table result.context) result.remaining
                  result.value.2 finalOutput hfinalOutput
              exact hprefix.trans hnext
      | inr message =>
          apply privateWitnessPlanExtends_of_mem_runDirectWitnessPlanObserve _ candidates context
            fuel table ((maskedSign parameter root ftsSecret message).run cache) (output := output)
            (houtput := houtput)
          intro result _hresult nextOutput hnextOutput
          apply privateWitnessPlanExtends_of_mem_canonicalizeDirectWitnessPlanObserve table _
            result.context result.remaining result.value candidates (output := nextOutput)
            (houtput := hnextOutput)
          intro finalOutput hfinalOutput
          exact ih result.value.1 candidates
            (canonicalizeMaterializedValues table result.context) result.remaining result.value.2
            finalOutput hfinalOutput

theorem privateWitnessPlanExtends_of_mem_retainedResolvedFinalizationPrivateWitnessPlanObserve
    (table : OtsSecretIndex → HashOutput) (root : Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : RetainedRestResult × SplitHashCache) (candidates : List Probe)
    (output : PrivateWitnessPlanOutput)
    (houtput : output ∈ support
      (retainedResolvedFinalizationPrivateWitnessPlanObserve table root context fuel value
        candidates)) :
    PrivateWitnessPlanExtends candidates output := by
  unfold retainedResolvedFinalizationPrivateWitnessPlanObserve at houtput
  by_cases hhit : PrivateStructuralHit context <;>
    simp [hhit] at houtput <;> subst output <;> simp [PrivateWitnessPlanExtends]

theorem privateWitnessPlanExtends_of_mem_granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (candidates : List Probe)
    (output : PrivateWitnessPlanOutput)
    (houtput : output ∈ support
      (granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve adversary parameter table
        ftsSecret context fuel value candidates)) :
    PrivateWitnessPlanExtends candidates output := by
  unfold granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve at houtput
  apply privateWitnessPlanExtends_of_mem_directDetailedBoundaryNormalizedPrivateWitnessPlanObserve
    parameter value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
    (retainedResolvedFinalizationPrivateWitnessPlanObserve table value.1)
    candidates context fuel table value.2 (output := output) (houtput := houtput)
  intro nextContext remaining nextValue nextCandidates nextOutput hnextOutput
  exact privateWitnessPlanExtends_of_mem_retainedResolvedFinalizationPrivateWitnessPlanObserve
    table value.1 nextContext remaining nextValue nextCandidates nextOutput hnextOutput

theorem privateWitnessPlanMatchesCandidate_of_usesOrdinal_of_prefix
    (current : List Probe) (output : PrivateWitnessPlanOutput) (ordinal : Nat)
    (hlt : ordinal < current.length)
    (hprefix : PrivateWitnessPlanExtends current output)
    (huses : WitnessUsesOrdinal ordinal output) :
    PrivateWitnessPlanMatchesCandidate (current.get ⟨ordinal, hlt⟩) output := by
  obtain ⟨witness, sourceOrdinal, hwitness, hordinal, hsource⟩ := huses
  subst ordinal
  refine ⟨witness, hwitness, ?_⟩
  have hselected : current.get ⟨sourceOrdinal.val, hlt⟩ =
      output.2.get sourceOrdinal := by
    change current[sourceOrdinal.val] = output.2[sourceOrdinal.val]
    exact hprefix.getElem hlt
  unfold PrivateWitnessAtOrdinal at hsource
  unfold PrivateHitWitness.MatchesCandidate
  rw [hselected]
  exact hsource

theorem probEvent_granularDetailedRetainedRestWitnessUsesOrdinal_le_of_selected
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (candidates : List Probe)
    (ordinal : Nat) (hlt : ordinal < candidates.length)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table) :
    Pr[WitnessUsesOrdinal ordinal |
        granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve adversary parameter table
          ftsSecret context fuel value candidates] ≤
      Pr[fun hit : Bool => hit = true |
        privateCandidateFire (candidates.get ⟨ordinal, hlt⟩) context] := by
  apply (probEvent_mono (mx :=
    granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve adversary parameter table
      ftsSecret context fuel value candidates) (p := WitnessUsesOrdinal ordinal)
    (q := PrivateWitnessPlanMatchesCandidate (candidates.get ⟨ordinal, hlt⟩)) ?_).trans
  · exact probEvent_granularDetailedRetainedRestNormalizedWitnessMatchesCandidate_le
      adversary parameter table ftsSecret (candidates.get ⟨ordinal, hlt⟩) context fuel value
      candidates hconsistent hstarts
  · intro output houtput huses
    exact privateWitnessPlanMatchesCandidate_of_usesOrdinal_of_prefix candidates output ordinal hlt
      (privateWitnessPlanExtends_of_mem_granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve
        adversary parameter table ftsSecret context fuel value candidates output houtput)
      huses

end SphincsSecurity.Concrete.OtsProbeSimulation
