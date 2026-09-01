import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitness

/-!
# Planned private witnesses

Private first-fire witnesses are threaded together with the chronological candidate list. Erasing
the witness recovers the existing Boolean plan observer exactly.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

abbrev PrivateWitnessPlanOutput := Option PrivateHitWitness × List Probe

def erasePrivateWitnessPlanOutput
    (output : PrivateWitnessPlanOutput) : Bool × List Probe :=
  (output.1.isSome, output.2)

def PrivateWitnessCovered (output : PrivateWitnessPlanOutput) : Prop :=
  ∀ witness, output.1 = some witness →
    candidateListHits witness.position output.2 witness.output

noncomputable def privateHitWitnessOf
    (context : DeferredContext) (hhit : PrivateStructuralHit context) : PrivateHitWitness :=
  ⟨hhit.choose, hhit.choose_spec.choose, context.state.revealed⟩

theorem privateHitWitnessOf_spec
    (context : DeferredContext) (hhit : PrivateStructuralHit context) :
    context.state.values (.position (privateHitWitnessOf context hhit).position) = none ∧
      context.values (privateHitWitnessOf context hhit).position =
        some (privateHitWitnessOf context hhit).output ∧
      context.state.hitAt (.position (privateHitWitnessOf context hhit).position)
        (privateHitWitnessOf context hhit).output := by
  unfold privateHitWitnessOf
  exact hhit.choose_spec.choose_spec

theorem candidateListHits_privateHitWitnessOf
    (context : DeferredContext) (candidates : List Probe)
    (hcovered : PendingCoveredBy candidates context)
    (hhit : PrivateStructuralHit context) :
    candidateListHits (privateHitWitnessOf context hhit).position candidates
      (privateHitWitnessOf context hhit).output := by
  have hspec := privateHitWitnessOf_spec context hhit
  have hpending :
      (Coordinate.position (privateHitWitnessOf context hhit).position,
          truncateHash (privateHitWitnessOf context hhit).output) ∈ context.state.pending := by
    rw [← LazyRevealProbe.State.mem_pendingAt_iff]
    exact hspec.2.2
  obtain ⟨candidate, hcandidate, hcoordinate, hdigest⟩ := hcovered _ hpending
  exact candidateListHits_of_mem (privateHitWitnessOf context hhit).position
    (privateHitWitnessOf context hhit).output candidate candidates hcandidate hcoordinate
    hdigest

noncomputable def finishDirectWitnessPlanObserve
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (candidates : List Probe) : DirectWitnessResult α →
      ProbComp PrivateWitnessPlanOutput
  | .stoppedFuel => pure (none, candidates)
  | .stoppedOrdinary => pure (none, candidates)
  | .stoppedPrivate witness => pure (some witness, candidates)
  | .done result => observe result.context result.remaining result.value candidates

noncomputable def classifyDirectWitnessPlanObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (context : DeferredContext) (fuel : Nat) (value : α) (candidates : List Probe) :
    ProbComp PrivateWitnessPlanOutput := by
  classical
  exact if hhit : PrivateStructuralHit context then
      pure (some (privateHitWitnessOf context hhit), candidates)
    else if DeferredCompletable table context then
      observe context fuel value candidates
    else
      pure (none, candidates)

noncomputable def canonicalizeDirectWitnessPlanObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (context : DeferredContext) (fuel : Nat) (value : α) (candidates : List Probe) :
    ProbComp PrivateWitnessPlanOutput := by
  classical
  let canonical := canonicalizeMaterializedValues table context
  exact if hhit : PrivateStructuralHit canonical then
      pure (some (privateHitWitnessOf canonical hhit), candidates)
    else if PublishedValues context.state then
      classifyDirectWitnessPlanObserve table observe canonical fuel value candidates
    else
      pure (none, candidates)

noncomputable def runDirectWitnessPlanObserve
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    ProbComp PrivateWitnessPlanOutput :=
  runDirectResolvedWitnessFromTable context fuel table computation >>=
    finishDirectWitnessPlanObserve observe candidates

theorem map_erase_finishDirectWitnessPlanObserve
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (boolObserve : DeferredContext → Nat → α → List Probe →
      ProbComp (Bool × List Probe))
    (candidates : List Probe) (result : DirectWitnessResult α)
    (hproject : ∀ context fuel value candidates,
      erasePrivateWitnessPlanOutput <$> observe context fuel value candidates =
        boolObserve context fuel value candidates) :
    erasePrivateWitnessPlanOutput <$>
        finishDirectWitnessPlanObserve observe candidates result =
      finishDirectDetailedPrivatePlanObserve boolObserve candidates result.erase := by
  cases result with
  | stoppedFuel => simp [finishDirectWitnessPlanObserve,
      finishDirectDetailedPrivatePlanObserve, DirectWitnessResult.erase,
      erasePrivateWitnessPlanOutput]
  | stoppedOrdinary => simp [finishDirectWitnessPlanObserve,
      finishDirectDetailedPrivatePlanObserve, DirectWitnessResult.erase,
      erasePrivateWitnessPlanOutput]
  | stoppedPrivate witness => simp [finishDirectWitnessPlanObserve,
      finishDirectDetailedPrivatePlanObserve, DirectWitnessResult.erase,
      erasePrivateWitnessPlanOutput]
  | done result => exact hproject result.context result.remaining result.value candidates

theorem map_erase_classifyDirectWitnessPlanObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (boolObserve : DeferredContext → Nat → α → List Probe →
      ProbComp (Bool × List Probe))
    (context : DeferredContext) (fuel : Nat) (value : α) (candidates : List Probe)
    (hproject : ∀ nextContext remaining nextValue nextCandidates,
      erasePrivateWitnessPlanOutput <$>
          observe nextContext remaining nextValue nextCandidates =
        boolObserve nextContext remaining nextValue nextCandidates) :
    erasePrivateWitnessPlanOutput <$>
        classifyDirectWitnessPlanObserve table observe context fuel value candidates =
      classifyDirectDetailedPrivatePlanObserve table boolObserve context fuel value
        candidates := by
  classical
  unfold classifyDirectWitnessPlanObserve classifyDirectDetailedPrivatePlanObserve
  by_cases hhit : PrivateStructuralHit context
  · simp [hhit, erasePrivateWitnessPlanOutput]
  · simp only [hhit, ↓reduceDIte, ↓reduceIte]
    by_cases hcompletable : DeferredCompletable table context
    · simp only [hcompletable, ↓reduceIte]
      exact hproject context fuel value candidates
    · simp [hcompletable, erasePrivateWitnessPlanOutput]

theorem map_erase_canonicalizeDirectWitnessPlanObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (boolObserve : DeferredContext → Nat → α → List Probe →
      ProbComp (Bool × List Probe))
    (context : DeferredContext) (fuel : Nat) (value : α) (candidates : List Probe)
    (hproject : ∀ nextContext remaining nextValue nextCandidates,
      erasePrivateWitnessPlanOutput <$>
          observe nextContext remaining nextValue nextCandidates =
        boolObserve nextContext remaining nextValue nextCandidates) :
    erasePrivateWitnessPlanOutput <$>
        canonicalizeDirectWitnessPlanObserve table observe context fuel value candidates =
      canonicalizeDirectDetailedPrivatePlanObserve table boolObserve context fuel value
        candidates := by
  classical
  unfold canonicalizeDirectWitnessPlanObserve
    canonicalizeDirectDetailedPrivatePlanObserve
  let canonical := canonicalizeMaterializedValues table context
  by_cases hhit : PrivateStructuralHit canonical
  · simp [canonical, hhit, erasePrivateWitnessPlanOutput]
  · simp only [canonical, hhit, ↓reduceDIte, ↓reduceIte]
    by_cases hpublished : PublishedValues context.state
    · simp only [hpublished, ↓reduceIte]
      exact map_erase_classifyDirectWitnessPlanObserve table observe boolObserve canonical fuel
        value candidates hproject
    · simp [hpublished, erasePrivateWitnessPlanOutput]

set_option maxRecDepth 100000 in
theorem map_erase_runDirectWitnessPlanObserve
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (boolObserve : DeferredContext → Nat → α → List Probe →
      ProbComp (Bool × List Probe))
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hproject : ∀ nextContext remaining value nextCandidates,
      erasePrivateWitnessPlanOutput <$>
          observe nextContext remaining value nextCandidates =
        boolObserve nextContext remaining value nextCandidates) :
    erasePrivateWitnessPlanOutput <$>
        runDirectWitnessPlanObserve observe candidates context fuel table computation =
      runDirectDetailedPrivatePlanObserve boolObserve candidates context fuel table computation := by
  unfold runDirectWitnessPlanObserve runDirectDetailedPrivatePlanObserve
  rw [map_bind]
  calc
    _ = runDirectResolvedWitnessFromTable context fuel table computation >>= fun result =>
          finishDirectDetailedPrivatePlanObserve boolObserve candidates result.erase := by
      apply bind_congr
      intro result
      exact map_erase_finishDirectWitnessPlanObserve observe boolObserve candidates result hproject
    _ = DirectWitnessResult.erase <$>
          runDirectResolvedWitnessFromTable context fuel table computation >>=
            finishDirectDetailedPrivatePlanObserve boolObserve candidates := by
      simp [map_eq_bind_pure_comp, bind_assoc]
    _ = _ := by rw [map_erase_runDirectResolvedWitnessFromTable]

set_option maxRecDepth 100000 in
theorem privateWitnessCovered_of_mem_runDirectWitnessPlanObserve
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hcovered : PendingCoveredBy candidates context)
    (hbound : computation.IsQueryBoundP (IsUncoveredProbe candidates) 0)
    (hobserve : ∀ result : ResolvedRunResult α,
      DirectDetailedResult.done result ∈ support
        (runDirectResolvedDetailedFromTable context fuel table computation) →
      PendingCoveredBy candidates result.context →
      ∀ output ∈ support
        (observe result.context result.remaining result.value candidates),
        PrivateWitnessCovered output)
    (output : PrivateWitnessPlanOutput)
    (houtput : output ∈ support
      (runDirectWitnessPlanObserve observe candidates context fuel table computation)) :
    PrivateWitnessCovered output := by
  unfold runDirectWitnessPlanObserve at houtput
  rw [mem_support_bind_iff] at houtput
  obtain ⟨result, hresult, hfinish⟩ := houtput
  cases result with
  | stoppedFuel =>
      simp [finishDirectWitnessPlanObserve] at hfinish
      subst output
      simp [PrivateWitnessCovered]
  | stoppedOrdinary =>
      simp [finishDirectWitnessPlanObserve] at hfinish
      subst output
      simp [PrivateWitnessCovered]
  | stoppedPrivate witness =>
      simp [finishDirectWitnessPlanObserve] at hfinish
      subst output
      intro found heq
      simp only [Option.some.injEq] at heq
      subst found
      exact candidateListHits_of_stoppedPrivate_mem_runDirectResolvedWitnessFromTable
        candidates computation context fuel table witness hcovered hbound hresult
  | done result =>
      have hdetailed : DirectDetailedResult.done result ∈ support
          (runDirectResolvedDetailedFromTable context fuel table computation) := by
        rw [← map_erase_runDirectResolvedWitnessFromTable computation context fuel table,
          support_map]
        exact ⟨DirectWitnessResult.done result, hresult, rfl⟩
      have hnextCovered := pendingCoveredBy_of_done_runDirectResolvedDetailedFromTable
        candidates computation context fuel table result hcovered hbound hdetailed
      exact hobserve result hdetailed hnextCovered output hfinish

theorem privateWitnessCovered_of_mem_classifyDirectWitnessPlanObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (context : DeferredContext) (fuel : Nat) (value : α) (candidates : List Probe)
    (hcovered : PendingCoveredBy candidates context)
    (hobserve : ∀ output ∈ support (observe context fuel value candidates),
      PrivateWitnessCovered output)
    (output : PrivateWitnessPlanOutput)
    (houtput : output ∈ support
      (classifyDirectWitnessPlanObserve table observe context fuel value candidates)) :
    PrivateWitnessCovered output := by
  classical
  unfold classifyDirectWitnessPlanObserve at houtput
  by_cases hhit : PrivateStructuralHit context
  · simp [hhit] at houtput
    subst output
    intro witness heq
    simp only [Option.some.injEq] at heq
    subst witness
    exact candidateListHits_privateHitWitnessOf context candidates hcovered hhit
  · simp only [hhit, ↓reduceDIte] at houtput
    by_cases hcompletable : DeferredCompletable table context
    · simp only [hcompletable, ↓reduceIte] at houtput
      exact hobserve output houtput
    · simp [hcompletable] at houtput
      subst output
      simp [PrivateWitnessCovered]

theorem privateWitnessCovered_of_mem_canonicalizeDirectWitnessPlanObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (context : DeferredContext) (fuel : Nat) (value : α) (candidates : List Probe)
    (hcovered : PendingCoveredBy candidates context)
    (hobserve : ∀ output ∈ support
      (observe (canonicalizeMaterializedValues table context) fuel value candidates),
      PrivateWitnessCovered output)
    (output : PrivateWitnessPlanOutput)
    (houtput : output ∈ support
      (canonicalizeDirectWitnessPlanObserve table observe context fuel value candidates)) :
    PrivateWitnessCovered output := by
  classical
  let canonical := canonicalizeMaterializedValues table context
  have hcanonicalCovered : PendingCoveredBy candidates canonical :=
    (pendingCoveredBy_canonicalize_iff table candidates context).2 hcovered
  unfold canonicalizeDirectWitnessPlanObserve at houtput
  by_cases hhit : PrivateStructuralHit canonical
  · simp [canonical, hhit] at houtput
    subst output
    intro witness heq
    simp only [Option.some.injEq] at heq
    subst witness
    exact candidateListHits_privateHitWitnessOf canonical candidates hcanonicalCovered hhit
  · simp only [canonical, hhit, ↓reduceDIte] at houtput
    by_cases hpublished : PublishedValues context.state
    · simp only [hpublished, ↓reduceIte] at houtput
      exact privateWitnessCovered_of_mem_classifyDirectWitnessPlanObserve table observe canonical
        fuel value candidates hcanonicalCovered hobserve output houtput
    · simp [hpublished] at houtput
      subst output
      simp [PrivateWitnessCovered]

noncomputable def directDetailedBoundaryNormalizedPrivateWitnessPlanObserve
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) →
      List Probe → ProbComp PrivateWitnessPlanOutput)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ProbComp PrivateWitnessPlanOutput := by
  classical
  exact OracleComp.construct
    (C := fun _ : OracleComp (OracleWorld + SigningSpec) α =>
      (DeferredContext → Nat → (α × SplitHashCache) →
        List Probe → ProbComp PrivateWitnessPlanOutput) →
      List Probe → DeferredContext → Nat → (OtsSecretIndex → HashOutput) →
        SplitHashCache → ProbComp PrivateWitnessPlanOutput)
    (fun value observe candidates context fuel _table cache =>
      observe context fuel (value, cache) candidates)
    (fun query _next recursivelyRun observe candidates context fuel table cache =>
      match query with
      | .inl (.inl n) =>
          runDirectWitnessPlanObserve
            (canonicalizeDirectWitnessPlanObserve table
              (fun nextContext remaining value nextCandidates =>
                recursivelyRun value.1 observe nextCandidates nextContext remaining table
                  value.2))
            candidates context fuel table ((splitUniformImpl n).run cache)
      | .inl (.inr input) =>
          let plan := purePlanProbingHashQuery parameter input context.state
          let nextCandidates := appendPlannedCandidate candidates
            (rootAwarePlannedCandidate? parameter input context.state)
          runDirectWitnessPlanObserve
            (canonicalizeDirectWitnessPlanObserve table
              (fun nextContext remaining value laterCandidates =>
                recursivelyRun value.1 observe laterCandidates nextContext remaining table
                  value.2))
            nextCandidates context fuel table
              ((probingHashQueryAfterPlan parameter input plan).run cache)
      | .inr message =>
          runDirectWitnessPlanObserve
            (canonicalizeDirectWitnessPlanObserve table
              (fun nextContext remaining value nextCandidates =>
                recursivelyRun value.1 observe nextCandidates nextContext remaining table
                  value.2))
            candidates context fuel table
              ((maskedSign parameter root ftsSecret message).run cache))
    computation observe candidates context fuel table cache

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem map_erase_directDetailedBoundaryNormalizedPrivateWitnessPlanObserve
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) →
      List Probe → ProbComp PrivateWitnessPlanOutput)
    (boolObserve : DeferredContext → Nat → (α × SplitHashCache) →
      List Probe → ProbComp (Bool × List Probe))
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hproject : ∀ nextContext remaining value nextCandidates,
      erasePrivateWitnessPlanOutput <$>
          observe nextContext remaining value nextCandidates =
        boolObserve nextContext remaining value nextCandidates) :
    erasePrivateWitnessPlanOutput <$>
        directDetailedBoundaryNormalizedPrivateWitnessPlanObserve parameter root ftsSecret
          computation observe candidates context fuel table cache =
      directDetailedBoundaryNormalizedPrivatePlanObserve parameter root ftsSecret computation
        boolObserve candidates context fuel table cache := by
  induction computation using OracleComp.inductionOn generalizing candidates context fuel cache with
  | pure value =>
      rw [directDetailedBoundaryNormalizedPrivateWitnessPlanObserve,
        OracleComp.construct_pure,
        directDetailedBoundaryNormalizedPrivatePlanObserve, OracleComp.construct_pure]
      exact hproject context fuel (value, cache) candidates
  | query_bind query next ih =>
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              rw [directDetailedBoundaryNormalizedPrivateWitnessPlanObserve,
                OracleComp.construct_query_bind,
                directDetailedBoundaryNormalizedPrivatePlanObserve,
                OracleComp.construct_query_bind]
              apply map_erase_runDirectWitnessPlanObserve
              intro nextContext remaining value nextCandidates
              apply map_erase_canonicalizeDirectWitnessPlanObserve
              intro finalContext finalRemaining finalValue finalCandidates
              exact ih finalValue.1 finalCandidates finalContext finalRemaining finalValue.2
          | inr input =>
              rw [directDetailedBoundaryNormalizedPrivateWitnessPlanObserve,
                OracleComp.construct_query_bind,
                directDetailedBoundaryNormalizedPrivatePlanObserve,
                OracleComp.construct_query_bind]
              let plan := purePlanProbingHashQuery parameter input context.state
              let nextCandidates := appendPlannedCandidate candidates
                (rootAwarePlannedCandidate? parameter input context.state)
              apply map_erase_runDirectWitnessPlanObserve
              intro nextContext remaining value laterCandidates
              apply map_erase_canonicalizeDirectWitnessPlanObserve
              intro finalContext finalRemaining finalValue finalCandidates
              exact ih finalValue.1 finalCandidates finalContext finalRemaining finalValue.2
      | inr message =>
          rw [directDetailedBoundaryNormalizedPrivateWitnessPlanObserve,
            OracleComp.construct_query_bind,
            directDetailedBoundaryNormalizedPrivatePlanObserve,
            OracleComp.construct_query_bind]
          apply map_erase_runDirectWitnessPlanObserve
          intro nextContext remaining value nextCandidates
          apply map_erase_canonicalizeDirectWitnessPlanObserve
          intro finalContext finalRemaining finalValue finalCandidates
          exact ih finalValue.1 finalCandidates finalContext finalRemaining finalValue.2

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem privateWitnessCovered_of_mem_directDetailedBoundaryNormalizedPrivateWitnessPlanObserve
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) →
      List Probe → ProbComp PrivateWitnessPlanOutput)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hcovered : PendingCoveredBy candidates context)
    (hobserve : ∀ nextContext remaining value nextCandidates output,
      PendingCoveredBy nextCandidates nextContext →
      output ∈ support (observe nextContext remaining value nextCandidates) →
      PrivateWitnessCovered output)
    (output : PrivateWitnessPlanOutput)
    (houtput : output ∈ support
      (directDetailedBoundaryNormalizedPrivateWitnessPlanObserve parameter root ftsSecret
        computation observe candidates context fuel table cache)) :
    PrivateWitnessCovered output := by
  induction computation using OracleComp.inductionOn generalizing candidates context fuel cache output with
  | pure value =>
      rw [directDetailedBoundaryNormalizedPrivateWitnessPlanObserve,
        OracleComp.construct_pure] at houtput
      exact hobserve context fuel (value, cache) candidates output hcovered houtput
  | query_bind query next ih =>
      rw [directDetailedBoundaryNormalizedPrivateWitnessPlanObserve,
        OracleComp.construct_query_bind] at houtput
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              have hprobeBound : ((splitUniformImpl n).run cache).IsQueryBoundP
                  (IsUncoveredProbe candidates) 0 :=
                OracleComp.IsQueryBoundP.of_imp (isUncoveredProbe_imp_isProbe candidates)
                  (splitUniformImpl_probeFree n cache)
              apply privateWitnessCovered_of_mem_runDirectWitnessPlanObserve _ candidates
                context fuel table ((splitUniformImpl n).run cache) hcovered hprobeBound
                (output := output) (houtput := houtput)
              intro result _hdetailed hresultCovered nextOutput hnextOutput
              apply privateWitnessCovered_of_mem_canonicalizeDirectWitnessPlanObserve table _
                result.context result.remaining result.value candidates hresultCovered
                (output := nextOutput) (houtput := hnextOutput)
              intro finalOutput hfinalOutput
              have hcanonicalCovered : PendingCoveredBy candidates
                  (canonicalizeMaterializedValues table result.context) :=
                (pendingCoveredBy_canonicalize_iff table candidates result.context).2
                  hresultCovered
              exact ih result.value.1 candidates
                (canonicalizeMaterializedValues table result.context) result.remaining
                result.value.2 hcanonicalCovered (output := finalOutput) hfinalOutput
          | inr input =>
              let plan := purePlanProbingHashQuery parameter input context.state
              let nextCandidates := appendPlannedCandidate candidates
                (rootAwarePlannedCandidate? parameter input context.state)
              have hplanMem : ∀ candidate, plan.candidate? = some candidate →
                  candidate ∈ nextCandidates := by
                intro candidate hcandidate
                have hrecorded := rootAwarePlannedCandidate?_eq_of_plan_some hcandidate
                simp [nextCandidates, appendPlannedCandidate, hrecorded]
              have hprobeBound := probingHashQueryAfterPlan_probeBound parameter input plan
                nextCandidates hplanMem cache
              have hnextCovered : PendingCoveredBy nextCandidates context := by
                have hsublist : candidates.Sublist nextCandidates := by
                  unfold nextCandidates appendPlannedCandidate
                  cases rootAwarePlannedCandidate? parameter input context.state <;> simp
                exact hcovered.mono_candidates hsublist
              apply privateWitnessCovered_of_mem_runDirectWitnessPlanObserve _ nextCandidates
                context fuel table ((probingHashQueryAfterPlan parameter input plan).run cache)
                hnextCovered hprobeBound (output := output) (houtput := houtput)
              intro result _hdetailed hresultCovered nextOutput hnextOutput
              apply privateWitnessCovered_of_mem_canonicalizeDirectWitnessPlanObserve table _
                result.context result.remaining result.value nextCandidates hresultCovered
                (output := nextOutput) (houtput := hnextOutput)
              intro finalOutput hfinalOutput
              have hcanonicalCovered : PendingCoveredBy nextCandidates
                  (canonicalizeMaterializedValues table result.context) :=
                (pendingCoveredBy_canonicalize_iff table nextCandidates result.context).2
                  hresultCovered
              exact ih result.value.1 nextCandidates
                (canonicalizeMaterializedValues table result.context) result.remaining
                result.value.2 hcanonicalCovered (output := finalOutput) hfinalOutput
      | inr message =>
          have hprobeBound : ((maskedSign parameter root ftsSecret message).run cache).IsQueryBoundP
              (IsUncoveredProbe candidates) 0 :=
            OracleComp.IsQueryBoundP.of_imp (isUncoveredProbe_imp_isProbe candidates)
              (maskedSign_probeFree parameter root ftsSecret message cache)
          apply privateWitnessCovered_of_mem_runDirectWitnessPlanObserve _ candidates context
            fuel table ((maskedSign parameter root ftsSecret message).run cache) hcovered
            hprobeBound (output := output) (houtput := houtput)
          intro result _hdetailed hresultCovered nextOutput hnextOutput
          apply privateWitnessCovered_of_mem_canonicalizeDirectWitnessPlanObserve table _
            result.context result.remaining result.value candidates hresultCovered
            (output := nextOutput) (houtput := hnextOutput)
          intro finalOutput hfinalOutput
          have hcanonicalCovered : PendingCoveredBy candidates
              (canonicalizeMaterializedValues table result.context) :=
            (pendingCoveredBy_canonicalize_iff table candidates result.context).2 hresultCovered
          exact ih result.value.1 candidates
            (canonicalizeMaterializedValues table result.context) result.remaining result.value.2
            hcanonicalCovered (output := finalOutput) hfinalOutput

noncomputable def retainedResolvedFinalizationPrivateWitnessPlanObserve
    (_table : OtsSecretIndex → HashOutput) (_root : Digest)
    (context : DeferredContext) (_fuel : Nat)
    (_value : RetainedRestResult × SplitHashCache) (candidates : List Probe) :
    ProbComp PrivateWitnessPlanOutput := by
  classical
  exact if hhit : PrivateStructuralHit context then
    pure (some (privateHitWitnessOf context hhit), candidates)
  else
    pure (none, candidates)

theorem map_erase_retainedResolvedFinalizationPrivateWitnessPlanObserve
    (table : OtsSecretIndex → HashOutput) (root : Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : RetainedRestResult × SplitHashCache) (candidates : List Probe) :
    erasePrivateWitnessPlanOutput <$>
        retainedResolvedFinalizationPrivateWitnessPlanObserve table root context fuel value
          candidates =
      retainedResolvedFinalizationPrivatePlanObserve table root context fuel value candidates := by
  classical
  unfold retainedResolvedFinalizationPrivateWitnessPlanObserve
    retainedResolvedFinalizationPrivatePlanObserve
    retainedResolvedFinalizationPrivateObserve classifyDirectPrivateObserve
  by_cases hhit : PrivateStructuralHit context <;>
    simp [hhit, erasePrivateWitnessPlanOutput]

theorem privateWitnessCovered_of_mem_retainedResolvedFinalizationPrivateWitnessPlanObserve
    (table : OtsSecretIndex → HashOutput) (root : Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : RetainedRestResult × SplitHashCache) (candidates : List Probe)
    (hcovered : PendingCoveredBy candidates context)
    (output : PrivateWitnessPlanOutput)
    (houtput : output ∈ support
      (retainedResolvedFinalizationPrivateWitnessPlanObserve table root context fuel value
        candidates)) :
    PrivateWitnessCovered output := by
  classical
  unfold retainedResolvedFinalizationPrivateWitnessPlanObserve at houtput
  by_cases hhit : PrivateStructuralHit context
  · simp [hhit] at houtput
    subst output
    intro witness heq
    simp only [Option.some.injEq] at heq
    subst witness
    exact candidateListHits_privateHitWitnessOf context candidates hcovered hhit
  · simp [hhit] at houtput
    subst output
    simp [PrivateWitnessCovered]

noncomputable def granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (candidates : List Probe) :
    ProbComp PrivateWitnessPlanOutput :=
  directDetailedBoundaryNormalizedPrivateWitnessPlanObserve parameter value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
    (retainedResolvedFinalizationPrivateWitnessPlanObserve table value.1)
    candidates context fuel table value.2

theorem map_erase_granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (candidates : List Probe) :
    erasePrivateWitnessPlanOutput <$>
        granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve adversary parameter table
          ftsSecret context fuel value candidates =
      granularDetailedRetainedRestNormalizedPrivatePlanObserve adversary parameter table
        ftsSecret context fuel value candidates := by
  unfold granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve
    granularDetailedRetainedRestNormalizedPrivatePlanObserve
  apply map_erase_directDetailedBoundaryNormalizedPrivateWitnessPlanObserve
  intro nextContext remaining nextValue nextCandidates
  exact map_erase_retainedResolvedFinalizationPrivateWitnessPlanObserve table value.1 nextContext
    remaining nextValue nextCandidates

theorem privateWitnessCovered_of_mem_granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (candidates : List Probe)
    (hcovered : PendingCoveredBy candidates context)
    (output : PrivateWitnessPlanOutput)
    (houtput : output ∈ support
      (granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve adversary parameter table
        ftsSecret context fuel value candidates)) :
    PrivateWitnessCovered output := by
  unfold granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve at houtput
  apply privateWitnessCovered_of_mem_directDetailedBoundaryNormalizedPrivateWitnessPlanObserve
    parameter value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
    (retainedResolvedFinalizationPrivateWitnessPlanObserve table value.1)
    candidates context fuel table value.2 hcovered
    (output := output) (houtput := houtput)
  intro nextContext remaining nextValue nextCandidates nextOutput hnextCovered hnextOutput
  exact privateWitnessCovered_of_mem_retainedResolvedFinalizationPrivateWitnessPlanObserve table
    value.1 nextContext remaining nextValue nextCandidates hnextCovered nextOutput hnextOutput

noncomputable def granularAllDirectBoundaryNormalizedPrivateWitnessPlan
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp PrivateWitnessPlanOutput :=
  runDirectWitnessPlanObserve
    (granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve adversary parameter table
      ftsSecret)
    []
    { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
      values := emptyDeferredStructuralValues }
    fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)

theorem map_erase_granularAllDirectBoundaryNormalizedPrivateWitnessPlan
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    erasePrivateWitnessPlanOutput <$>
        granularAllDirectBoundaryNormalizedPrivateWitnessPlan adversary parameter table ftsSecret
          fuel =
      granularAllDirectBoundaryNormalizedPrivatePlan adversary parameter table ftsSecret fuel := by
  unfold granularAllDirectBoundaryNormalizedPrivateWitnessPlan
    granularAllDirectBoundaryNormalizedPrivatePlan
  apply map_erase_runDirectWitnessPlanObserve
  intro nextContext remaining value nextCandidates
  exact map_erase_granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve adversary
    parameter table ftsSecret nextContext remaining value nextCandidates

end SphincsSecurity.Concrete.OtsProbeSimulation
