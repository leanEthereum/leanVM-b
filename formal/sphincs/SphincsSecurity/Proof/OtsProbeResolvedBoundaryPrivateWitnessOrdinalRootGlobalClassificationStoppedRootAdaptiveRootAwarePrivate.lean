import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptivePrefix
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedLift

/-!
# Root-aware private hash execution

The delayed proof executor records every root-aware candidate, so it must execute that same probe.
This module relates the corrected private executor to the materialized public executor used by the
observed game.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

theorem probingHashQueryAfterRootAwarePlan_uncoveredProbeBound
    (parameter : PublicParameter) (input : HashInput) (plan : PlannedHashQuery)
    (candidates : List Probe)
    (hplanned : ∀ candidate,
      rootAwareCandidateForPlan? parameter input plan = some candidate → candidate ∈ candidates)
    (cache : SplitHashCache) :
    ((probingHashQueryAfterRootAwarePlan parameter input plan).run cache).IsQueryBoundP
      (IsUncoveredProbe candidates) 0 := by
  unfold probingHashQueryAfterRootAwarePlan
  rw [StateT.run_bind]
  apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
  · cases hcandidate : rootAwareCandidateForPlan? parameter input plan with
    | none => simp [executeCandidate?]
    | some candidate =>
        have hmem := hplanned candidate hcandidate
        change (LazyRevealProbe.probeQuery candidate.coordinate candidate.candidate).IsQueryBoundP
          (IsUncoveredProbe candidates) 0
        unfold LazyRevealProbe.probeQuery
        rw [OracleComp.isQueryBoundP_query_iff]
        simp [IsUncoveredProbe, hmem]
  · intro result _hresult
    cases plan.action with
    | ordinary =>
        exact OracleComp.IsQueryBoundP.of_imp
          (isUncoveredProbe_imp_isProbe candidates)
          (splitHashQuery_probeFree (.ordinary input) result.2)
    | resolve coordinate =>
        exact OracleComp.IsQueryBoundP.of_imp
          (isUncoveredProbe_imp_isProbe candidates)
          (resolveKnownInput_probeFree parameter coordinate input result.2)

set_option maxRecDepth 100000 in
theorem runDirectResolvedWitnessFromTable_rootAwarePrivate_eq_public
    (parameter : PublicParameter) (input : HashInput) (plan : PlannedHashQuery)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    runDirectResolvedWitnessFromTable context fuel table
        ((probingHashQueryAfterRootAwarePlan parameter input plan).run cache) =
      runDirectResolvedWitnessFromTable context fuel table
        ((probingHashQueryAfterRootAwarePublicPlan parameter input context.state plan).run cache) := by
  unfold probingHashQueryAfterRootAwarePlan
    probingHashQueryAfterRootAwarePublicPlan probingHashQueryPublicAction
  cases hcandidate : rootAwareCandidateForPlan? parameter input plan with
  | none =>
      simp only [executeCandidate?, pure_bind]
      cases haction : plan.action with
      | ordinary => rfl
      | resolve coordinate =>
          exact runDirectResolvedWitnessFromTable_resolveKnownInput_eq_public parameter
            coordinate input context fuel table cache
  | some candidate =>
      simp only [executeCandidate?]
      rw [StateT.run_bind, StateT.run_bind, runDirectResolvedWitnessFromTable_bind,
        runDirectResolvedWitnessFromTable_bind]
      simp only [probe, StateT.run_liftM, LazyRevealProbe.probeQuery,
        runDirectResolvedWitnessFromTable_probe_query_bind]
      cases fuel with
      | zero => rfl
      | succ remaining =>
          by_cases hrevealed : candidate.coordinate ∈ context.state.revealed
          · simp only [hrevealed, ↓reduceIte]
            simp only [runDirectResolvedWitnessFromTable]
            cases haction : plan.action with
            | ordinary => rfl
            | resolve coordinate =>
                exact runDirectResolvedWitnessFromTable_resolveKnownInput_eq_public parameter
                  coordinate input context remaining table cache
          · simp only [hrevealed, ↓reduceIte]
            let nextContext : DeferredContext :=
              { context with state :=
                  context.state.addPending candidate.coordinate candidate.candidate }
            rw [show
              runDirectResolvedWitnessFromTable nextContext remaining table (pure ((), cache)) =
                pure (.done ⟨nextContext, remaining, ((), cache), table⟩) by
              simp [runDirectResolvedWitnessFromTable]]
            simp only [pure_bind]
            cases haction : plan.action with
            | ordinary => rfl
            | resolve coordinate =>
                have hbase := runDirectResolvedWitnessFromTable_resolveKnownInput_eq_public
                  parameter coordinate input nextContext remaining table cache
                have hpublic := resolvePublicKnownInput_eq_of_values_eq parameter
                  (left := nextContext.state) (right := context.state) (by rfl) coordinate input
                rw [hpublic] at hbase
                exact hbase

theorem witnessMaterializedStableCouplesBetweenPositive_rootAwarePublicPlan
    (table : OtsSecretIndex → HashOutput)
    (parameter : PublicParameter) (input : HashInput)
    (publicState : LazyRevealProbe.State Coordinate) (plan : PlannedHashQuery) :
    WitnessMaterializedStableCouplesBetweenPositive table
      (probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan)
      (probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan) := by
  unfold probingHashQueryAfterRootAwarePublicPlan
  cases hcandidate : rootAwareCandidateForPlan? parameter input plan with
  | none =>
      simp only [executeCandidate?, pure_bind]
      intro left right leftFuel rightFuel leftCache rightCache _hpositive
      exact witnessMaterializedStableCouplesBetween_publicAction table parameter input
        publicState plan.action left right leftFuel rightFuel leftCache rightCache
  | some candidate =>
      apply (witnessMaterializedStableCouplesBetween_probe table candidate).bind
      intro _
      exact witnessMaterializedStableCouplesBetween_publicAction table parameter input
        publicState plan.action

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedWitness_rootAwarePrivate_rootAwarePublic
    (table : OtsSecretIndex → HashOutput)
    (parameter : PublicParameter) (input : HashInput)
    (publicState : LazyRevealProbe.State Coordinate) (plan : PlannedHashQuery)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hpublicState : publicState = left.state)
    (hpositive : 0 < leftFuel)
    (hcontext : FinalizationContextLE table left right)
    (hfuel : leftFuel ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state) :
    RelTriple
      (runDirectResolvedWitnessFromTable left leftFuel table
        ((probingHashQueryAfterRootAwarePlan parameter input plan).run leftCache))
      (runDirectResolvedDetailedFromTable right rightFuel table
        ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run
          rightCache))
      (DirectWitnessMaterializedStableRunEq table) := by
  subst publicState
  rw [runDirectResolvedWitnessFromTable_rootAwarePrivate_eq_public parameter input plan left
    leftFuel table leftCache]
  exact witnessMaterializedStableCouplesBetweenPositive_rootAwarePublicPlan table parameter input
    left.state plan left right leftFuel rightFuel leftCache rightCache hpositive hcontext hfuel
    hcache hrevealed hvalues hpublished hrightMaterialized

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedWitness_rootAwarePrivate_observedMaterialized
    (table : OtsSecretIndex → HashOutput)
    (parameter : PublicParameter) (input : HashInput)
    (publicState : LazyRevealProbe.State Coordinate) (plan : PlannedHashQuery)
    (observations : List CleanProbeObservation)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hpublicState : publicState = left.state)
    (hpositive : 0 < leftFuel)
    (hcontext : FinalizationContextLE table left right)
    (hfuel : leftFuel ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state) :
    RelTriple
      (runDirectResolvedWitnessFromTable left leftFuel table
        ((probingHashQueryAfterRootAwarePlan parameter input plan).run leftCache))
      (runObservedCleanFromTable observations right.state rightFuel table
        ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run
          rightCache))
      (WitnessObservedStepRel table
        (observationsAfterCandidate observations right.state
          (rootAwareCandidateForPlan? parameter input plan))) := by
  have hbase := relTriple_runDirectResolvedWitness_rootAwarePrivate_rootAwarePublic table parameter
    input publicState plan left right leftFuel rightFuel leftCache rightCache hpublicState hpositive
    hcontext hfuel hcache hrevealed hvalues hpublished hrightMaterialized
  have hstrength : RelTriple
      (runDirectResolvedWitnessFromTable left leftFuel table
        ((probingHashQueryAfterRootAwarePlan parameter input plan).run leftCache))
      (runDirectResolvedDetailedFromTable right rightFuel table
        ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run
          rightCache))
      (fun leftResult rightResult =>
        WitnessObservedStepRel table
          (observationsAfterCandidate observations right.state
            (rootAwareCandidateForPlan? parameter input plan))
          leftResult
          (projectDirectDetailedObserved
            (observationsAfterCandidate observations right.state
              (rootAwareCandidateForPlan? parameter input plan)) rightResult)) := by
    apply relTriple_post_mono hbase
    intro leftResult rightResult hrelation
    exact ⟨rightResult, rfl, hrelation⟩
  have hmapped := relTriple_map
    (R := fun leftResult rightResult =>
      WitnessObservedStepRel table
        (observationsAfterCandidate observations right.state
          (rootAwareCandidateForPlan? parameter input plan)) leftResult rightResult)
    (f := id)
    (g := projectDirectDetailedObserved
      (observationsAfterCandidate observations right.state
        (rootAwareCandidateForPlan? parameter input plan))) hstrength
  have hpost : RelTriple
      (id <$> runDirectResolvedWitnessFromTable left leftFuel table
        ((probingHashQueryAfterRootAwarePlan parameter input plan).run leftCache))
      (projectDirectDetailedObserved
          (observationsAfterCandidate observations right.state
            (rootAwareCandidateForPlan? parameter input plan)) <$>
        runDirectResolvedDetailedFromTable right rightFuel table
          ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run
            rightCache))
      (WitnessObservedStepRel table
        (observationsAfterCandidate observations right.state
          (rootAwareCandidateForPlan? parameter input plan))) := hmapped
  rw [id_map] at hpost
  have hmap :
      projectDirectDetailedObserved
          (observationsAfterCandidate observations right.state
            (rootAwareCandidateForPlan? parameter input plan)) <$>
        runDirectResolvedDetailedFromTable right rightFuel table
          ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run
            rightCache) =
        runObservedCleanFromTable observations right.state rightFuel table
          ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run
            rightCache) := by
    rw [hrightMaterialized]
    simpa [directDeferredContext] using
      (map_projectDirectDetailedObserved_rootAwarePublic parameter input publicState plan
        observations right.state rightFuel table rightCache)
  exact relTriple_of_evalDist_eq_right (congrArg evalDist hmap) hpost

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedWitness_rootAwarePrivate_observed_firstStopped
    (table : OtsSecretIndex → HashOutput)
    (parameter : PublicParameter) (input : HashInput)
    (publicState : LazyRevealProbe.State Coordinate) (plan : PlannedHashQuery)
    (observations : List CleanProbeObservation)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hpublicState : publicState = left.state)
    (hpositive : 0 < leftFuel)
    (hcontext : FinalizationContextLE table left right)
    (hfuel : leftFuel ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state)
    (hcandidateCompletable : ∀ candidate,
      rootAwareCandidateForPlan? parameter input plan = some candidate →
      candidate.coordinate ∉ left.state.revealed →
      DeferredCompletable table
        { left with state :=
            left.state.addPending candidate.coordinate candidate.candidate })
    (htracked : CleanProbeObservationsTrackedBy observations right.state)
    (hcovered : CleanProbeObservationsCoverPending observations right.state)
    (hnextNoHit : ∀ observation ∈ observationsAfterCandidate observations right.state
      (rootAwareCandidateForPlan? parameter input plan),
      ¬observation.ExistingHiddenHit)
    (hbudget : rightFuel + right.state.pending.card < Fintype.card Digest) :
    RelTriple
      (runDirectResolvedWitnessFromTable left leftFuel table
        ((probingHashQueryAfterRootAwarePlan parameter input plan).run leftCache))
      (runObservedCleanFromTable observations right.state rightFuel table
        ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run
          rightCache))
      (WitnessObservedFirstStoppedStepRel table
        (observationsAfterCandidate observations right.state
          (rootAwareCandidateForPlan? parameter input plan))) := by
  let executionPlan : PlannedHashQuery :=
    ⟨rootAwareCandidateForPlan? parameter input plan, plan.action⟩
  have hexecution : probingHashQueryAfterRootAwarePlan parameter input plan =
      probingHashQueryAfterPlan parameter input executionPlan := by
    rfl
  have hlocal := relTriple_runDirectResolvedWitness_rootAwarePrivate_observedMaterialized table
    parameter input publicState plan observations left right leftFuel rightFuel leftCache rightCache
    hpublicState hpositive hcontext hfuel hcache hrevealed hvalues hpublished hrightMaterialized
  have hleftSupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hlocal
      (fun result => result ∈ support
        (runDirectResolvedWitnessFromTable left leftFuel table
          ((probingHashQueryAfterRootAwarePlan parameter input plan).run leftCache)))
      (fun result hresult => hresult)
  have hbothSupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleftSupported
  apply relTriple_post_mono hbothSupported
  intro leftResult rightResult hrelation
  rcases hrelation with ⟨⟨hstep, hleftSupport⟩, hrightSupport⟩
  have hnotPrivate : ∀ witness, leftResult ≠ .stoppedPrivate witness := by
    intro witness heq
    subst leftResult
    apply not_stoppedPrivate_mem_afterPlan_of_completable parameter input executionPlan left
      leftFuel table leftCache witness hpositive hcontext.leftValid hcontext.leftCompletable
    · intro candidate hcandidate hhidden
      apply hcandidateCompletable candidate
      · simpa [executionPlan] using hcandidate
      · exact hhidden
    · rw [← hexecution]
      exact hleftSupport
  apply hstep.to_firstStoppedStep_of_not_private hnotPrivate
  · intro resolved hresolved
    have htrackedResult := cleanProbeObservationsTrackedBy_of_mem_runObservedCleanFromTable
      ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run rightCache)
      observations right.state rightFuel table htracked
      (observedResolvedResult
        (observationsAfterCandidate observations right.state
          (rootAwareCandidateForPlan? parameter input plan)) resolved)
      (by simpa [hresolved] using hrightSupport)
    have hcoveredResult := cleanProbeObservationsCoverPending_of_mem_runObservedCleanFromTable
      ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run rightCache)
      observations right.state rightFuel table hcovered
      (observedResolvedResult
        (observationsAfterCandidate observations right.state
          (rootAwareCandidateForPlan? parameter input plan)) resolved)
      (by simpa [hresolved] using hrightSupport)
    apply directDeferredContext_valid_of_no_existingHiddenHit
      (observedResolvedResult
        (observationsAfterCandidate observations right.state
          (rootAwareCandidateForPlan? parameter input plan)) resolved)
      htrackedResult hcoveredResult
    intro hhit
    obtain ⟨observation, hobservation, hobservationHit⟩ := hhit
    apply hnextNoHit observation
    · simpa [observedResolvedResult] using hobservation
    · exact hobservationHit
  · intro resolved hresolved
    have hremaining := remaining_add_pending_card_le_of_mem_runObservedCleanFromTable
      ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run rightCache)
      observations right.state rightFuel table
      (observedResolvedResult
        (observationsAfterCandidate observations right.state
          (rootAwareCandidateForPlan? parameter input plan)) resolved)
      (by simpa [hresolved] using hrightSupport)
    simp only [observedResolvedResult] at hremaining
    exact (Nat.le_add_left _ _).trans (hremaining.trans_lt hbudget)

end SphincsSecurity.Concrete.OtsProbeSimulation
