import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedHash

/-!
# Adaptive stopped lift

The recursive lift stays aligned while the materialized comparison is completable. A completed
local step either supplies the ordinary aligned result or a persistent missing-chain obstruction.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def WitnessObservedFirstStoppedStepRel
    (table : OtsSecretIndex → HashOutput)
    (observations : List CleanProbeObservation)
    (left : DirectWitnessResult (α × SplitHashCache))
    (right : Option (ObservedCleanRunResult (α × SplitHashCache))) : Prop :=
  right = none ∨
    (∃ leftResult rightResult,
      left = .done leftResult ∧
      right = some (observedResolvedResult observations rightResult) ∧
      OrdinaryMaterializedRunEq table leftResult rightResult) ∨
    ∃ rightResult,
      right = some (observedResolvedResult observations rightResult) ∧
      OrdinaryMaterializedDoomedRun table rightResult ∧
      MissingChainStartHit table rightResult.context

theorem WitnessObservedStepRel.to_firstStoppedStep_of_not_private
    {table : OtsSecretIndex → HashOutput}
    {observations : List CleanProbeObservation}
    {leftResult : DirectWitnessResult (α × SplitHashCache)}
    {rightResult : Option (ObservedCleanRunResult (α × SplitHashCache))}
    (hrelation : WitnessObservedStepRel table observations leftResult rightResult)
    (hnotPrivate : ∀ witness, leftResult ≠ .stoppedPrivate witness)
    (hvalid : ∀ right,
      rightResult = some (observedResolvedResult observations right) →
        (directDeferredContext right.context.state).Valid)
    (hcard : ∀ right,
      rightResult = some (observedResolvedResult observations right) →
        right.context.state.pending.card < Fintype.card Digest) :
    WitnessObservedFirstStoppedStepRel table observations leftResult rightResult := by
  obtain ⟨detailed, hproject, hstable⟩ := hrelation
  cases detailed with
  | stopped reason =>
      left
      simpa [projectDirectDetailedObserved] using hproject.symm
  | done right =>
      have hright : rightResult = some (observedResolvedResult observations right) := by
        simpa [projectDirectDetailedObserved, observedResolvedResult] using hproject.symm
      right
      cases leftResult with
      | stoppedFuel =>
          right
          refine ⟨right, hright, hstable, ?_⟩
          exact missingChainStartHit_of_doomed_direct_valid table right.context.state
            (by rw [← hstable.2]; exact hstable.1.2) (hvalid right hright)
            (hcard right hright)

      | stoppedOrdinary =>
          right
          refine ⟨right, hright, hstable, ?_⟩
          exact missingChainStartHit_of_doomed_direct_valid table right.context.state
            (by rw [← hstable.2]; exact hstable.1.2) (hvalid right hright)
            (hcard right hright)
      | stoppedPrivate witness => exact (hnotPrivate witness rfl).elim
      | done left =>
          rcases hstable with hclean | hdoomed
          · left
            exact ⟨left, right, rfl, hright, hclean⟩
          · right
            refine ⟨right, hright, hdoomed, ?_⟩
            exact missingChainStartHit_of_doomed_direct_valid table right.context.state
              (by rw [← hdoomed.2]; exact hdoomed.1.2) (hvalid right hright)
              (hcard right hright)

set_option maxRecDepth 100000 in
theorem not_stoppedPrivate_mem_runDirectResolvedWitnessFromTable_of_probeFree
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (witness : PrivateHitWitness)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hprobeFree : computation.IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 0)
    (hresult : DirectWitnessResult.stoppedPrivate witness ∈ support
      (runDirectResolvedWitnessFromTable context fuel table computation)) : False := by
  have hdetailed : DirectDetailedResult.stopped .privateStructuralHit ∈ support
      (runDirectResolvedDetailedFromTable context fuel table computation) := by
    rw [← map_erase_runDirectResolvedWitnessFromTable computation context fuel table, support_map]
    exact ⟨.stoppedPrivate witness, hresult, rfl⟩
  have hcanonicalCompletable :=
    (valid_completable_canonicalizeMaterializedValues table context hvalid hcompletable).2
  exact canonicalPrivateSafeResult_of_probeFree computation context fuel table hprobeFree
    (not_privateStructuralHit_of_deferredCompletable hcompletable)
    (not_privateStructuralHit_of_deferredCompletable hcanonicalCompletable)
    (.stopped .privateStructuralHit) hdetailed

set_option maxRecDepth 100000 in
theorem not_stoppedPrivate_mem_afterPlan_of_completable
    (parameter : PublicParameter) (input : HashInput) (plan : PlannedHashQuery)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (witness : PrivateHitWitness)
    (hpositive : 0 < fuel) (hvalid : context.Valid)
    (hcompletable : DeferredCompletable table context)
    (hnextCompletable : ∀ candidate,
      plan.candidate? = some candidate → candidate.coordinate ∉ context.state.revealed →
        DeferredCompletable table
          ({ context with state :=
            context.state.addPending candidate.coordinate candidate.candidate } :
            DeferredContext))
    (hresult : DirectWitnessResult.stoppedPrivate witness ∈ support
      (runDirectResolvedWitnessFromTable context fuel table
        ((probingHashQueryAfterPlan parameter input plan).run cache))) : False := by
  rw [runDirectResolvedWitnessFromTable_afterPlan_eq_publicPlan parameter input plan context fuel
    table cache] at hresult
  unfold probingHashQueryAfterPublicPlan at hresult
  cases hcandidate : plan.candidate? with
  | none =>
      rw [hcandidate] at hresult
      simp only [executeCandidate?, runDirectResolvedWitnessFromTable, pure_bind] at hresult
      exact not_stoppedPrivate_mem_runDirectResolvedWitnessFromTable_of_probeFree
        ((probingHashQueryPublicAction parameter input context.state plan.action).run cache)
        context fuel table witness hvalid hcompletable
        (probingHashQueryPublicAction_probeFree parameter input context.state plan.action cache)
        hresult
  | some candidate =>
      rw [hcandidate] at hresult
      simp only [executeCandidate?, StateT.run_bind, probe, StateT.run_liftM,
        LazyRevealProbe.probeQuery, bind_assoc, pure_bind] at hresult
      rw [runDirectResolvedWitnessFromTable_probe_query_bind] at hresult
      cases fuel with
      | zero => omega
      | succ remaining =>
          by_cases hrevealed : candidate.coordinate ∈ context.state.revealed
          · simp only [hrevealed, ↓reduceIte] at hresult
            exact not_stoppedPrivate_mem_runDirectResolvedWitnessFromTable_of_probeFree
              ((probingHashQueryPublicAction parameter input context.state plan.action).run cache)
              context remaining table witness hvalid hcompletable
              (probingHashQueryPublicAction_probeFree parameter input context.state plan.action
                cache) hresult

          · simp only [hrevealed, ↓reduceIte] at hresult
            let nextContext : DeferredContext :=
              { context with state :=
                  context.state.addPending candidate.coordinate candidate.candidate }
            have hnextCompletable' : DeferredCompletable table nextContext :=
              hnextCompletable candidate hcandidate hrevealed
            have hnextValid : nextContext.Valid :=
              hvalid.addPending_of_completable candidate.coordinate candidate.candidate
                hnextCompletable'
            exact not_stoppedPrivate_mem_runDirectResolvedWitnessFromTable_of_probeFree
              ((probingHashQueryPublicAction parameter input context.state plan.action).run cache)
              nextContext remaining table witness hnextValid hnextCompletable'
              (probingHashQueryPublicAction_probeFree parameter input context.state plan.action
                cache) hresult

set_option maxRecDepth 100000 in
theorem observations_eq_of_mem_runObservedCleanFromTable_of_probeFree
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (result : ObservedCleanRunResult α)
    (hprobeFree : computation.IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 0)
    (hresult : some result ∈ support
      (runObservedCleanFromTable observations state fuel table computation)) :
    result.observations = observations := by
  have hmapped : some result ∈ support
      (attachCleanProbeObservations observations <$>
        runCleanFromTable state fuel table computation) := by
    rw [map_attachCleanProbeObservations_runCleanFromTable_of_probeFree computation observations
      state fuel table hprobeFree]
    exact hresult
  rw [support_map] at hmapped
  obtain ⟨clean, _hclean, hattach⟩ := hmapped
  cases clean with
  | none => simp [attachCleanProbeObservations] at hattach
  | some clean =>
      have heq : result =
          (⟨clean.state, clean.remaining, clean.value, clean.table, observations⟩ :
            ObservedCleanRunResult α) := by
        simpa [attachCleanProbeObservations] using Option.some.inj hattach.symm
      exact congrArg ObservedCleanRunResult.observations heq

theorem not_existingHiddenHit_cleanProbeObservation_of_addPending_completable
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (candidate : Probe)
    (hcompletable : DeferredCompletable table
      ({ context with state :=
        context.state.addPending candidate.coordinate candidate.candidate } :
        DeferredContext)) :
    ¬(cleanProbeObservation context.state candidate.coordinate
      candidate.candidate).ExistingHiddenHit := by
  rintro ⟨_hhidden, output, hvalue, hcandidate⟩
  obtain ⟨completion, hcompletion⟩ := hcompletable
  have hstate : context.state.values candidate.coordinate = some output := by
    simpa [cleanProbeObservation] using hvalue
  have hpostState : (context.state.addPending candidate.coordinate
      candidate.candidate).values candidate.coordinate = some output := by
    simpa [LazyRevealProbe.State.addPending] using hstate
  have houtput := hcompletion.1 candidate.coordinate output hpostState
  have havoids := hcompletion.2.2.1 candidate.coordinate candidate.candidate (by
    simp [LazyRevealProbe.State.addPending])
  apply havoids
  rw [houtput]
  simpa [cleanProbeObservation] using hcandidate

theorem runObservedCleanFromTable_rootAwarePublic_of_revealed
    (parameter : PublicParameter) (input : HashInput)
    (publicState : LazyRevealProbe.State Coordinate) (plan : PlannedHashQuery)
    (candidate : Probe)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (remaining : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hcandidate : rootAwareCandidateForPlan? parameter input plan = some candidate)
    (hrevealed : candidate.coordinate ∈ state.revealed) :
    runObservedCleanFromTable observations state (remaining + 1) table
        ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run cache) =
      runObservedCleanFromTable
        (observations ++ [cleanProbeObservation state
          candidate.coordinate candidate.candidate])
        state remaining table
        ((probingHashQueryPublicAction parameter input publicState plan.action).run cache) := by
  unfold probingHashQueryAfterRootAwarePublicPlan
  rw [StateT.run_bind]
  simp only [executeCandidate?, hcandidate, probe, StateT.run_liftM,
    LazyRevealProbe.probeQuery]
  simp only [bind_assoc, pure_bind]
  rw [runObservedCleanFromTable_probe_query_bind]
  simp [hrevealed]

theorem runObservedCleanFromTable_rootAwarePublic_of_none
    (parameter : PublicParameter) (input : HashInput)
    (publicState : LazyRevealProbe.State Coordinate) (plan : PlannedHashQuery)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hcandidate : rootAwareCandidateForPlan? parameter input plan = none) :
    runObservedCleanFromTable observations state fuel table
        ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run cache) =
      runObservedCleanFromTable observations state fuel table
        ((probingHashQueryPublicAction parameter input publicState plan.action).run cache) := by
  unfold probingHashQueryAfterRootAwarePublicPlan
  rw [StateT.run_bind]
  simp [executeCandidate?, hcandidate]

theorem runDirectResolvedWitnessFromTable_afterPlan_of_none
    (parameter : PublicParameter) (input : HashInput) (plan : PlannedHashQuery)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hcandidate : plan.candidate? = none) :
    runDirectResolvedWitnessFromTable context fuel table
        ((probingHashQueryAfterPlan parameter input plan).run cache) =
      runDirectResolvedWitnessFromTable context fuel table
        ((probingHashQueryPublicAction parameter input context.state plan.action).run cache) := by
  rw [runDirectResolvedWitnessFromTable_afterPlan_eq_publicPlan parameter input plan context fuel
    table cache]
  unfold probingHashQueryAfterPublicPlan
  rw [hcandidate]
  simp only [executeCandidate?, pure_bind]
  unfold probingHashQueryPublicAction
  cases plan.action <;> rfl

theorem runDirectResolvedWitnessFromTable_afterPlan_of_revealed
    (parameter : PublicParameter) (input : HashInput) (plan : PlannedHashQuery)
    (candidate : Probe) (context : DeferredContext) (remaining : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hcandidate : plan.candidate? = some candidate)
    (hrevealed : candidate.coordinate ∈ context.state.revealed) :
    runDirectResolvedWitnessFromTable context (remaining + 1) table
        ((probingHashQueryAfterPlan parameter input plan).run cache) =
      runDirectResolvedWitnessFromTable context remaining table
        ((probingHashQueryPublicAction parameter input context.state plan.action).run cache) := by
  rw [runDirectResolvedWitnessFromTable_afterPlan_eq_publicPlan parameter input plan context
    (remaining + 1) table cache]
  unfold probingHashQueryAfterPublicPlan
  rw [hcandidate]
  simp only [executeCandidate?, StateT.run_bind, probe, StateT.run_liftM,
    LazyRevealProbe.probeQuery, bind_assoc, pure_bind]
  rw [runDirectResolvedWitnessFromTable_probe_query_bind]
  simp only [hrevealed, ↓reduceIte]
  unfold probingHashQueryPublicAction
  cases plan.action <;> rfl

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedWitness_afterPlan_observedMaterialized_firstStopped_of_hidden_completable
    (table : OtsSecretIndex → HashOutput)
    (parameter : PublicParameter) (input : HashInput)
    (plan : PlannedHashQuery) (candidate : Probe)
    (observations : List CleanProbeObservation)
    (left right : DeferredContext) (leftFuel remaining : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcandidate : rootAwareCandidateForPlan? parameter input plan = some candidate)
    (hpositive : 0 < leftFuel) (hstrictFuel : leftFuel < remaining + 1)
    (hcontext : FinalizationContextLE table left right)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state)
    (hhidden : candidate.coordinate ∉ right.state.revealed)
    (hpostCompletable : DeferredCompletable table
      ({ right with state :=
        right.state.addPending candidate.coordinate candidate.candidate } : DeferredContext))
    (htracked : CleanProbeObservationsTrackedBy observations right.state)
    (hcovered : CleanProbeObservationsCoverPending observations right.state)
    (hnoEarlier : ∀ observation ∈ observations, ¬observation.ExistingHiddenHit)
    (hbudget : remaining +
      (right.state.addPending candidate.coordinate candidate.candidate).pending.card <
        Fintype.card Digest) :
    RelTriple
      (runDirectResolvedWitnessFromTable left leftFuel table
        ((probingHashQueryAfterPlan parameter input plan).run leftCache))
      (runObservedCleanFromTable observations right.state (remaining + 1) table
        ((probingHashQueryAfterRootAwarePublicPlan parameter input left.state plan).run
          rightCache))
      (WitnessObservedFirstStoppedStepRel table
        (observations ++ [cleanProbeObservation right.state
          candidate.coordinate candidate.candidate])) := by
  let nextObservations := observations ++ [cleanProbeObservation right.state
    candidate.coordinate candidate.candidate]
  let nextRight : DeferredContext :=
    { right with state :=
        right.state.addPending candidate.coordinate candidate.candidate }
  have hlocal := relTriple_runDirectResolvedWitness_afterPlan_observedMaterialized table parameter
    input left.state plan observations left right leftFuel (remaining + 1) leftCache rightCache rfl
    hpositive hstrictFuel hcontext hcache hrevealed hvalues hpublished hrightMaterialized
  have hleftSupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hlocal
      (fun result => result ∈ support
        (runDirectResolvedWitnessFromTable left leftFuel table
          ((probingHashQueryAfterPlan parameter input plan).run leftCache)))
      (fun result hresult => hresult)
  have hbothSupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleftSupported
  apply relTriple_post_mono hbothSupported
  intro leftResult rightResult hrelation
  rcases hrelation with ⟨⟨hstep, hleftSupport⟩, hrightSupport⟩
  have hleftHidden : candidate.coordinate ∉ left.state.revealed := by
    rwa [hrevealed]
  have hnotPrivate : ∀ witness, leftResult ≠ .stoppedPrivate witness := by
    intro witness heq
    subst leftResult
    apply not_stoppedPrivate_mem_afterPlan_of_completable parameter input plan left leftFuel table
      leftCache witness hpositive hcontext.leftValid hcontext.leftCompletable
    · intro planned hplanned hplannedHidden
      have hsame : planned = candidate := by
        unfold rootAwareCandidateForPlan? at hcandidate
        rw [hplanned] at hcandidate
        exact Option.some.inj hcandidate
      subst planned
      exact (hcontext.addPending_both_of_right_completable candidate.coordinate
        candidate.candidate hpostCompletable).leftCompletable
    · exact hleftSupport
  have hnextTracked : CleanProbeObservationsTrackedBy nextObservations nextRight.state := by
    exact cleanProbeObservationsTrackedBy_append_hidden htracked candidate.coordinate
      candidate.candidate hhidden
  have hnextCovered : CleanProbeObservationsCoverPending nextObservations nextRight.state := by
    exact cleanProbeObservationsCoverPending_append_hidden hcovered candidate.coordinate
      candidate.candidate hhidden
  have hnewNoHit : ¬(cleanProbeObservation right.state candidate.coordinate
      candidate.candidate).ExistingHiddenHit :=
    not_existingHiddenHit_cleanProbeObservation_of_addPending_completable table right candidate
      hpostCompletable
  have hnextNoHit : ∀ observation ∈ nextObservations,
      ¬observation.ExistingHiddenHit := by
    intro observation hobservation
    simp only [nextObservations, List.mem_append, List.mem_singleton] at hobservation
    rcases hobservation with hold | rfl
    · exact hnoEarlier observation hold
    · exact hnewNoHit
  have hobservations : observationsAfterCandidate observations right.state
      (rootAwareCandidateForPlan? parameter input plan) = nextObservations := by
    simp [observationsAfterCandidate, hcandidate, nextObservations]
  rw [hobservations] at hstep
  apply hstep.to_firstStoppedStep_of_not_private hnotPrivate
  · intro resolved hresolved
    have hsupport : some (observedResolvedResult nextObservations resolved) ∈ support
        (runObservedCleanFromTable nextObservations nextRight.state remaining table
          ((probingHashQueryPublicAction parameter input left.state plan.action).run
            rightCache)) := by
      have hrightSupport' := hrightSupport
      rw [hresolved] at hrightSupport'
      rw [runObservedCleanFromTable_rootAwarePublic_of_hidden parameter input left.state plan
        candidate observations right.state remaining table rightCache hcandidate hhidden]
        at hrightSupport'
      simpa [nextObservations, nextRight] using hrightSupport'
    have hobservations := observations_eq_of_mem_runObservedCleanFromTable_of_probeFree
      ((probingHashQueryPublicAction parameter input left.state plan.action).run rightCache)
      nextObservations nextRight.state remaining table
      (observedResolvedResult nextObservations resolved)
      (probingHashQueryPublicAction_probeFree parameter input left.state plan.action rightCache)
      hsupport
    have htrackedResult := cleanProbeObservationsTrackedBy_of_mem_runObservedCleanFromTable
      ((probingHashQueryPublicAction parameter input left.state plan.action).run rightCache)
      nextObservations nextRight.state remaining table hnextTracked
      (observedResolvedResult nextObservations resolved) hsupport
    have hcoveredResult := cleanProbeObservationsCoverPending_of_mem_runObservedCleanFromTable
      ((probingHashQueryPublicAction parameter input left.state plan.action).run rightCache)
      nextObservations nextRight.state remaining table hnextCovered
      (observedResolvedResult nextObservations resolved) hsupport
    apply directDeferredContext_valid_of_no_existingHiddenHit
      (observedResolvedResult nextObservations resolved) htrackedResult hcoveredResult
    intro hhit
    obtain ⟨observation, hobservation, hobservationHit⟩ := hhit
    apply hnextNoHit observation
    · simpa [observedResolvedResult, hobservations] using hobservation
    · exact hobservationHit
  · intro resolved hresolved
    have hsupport : some (observedResolvedResult nextObservations resolved) ∈ support
        (runObservedCleanFromTable nextObservations nextRight.state remaining table
          ((probingHashQueryPublicAction parameter input left.state plan.action).run
            rightCache)) := by
      have hrightSupport' := hrightSupport
      rw [hresolved] at hrightSupport'
      rw [runObservedCleanFromTable_rootAwarePublic_of_hidden parameter input left.state plan
        candidate observations right.state remaining table rightCache hcandidate hhidden]
        at hrightSupport'
      simpa [nextObservations, nextRight] using hrightSupport'
    have hremaining := remaining_add_pending_card_le_of_mem_runObservedCleanFromTable
      ((probingHashQueryPublicAction parameter input left.state plan.action).run rightCache)
      nextObservations nextRight.state remaining table
      (observedResolvedResult nextObservations resolved) hsupport
    simp only [observedResolvedResult] at hremaining
    exact (Nat.le_add_left _ _).trans (hremaining.trans_lt hbudget)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedWitness_observed_firstStopped_of_probeFree
    (table : OtsSecretIndex → HashOutput)
    (leftComputation rightComputation :
      OracleComp (LazyRevealProbe.World Coordinate) (α × SplitHashCache))
    (observations : List CleanProbeObservation)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (hbase : RelTriple
      (runDirectResolvedWitnessFromTable left leftFuel table leftComputation)
      (runDirectResolvedDetailedFromTable right rightFuel table rightComputation)
      (DirectWitnessMaterializedStableRunEq table))
    (hleftProbeFree : leftComputation.IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 0)
    (hrightProbeFree : rightComputation.IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 0)
    (hleftValid : left.Valid) (hleftCompletable : DeferredCompletable table left)
    (hrightMaterialized : right = directDeferredContext right.state)
    (htracked : CleanProbeObservationsTrackedBy observations right.state)
    (hcovered : CleanProbeObservationsCoverPending observations right.state)
    (hnoHit : ∀ observation ∈ observations, ¬observation.ExistingHiddenHit)
    (hbudget : rightFuel + right.state.pending.card < Fintype.card Digest) :
    RelTriple
      (runDirectResolvedWitnessFromTable left leftFuel table leftComputation)
      (runObservedCleanFromTable observations right.state rightFuel table rightComputation)
      (WitnessObservedFirstStoppedStepRel table observations) := by
  have hlocal := relTriple_runDirectResolvedWitness_observed_of_probeFree table leftComputation
    rightComputation observations left right leftFuel rightFuel hbase hrightProbeFree
    hrightMaterialized
  have hleftSupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hlocal
      (fun result => result ∈ support
        (runDirectResolvedWitnessFromTable left leftFuel table leftComputation))
      (fun result hresult => hresult)
  have hbothSupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleftSupported
  apply relTriple_post_mono hbothSupported
  intro leftResult rightResult hrelation
  rcases hrelation with ⟨⟨hstep, hleftSupport⟩, hrightSupport⟩
  have hnotPrivate : ∀ witness, leftResult ≠ .stoppedPrivate witness := by
    intro witness heq
    subst leftResult
    exact (not_stoppedPrivate_mem_runDirectResolvedWitnessFromTable_of_probeFree leftComputation
      left leftFuel table witness hleftValid hleftCompletable hleftProbeFree hleftSupport).elim
  apply hstep.to_firstStoppedStep_of_not_private hnotPrivate
  · intro resolved hresolved
    have hsupport : some (observedResolvedResult observations resolved) ∈ support
        (runObservedCleanFromTable observations right.state rightFuel table rightComputation) := by
      rwa [hresolved] at hrightSupport
    have hobservations := observations_eq_of_mem_runObservedCleanFromTable_of_probeFree
      rightComputation observations right.state rightFuel table
      (observedResolvedResult observations resolved) hrightProbeFree hsupport
    have htrackedResult := cleanProbeObservationsTrackedBy_of_mem_runObservedCleanFromTable
      rightComputation observations right.state rightFuel table htracked
      (observedResolvedResult observations resolved) hsupport
    have hcoveredResult := cleanProbeObservationsCoverPending_of_mem_runObservedCleanFromTable
      rightComputation observations right.state rightFuel table hcovered
      (observedResolvedResult observations resolved) hsupport
    apply directDeferredContext_valid_of_no_existingHiddenHit
      (observedResolvedResult observations resolved) htrackedResult hcoveredResult
    intro hhit
    obtain ⟨observation, hobservation, hobservationHit⟩ := hhit
    apply hnoHit observation
    · simpa [observedResolvedResult, hobservations] using hobservation
    · exact hobservationHit
  · intro resolved hresolved
    have hsupport : some (observedResolvedResult observations resolved) ∈ support
        (runObservedCleanFromTable observations right.state rightFuel table rightComputation) := by
      rwa [hresolved] at hrightSupport
    have hremaining := remaining_add_pending_card_le_of_mem_runObservedCleanFromTable
      rightComputation observations right.state rightFuel table
      (observedResolvedResult observations resolved) hsupport
    simp only [observedResolvedResult] at hremaining
    exact (Nat.le_add_left _ _).trans (hremaining.trans_lt hbudget)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedWitness_afterPlan_observedMaterialized_firstStopped_of_revealed
    (table : OtsSecretIndex → HashOutput)
    (parameter : PublicParameter) (input : HashInput)
    (plan : PlannedHashQuery) (candidate : Probe)
    (observations : List CleanProbeObservation)
    (left right : DeferredContext) (leftFuel remaining : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcandidate : rootAwareCandidateForPlan? parameter input plan = some candidate)
    (hpositive : 0 < leftFuel) (hstrictFuel : leftFuel < remaining + 1)
    (hcontext : FinalizationContextLE table left right)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state)
    (hcandidateRevealed : candidate.coordinate ∈ right.state.revealed)
    (htracked : CleanProbeObservationsTrackedBy observations right.state)
    (hcovered : CleanProbeObservationsCoverPending observations right.state)
    (hnoEarlier : ∀ observation ∈ observations, ¬observation.ExistingHiddenHit)
    (hbudget : remaining + right.state.pending.card < Fintype.card Digest) :
    RelTriple
      (runDirectResolvedWitnessFromTable left leftFuel table
        ((probingHashQueryAfterPlan parameter input plan).run leftCache))
      (runObservedCleanFromTable observations right.state (remaining + 1) table
        ((probingHashQueryAfterRootAwarePublicPlan parameter input left.state plan).run
          rightCache))
      (WitnessObservedFirstStoppedStepRel table
        (observations ++ [cleanProbeObservation right.state
          candidate.coordinate candidate.candidate])) := by
  let nextObservations := observations ++ [cleanProbeObservation right.state
    candidate.coordinate candidate.candidate]
  have hleftRevealed : candidate.coordinate ∈ left.state.revealed := by
    rwa [hrevealed]
  have hnextTracked : CleanProbeObservationsTrackedBy nextObservations right.state := by
    exact cleanProbeObservationsTrackedBy_append_revealed htracked candidate.coordinate
      candidate.candidate hcandidateRevealed
  have hnextCovered : CleanProbeObservationsCoverPending nextObservations right.state := by
    exact cleanProbeObservationsCoverPending_append_revealed hcovered candidate.coordinate
      candidate.candidate
  have hnewNoHit : ¬(cleanProbeObservation right.state candidate.coordinate
      candidate.candidate).ExistingHiddenHit := by
    rintro ⟨hhidden, _output, _hvalue, _hcandidate⟩
    simp [cleanProbeObservation, hcandidateRevealed] at hhidden
  have hnextNoHit : ∀ observation ∈ nextObservations,
      ¬observation.ExistingHiddenHit := by
    intro observation hobservation
    simp only [nextObservations, List.mem_append, List.mem_singleton] at hobservation
    rcases hobservation with hold | rfl
    · exact hnoEarlier observation hold
    · exact hnewNoHit
  cases hplanCandidate : plan.candidate? with
  | none =>
      have hleftEq := runDirectResolvedWitnessFromTable_afterPlan_of_none parameter input plan
        left leftFuel table leftCache hplanCandidate
      have hrightEq := runObservedCleanFromTable_rootAwarePublic_of_revealed parameter input
        left.state plan candidate observations right.state remaining table rightCache hcandidate
        hcandidateRevealed
      rw [hleftEq, hrightEq]
      have hbase := witnessMaterializedStableCouplesBetween_publicAction table parameter input
        left.state plan.action left right leftFuel remaining leftCache rightCache hcontext
        (by omega) hcache hrevealed hvalues hpublished hrightMaterialized
      exact relTriple_runDirectResolvedWitness_observed_firstStopped_of_probeFree table
        ((probingHashQueryPublicAction parameter input left.state plan.action).run leftCache)
        ((probingHashQueryPublicAction parameter input left.state plan.action).run rightCache)
        nextObservations left right leftFuel remaining hbase
        (probingHashQueryPublicAction_probeFree parameter input left.state plan.action leftCache)
        (probingHashQueryPublicAction_probeFree parameter input left.state plan.action rightCache)
        hcontext.leftValid hcontext.leftCompletable hrightMaterialized hnextTracked hnextCovered
        hnextNoHit hbudget
  | some planned =>
      have hsame : planned = candidate := by
        unfold rootAwareCandidateForPlan? at hcandidate
        rw [hplanCandidate] at hcandidate
        exact Option.some.inj hcandidate
      subst planned
      cases leftFuel with
      | zero => omega
      | succ leftRemaining =>
          have hleftEq := runDirectResolvedWitnessFromTable_afterPlan_of_revealed parameter input
            plan candidate left leftRemaining table leftCache hplanCandidate hleftRevealed
          have hrightEq := runObservedCleanFromTable_rootAwarePublic_of_revealed parameter input
            left.state plan candidate observations right.state remaining table rightCache
            hcandidate hcandidateRevealed
          rw [hleftEq, hrightEq]
          have hbase := witnessMaterializedStableCouplesBetween_publicAction table parameter input
            left.state plan.action left right leftRemaining remaining leftCache rightCache hcontext
            (by omega) hcache hrevealed hvalues hpublished hrightMaterialized
          exact relTriple_runDirectResolvedWitness_observed_firstStopped_of_probeFree table
            ((probingHashQueryPublicAction parameter input left.state plan.action).run leftCache)
            ((probingHashQueryPublicAction parameter input left.state plan.action).run rightCache)
            nextObservations left right leftRemaining remaining hbase
            (probingHashQueryPublicAction_probeFree parameter input left.state plan.action leftCache)
            (probingHashQueryPublicAction_probeFree parameter input left.state plan.action rightCache)
            hcontext.leftValid hcontext.leftCompletable hrightMaterialized hnextTracked hnextCovered
            hnextNoHit hbudget

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedWitness_afterPlan_observedMaterialized_firstStopped_of_none
    (table : OtsSecretIndex → HashOutput)
    (parameter : PublicParameter) (input : HashInput) (plan : PlannedHashQuery)
    (observations : List CleanProbeObservation)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcandidate : rootAwareCandidateForPlan? parameter input plan = none)
    (hfuel : leftFuel ≤ rightFuel)
    (hcontext : FinalizationContextLE table left right)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state)
    (htracked : CleanProbeObservationsTrackedBy observations right.state)
    (hcovered : CleanProbeObservationsCoverPending observations right.state)
    (hnoHit : ∀ observation ∈ observations, ¬observation.ExistingHiddenHit)
    (hbudget : rightFuel + right.state.pending.card < Fintype.card Digest) :
    RelTriple
      (runDirectResolvedWitnessFromTable left leftFuel table
        ((probingHashQueryAfterPlan parameter input plan).run leftCache))
      (runObservedCleanFromTable observations right.state rightFuel table
        ((probingHashQueryAfterRootAwarePublicPlan parameter input left.state plan).run
          rightCache))
      (WitnessObservedFirstStoppedStepRel table observations) := by
  have hplanCandidate : plan.candidate? = none := by
    unfold rootAwareCandidateForPlan? at hcandidate
    cases hplan : plan.candidate? with
    | none => exact rfl
    | some candidate => simp [hplan] at hcandidate
  have hleftEq := runDirectResolvedWitnessFromTable_afterPlan_of_none parameter input plan left
    leftFuel table leftCache hplanCandidate
  have hrightEq := runObservedCleanFromTable_rootAwarePublic_of_none parameter input left.state
    plan observations right.state rightFuel table rightCache hcandidate
  rw [hleftEq, hrightEq]
  have hbase := witnessMaterializedStableCouplesBetween_publicAction table parameter input
    left.state plan.action left right leftFuel rightFuel leftCache rightCache hcontext hfuel hcache
    hrevealed hvalues hpublished hrightMaterialized
  exact relTriple_runDirectResolvedWitness_observed_firstStopped_of_probeFree table
    ((probingHashQueryPublicAction parameter input left.state plan.action).run leftCache)
    ((probingHashQueryPublicAction parameter input left.state plan.action).run rightCache)
    observations left right leftFuel rightFuel hbase
    (probingHashQueryPublicAction_probeFree parameter input left.state plan.action leftCache)
    (probingHashQueryPublicAction_probeFree parameter input left.state plan.action rightCache)
    hcontext.leftValid hcontext.leftCompletable hrightMaterialized htracked hcovered hnoHit hbudget

set_option maxRecDepth 100000 in
theorem relTriple_finishWitnessObservedFirstStoppedStep
    (parameter : PublicParameter) (rootOf : α → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (next : α → OracleComp (OracleWorld + SigningSpec) β)
    (leftObserve : DeferredContext → Nat → (α × SplitHashCache) →
      List PlannedProbeSnapshot → ProbComp PrivateWitnessSnapshotOutput)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (table : OtsSecretIndex → HashOutput)
    (leftResult : DirectWitnessResult (α × SplitHashCache))
    (rightResult : Option (ObservedCleanRunResult (α × SplitHashCache)))
    (hrelation : WitnessObservedFirstStoppedStepRel table observations leftResult rightResult)
    (hrecursive : ∀ left right,
      leftResult = .done left →
      rightResult = some (observedResolvedResult observations right) →
      OrdinaryMaterializedRunEq table left right →
      RelTriple
        (canonicalizeDirectWitnessSnapshotObserve table leftObserve left.context left.remaining
          (left.value.1, left.value.2) snapshots)
        (observedMaterializedBoundary parameter (rootOf right.value.1) ftsSecret
          (next right.value.1) observations right.context.state right.remaining table
          right.value.2)
        (SnapshotObservedFirstStoppedRel table)) :
    RelTriple
      (finishDirectWitnessSnapshotObserve
        (canonicalizeDirectWitnessSnapshotObserve table leftObserve) snapshots leftResult)
      (match rightResult with
        | none => pure none
        | some result =>
            observedMaterializedBoundary parameter (rootOf result.value.1) ftsSecret
              (next result.value.1) result.observations result.state result.remaining table
              result.value.2)
      (SnapshotObservedFirstStoppedRel table) := by
  rcases hrelation with hfailed | haligned | hmissing
  · subst rightResult
    have hbase := relTriple_true
      (finishDirectWitnessSnapshotObserve
        (canonicalizeDirectWitnessSnapshotObserve table leftObserve) snapshots leftResult)
      (pure none : ProbComp (Option (ObservedCleanRunResult (β × SplitHashCache))))
    have hsupported :=
      SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hbase
    apply relTriple_post_mono hsupported
    intro source observed hsupport
    have : observed = none := by simpa using hsupport.2
    exact Or.inl this
  · obtain ⟨left, right, hleft, hright, hclean⟩ := haligned
    subst leftResult
    subst rightResult
    simp only [finishDirectWitnessSnapshotObserve, observedResolvedResult]
    exact hrecursive left right rfl rfl hclean
  · obtain ⟨right, hright, hdoomed, hmissing⟩ := hmissing
    subst rightResult
    exact relTriple_any_observedMaterializedBoundary_firstStopped_of_cause parameter
      (rootOf right.value.1) ftsSecret (next right.value.1)
      (finishDirectWitnessSnapshotObserve
        (canonicalizeDirectWitnessSnapshotObserve table leftObserve) snapshots leftResult)
      observations right.context.state right.remaining table right.value.2
      (by rw [← hdoomed.2]; exact hdoomed.1.2) (Or.inl (by rwa [← hdoomed.2]))

set_option maxRecDepth 100000 in
theorem relTriple_bind_finishWitnessObservedFirstStoppedStep
    (parameter : PublicParameter) (rootOf : α → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (next : α → OracleComp (OracleWorld + SigningSpec) β)
    (leftObserve : DeferredContext → Nat → (α × SplitHashCache) →
      List PlannedProbeSnapshot → ProbComp PrivateWitnessSnapshotOutput)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (table : OtsSecretIndex → HashOutput)
    (leftStep : ProbComp (DirectWitnessResult (α × SplitHashCache)))
    (rightStep : ProbComp (Option (ObservedCleanRunResult (α × SplitHashCache))))
    (hstep : RelTriple leftStep rightStep
      (WitnessObservedFirstStoppedStepRel table observations))
    (hrecursive : ∀ left right,
      DirectWitnessResult.done left ∈ support leftStep →
      some (observedResolvedResult observations right) ∈ support rightStep →
      OrdinaryMaterializedRunEq table left right →
      RelTriple
        (canonicalizeDirectWitnessSnapshotObserve table leftObserve left.context left.remaining
          (left.value.1, left.value.2) snapshots)
        (observedMaterializedBoundary parameter (rootOf right.value.1) ftsSecret
          (next right.value.1) observations right.context.state right.remaining table
          right.value.2)
        (SnapshotObservedFirstStoppedRel table)) :
    RelTriple
      (leftStep >>= finishDirectWitnessSnapshotObserve
        (canonicalizeDirectWitnessSnapshotObserve table leftObserve) snapshots)
      (rightStep >>= fun result =>
        match result with
        | none => pure none
        | some result =>
            observedMaterializedBoundary parameter (rootOf result.value.1) ftsSecret
              (next result.value.1) result.observations result.state result.remaining table
              result.value.2)
      (SnapshotObservedFirstStoppedRel table) := by
  have hleftSupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hstep
      (fun result => result ∈ support leftStep) (fun result hresult => hresult)
  have hbothSupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleftSupported
  apply relTriple_bind hbothSupported
  intro leftResult rightResult hrelation
  rcases hrelation with ⟨⟨hrelation, hleftSupport⟩, hrightSupport⟩
  exact relTriple_finishWitnessObservedFirstStoppedStep parameter rootOf ftsSecret next leftObserve
    snapshots observations table leftResult rightResult hrelation (by
      intro left right hleft hright hclean
      subst leftResult
      subst rightResult
      exact hrecursive left right hleftSupport hrightSupport hclean)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem relTriple_directSnapshotBoundary_observedMaterialized_firstStopped
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) RetainedRestResult)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (leftCache rightCache : SplitHashCache) (q bound : Nat)
    (hbound :
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
            SecretKey)) computation).IsQueryBoundP
        (fun query => query matches Sum.inr _) bound)
    (hcontext : FinalizationContextLE table left right)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state)
    (hcanonical : CanonicalMaterializedValues table left)
    (haligned : SnapshotsObservedAt table snapshots observations)
    (hbefore : SnapshotsBefore snapshots left)
    (htracked : CleanProbeObservationsTrackedBy observations right.state)
    (hcovered : CleanProbeObservationsCoverPending observations right.state)
    (hnoHit : ∀ observation ∈ observations, ¬observation.ExistingHiddenHit)
    (hleftLower : bound ≤ leftFuel) (hleftUpper : leftFuel ≤ q)
    (hrightLower : q + bound ≤ rightFuel)
    (hbudget : rightFuel + right.state.pending.card < Fintype.card Digest) :
    RelTriple
      (directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve parameter root ftsSecret
        computation (retainedResolvedFinalizationPrivateWitnessSnapshotObserve table root)
        snapshots left leftFuel table leftCache)
      (observedMaterializedBoundary parameter root ftsSecret computation observations right.state
        rightFuel table rightCache)
      (SnapshotObservedFirstStoppedRel table) := by
  induction computation using OracleComp.inductionOn generalizing
      snapshots observations left right leftFuel rightFuel leftCache rightCache bound with
  | pure value =>
      rw [directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve,
        OracleComp.construct_pure, observedMaterializedBoundary, OracleComp.construct_pure]
      have hnotPrivate : ¬PrivateStructuralHit left :=
        not_privateStructuralHit_of_deferredCompletable hcontext.leftCompletable
      simp [retainedResolvedFinalizationPrivateWitnessSnapshotObserve, hnotPrivate]
      right
      left
      exact ⟨_, observations, rfl, List.prefix_rfl, haligned, hnoHit, by simp⟩
  | query_bind query next ih =>
      rw [directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve,
        OracleComp.construct_query_bind, observedMaterializedBoundary,
        OracleComp.construct_query_bind]
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              rw [simulateQ_expandedAdversaryImpl_query_bind_inl,
                OracleComp.isQueryBoundP_query_bind_iff] at hbound
              simp only
              let leftObserve : DeferredContext → Nat →
                  (Fin (n + 1) × SplitHashCache) → List PlannedProbeSnapshot →
                    ProbComp PrivateWitnessSnapshotOutput :=
                fun nextContext remaining value laterSnapshots =>
                  directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve parameter root
                    ftsSecret (next value.1)
                    (retainedResolvedFinalizationPrivateWitnessSnapshotObserve table root)
                    laterSnapshots nextContext remaining table value.2
              let leftStep : ProbComp
                  (DirectWitnessResult (Fin (n + 1) × SplitHashCache)) :=
                runDirectResolvedWitnessFromTable left leftFuel table
                  ((splitUniformImpl n).run leftCache)
              let rightStep : ProbComp
                  (Option (ObservedCleanRunResult (Fin (n + 1) × SplitHashCache))) :=
                runObservedCleanFromTable observations right.state rightFuel table
                  ((splitUniformImpl n).run rightCache)
              have hbase := (witnessMaterializedStableCouples_splitUniformImpl table n)
                left right leftFuel rightFuel leftCache rightCache hcontext (by omega) hcache
                hrevealed hvalues hpublished hrightMaterialized
              have hlocal := relTriple_runDirectResolvedWitness_observed_firstStopped_of_probeFree
                table ((splitUniformImpl n).run leftCache) ((splitUniformImpl n).run rightCache)
                observations left right leftFuel rightFuel hbase
                (splitUniformImpl_probeFree n leftCache) (splitUniformImpl_probeFree n rightCache)
                hcontext.leftValid hcontext.leftCompletable hrightMaterialized htracked hcovered
                hnoHit hbudget
              unfold runDirectWitnessSnapshotObserve
              change RelTriple
                (leftStep >>= finishDirectWitnessSnapshotObserve
                  (canonicalizeDirectWitnessSnapshotObserve table leftObserve) snapshots)
                (rightStep >>= fun result =>
                  match result with
                  | none => pure none
                  | some result =>
                      observedMaterializedBoundary parameter root ftsSecret
                        (next result.value.1) result.observations result.state result.remaining
                        table result.value.2)
                (SnapshotObservedFirstStoppedRel table)
              apply relTriple_bind_finishWitnessObservedFirstStoppedStep
                (α := Fin (n + 1)) (β := RetainedRestResult) parameter (fun _ => root)
                ftsSecret next leftObserve snapshots observations table leftStep rightStep
                (by simpa [leftStep, rightStep] using hlocal)
              intro nextLeft nextRight hleftSupport hrightSupport hclean
              have hcanonicalRun := hclean.canonicalize_left
              let canonical := canonicalizeMaterializedValues table nextLeft.context
              have hleftCompletable : DeferredCompletable table canonical :=
                hcanonicalRun.context_le.leftCompletable
              have hnotPrivate : ¬PrivateStructuralHit canonical :=
                not_privateStructuralHit_of_deferredCompletable hleftCompletable
              have hleftFuelPreserved : leftFuel ≤ nextLeft.remaining := by
                have := fuel_le_remaining_add_of_done_runDirectResolvedWitnessFromTable
                  ((splitUniformImpl n).run leftCache) left leftFuel table nextLeft 0
                  (splitUniformImpl_probeFree n leftCache)
                  (by exact hleftSupport)
                omega
              have hrightFuelPreserved : rightFuel ≤ nextRight.remaining := by
                have := fuel_le_remaining_add_of_mem_runObservedCleanFromTable
                  ((splitUniformImpl n).run rightCache) observations right.state rightFuel table
                  (observedResolvedResult observations nextRight) 0
                  (splitUniformImpl_probeFree n rightCache)
                  (by exact hrightSupport)
                simpa [observedResolvedResult] using this
              have hleftRemainingUpper : nextLeft.remaining ≤ leftFuel :=
                remaining_le_fuel_of_done_runDirectResolvedDetailedFromTable
                  ((splitUniformImpl n).run leftCache) left leftFuel table nextLeft (by
                    rw [← map_erase_runDirectResolvedWitnessFromTable
                      ((splitUniformImpl n).run leftCache) left leftFuel table, support_map]
                    exact ⟨.done nextLeft, hleftSupport, rfl⟩)
              have hnextTracked : CleanProbeObservationsTrackedBy observations
                  nextRight.context.state := by
                simpa [rightStep, observedResolvedResult] using
                  (cleanProbeObservationsTrackedBy_of_mem_runObservedCleanFromTable
                    ((splitUniformImpl n).run rightCache) observations right.state rightFuel table
                    htracked (observedResolvedResult observations nextRight)
                    hrightSupport)
              have hnextCovered : CleanProbeObservationsCoverPending observations
                  nextRight.context.state := by
                simpa [rightStep, observedResolvedResult] using
                  (cleanProbeObservationsCoverPending_of_mem_runObservedCleanFromTable
                    ((splitUniformImpl n).run rightCache) observations right.state rightFuel table
                    hcovered (observedResolvedResult observations nextRight)
                    hrightSupport)
              have hnextBudget : nextRight.remaining + nextRight.context.state.pending.card <
                  Fintype.card Digest := by
                have hremaining := remaining_add_pending_card_le_of_mem_runObservedCleanFromTable
                  ((splitUniformImpl n).run rightCache) observations right.state rightFuel table
                  (observedResolvedResult observations nextRight)
                  hrightSupport
                simpa [observedResolvedResult] using hremaining.trans_lt hbudget
              have hnextBefore : SnapshotsBefore snapshots canonical :=
                (hbefore.of_done_runDirectResolvedWitnessFromTable
                  ((splitUniformImpl n).run leftCache) left leftFuel table nextLeft
                  hleftSupport).canonicalize_right table
              unfold canonicalizeDirectWitnessSnapshotObserve
                classifyDirectWitnessSnapshotObserve
              simp only [canonical, hnotPrivate, ↓reduceDIte, hclean.left_published,
                ↓reduceIte, hleftCompletable]
              rw [← hclean.value_eq]
              simpa [leftObserve] using
                (ih nextLeft.value.1 snapshots observations canonical nextRight.context
                  nextLeft.remaining nextRight.remaining nextLeft.value.2 nextRight.value.2 bound
                  (hbound.2 nextLeft.value.1) hcanonicalRun.context_le hcanonicalRun.cache_eq
                  hcanonicalRun.revealed_eq hcanonicalRun.values_le hcanonicalRun.left_published
                  hcanonicalRun.right_materialized
                  (canonicalizeMaterializedValues_canonical table nextLeft.context
                    hclean.context_le.view.leftConsistent)
                  haligned hnextBefore hnextTracked hnextCovered hnoHit (by omega) (by omega)
                  (by omega)
                  hnextBudget)
          | inr input =>
              rw [simulateQ_expandedAdversaryImpl_query_bind_inl,
                OracleComp.isQueryBoundP_query_bind_iff] at hbound
              simp only
              have hrightValues :
                  (materializedCanonicalContext table right.state).state.values =
                    left.state.values := by
                unfold materializedCanonicalContext
                rw [← hrightMaterialized]
                exact canonicalized_right_values_eq_of_finalizationContextLE hcontext hrevealed
                  hcanonical
              have hplanEq :
                  purePlanProbingHashQuery parameter input
                      (materializedCanonicalContext table right.state).state =
                    purePlanProbingHashQuery parameter input left.state :=
                purePlanProbingHashQuery_eq_of_values_eq hrightValues parameter input
              rw [hplanEq]
              rw [← rootAwareCandidateForPlan?_purePlan parameter input left.state]
              let plan := purePlanProbingHashQuery parameter input left.state
              have hpublicExecutor :
                  probingHashQueryAfterRootAwarePublicPlan parameter input
                      (materializedCanonicalContext table right.state).state plan =
                    probingHashQueryAfterRootAwarePublicPlan parameter input left.state plan :=
                probingHashQueryAfterRootAwarePublicPlan_eq_of_values_eq parameter input
                  hrightValues plan
              rw [hpublicExecutor]
              let candidate? := rootAwareCandidateForPlan? parameter input plan
              let nextSnapshots := appendPlannedSnapshot snapshots candidate? left
              let leftObserve : DeferredContext → Nat →
                  ((OracleWorld + SigningSpec).Range (.inl (.inr input)) × SplitHashCache) →
                    List PlannedProbeSnapshot →
                    ProbComp PrivateWitnessSnapshotOutput :=
                fun nextContext remaining value laterSnapshots =>
                  directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve parameter root
                    ftsSecret (next value.1)
                    (retainedResolvedFinalizationPrivateWitnessSnapshotObserve table root)
                    laterSnapshots nextContext remaining table value.2
              let leftStep : ProbComp (DirectWitnessResult
                  ((OracleWorld + SigningSpec).Range (.inl (.inr input)) × SplitHashCache)) :=
                runDirectResolvedWitnessFromTable left leftFuel table
                  ((probingHashQueryAfterPlan parameter input plan).run leftCache)
              let rightStep : ProbComp (Option (ObservedCleanRunResult
                  ((OracleWorld + SigningSpec).Range (.inl (.inr input)) × SplitHashCache))) :=
                runObservedCleanFromTable observations right.state rightFuel table
                  ((probingHashQueryAfterRootAwarePublicPlan parameter input left.state plan).run
                    rightCache)
              have hcontextDirect :
                  FinalizationContextLE table left (directDeferredContext right.state) := by
                rwa [← hrightMaterialized]
              have houter : IsOuterHash (.inl (.inr input)) := by simp [IsOuterHash]
              have hboundPositive : 0 < bound := by
                rcases hbound.1 with hnot | hpositive
                · exact (hnot (by simp)).elim
                · exact hpositive
              have hleftPositive : 0 < leftFuel := by omega
              have hstrictFuel : leftFuel < rightFuel := by omega
              have hcontinue : ∀ nextObservations,
                  SnapshotsObservedAt table nextSnapshots nextObservations →
                  (∀ observation ∈ nextObservations, ¬observation.ExistingHiddenHit) →
                  RelTriple leftStep rightStep
                    (WitnessObservedFirstStoppedStepRel table nextObservations) →
                  RelTriple
                    (leftStep >>= finishDirectWitnessSnapshotObserve
                      (canonicalizeDirectWitnessSnapshotObserve table leftObserve) nextSnapshots)
                    (rightStep >>= fun result =>
                      match result with
                      | none => pure none
                      | some result =>
                          observedMaterializedBoundary parameter root ftsSecret
                            (next result.value.1) result.observations result.state
                            result.remaining table result.value.2)
                    (SnapshotObservedFirstStoppedRel table) := by
                intro nextObservations hnextAligned hnextNoHit hlocal
                convert relTriple_bind_finishWitnessObservedFirstStoppedStep
                  (α := (OracleWorld + SigningSpec).Range (.inl (.inr input)))
                  (β := RetainedRestResult) parameter (fun _ => root) ftsSecret
                  next leftObserve nextSnapshots nextObservations table leftStep rightStep hlocal ?_
                  using 1 <;>
                    try (apply bind_congr; intro result; cases result <;> rfl)
                intro nextLeft nextRight hleftSupport hrightSupport hclean
                have hcanonicalRun := hclean.canonicalize_left
                let canonical := canonicalizeMaterializedValues table nextLeft.context
                have hleftCompletable : DeferredCompletable table canonical :=
                  hcanonicalRun.context_le.leftCompletable
                have hnotPrivate : ¬PrivateStructuralHit canonical :=
                  not_privateStructuralHit_of_deferredCompletable hleftCompletable
                have hleftFuelSpent : leftFuel ≤ nextLeft.remaining + 1 :=
                  fuel_le_remaining_add_of_done_runDirectResolvedWitnessFromTable
                    ((probingHashQueryAfterPlan parameter input plan).run leftCache) left leftFuel
                    table nextLeft 1
                    (probingHashQueryAfterPlan_isProbeBound_one parameter input plan leftCache)
                    (by exact hleftSupport)
                have hrightFuelSpent : rightFuel ≤ nextRight.remaining + 1 := by
                  have := fuel_le_remaining_add_of_mem_runObservedCleanFromTable
                    ((probingHashQueryAfterRootAwarePublicPlan parameter input left.state plan).run
                      rightCache) observations right.state rightFuel table
                    (observedResolvedResult nextObservations nextRight) 1
                    (probingHashQueryAfterRootAwarePublicPlan_isProbeBound_one parameter input
                      left.state plan rightCache) (by exact hrightSupport)
                  simpa [observedResolvedResult] using this
                have hleftRemainingUpper : nextLeft.remaining ≤ leftFuel :=
                  remaining_le_fuel_of_done_runDirectResolvedDetailedFromTable
                    ((probingHashQueryAfterPlan parameter input plan).run leftCache) left leftFuel
                    table nextLeft (by
                      rw [← map_erase_runDirectResolvedWitnessFromTable
                        ((probingHashQueryAfterPlan parameter input plan).run leftCache) left
                        leftFuel table, support_map]
                      exact ⟨.done nextLeft, hleftSupport, rfl⟩)
                have hnextTracked : CleanProbeObservationsTrackedBy nextObservations
                    nextRight.context.state := by
                  simpa [rightStep, observedResolvedResult] using
                    (cleanProbeObservationsTrackedBy_of_mem_runObservedCleanFromTable
                      ((probingHashQueryAfterRootAwarePublicPlan parameter input left.state
                        plan).run rightCache) observations right.state rightFuel table htracked
                      (observedResolvedResult nextObservations nextRight)
                      hrightSupport)
                have hnextCovered : CleanProbeObservationsCoverPending nextObservations
                    nextRight.context.state := by
                  simpa [rightStep, observedResolvedResult] using
                    (cleanProbeObservationsCoverPending_of_mem_runObservedCleanFromTable
                      ((probingHashQueryAfterRootAwarePublicPlan parameter input left.state
                        plan).run rightCache) observations right.state rightFuel table hcovered
                      (observedResolvedResult nextObservations nextRight)
                      hrightSupport)
                have hnextBudget : nextRight.remaining + nextRight.context.state.pending.card <
                    Fintype.card Digest := by
                  have hremaining := remaining_add_pending_card_le_of_mem_runObservedCleanFromTable
                    ((probingHashQueryAfterRootAwarePublicPlan parameter input left.state plan).run
                      rightCache) observations right.state rightFuel table
                    (observedResolvedResult nextObservations nextRight)
                    hrightSupport
                  simpa [observedResolvedResult] using hremaining.trans_lt hbudget
                have hnextBefore : SnapshotsBefore nextSnapshots canonical :=
                  ((hbefore.appendPlannedSnapshot candidate?).of_done_runDirectResolvedWitnessFromTable
                    ((probingHashQueryAfterPlan parameter input plan).run leftCache) left leftFuel
                    table nextLeft hleftSupport).canonicalize_right table
                unfold canonicalizeDirectWitnessSnapshotObserve
                  classifyDirectWitnessSnapshotObserve
                simp only [canonical, hnotPrivate, ↓reduceDIte, hclean.left_published,
                  ↓reduceIte, hleftCompletable]
                rw [← hclean.value_eq]
                simpa [leftObserve, IsOuterHash] using
                  (ih nextLeft.value.1 nextSnapshots nextObservations canonical nextRight.context
                    nextLeft.remaining nextRight.remaining nextLeft.value.2 nextRight.value.2
                    (bound - 1) (by simpa [IsOuterHash] using hbound.2 nextLeft.value.1)
                    hcanonicalRun.context_le hcanonicalRun.cache_eq hcanonicalRun.revealed_eq
                    hcanonicalRun.values_le hcanonicalRun.left_published
                    hcanonicalRun.right_materialized
                    (canonicalizeMaterializedValues_canonical table nextLeft.context
                      hclean.context_le.view.leftConsistent)
                    hnextAligned hnextBefore hnextTracked hnextCovered hnextNoHit (by omega)
                    (by omega)
                    (by omega) hnextBudget)
              unfold runDirectWitnessSnapshotObserve
              cases hcandidate : candidate? with
              | none =>
                  have hnextSnapshots : nextSnapshots = snapshots := by
                    simp [nextSnapshots, candidate?, hcandidate, appendPlannedSnapshot]
                  have hlocal :=
                    relTriple_runDirectResolvedWitness_afterPlan_observedMaterialized_firstStopped_of_none
                      table parameter input plan observations left right leftFuel rightFuel
                      leftCache rightCache hcandidate (by omega) hcontext hcache hrevealed hvalues
                      hpublished hrightMaterialized htracked hcovered hnoHit hbudget
                  have hresult := hcontinue observations
                    (by simpa [hnextSnapshots] using haligned) hnoHit
                    (by simpa [leftStep, rightStep] using hlocal)
                  convert hresult using 1 <;>
                    try (apply bind_congr; intro result; cases result <;> rfl)
              | some candidate =>
                  have hnextSnapshots : nextSnapshots =
                      snapshots ++ [(⟨candidate, left⟩ : PlannedProbeSnapshot)] := by
                    simp [nextSnapshots, candidate?, hcandidate, appendPlannedSnapshot]
                  let nextObservations := observations ++ [cleanProbeObservation right.state
                    candidate.coordinate candidate.candidate]
                  have hnextAligned : SnapshotsObservedAt table nextSnapshots nextObservations := by
                    have hnext := haligned.appendCandidate (some candidate) hcontextDirect hrevealed
                      hpublished hcanonical
                    rw [hnextSnapshots]
                    simpa [nextObservations, observationsAfterCandidate, hcandidate,
                      appendPlannedSnapshot] using hnext
                  by_cases hcandidateRevealed : candidate.coordinate ∈ right.state.revealed
                  · have hnewNoHit : ¬(cleanProbeObservation right.state candidate.coordinate
                        candidate.candidate).ExistingHiddenHit := by
                      rintro ⟨hhidden, _output, _hvalue, _hcandidate⟩
                      simp [cleanProbeObservation, hcandidateRevealed] at hhidden
                    have hnextNoHit : ∀ observation ∈ nextObservations,
                        ¬observation.ExistingHiddenHit := by
                      intro observation hobservation
                      simp only [nextObservations, List.mem_append, List.mem_singleton]
                        at hobservation
                      rcases hobservation with hold | rfl
                      · exact hnoHit observation hold
                      · exact hnewNoHit
                    have hlocal :=
                      relTriple_runDirectResolvedWitness_afterPlan_observedMaterialized_firstStopped_of_revealed
                        table parameter input plan candidate observations left right leftFuel
                        (rightFuel - 1) leftCache rightCache hcandidate hleftPositive (by omega)
                        hcontext hcache hrevealed hvalues hpublished hrightMaterialized
                        hcandidateRevealed htracked hcovered hnoHit (by omega)
                    have hrightFuelEq : rightFuel - 1 + 1 = rightFuel := by omega
                    have hresult := hcontinue nextObservations hnextAligned hnextNoHit
                      (by simpa [leftStep, rightStep, nextObservations, hrightFuelEq] using hlocal)
                    convert hresult using 1 <;>
                      try (apply bind_congr; intro result; cases result <;> rfl)
                  · let postRight : DeferredContext :=
                      { right with state :=
                          (right.state.addPending candidate.coordinate candidate.candidate) }
                    by_cases hpostCompletable : DeferredCompletable table postRight
                    · have hnewNoHit : ¬(cleanProbeObservation right.state candidate.coordinate
                          candidate.candidate).ExistingHiddenHit :=
                        not_existingHiddenHit_cleanProbeObservation_of_addPending_completable table
                          right candidate hpostCompletable
                      have hnextNoHit : ∀ observation ∈ nextObservations,
                          ¬observation.ExistingHiddenHit := by
                        intro observation hobservation
                        simp only [nextObservations, List.mem_append, List.mem_singleton]
                          at hobservation
                        rcases hobservation with hold | rfl
                        · exact hnoHit observation hold
                        · exact hnewNoHit
                      have hpostBudget : (rightFuel - 1) +
                          (right.state.addPending candidate.coordinate
                            candidate.candidate).pending.card < Fintype.card Digest := by
                        have hcard := LazyRevealProbe.State.pending_card_addPending_le
                          right.state candidate.coordinate candidate.candidate
                        omega
                      have hlocal :=
                        relTriple_runDirectResolvedWitness_afterPlan_observedMaterialized_firstStopped_of_hidden_completable
                          table parameter input plan candidate observations left right leftFuel
                          (rightFuel - 1) leftCache rightCache hcandidate hleftPositive (by omega)
                          hcontext hcache hrevealed hvalues hpublished hrightMaterialized
                          hcandidateRevealed hpostCompletable htracked hcovered hnoHit hpostBudget
                      have hrightFuelEq : rightFuel - 1 + 1 = rightFuel := by omega
                      have hresult := hcontinue nextObservations hnextAligned hnextNoHit
                        (by simpa [leftStep, rightStep, nextObservations, hrightFuelEq] using hlocal)
                      convert hresult using 1 <;>
                        try (apply bind_congr; intro result; cases result <;> rfl)
                    · have hpostCard :
                          (right.state.addPending candidate.coordinate
                            candidate.candidate).pending.card < Fintype.card Digest := by
                        have hcard := LazyRevealProbe.State.pending_card_addPending_le
                          right.state candidate.coordinate candidate.candidate
                        omega
                      have hsource : ∀ output ∈ support
                          (leftStep >>= finishDirectWitnessSnapshotObserve
                            (canonicalizeDirectWitnessSnapshotObserve table leftObserve)
                            nextSnapshots),
                          PrivateWitnessSnapshotExtends
                            (snapshots ++ [(⟨candidate, left⟩ : PlannedProbeSnapshot)]) output := by
                        intro output houtput
                        change output ∈ support
                          (runDirectWitnessSnapshotObserve
                            (canonicalizeDirectWitnessSnapshotObserve table leftObserve)
                            nextSnapshots left leftFuel table
                            ((probingHashQueryAfterPlan parameter input plan).run leftCache))
                          at houtput
                        have hextends :=
                          privateWitnessSnapshotExtends_of_mem_runDirectWitnessSnapshotObserve
                            (canonicalizeDirectWitnessSnapshotObserve table leftObserve)
                            nextSnapshots left leftFuel table
                            ((probingHashQueryAfterPlan parameter input plan).run leftCache)
                            (by
                              intro result _hresult nextOutput hnextOutput
                              apply privateWitnessSnapshotExtends_of_mem_canonicalizeDirectWitnessSnapshotObserve
                                table leftObserve result.context result.remaining result.value
                                nextSnapshots (output := nextOutput) (houtput := hnextOutput)
                              intro finalOutput hfinalOutput
                              change finalOutput ∈ support
                                (directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve
                                  parameter root ftsSecret (next result.value.1)
                                  (retainedResolvedFinalizationPrivateWitnessSnapshotObserve table
                                    root) nextSnapshots
                                  (canonicalizeMaterializedValues table result.context)
                                  result.remaining table result.value.2) at hfinalOutput
                              exact privateWitnessSnapshotExtends_of_mem_directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve
                                parameter root ftsSecret (next result.value.1)
                                (retainedResolvedFinalizationPrivateWitnessSnapshotObserve table
                                  root) nextSnapshots
                                (canonicalizeMaterializedValues table result.context)
                                result.remaining table result.value.2 (by
                                  intro finalContext finalRemaining finalValue finalSnapshots
                                    retainedOutput hretained
                                  exact privateWitnessSnapshotExtends_of_mem_retainedResolvedFinalizationPrivateWitnessSnapshotObserve
                                    table root finalContext finalRemaining finalValue finalSnapshots
                                    retainedOutput hretained)
                                finalOutput hfinalOutput)
                            output houtput
                        simpa [hnextSnapshots] using hextends
                      have hstopped :=
                        relTriple_source_observedMaterializedHashContinuation_firstStopped_of_notCompletable
                          parameter root ftsSecret input plan candidate next
                          (leftStep >>= finishDirectWitnessSnapshotObserve
                            (canonicalizeDirectWitnessSnapshotObserve table leftObserve)
                            nextSnapshots)
                          snapshots observations left right (rightFuel - 1) table rightCache
                          hcandidate hcontext hrevealed hcanonical hrightMaterialized
                          hcandidateRevealed hnoHit haligned hbefore htracked hsource hpostCard (by
                            simpa [postRight] using hpostCompletable)
                      have hrightFuelEq : rightFuel - 1 + 1 = rightFuel := by omega
                      have hresult : RelTriple
                          (leftStep >>= finishDirectWitnessSnapshotObserve
                            (canonicalizeDirectWitnessSnapshotObserve table leftObserve)
                            nextSnapshots)
                          (rightStep >>= fun result =>
                            match result with
                            | none => pure none
                            | some result =>
                                observedMaterializedBoundary parameter root ftsSecret
                                  (next result.value.1) result.observations result.state
                                  result.remaining table result.value.2)
                          (SnapshotObservedFirstStoppedRel table) := by
                        convert hstopped using 1
                        all_goals try simp [rightStep, observedMaterializedHashContinuation,
                          hpublicExecutor, hrightFuelEq]
                        all_goals try (apply bind_congr; intro result; cases result <;> rfl)
                      convert hresult using 1 <;>
                        try (apply bind_congr; intro result; cases result <;> rfl)
      | inr message =>
          rw [simulateQ_expandedAdversaryImpl_query_bind_inr] at hbound
          simp only
          let leftObserve : DeferredContext → Nat →
              (Option Signature × SplitHashCache) →
                List PlannedProbeSnapshot →
                ProbComp PrivateWitnessSnapshotOutput :=
            fun nextContext remaining value laterSnapshots =>
              directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve parameter root
                ftsSecret (next value.1)
                (retainedResolvedFinalizationPrivateWitnessSnapshotObserve table root)
                laterSnapshots nextContext remaining table value.2
          let leftStep : ProbComp (DirectWitnessResult
              (Option Signature × SplitHashCache)) :=
            runDirectResolvedWitnessFromTable left leftFuel table
              ((maskedSign parameter root ftsSecret message).run leftCache)
          let rightStep : ProbComp (Option (ObservedCleanRunResult
              (Option Signature × SplitHashCache))) :=
            runObservedCleanFromTable observations right.state rightFuel table
              ((maskedSign parameter root ftsSecret message).run rightCache)
          have hbase := (witnessMaterializedStableCouples_maskedSign table parameter root
            ftsSecret message) left right leftFuel rightFuel leftCache rightCache hcontext
              (by omega) hcache hrevealed hvalues hpublished hrightMaterialized
          have hlocal := relTriple_runDirectResolvedWitness_observed_firstStopped_of_probeFree
            table ((maskedSign parameter root ftsSecret message).run leftCache)
            ((maskedSign parameter root ftsSecret message).run rightCache) observations left right
            leftFuel rightFuel hbase
            (maskedSign_probeFree parameter root ftsSecret message leftCache)
            (maskedSign_probeFree parameter root ftsSecret message rightCache) hcontext.leftValid
            hcontext.leftCompletable hrightMaterialized htracked hcovered hnoHit hbudget
          unfold runDirectWitnessSnapshotObserve
          convert relTriple_bind_finishWitnessObservedFirstStoppedStep
            (α := Option Signature)
            (β := RetainedRestResult) parameter (fun _ => root)
            ftsSecret next leftObserve snapshots observations table leftStep rightStep
            (by simpa [leftStep, rightStep] using hlocal) ?_ using 1 <;>
              try (apply bind_congr; intro result; cases result <;> rfl)
          intro nextLeft nextRight hleftSupport hrightSupport hclean
          have hcanonicalRun := hclean.canonicalize_left
          let canonical := canonicalizeMaterializedValues table nextLeft.context
          have hleftCompletable : DeferredCompletable table canonical :=
            hcanonicalRun.context_le.leftCompletable
          have hnotPrivate : ¬PrivateStructuralHit canonical :=
            not_privateStructuralHit_of_deferredCompletable hleftCompletable
          have hleftFuelPreserved : leftFuel ≤ nextLeft.remaining := by
            have := fuel_le_remaining_add_of_done_runDirectResolvedWitnessFromTable
              ((maskedSign parameter root ftsSecret message).run leftCache) left leftFuel table
              nextLeft 0 (maskedSign_probeFree parameter root ftsSecret message leftCache)
              (by exact hleftSupport)
            omega
          have hrightFuelPreserved : rightFuel ≤ nextRight.remaining := by
            have := fuel_le_remaining_add_of_mem_runObservedCleanFromTable
              ((maskedSign parameter root ftsSecret message).run rightCache) observations
              right.state rightFuel table (observedResolvedResult observations nextRight) 0
              (maskedSign_probeFree parameter root ftsSecret message rightCache)
              (by exact hrightSupport)
            simpa [observedResolvedResult] using this
          have hleftRemainingUpper : nextLeft.remaining ≤ leftFuel :=
            remaining_le_fuel_of_done_runDirectResolvedDetailedFromTable
              ((maskedSign parameter root ftsSecret message).run leftCache) left leftFuel table
              nextLeft (by
                rw [← map_erase_runDirectResolvedWitnessFromTable
                  ((maskedSign parameter root ftsSecret message).run leftCache) left leftFuel
                  table, support_map]
                exact ⟨.done nextLeft, hleftSupport, rfl⟩)
          have hnextTracked : CleanProbeObservationsTrackedBy observations
              nextRight.context.state := by
            simpa [rightStep, observedResolvedResult] using
              (cleanProbeObservationsTrackedBy_of_mem_runObservedCleanFromTable
                ((maskedSign parameter root ftsSecret message).run rightCache) observations
                right.state rightFuel table htracked
                (observedResolvedResult observations nextRight)
                hrightSupport)
          have hnextCovered : CleanProbeObservationsCoverPending observations
              nextRight.context.state := by
            simpa [rightStep, observedResolvedResult] using
              (cleanProbeObservationsCoverPending_of_mem_runObservedCleanFromTable
                ((maskedSign parameter root ftsSecret message).run rightCache) observations
                right.state rightFuel table hcovered
                (observedResolvedResult observations nextRight)
                hrightSupport)
          have hnextBudget : nextRight.remaining + nextRight.context.state.pending.card <
              Fintype.card Digest := by
            have hremaining := remaining_add_pending_card_le_of_mem_runObservedCleanFromTable
              ((maskedSign parameter root ftsSecret message).run rightCache) observations
              right.state rightFuel table (observedResolvedResult observations nextRight)
              hrightSupport
            simpa [observedResolvedResult] using hremaining.trans_lt hbudget
          have hnextBefore : SnapshotsBefore snapshots canonical :=
            (hbefore.of_done_runDirectResolvedWitnessFromTable
              ((maskedSign parameter root ftsSecret message).run leftCache) left leftFuel table
              nextLeft hleftSupport).canonicalize_right table
          unfold canonicalizeDirectWitnessSnapshotObserve classifyDirectWitnessSnapshotObserve
          simp only [canonical, hnotPrivate, ↓reduceDIte, hclean.left_published,
            ↓reduceIte, hleftCompletable]
          rw [← hclean.value_eq]
          have hdetailed : DirectDetailedResult.done nextLeft ∈ support
              (runDirectResolvedDetailedFromTable left leftFuel table
                ((maskedSign parameter root ftsSecret message).run leftCache)) := by
            rw [← map_erase_runDirectResolvedWitnessFromTable
              ((maskedSign parameter root ftsSecret message).run leftCache)
              left leftFuel table, support_map]
            exact ⟨.done nextLeft, hleftSupport, rfl⟩
          have hdirect : some nextLeft ∈ support
              (runDirectResolvedFromTable left leftFuel table
                ((maskedSign parameter root ftsSecret message).run leftCache)) :=
            mem_support_runDirectResolvedFromTable_of_done_detailed
              ((maskedSign parameter root ftsSecret message).run leftCache)
              left leftFuel table nextLeft hdetailed
          have hraw := raw_done_of_mem_runDirectResolvedFromTable
            ((maskedSign parameter root ftsSecret message).run leftCache)
            left leftFuel table nextLeft hdirect
          have houtput : nextLeft.value.1 ∈ support
              (scheme.sign
                (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
                  SecretKey) message) := by
            exact maskedSign_done_output_mem_support parameter root table ftsSecret
              message left.state nextLeft.context.state leftCache nextLeft.value.2
              leftFuel nextLeft.remaining nextLeft.value.1
                hclean.context_le.view.leftStarts (by
                  simpa only [SigningSpec, maskedExpandedAdversaryImpl,
                    maskedSigningImpl] using hraw)
          have htailBound := isQueryBoundP_of_bind hbound nextLeft.value.1 houtput
          simpa [leftObserve, IsOuterHash] using
            (ih nextLeft.value.1 snapshots observations canonical nextRight.context
              nextLeft.remaining nextRight.remaining nextLeft.value.2 nextRight.value.2 bound
              (htailBound.mono (by omega))
              hcanonicalRun.context_le hcanonicalRun.cache_eq hcanonicalRun.revealed_eq
              hcanonicalRun.values_le hcanonicalRun.left_published
              hcanonicalRun.right_materialized
              (canonicalizeMaterializedValues_canonical table nextLeft.context
                hclean.context_le.view.leftConsistent)
              haligned hnextBefore hnextTracked hnextCovered hnoHit (by omega) (by omega)
              (by omega)
              hnextBudget)
