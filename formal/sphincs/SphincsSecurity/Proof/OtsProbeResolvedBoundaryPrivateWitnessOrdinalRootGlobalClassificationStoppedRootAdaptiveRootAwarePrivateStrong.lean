import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveNormalizedSignerStrong
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveRootAwarePrivate

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def DirectWitnessFinalizationMaterializedSpentRunEq
    (table : OtsSecretIndex → HashOutput) (initialValues : DeferredStructuralValues)
    (leftInitialFuel rightInitialFuel spent : Nat) :
    DirectWitnessResult (α × SplitHashCache) →
      DirectDetailedResult (α × SplitHashCache) → Prop
  | .done left, .done right =>
      left.value.1 = right.value.1 ∧
        FinalizationContextEq table (some left.context) (some right.context) ∧
        left.remaining + spent = leftInitialFuel ∧
        right.remaining + spent = rightInitialFuel ∧
        left.table = table ∧ right.table = table ∧
        left.value.2 = right.value.2 ∧
        left.context.state.revealed = right.context.state.revealed ∧
        (materializedDeferredState left.context).values = right.context.state.values ∧
        DeferredStructuralValuesLE initialValues left.context.values ∧
        right.context = directDeferredContext right.context.state
  | .done _, .stopped _ => False
  | _, _ => True

theorem materializedDeferredState_addPending_values
    (context : DeferredContext) (coordinate : Coordinate) (candidate : Digest) :
    (materializedDeferredState
      { context with state := context.state.addPending coordinate candidate }).values =
        (materializedDeferredState context).values := by
  funext other
  cases other <;>
    simp [materializedDeferredState, DeferredContext.positionValue,
      LazyRevealProbe.State.addPending]

theorem directWitnessFinalizationMaterializedCouples_modify
    (table : OtsSecretIndex → HashOutput) (f : SplitHashCache → SplitHashCache) :
    DirectWitnessFinalizationMaterializedCouples table
      (modify f : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) Unit) := by
  intro left right leftFuel rightFuel leftCache rightCache hcontext hcache hrevealed hmaterialized
    hright
  simp only [modify, runDirectResolvedWitnessFromTable,
    runDirectResolvedDetailedFromTable]
  apply relTriple_pure_pure
  refine ⟨rfl, hcontext, rfl, rfl, rfl, rfl, ?_, hrevealed, hmaterialized,
    DeferredStructuralValuesLE.refl left.values, hright⟩
  simpa [hcache]

theorem directWitnessFinalizationMaterializedCouples_resolvePublicKnownInput
    (table : OtsSecretIndex → HashOutput)
    (parameter : PublicParameter) (publicState : LazyRevealProbe.State Coordinate)
    (coordinate : Coordinate) (input : HashInput) :
    DirectWitnessFinalizationMaterializedCouples table
      (resolvePublicKnownInput parameter publicState coordinate input) := by
  unfold resolvePublicKnownInput
  cases hknown : purePeekTableInput parameter publicState coordinate with
  | none =>
      exact directWitnessFinalizationMaterializedCouples_splitHashQuery_ordinary table input
  | some knownInput =>
      by_cases heq : knownInput = input
      · simp only [heq, ↓reduceIte]
        apply (directWitnessFinalizationMaterializedCouples_revealCoordinateOutput
          table coordinate).bind
        intro output
        apply (directWitnessFinalizationMaterializedCouples_publishCoordinate
          table coordinate).bind
        intro _
        apply (directWitnessFinalizationMaterializedCouples_modify table
          (fun cache => Function.update cache (.ordinary input) (some output))).bind
        intro _
        exact directWitnessFinalizationMaterializedCouples_pure table output
      · simp only [heq, ↓reduceIte]
        exact directWitnessFinalizationMaterializedCouples_splitHashQuery_ordinary table input

theorem directWitnessFinalizationMaterializedCouples_publicAction
    (table : OtsSecretIndex → HashOutput)
    (parameter : PublicParameter) (input : HashInput)
    (publicState : LazyRevealProbe.State Coordinate) (action : PlannedHashAction) :
    DirectWitnessFinalizationMaterializedCouples table
      (probingHashQueryPublicAction parameter input publicState action) := by
  cases action with
  | ordinary =>
      exact directWitnessFinalizationMaterializedCouples_splitHashQuery_ordinary table input
  | resolve coordinate =>
      exact directWitnessFinalizationMaterializedCouples_resolvePublicKnownInput table parameter
        publicState coordinate input

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedWitness_rootAwarePrivate_finalizationMaterialized
    (table : OtsSecretIndex → HashOutput)
    (parameter : PublicParameter) (input : HashInput)
    (publicState : LazyRevealProbe.State Coordinate) (plan : PlannedHashQuery)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hpublicState : publicState = left.state)
    (hpositive : 0 < leftFuel) (hfuel : leftFuel ≤ rightFuel)
    (hcontext : FinalizationContextEq table (some left) (some right))
    (hcache : leftCache = rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hmaterialized : (materializedDeferredState left).values = right.state.values)
    (hright : right = directDeferredContext right.state)
    (hcandidateCompletable : ∀ candidate,
      rootAwareCandidateForPlan? parameter input plan = some candidate →
      candidate.coordinate ∉ left.state.revealed →
      DeferredCompletable table
        { left with state :=
            left.state.addPending candidate.coordinate candidate.candidate }) :
    RelTriple
      (runDirectResolvedWitnessFromTable left leftFuel table
        ((probingHashQueryAfterRootAwarePlan parameter input plan).run leftCache))
      (runDirectResolvedDetailedFromTable right rightFuel table
        ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run
          rightCache))
      (DirectWitnessFinalizationMaterializedSpentRunEq table left.values leftFuel rightFuel
        (if (rootAwareCandidateForPlan? parameter input plan).isSome then 1 else 0)) := by
  subst publicState
  rw [runDirectResolvedWitnessFromTable_rootAwarePrivate_eq_public parameter input plan left
    leftFuel table leftCache]
  unfold probingHashQueryAfterRootAwarePublicPlan
  cases hcandidate : rootAwareCandidateForPlan? parameter input plan with
  | none =>
      simp only [executeCandidate?, pure_bind, Option.isSome_none, ↓reduceIte]
      have hbase := directWitnessFinalizationMaterializedCouples_publicAction table parameter input
        left.state plan.action left right leftFuel rightFuel leftCache rightCache hcontext hcache
        hrevealed hmaterialized hright
      apply relTriple_post_mono hbase
      intro leftResult rightResult hrelation
      cases leftResult <;> cases rightResult <;>
        simpa [DirectWitnessFinalizationMaterializedSpentRunEq,
          DirectWitnessFinalizationMaterializedRunEq] using hrelation
  | some candidate =>
      simp only [executeCandidate?, Option.isSome_some, ↓reduceIte]
      rw [StateT.run_bind, StateT.run_bind, runDirectResolvedWitnessFromTable_bind,
        runDirectResolvedDetailedFromTable_bind]
      simp only [probe, StateT.run_liftM, LazyRevealProbe.probeQuery,
        runDirectResolvedWitnessFromTable_probe_query_bind,
        runDirectResolvedDetailedFromTable_probe_query_bind]
      cases leftFuel with
      | zero => omega
      | succ leftRemaining =>
          cases rightFuel with
          | zero => omega
          | succ rightRemaining =>
              by_cases hleftRevealed : candidate.coordinate ∈ left.state.revealed
              · have hrightRevealed : candidate.coordinate ∈ right.state.revealed := by
                  rw [← hrevealed]
                  exact hleftRevealed
                simp only [hleftRevealed, hrightRevealed, ↓reduceIte]
                have hbase := directWitnessFinalizationMaterializedCouples_publicAction table
                  parameter input left.state plan.action left right leftRemaining rightRemaining
                  leftCache rightCache hcontext hcache hrevealed hmaterialized hright
                apply relTriple_post_mono hbase
                intro leftResult rightResult hrelation
                cases leftResult <;> cases rightResult <;>
                  simpa [DirectWitnessFinalizationMaterializedSpentRunEq,
                    DirectWitnessFinalizationMaterializedRunEq] using hrelation
              · have hrightRevealed : candidate.coordinate ∉ right.state.revealed := by
                  rwa [← hrevealed]
                simp only [hleftRevealed, hrightRevealed, ↓reduceIte]
                let nextLeft : DeferredContext :=
                  { left with state :=
                      left.state.addPending candidate.coordinate candidate.candidate }
                let nextRight : DeferredContext :=
                  { right with state :=
                      right.state.addPending candidate.coordinate candidate.candidate }
                have hleftCompletable : DeferredCompletable table nextLeft := by
                  exact hcandidateCompletable candidate hcandidate hleftRevealed
                have hrightCompletable : DeferredCompletable table nextRight := by
                  exact (deferredCompletable_addPending_iff_of_finalizationViewEq hcontext.1
                    candidate.coordinate candidate.candidate).mp hleftCompletable
                have hnextContext : FinalizationContextEq table (some nextLeft)
                    (some nextRight) := by
                  refine ⟨hcontext.1.addPending_of_completable candidate.coordinate
                      candidate.candidate hleftCompletable hrightCompletable,
                    hcontext.2.1.addPending_of_completable candidate.coordinate
                      candidate.candidate hleftCompletable,
                    hcontext.2.2.1.addPending_of_completable candidate.coordinate
                      candidate.candidate hrightCompletable,
                    hleftCompletable⟩
                have hnextRevealed : nextLeft.state.revealed = nextRight.state.revealed := by
                  simpa [nextLeft, nextRight, LazyRevealProbe.State.addPending] using hrevealed
                have hnextMaterialized : (materializedDeferredState nextLeft).values =
                    nextRight.state.values := by
                  rw [show (materializedDeferredState nextLeft).values =
                      (materializedDeferredState left).values by
                    simpa [nextLeft] using materializedDeferredState_addPending_values left
                      candidate.coordinate candidate.candidate]
                  simpa [nextRight, LazyRevealProbe.State.addPending] using hmaterialized
                have hnextRight : nextRight = directDeferredContext nextRight.state := by
                  dsimp only [nextRight]
                  rw [hright]
                  simp [directDeferredContext, directDeferredValues_addPending]
                have hbase := directWitnessFinalizationMaterializedCouples_publicAction table
                  parameter input left.state plan.action nextLeft nextRight leftRemaining
                  rightRemaining leftCache rightCache hnextContext hcache hnextRevealed
                  hnextMaterialized hnextRight
                apply relTriple_post_mono hbase
                intro leftResult rightResult hrelation
                cases leftResult <;> cases rightResult <;>
                  simpa [DirectWitnessFinalizationMaterializedSpentRunEq,
                    DirectWitnessFinalizationMaterializedRunEq, nextLeft] using hrelation

def WitnessObservedFinalizationMaterializedSpentStepRel
    (table : OtsSecretIndex → HashOutput) (initialValues : DeferredStructuralValues)
    (leftInitialFuel rightInitialFuel spent : Nat)
    (observations : List CleanProbeObservation)
    (left : DirectWitnessResult (α × SplitHashCache))
    (right : Option (ObservedCleanRunResult (α × SplitHashCache))) : Prop :=
  ∃ detailed,
    projectDirectDetailedObserved observations detailed = right ∧
      DirectWitnessFinalizationMaterializedSpentRunEq table initialValues leftInitialFuel
        rightInitialFuel spent left detailed

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedWitness_rootAwarePrivate_observedFinalizationMaterialized
    (table : OtsSecretIndex → HashOutput)
    (parameter : PublicParameter) (input : HashInput)
    (publicState : LazyRevealProbe.State Coordinate) (plan : PlannedHashQuery)
    (observations : List CleanProbeObservation)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hpublicState : publicState = left.state)
    (hpositive : 0 < leftFuel) (hfuel : leftFuel ≤ rightFuel)
    (hcontext : FinalizationContextEq table (some left) (some right))
    (hcache : leftCache = rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hmaterialized : (materializedDeferredState left).values = right.state.values)
    (hright : right = directDeferredContext right.state)
    (hcandidateCompletable : ∀ candidate,
      rootAwareCandidateForPlan? parameter input plan = some candidate →
      candidate.coordinate ∉ left.state.revealed →
      DeferredCompletable table
        { left with state :=
            left.state.addPending candidate.coordinate candidate.candidate }) :
    RelTriple
      (runDirectResolvedWitnessFromTable left leftFuel table
        ((probingHashQueryAfterRootAwarePlan parameter input plan).run leftCache))
      (runObservedCleanFromTable observations right.state rightFuel table
        ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run
          rightCache))
      (WitnessObservedFinalizationMaterializedSpentStepRel table left.values leftFuel rightFuel
        (if (rootAwareCandidateForPlan? parameter input plan).isSome then 1 else 0)
        (observationsAfterCandidate observations right.state
          (rootAwareCandidateForPlan? parameter input plan))) := by
  have hbase := relTriple_runDirectResolvedWitness_rootAwarePrivate_finalizationMaterialized table
    parameter input publicState plan left right leftFuel rightFuel leftCache rightCache hpublicState
    hpositive hfuel hcontext hcache hrevealed hmaterialized hright hcandidateCompletable
  let nextObservations := observationsAfterCandidate observations right.state
    (rootAwareCandidateForPlan? parameter input plan)
  have hstrength : RelTriple
      (runDirectResolvedWitnessFromTable left leftFuel table
        ((probingHashQueryAfterRootAwarePlan parameter input plan).run leftCache))
      (runDirectResolvedDetailedFromTable right rightFuel table
        ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run
          rightCache))
      (fun leftResult rightResult =>
        WitnessObservedFinalizationMaterializedSpentStepRel table left.values leftFuel rightFuel
          (if (rootAwareCandidateForPlan? parameter input plan).isSome then 1 else 0)
          nextObservations leftResult
          (projectDirectDetailedObserved nextObservations rightResult)) := by
    apply relTriple_post_mono hbase
    intro leftResult rightResult hrelation
    exact ⟨rightResult, rfl, hrelation⟩
  have hmapped := relTriple_map
    (R := WitnessObservedFinalizationMaterializedSpentStepRel table left.values leftFuel rightFuel
      (if (rootAwareCandidateForPlan? parameter input plan).isSome then 1 else 0)
      nextObservations)
    (f := id) (g := projectDirectDetailedObserved nextObservations) hstrength
  rw [id_map] at hmapped
  have hmap :
      projectDirectDetailedObserved nextObservations <$>
          runDirectResolvedDetailedFromTable right rightFuel table
            ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run
              rightCache) =
        runObservedCleanFromTable observations right.state rightFuel table
          ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run
            rightCache) := by
    rw [hright]
    simpa [nextObservations, directDeferredContext] using
      (map_projectDirectDetailedObserved_rootAwarePublic parameter input publicState plan
        observations right.state rightFuel table rightCache)
  exact relTriple_of_evalDist_eq_right (congrArg evalDist hmap) hmapped

theorem relTriple_bind_finishDirectDelayed_observed_of_spent
    (table : OtsSecretIndex → HashOutput) (initialValues : DeferredStructuralValues)
    (leftInitialFuel rightInitialFuel spent : Nat)
    (observations : List CleanProbeObservation)
    (leftRun : ProbComp (DirectWitnessResult (α × SplitHashCache)))
    (rightRun : ProbComp (Option (ObservedCleanRunResult (α × SplitHashCache))))
    (leftObserve : DeferredContext → Nat → (α × SplitHashCache) →
      List PlannedProbeSnapshot → List CleanProbeObservation → ProbComp Bool)
    (rightObserve : LazyRevealProbe.State Coordinate → Nat → α → SplitHashCache →
      List CleanProbeObservation → ProbComp Bool)
    (snapshots : List PlannedProbeSnapshot)
    (delayedObservations : List CleanProbeObservation)
    (hstep : RelTriple leftRun rightRun
      (WitnessObservedFinalizationMaterializedSpentStepRel table initialValues leftInitialFuel
        rightInitialFuel spent observations))
    (hnext : ∀ left right,
      DirectWitnessResult.done left ∈ support leftRun →
      some (observedResolvedResult observations right) ∈ support rightRun →
      DirectWitnessFinalizationMaterializedSpentRunEq table initialValues leftInitialFuel
          rightInitialFuel spent (.done left) (.done right) →
      RelTriple
        (leftObserve left.context left.remaining left.value snapshots delayedObservations)
        (rightObserve right.context.state right.remaining right.value.1 right.value.2 observations)
        BoolImp) :
    RelTriple
      (leftRun >>= finishDirectDelayedSelectedRootIndicator leftObserve snapshots
        delayedObservations)
      (rightRun >>= fun result => match result with
        | none => pure false
        | some result => rightObserve result.state result.remaining result.value.1 result.value.2
            result.observations)
      BoolImp := by
  have hleftSupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hstep
      (fun result => result ∈ support leftRun) (fun _ hresult => hresult)
  have hbothSupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleftSupported
  apply relTriple_bind hbothSupported
  intro leftResult rightResult hrelation
  rcases hrelation with ⟨⟨hrelation, hleftSupport⟩, hrightSupport⟩
  cases leftResult with
  | stoppedFuel => exact relTriple_false_any _
  | stoppedOrdinary => exact relTriple_false_any _
  | stoppedPrivate witness => exact relTriple_false_any _
  | done left =>
      rcases hrelation with ⟨detailed, hproject, hrun⟩
      cases detailed with
      | stopped reason =>
          simp [DirectWitnessFinalizationMaterializedSpentRunEq] at hrun
      | done right =>
          have hrightResult : rightResult =
              some (observedResolvedResult observations right) := by
            simpa [projectDirectDetailedObserved, observedResolvedResult] using hproject.symm
          subst rightResult
          simp only [finishDirectDelayedSelectedRootIndicator, observedResolvedResult]
          exact hnext left right hleftSupport hrightSupport hrun

end SphincsSecurity.Concrete.OtsProbeSimulation
