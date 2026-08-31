import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivatePreparationCanonical

/-!
# Hindsight preparation for the normalized plan trace

Fixing a final candidate list turns the normalized outer trace into a Boolean recursion. Every suffix probe belongs to that final list, so the guarded direct-interpreter theorem moves its private structural risk into the finite preparation observer.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local instance] Classical.propDecidable

def PlanHitAt (finalCandidates : List Probe) (output : Bool × List Probe) : Prop :=
  output.1 = true ∧ output.2 = finalCandidates

noncomputable def finishDirectDetailedPlanHitObserve
    (finalCandidates currentCandidates : List Probe)
    (observe : DeferredContext → Nat → α → ProbComp Bool) :
    DirectDetailedResult α → ProbComp Bool
  | .stopped .privateStructuralHit => pure (decide (currentCandidates = finalCandidates))
  | .stopped _ => pure false
  | .done result => observe result.context result.remaining result.value

noncomputable def runDirectDetailedPlanHitObserve
    (finalCandidates currentCandidates : List Probe)
    (observe : DeferredContext → Nat → α → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) : ProbComp Bool :=
  runDirectResolvedDetailedFromTable context fuel table computation >>=
    finishDirectDetailedPlanHitObserve finalCandidates currentCandidates observe

theorem probEvent_runDirectDetailedPlanHitObserve_le_privatePreparation
    (finalCandidates currentCandidates : List Probe)
    (observe : DeferredContext → Nat → α → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hterminal : ∀ result : ResolvedRunResult α,
      DirectDetailedResult.done result ∈ support
        (runDirectResolvedDetailedFromTable context fuel table computation) →
      Pr[= true | observe result.context result.remaining result.value] ≤
        Pr[= true | guardedPreparationObserve finalCandidates result.context]) :
    Pr[= true | runDirectDetailedPlanHitObserve finalCandidates currentCandidates observe
      context fuel table computation] ≤
      Pr[= true | runPrivatePreparation finalCandidates context fuel table computation] := by
  unfold runDirectDetailedPlanHitObserve runPrivatePreparation
    runDirectDetailedPrivateObserve
  rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
  apply probEvent_bind_le_bind_of_forall_le
  intro result hresult
  cases result with
  | stopped reason =>
      cases reason with
      | fuelExhausted => simp [finishDirectDetailedPlanHitObserve,
          finishDirectDetailedPrivateObserve]
      | ordinaryHit => simp [finishDirectDetailedPlanHitObserve,
          finishDirectDetailedPrivateObserve]
      | privateStructuralHit =>
          by_cases heq : currentCandidates = finalCandidates <;>
            simp [finishDirectDetailedPlanHitObserve, finishDirectDetailedPrivateObserve, heq]
  | done result =>
      simpa [finishDirectDetailedPlanHitObserve, finishDirectDetailedPrivateObserve] using
        hterminal result hresult

theorem probEvent_runDirectDetailedPlanHitObserve_eq_zero
    (finalCandidates currentCandidates : List Probe)
    (observe : DeferredContext → Nat → α → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hne : currentCandidates ≠ finalCandidates)
    (hterminal : ∀ result : ResolvedRunResult α,
      DirectDetailedResult.done result ∈ support
        (runDirectResolvedDetailedFromTable context fuel table computation) →
      Pr[= true | observe result.context result.remaining result.value] = 0) :
    Pr[= true | runDirectDetailedPlanHitObserve finalCandidates currentCandidates observe
      context fuel table computation] = 0 := by
  unfold runDirectDetailedPlanHitObserve
  apply le_antisymm
  · rw [← probEvent_eq_eq_probOutput]
    apply probEvent_bind_le_of_forall_le
    intro result hresult
    cases result with
    | stopped reason => cases reason <;>
        simp [finishDirectDetailedPlanHitObserve, hne]
    | done result =>
        rw [probEvent_eq_eq_probOutput]
        simpa [finishDirectDetailedPlanHitObserve] using hterminal result hresult
  · exact zero_le

theorem probEvent_runDirectDetailedPlanHitObserve_le_guarded
    (finalCandidates currentCandidates : List Probe)
    (observe : DeferredContext → Nat → α → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hcovered : PendingCoveredBy finalCandidates context)
    (hbound : computation.IsQueryBoundP (IsUncoveredProbe finalCandidates) 0)
    (hterminal : ∀ result : ResolvedRunResult α,
      DirectDetailedResult.done result ∈ support
        (runDirectResolvedDetailedFromTable context fuel table computation) →
      Pr[= true | observe result.context result.remaining result.value] ≤
        Pr[= true | guardedPreparationObserve finalCandidates result.context]) :
    Pr[= true | runDirectDetailedPlanHitObserve finalCandidates currentCandidates observe
      context fuel table computation] ≤
      Pr[= true | guardedPreparationObserve finalCandidates context] :=
  (probEvent_runDirectDetailedPlanHitObserve_le_privatePreparation finalCandidates
      currentCandidates observe context fuel table computation hterminal).trans
    (probEvent_runPrivatePreparation_le_guarded finalCandidates computation context fuel table
      hcovered hbound)

noncomputable def canonicalizeDirectDetailedPlanHitObserve
    (table : OtsSecretIndex → HashOutput)
    (finalCandidates currentCandidates : List Probe)
    (observe : DeferredContext → Nat → α → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (value : α) : ProbComp Bool := by
  classical
  let canonical := canonicalizeMaterializedValues table context
  exact if PrivateStructuralHit canonical then
      pure (decide (currentCandidates = finalCandidates))
    else if PublishedValues context.state then
      if DeferredCompletable table canonical then
        observe canonical fuel value
      else
        pure false
    else
      pure false

theorem evalDist_planHit_canonicalizeDirectDetailedPrivatePlanObserve
    (table : OtsSecretIndex → HashOutput)
    (finalCandidates currentCandidates : List Probe)
    (observe : DeferredContext → Nat → α → List Probe → ProbComp (Bool × List Probe))
    (boolObserve : DeferredContext → Nat → α → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (value : α)
    (hproject : ∀ nextContext remaining nextValue,
      evalDist ((fun output => decide (PlanHitAt finalCandidates output)) <$>
          observe nextContext remaining nextValue currentCandidates) =
        evalDist (boolObserve nextContext remaining nextValue)) :
    evalDist ((fun output => decide (PlanHitAt finalCandidates output)) <$>
        canonicalizeDirectDetailedPrivatePlanObserve table observe context fuel value
          currentCandidates) =
      evalDist (canonicalizeDirectDetailedPlanHitObserve table finalCandidates currentCandidates
        boolObserve context fuel value) := by
  unfold canonicalizeDirectDetailedPrivatePlanObserve
    canonicalizeDirectDetailedPlanHitObserve
  let canonical := canonicalizeMaterializedValues table context
  by_cases hprivate : PrivateStructuralHit canonical
  · simp [canonical, hprivate, PlanHitAt]
  · by_cases hpublished : PublishedValues context.state
    · simp only [canonical, hprivate, hpublished, ↓reduceIte]
      change evalDist ((fun output => decide (PlanHitAt finalCandidates output)) <$>
          classifyDirectDetailedPrivatePlanObserve table observe canonical fuel value
            currentCandidates) =
        evalDist (if DeferredCompletable table canonical then
          boolObserve canonical fuel value
        else pure false)
      unfold classifyDirectDetailedPrivatePlanObserve
      simp only [hprivate, ↓reduceIte]
      by_cases hcompletable : DeferredCompletable table canonical
      · simpa [hcompletable] using hproject canonical fuel value
      · simp [hcompletable, PlanHitAt]
    · simp [canonical, hprivate, hpublished, PlanHitAt]

theorem evalDist_planHit_finishDirectDetailedPrivatePlanObserve
    (finalCandidates currentCandidates : List Probe)
    (observe : DeferredContext → Nat → α → List Probe → ProbComp (Bool × List Probe))
    (boolObserve : DeferredContext → Nat → α → ProbComp Bool)
    (result : DirectDetailedResult α)
    (hproject : ∀ nextContext remaining nextValue,
      evalDist ((fun output => decide (PlanHitAt finalCandidates output)) <$>
          observe nextContext remaining nextValue currentCandidates) =
        evalDist (boolObserve nextContext remaining nextValue)) :
    evalDist ((fun output => decide (PlanHitAt finalCandidates output)) <$>
        finishDirectDetailedPrivatePlanObserve observe currentCandidates result) =
      evalDist (finishDirectDetailedPlanHitObserve finalCandidates currentCandidates boolObserve
        result) := by
  cases result with
  | stopped reason => cases reason <;> simp [finishDirectDetailedPrivatePlanObserve,
      finishDirectDetailedPlanHitObserve, PlanHitAt]
  | done result => exact hproject result.context result.remaining result.value

theorem probEvent_canonicalizeDirectDetailedPlanHitObserve_le_guarded
    (table : OtsSecretIndex → HashOutput)
    (finalCandidates currentCandidates : List Probe)
    (observe : DeferredContext → Nat → α → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (value : α)
    (hconsistent : context.ValuesConsistent)
    (hpublished : PublishedValues context.state)
    (hcovered : PendingCoveredBy finalCandidates context)
    (hcontinuation :
      let canonical := canonicalizeMaterializedValues table context
      ¬PrivateStructuralHit canonical → DeferredCompletable table canonical →
      Pr[= true | observe canonical fuel value] ≤
        Pr[= true | guardedPreparationObserve finalCandidates canonical]) :
    Pr[= true | canonicalizeDirectDetailedPlanHitObserve table finalCandidates
      currentCandidates observe context fuel value] ≤
      Pr[= true | guardedPreparationObserve finalCandidates context] := by
  let canonical := canonicalizeMaterializedValues table context
  have hcanonicalCovered : PendingCoveredBy finalCandidates canonical := by
    exact (pendingCoveredBy_canonicalize_iff table finalCandidates context).2 hcovered
  have hguardedEq := evalDist_guardedPreparationObserve_canonicalize table finalCandidates
    context hconsistent hpublished
  unfold canonicalizeDirectDetailedPlanHitObserve
  by_cases hprivate : PrivateStructuralHit canonical
  · simp only [canonical, hprivate, ↓reduceIte]
    by_cases heq : currentCandidates = finalCandidates
    · simp only [heq, decide_true]
      have htrue := evalDist_guardedPreparationObserve_eq_true_of_privateStructuralHit
        finalCandidates canonical hcanonicalCovered hprivate
      have hrawTrue : evalDist (guardedPreparationObserve finalCandidates context) =
          evalDist (pure true : ProbComp Bool) := hguardedEq.symm.trans htrue
      exact le_of_eq (OracleComp.probOutput_congr rfl hrawTrue.symm)
    · simp [heq]
  · simp only [canonical, hprivate, ↓reduceIte, hpublished]
    by_cases hcompletable : DeferredCompletable table canonical
    · change DeferredCompletable table (canonicalizeMaterializedValues table context) at hcompletable
      simp only [hcompletable, ↓reduceIte]
      exact (hcontinuation hprivate hcompletable).trans
        (le_of_eq (OracleComp.probOutput_congr rfl hguardedEq))
    · change ¬DeferredCompletable table (canonicalizeMaterializedValues table context) at hcompletable
      simp [hcompletable]

noncomputable def directDetailedBoundaryNormalizedPlanHitObserve
    (finalCandidates : List Probe)
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) →
      List Probe → ProbComp (Bool × List Probe))
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) : ProbComp Bool := by
  classical
  exact OracleComp.construct
    (C := fun _ : OracleComp (OracleWorld + SigningSpec) α =>
      (DeferredContext → Nat → (α × SplitHashCache) →
        List Probe → ProbComp (Bool × List Probe)) →
      List Probe → DeferredContext → Nat → (OtsSecretIndex → HashOutput) →
        SplitHashCache → ProbComp Bool)
    (fun value observe candidates context fuel _table cache =>
      (fun output => decide (PlanHitAt finalCandidates output)) <$>
        observe context fuel (value, cache) candidates)
    (fun query _next recursivelyRun observe candidates context fuel table cache =>
      match query with
      | .inl (.inl n) =>
          runDirectDetailedPlanHitObserve finalCandidates candidates
            (canonicalizeDirectDetailedPlanHitObserve table finalCandidates candidates
              (fun nextContext remaining value =>
                recursivelyRun value.1 observe candidates nextContext remaining table value.2))
            context fuel table ((splitUniformImpl n).run cache)
      | .inl (.inr input) =>
          let plan := purePlanProbingHashQuery parameter input context.state
          let nextCandidates := appendPlannedCandidate candidates plan.candidate?
          runDirectDetailedPlanHitObserve finalCandidates nextCandidates
            (canonicalizeDirectDetailedPlanHitObserve table finalCandidates nextCandidates
              (fun nextContext remaining value =>
                recursivelyRun value.1 observe nextCandidates nextContext remaining table value.2))
            context fuel table ((probingHashQueryAfterPlan parameter input plan).run cache)
      | .inr message =>
          runDirectDetailedPlanHitObserve finalCandidates candidates
            (canonicalizeDirectDetailedPlanHitObserve table finalCandidates candidates
              (fun nextContext remaining value =>
                recursivelyRun value.1 observe candidates nextContext remaining table value.2))
            context fuel table ((maskedSign parameter root ftsSecret message).run cache))
    computation observe candidates context fuel table cache

end SphincsSecurity.Concrete.OtsProbeSimulation
