import SphincsSecurity.Proof.OtsProbeResolvedBoundaryWitnessEndpoint

/-!
# Boundary failure witness domination

The canonical execution retains both its boundary outcome and its first private witness. This is
the direction needed by the final reduction: a canonical failure is covered by that witness or by
an ordinary failure of the materialized execution.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

structure BoundaryWitnessPlanOutput where
  outcome : DirectBoundaryOutcome
  witnessPlan : PrivateWitnessPlanOutput

def BoundaryWitnessCovers
    (source : BoundaryWitnessPlanOutput) (materialized : DirectBoundaryOutcome) : Prop :=
  source.outcome.failed = true →
    source.witnessPlan.1.isSome = true ∨ materialized.ordinary = true

noncomputable def finishDirectBoundaryWitnessPlanObserve
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp BoundaryWitnessPlanOutput)
    (candidates : List Probe) : DirectWitnessResult α →
      ProbComp BoundaryWitnessPlanOutput
  | .stoppedFuel => pure ⟨.ordinaryFailure, none, candidates⟩
  | .stoppedOrdinary => pure ⟨.ordinaryFailure, none, candidates⟩
  | .stoppedPrivate witness => pure ⟨.privateStructuralFailure, some witness, candidates⟩
  | .done result => observe result.context result.remaining result.value candidates

noncomputable def classifyDirectBoundaryWitnessPlanObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp BoundaryWitnessPlanOutput)
    (context : DeferredContext) (fuel : Nat) (value : α) (candidates : List Probe) :
    ProbComp BoundaryWitnessPlanOutput := by
  classical
  exact if hhit : PrivateStructuralHit context then
      pure ⟨.privateStructuralFailure, some (privateHitWitnessOf context hhit), candidates⟩
    else if DeferredCompletable table context then
      observe context fuel value candidates
    else
      pure ⟨.ordinaryFailure, none, candidates⟩

noncomputable def canonicalizeDirectBoundaryWitnessPlanObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp BoundaryWitnessPlanOutput)
    (context : DeferredContext) (fuel : Nat) (value : α) (candidates : List Probe) :
    ProbComp BoundaryWitnessPlanOutput := by
  classical
  let canonical := canonicalizeMaterializedValues table context
  exact if hhit : PrivateStructuralHit canonical then
      pure ⟨.privateStructuralFailure, some (privateHitWitnessOf canonical hhit), candidates⟩
    else if PublishedValues context.state then
      classifyDirectBoundaryWitnessPlanObserve table observe canonical fuel value candidates
    else
      pure ⟨.ordinaryFailure, none, candidates⟩

noncomputable def runDirectBoundaryWitnessPlanObserve
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp BoundaryWitnessPlanOutput)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    ProbComp BoundaryWitnessPlanOutput :=
  runDirectResolvedWitnessFromTable context fuel table computation >>=
    finishDirectBoundaryWitnessPlanObserve observe candidates

noncomputable def directDetailedBoundaryNormalizedBoundaryWitnessPlanObserve
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) → List Probe →
      ProbComp BoundaryWitnessPlanOutput)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ProbComp BoundaryWitnessPlanOutput := by
  classical
  exact OracleComp.construct
    (C := fun _ : OracleComp (OracleWorld + SigningSpec) α =>
      (DeferredContext → Nat → (α × SplitHashCache) → List Probe →
        ProbComp BoundaryWitnessPlanOutput) →
      List Probe → DeferredContext → Nat → (OtsSecretIndex → HashOutput) →
        SplitHashCache → ProbComp BoundaryWitnessPlanOutput)
    (fun value observe candidates context fuel _table cache =>
      observe context fuel (value, cache) candidates)
    (fun query _next recursivelyRun observe candidates context fuel table cache =>
      match query with
      | .inl (.inl n) =>
          runDirectBoundaryWitnessPlanObserve
            (canonicalizeDirectBoundaryWitnessPlanObserve table
              (fun nextContext remaining value nextCandidates =>
                recursivelyRun value.1 observe nextCandidates nextContext remaining table
                  value.2))
            candidates context fuel table ((splitUniformImpl n).run cache)
      | .inl (.inr input) =>
          let plan := purePlanProbingHashQuery parameter input context.state
          let nextCandidates := appendPlannedCandidate candidates
            (rootAwarePlannedCandidate? parameter input context.state)
          runDirectBoundaryWitnessPlanObserve
            (canonicalizeDirectBoundaryWitnessPlanObserve table
              (fun nextContext remaining value laterCandidates =>
                recursivelyRun value.1 observe laterCandidates nextContext remaining table
                  value.2))
            nextCandidates context fuel table
              ((probingHashQueryAfterPlan parameter input plan).run cache)
      | .inr message =>
          runDirectBoundaryWitnessPlanObserve
            (canonicalizeDirectBoundaryWitnessPlanObserve table
              (fun nextContext remaining value nextCandidates =>
                recursivelyRun value.1 observe nextCandidates nextContext remaining table
                  value.2))
            candidates context fuel table ((maskedSign parameter root ftsSecret message).run cache))
    computation observe candidates context fuel table cache

noncomputable def retainedResolvedFinalizationBoundaryWitnessPlanObserve
    (table : OtsSecretIndex → HashOutput) (root : Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : RetainedRestResult × SplitHashCache) (candidates : List Probe) :
    ProbComp BoundaryWitnessPlanOutput := by
  classical
  exact if hhit : PrivateStructuralHit context then
      pure ⟨.privateStructuralFailure, some (privateHitWitnessOf context hhit), candidates⟩
    else if DeferredCompletable table context then do
      let failed ← resolvedFinalizationObserve table context fuel ((root, value.1), value.2)
      pure ⟨DirectBoundaryOutcome.ofFailed failed, none, candidates⟩
    else
      pure ⟨.ordinaryFailure, none, candidates⟩

noncomputable def granularDetailedRetainedRestNormalizedBoundaryWitnessPlanObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (candidates : List Probe) :
    ProbComp BoundaryWitnessPlanOutput :=
  directDetailedBoundaryNormalizedBoundaryWitnessPlanObserve parameter value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
    (retainedResolvedFinalizationBoundaryWitnessPlanObserve table value.1)
    candidates context fuel table value.2

noncomputable def granularAllCanonicalBoundaryWitnessPlan
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp BoundaryWitnessPlanOutput :=
  runDirectBoundaryWitnessPlanObserve
    (canonicalizeDirectBoundaryWitnessPlanObserve table
      (granularDetailedRetainedRestNormalizedBoundaryWitnessPlanObserve adversary parameter table
        ftsSecret))
    [] emptyWitnessDeferredContext fuel table
      (maskedPublishedTreeRoot.run emptySplitHashCache)

theorem boundaryWitnessCovers_of_witness
    (outcome : DirectBoundaryOutcome) (witness : PrivateHitWitness)
    (candidates : List Probe) :
    BoundaryWitnessCovers ⟨outcome, some witness, candidates⟩ outcome := by
  intro _
  exact Or.inl rfl

theorem relTriple_any_ordinaryFailure_boundaryWitnessCovers
    (left : ProbComp BoundaryWitnessPlanOutput) :
    RelTriple (spec₁ := unifSpec) (spec₂ := unifSpec) left
      (pure (.ordinaryFailure : DirectBoundaryOutcome)) BoundaryWitnessCovers := by
  have hbase : RelTriple left
      (pure .ordinaryFailure : ProbComp DirectBoundaryOutcome) (fun _ _ ↦ True) :=
    relTriple_true _ _
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hbase
  apply relTriple_post_mono hsupported
  intro source outcome hrelation
  have houtcome : outcome = .ordinaryFailure := by simpa using hrelation.2
  subst outcome
  intro _
  exact Or.inr rfl

set_option maxRecDepth 100000 in
theorem relTriple_retainedFinalizationBoundaryWitnessPlan_detailed
    (table : OtsSecretIndex → HashOutput) (root : Digest)
    (value : RetainedRestResult)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache) (candidates : List Probe)
    (hcontext : FinalizationContextLE table left right) :
    RelTriple
      (retainedResolvedFinalizationBoundaryWitnessPlanObserve table root left leftFuel
        (value, leftCache) candidates)
      (retainedResolvedFinalizationDetailedObserve table root right rightFuel
        (value, rightCache))
      BoundaryWitnessCovers := by
  have hleftNotPrivate := not_privateStructuralHit_of_deferredCompletable
    hcontext.leftCompletable
  have hrightNotPrivate := not_privateStructuralHit_of_deferredCompletable
    hcontext.rightCompletable
  unfold retainedResolvedFinalizationBoundaryWitnessPlanObserve
    retainedResolvedFinalizationDetailedObserve classifyDirectObserve
  simp only [hleftNotPrivate, hrightNotPrivate, ↓reduceDIte, hcontext.leftCompletable,
    hcontext.rightCompletable, ↓reduceIte, map_eq_bind_pure_comp]
  have hfinal := relTriple_finishResolvedRunIsNone_of_finalizationContextLE table left right
    leftFuel rightFuel ((root, value), leftCache) ((root, value), rightCache) hcontext
  apply relTriple_bind hfinal
  intro leftFailed rightFailed himp
  apply relTriple_pure_pure
  intro hsource
  right
  cases leftFailed <;> cases rightFailed <;>
    simp [BoolImp, DirectBoundaryOutcome.ofFailed, DirectBoundaryOutcome.failed,
      DirectBoundaryOutcome.ordinary] at himp hsource ⊢

set_option maxRecDepth 100000 in
theorem evalDist_witnessPlan_retainedFinalizationBoundaryWitnessPlan
    (table : OtsSecretIndex → HashOutput) (root : Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : RetainedRestResult × SplitHashCache) (candidates : List Probe) :
    evalDist (BoundaryWitnessPlanOutput.witnessPlan <$>
        retainedResolvedFinalizationBoundaryWitnessPlanObserve table root context fuel value
          candidates) =
      evalDist
        (retainedResolvedFinalizationPrivateWitnessPlanObserve table root context fuel value
          candidates) := by
  classical
  unfold retainedResolvedFinalizationBoundaryWitnessPlanObserve
    retainedResolvedFinalizationPrivateWitnessPlanObserve
  by_cases hhit : PrivateStructuralHit context
  · simp [hhit]
  · simp only [hhit, ↓reduceDIte, map_eq_bind_pure_comp]
    by_cases hcompletable : DeferredCompletable table context
    · simp only [hcompletable, ↓reduceIte]
      simp only [bind_assoc, pure_bind, Function.comp_apply]
      change evalDist
          (resolvedFinalizationObserve table context fuel ((root, value.1), value.2) >>=
            fun _ => pure (none, candidates)) =
        evalDist (pure (none, candidates) : ProbComp PrivateWitnessPlanOutput)
      exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        (resolvedFinalizationObserve table context fuel ((root, value.1), value.2))
        (by simp [resolvedFinalizationObserve]) _
    · simp [hcompletable]

theorem evalDist_witnessPlan_finishDirectBoundaryWitnessPlanObserve
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp BoundaryWitnessPlanOutput)
    (witnessObserve : DeferredContext → Nat → α → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (candidates : List Probe) (result : DirectWitnessResult α)
    (hproject : ∀ context fuel value nextCandidates,
      evalDist (BoundaryWitnessPlanOutput.witnessPlan <$>
          observe context fuel value nextCandidates) =
        evalDist (witnessObserve context fuel value nextCandidates)) :
    evalDist (BoundaryWitnessPlanOutput.witnessPlan <$>
        finishDirectBoundaryWitnessPlanObserve observe candidates result) =
      evalDist (finishDirectWitnessPlanObserve witnessObserve candidates result) := by
  cases result with
  | stoppedFuel => simp [finishDirectBoundaryWitnessPlanObserve, finishDirectWitnessPlanObserve]
  | stoppedOrdinary =>
      simp [finishDirectBoundaryWitnessPlanObserve, finishDirectWitnessPlanObserve]
  | stoppedPrivate witness =>
      simp [finishDirectBoundaryWitnessPlanObserve, finishDirectWitnessPlanObserve]
  | done result => exact hproject result.context result.remaining result.value candidates

theorem evalDist_witnessPlan_classifyDirectBoundaryWitnessPlanObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp BoundaryWitnessPlanOutput)
    (witnessObserve : DeferredContext → Nat → α → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (context : DeferredContext) (fuel : Nat) (value : α) (candidates : List Probe)
    (hproject : ∀ nextContext remaining nextValue nextCandidates,
      evalDist (BoundaryWitnessPlanOutput.witnessPlan <$>
          observe nextContext remaining nextValue nextCandidates) =
        evalDist (witnessObserve nextContext remaining nextValue nextCandidates)) :
    evalDist (BoundaryWitnessPlanOutput.witnessPlan <$>
        classifyDirectBoundaryWitnessPlanObserve table observe context fuel value candidates) =
      evalDist
        (classifyDirectWitnessPlanObserve table witnessObserve context fuel value candidates) := by
  classical
  unfold classifyDirectBoundaryWitnessPlanObserve classifyDirectWitnessPlanObserve
  by_cases hhit : PrivateStructuralHit context
  · simp [hhit]
  · simp only [hhit, ↓reduceDIte]
    by_cases hcompletable : DeferredCompletable table context
    · simp only [hcompletable, ↓reduceIte]
      exact hproject context fuel value candidates
    · simp [hcompletable]

theorem evalDist_witnessPlan_canonicalizeDirectBoundaryWitnessPlanObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp BoundaryWitnessPlanOutput)
    (witnessObserve : DeferredContext → Nat → α → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (context : DeferredContext) (fuel : Nat) (value : α) (candidates : List Probe)
    (hproject : ∀ nextContext remaining nextValue nextCandidates,
      evalDist (BoundaryWitnessPlanOutput.witnessPlan <$>
          observe nextContext remaining nextValue nextCandidates) =
        evalDist (witnessObserve nextContext remaining nextValue nextCandidates)) :
    evalDist (BoundaryWitnessPlanOutput.witnessPlan <$>
        canonicalizeDirectBoundaryWitnessPlanObserve table observe context fuel value candidates) =
      evalDist
        (canonicalizeDirectWitnessPlanObserve table witnessObserve context fuel value candidates) := by
  classical
  unfold canonicalizeDirectBoundaryWitnessPlanObserve canonicalizeDirectWitnessPlanObserve
  let canonical := canonicalizeMaterializedValues table context
  by_cases hhit : PrivateStructuralHit canonical
  · simp [canonical, hhit]
  · simp only [canonical, hhit, ↓reduceDIte]
    by_cases hpublished : PublishedValues context.state
    · simp only [hpublished, ↓reduceIte]
      exact evalDist_witnessPlan_classifyDirectBoundaryWitnessPlanObserve table observe
        witnessObserve canonical fuel value candidates hproject
    · simp [hpublished]

set_option maxRecDepth 100000 in
theorem evalDist_witnessPlan_runDirectBoundaryWitnessPlanObserve
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp BoundaryWitnessPlanOutput)
    (witnessObserve : DeferredContext → Nat → α → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hproject : ∀ nextContext remaining value nextCandidates,
      evalDist (BoundaryWitnessPlanOutput.witnessPlan <$>
          observe nextContext remaining value nextCandidates) =
        evalDist (witnessObserve nextContext remaining value nextCandidates)) :
    evalDist (BoundaryWitnessPlanOutput.witnessPlan <$>
        runDirectBoundaryWitnessPlanObserve observe candidates context fuel table computation) =
      evalDist
        (runDirectWitnessPlanObserve witnessObserve candidates context fuel table computation) := by
  unfold runDirectBoundaryWitnessPlanObserve runDirectWitnessPlanObserve
  rw [map_bind]
  apply evalDist_bind_congr
  intro result _hresult
  exact evalDist_witnessPlan_finishDirectBoundaryWitnessPlanObserve observe witnessObserve
    candidates result hproject

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem evalDist_witnessPlan_directDetailedBoundaryNormalizedBoundaryWitnessPlanObserve
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) → List Probe →
      ProbComp BoundaryWitnessPlanOutput)
    (witnessObserve : DeferredContext → Nat → (α × SplitHashCache) → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hproject : ∀ nextContext remaining value nextCandidates,
      evalDist (BoundaryWitnessPlanOutput.witnessPlan <$>
          observe nextContext remaining value nextCandidates) =
        evalDist (witnessObserve nextContext remaining value nextCandidates)) :
    evalDist (BoundaryWitnessPlanOutput.witnessPlan <$>
        directDetailedBoundaryNormalizedBoundaryWitnessPlanObserve parameter root ftsSecret
          computation observe candidates context fuel table cache) =
      evalDist (directDetailedBoundaryNormalizedPrivateWitnessPlanObserve parameter root ftsSecret
        computation witnessObserve candidates context fuel table cache) := by
  induction computation using OracleComp.inductionOn generalizing candidates context fuel cache with
  | pure value =>
      rw [directDetailedBoundaryNormalizedBoundaryWitnessPlanObserve,
        OracleComp.construct_pure,
        directDetailedBoundaryNormalizedPrivateWitnessPlanObserve, OracleComp.construct_pure]
      exact hproject context fuel (value, cache) candidates
  | query_bind query next ih =>
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              rw [directDetailedBoundaryNormalizedBoundaryWitnessPlanObserve,
                OracleComp.construct_query_bind,
                directDetailedBoundaryNormalizedPrivateWitnessPlanObserve,
                OracleComp.construct_query_bind]
              apply evalDist_witnessPlan_runDirectBoundaryWitnessPlanObserve
              intro nextContext remaining value nextCandidates
              apply evalDist_witnessPlan_canonicalizeDirectBoundaryWitnessPlanObserve
              intro finalContext finalRemaining finalValue finalCandidates
              exact ih finalValue.1 finalCandidates finalContext finalRemaining finalValue.2
          | inr input =>
              rw [directDetailedBoundaryNormalizedBoundaryWitnessPlanObserve,
                OracleComp.construct_query_bind,
                directDetailedBoundaryNormalizedPrivateWitnessPlanObserve,
                OracleComp.construct_query_bind]
              apply evalDist_witnessPlan_runDirectBoundaryWitnessPlanObserve
              intro nextContext remaining value laterCandidates
              apply evalDist_witnessPlan_canonicalizeDirectBoundaryWitnessPlanObserve
              intro finalContext finalRemaining finalValue finalCandidates
              exact ih finalValue.1 finalCandidates finalContext finalRemaining finalValue.2
      | inr message =>
          rw [directDetailedBoundaryNormalizedBoundaryWitnessPlanObserve,
            OracleComp.construct_query_bind,
            directDetailedBoundaryNormalizedPrivateWitnessPlanObserve,
            OracleComp.construct_query_bind]
          apply evalDist_witnessPlan_runDirectBoundaryWitnessPlanObserve
          intro nextContext remaining value nextCandidates
          apply evalDist_witnessPlan_canonicalizeDirectBoundaryWitnessPlanObserve
          intro finalContext finalRemaining finalValue finalCandidates
          exact ih finalValue.1 finalCandidates finalContext finalRemaining finalValue.2

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem evalDist_witnessPlan_granularDetailedRetainedRestNormalizedBoundaryWitnessPlanObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (candidates : List Probe) :
    evalDist (BoundaryWitnessPlanOutput.witnessPlan <$>
        granularDetailedRetainedRestNormalizedBoundaryWitnessPlanObserve adversary parameter table
          ftsSecret context fuel value candidates) =
      evalDist
        (granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve adversary parameter table
          ftsSecret context fuel value candidates) := by
  unfold granularDetailedRetainedRestNormalizedBoundaryWitnessPlanObserve
    granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve
  apply evalDist_witnessPlan_directDetailedBoundaryNormalizedBoundaryWitnessPlanObserve
  intro nextContext remaining nextValue nextCandidates
  exact evalDist_witnessPlan_retainedFinalizationBoundaryWitnessPlan table value.1 nextContext
    remaining nextValue nextCandidates

set_option maxRecDepth 100000 in
theorem evalDist_witnessPlan_granularAllCanonicalBoundaryWitnessPlan
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (BoundaryWitnessPlanOutput.witnessPlan <$>
        granularAllCanonicalBoundaryWitnessPlan adversary parameter table ftsSecret fuel) =
      evalDist
        (granularAllCanonicalPrivateWitnessPlan adversary parameter table ftsSecret fuel) := by
  unfold granularAllCanonicalBoundaryWitnessPlan granularAllCanonicalPrivateWitnessPlan
  apply evalDist_witnessPlan_runDirectBoundaryWitnessPlanObserve
  intro context remaining value candidates
  apply evalDist_witnessPlan_canonicalizeDirectBoundaryWitnessPlanObserve
  intro nextContext nextRemaining nextValue nextCandidates
  exact
    evalDist_witnessPlan_granularDetailedRetainedRestNormalizedBoundaryWitnessPlanObserve
      adversary parameter table ftsSecret nextContext nextRemaining nextValue nextCandidates

theorem evalDist_outcome_finishDirectBoundaryWitnessPlanObserve
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp BoundaryWitnessPlanOutput)
    (detailedObserve : DeferredContext → Nat → α → ProbComp DirectBoundaryOutcome)
    (candidates : List Probe) (result : DirectWitnessResult α)
    (hproject : ∀ context fuel value nextCandidates,
      evalDist (BoundaryWitnessPlanOutput.outcome <$> observe context fuel value nextCandidates) =
        evalDist (detailedObserve context fuel value)) :
    evalDist (BoundaryWitnessPlanOutput.outcome <$>
        finishDirectBoundaryWitnessPlanObserve observe candidates result) =
      evalDist (finishDirectDetailedObserve detailedObserve result.erase) := by
  cases result with
  | stoppedFuel => simp [finishDirectBoundaryWitnessPlanObserve, finishDirectDetailedObserve,
      DirectWitnessResult.erase]
  | stoppedOrdinary => simp [finishDirectBoundaryWitnessPlanObserve, finishDirectDetailedObserve,
      DirectWitnessResult.erase]
  | stoppedPrivate witness =>
      simp [finishDirectBoundaryWitnessPlanObserve, finishDirectDetailedObserve,
        DirectWitnessResult.erase]
  | done result => exact hproject result.context result.remaining result.value candidates

theorem evalDist_outcome_classifyDirectBoundaryWitnessPlanObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp BoundaryWitnessPlanOutput)
    (detailedObserve : DeferredContext → Nat → α → ProbComp DirectBoundaryOutcome)
    (context : DeferredContext) (fuel : Nat) (value : α) (candidates : List Probe)
    (hproject : ∀ nextContext remaining nextValue nextCandidates,
      evalDist (BoundaryWitnessPlanOutput.outcome <$>
          observe nextContext remaining nextValue nextCandidates) =
        evalDist (detailedObserve nextContext remaining nextValue)) :
    evalDist (BoundaryWitnessPlanOutput.outcome <$>
        classifyDirectBoundaryWitnessPlanObserve table observe context fuel value candidates) =
      evalDist (classifyDirectDetailedObserve table detailedObserve context fuel value) := by
  classical
  unfold classifyDirectBoundaryWitnessPlanObserve classifyDirectDetailedObserve
  by_cases hhit : PrivateStructuralHit context
  · simp [hhit]
  · simp only [hhit, ↓reduceDIte]
    by_cases hcompletable : DeferredCompletable table context
    · simp only [hcompletable, ↓reduceIte]
      exact hproject context fuel value candidates
    · simp [hcompletable]

theorem evalDist_outcome_canonicalizeDirectBoundaryWitnessPlanObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp BoundaryWitnessPlanOutput)
    (detailedObserve : DeferredContext → Nat → α → ProbComp DirectBoundaryOutcome)
    (context : DeferredContext) (fuel : Nat) (value : α) (candidates : List Probe)
    (hproject : ∀ nextContext remaining nextValue nextCandidates,
      evalDist (BoundaryWitnessPlanOutput.outcome <$>
          observe nextContext remaining nextValue nextCandidates) =
        evalDist (detailedObserve nextContext remaining nextValue)) :
    evalDist (BoundaryWitnessPlanOutput.outcome <$>
        canonicalizeDirectBoundaryWitnessPlanObserve table observe context fuel value candidates) =
      evalDist (canonicalizeDirectDetailedObserve table detailedObserve context fuel value) := by
  classical
  unfold canonicalizeDirectBoundaryWitnessPlanObserve canonicalizeDirectDetailedObserve
  let canonical := canonicalizeMaterializedValues table context
  by_cases hhit : PrivateStructuralHit canonical
  · simp [canonical, hhit]
  · simp only [canonical, hhit, ↓reduceDIte]
    by_cases hpublished : PublishedValues context.state
    · simp only [hpublished, ↓reduceIte]
      exact evalDist_outcome_classifyDirectBoundaryWitnessPlanObserve table observe
        detailedObserve canonical fuel value candidates hproject
    · simp [hpublished]

set_option maxRecDepth 100000 in
theorem evalDist_outcome_runDirectBoundaryWitnessPlanObserve
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp BoundaryWitnessPlanOutput)
    (detailedObserve : DeferredContext → Nat → α → ProbComp DirectBoundaryOutcome)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hproject : ∀ nextContext remaining value nextCandidates,
      evalDist (BoundaryWitnessPlanOutput.outcome <$>
          observe nextContext remaining value nextCandidates) =
        evalDist (detailedObserve nextContext remaining value)) :
    evalDist (BoundaryWitnessPlanOutput.outcome <$>
        runDirectBoundaryWitnessPlanObserve observe candidates context fuel table computation) =
      evalDist (runDirectDetailedObserve detailedObserve context fuel table computation) := by
  unfold runDirectBoundaryWitnessPlanObserve runDirectDetailedObserve
  rw [map_bind]
  calc
    _ = evalDist
        (runDirectResolvedWitnessFromTable context fuel table computation >>= fun result ↦
          finishDirectDetailedObserve detailedObserve result.erase) := by
      apply evalDist_bind_congr
      intro result _hresult
      exact evalDist_outcome_finishDirectBoundaryWitnessPlanObserve observe detailedObserve
        candidates result hproject
    _ = _ := by
      rw [← map_erase_runDirectResolvedWitnessFromTable computation context fuel table,
        map_eq_bind_pure_comp, bind_assoc]
      apply evalDist_bind_congr
      intro result _hresult
      rfl

set_option maxRecDepth 100000 in
theorem evalDist_runDirectDetailedObserve_probingHashQuery_eq_afterPlan
    (parameter : PublicParameter) (input : HashInput)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (observe : DeferredContext → Nat → (HashOutput × SplitHashCache) →
      ProbComp DirectBoundaryOutcome)
    (hfactor : probingHashQuery parameter input = (do
      let plan ← planProbingHashQuery parameter input
      probingHashQueryAfterPlan parameter input plan)) :
    evalDist (runDirectDetailedObserve observe context fuel table
        ((probingHashQuery parameter input).run cache)) =
      evalDist (runDirectDetailedObserve observe context fuel table
        ((probingHashQueryAfterPlan parameter input
          (purePlanProbingHashQuery parameter input context.state)).run cache)) := by
  rw [hfactor]
  unfold runDirectDetailedObserve
  rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind]
  rw [runDirectResolvedDetailed_planProbingHashQuery parameter input context.state context fuel
    table cache rfl]
  simp only [pure_bind]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 1000000 in
theorem evalDist_outcome_directDetailedBoundaryNormalizedBoundaryWitnessPlanObserve
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) → List Probe →
      ProbComp BoundaryWitnessPlanOutput)
    (detailedObserve : DeferredContext → Nat → (α × SplitHashCache) →
      ProbComp DirectBoundaryOutcome)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hproject : ∀ nextContext remaining value nextCandidates,
      evalDist (BoundaryWitnessPlanOutput.outcome <$>
          observe nextContext remaining value nextCandidates) =
        evalDist (detailedObserve nextContext remaining value)) :
    evalDist (BoundaryWitnessPlanOutput.outcome <$>
        directDetailedBoundaryNormalizedBoundaryWitnessPlanObserve parameter root ftsSecret
          computation observe candidates context fuel table cache) =
      evalDist (directDetailedBoundaryObserve
        (maskedExpandedAdversaryImpl parameter root ftsSecret) computation detailedObserve
        context fuel table cache) := by
  induction computation using OracleComp.inductionOn generalizing candidates context fuel cache with
  | pure value =>
      rw [directDetailedBoundaryNormalizedBoundaryWitnessPlanObserve,
        OracleComp.construct_pure, directDetailedBoundaryObserve, OracleComp.construct_pure]
      exact hproject context fuel (value, cache) candidates
  | query_bind query next ih =>
      rw [directDetailedBoundaryNormalizedBoundaryWitnessPlanObserve,
        OracleComp.construct_query_bind, directDetailedBoundaryObserve,
        OracleComp.construct_query_bind]
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              apply evalDist_outcome_runDirectBoundaryWitnessPlanObserve
              intro nextContext remaining value nextCandidates
              apply evalDist_outcome_canonicalizeDirectBoundaryWitnessPlanObserve
              intro finalContext finalRemaining finalValue finalCandidates
              exact ih finalValue.1 finalCandidates finalContext finalRemaining finalValue.2
          | inr input =>
              let plan := purePlanProbingHashQuery parameter input context.state
              let nextCandidates := appendPlannedCandidate candidates
                (rootAwarePlannedCandidate? parameter input context.state)
              let nextDetailed : DeferredContext → Nat →
                  (HashOutput × SplitHashCache) → ProbComp DirectBoundaryOutcome :=
                canonicalizeDirectDetailedObserve table
                  (fun nextContext remaining value ↦
                    directDetailedBoundaryObserve
                      (maskedExpandedAdversaryImpl parameter root ftsSecret)
                      (next value.1) detailedObserve nextContext remaining table value.2)
              calc
                _ = evalDist (runDirectDetailedObserve nextDetailed
                      context fuel table
                      ((probingHashQueryAfterPlan parameter input plan).run cache)) := by
                    apply evalDist_outcome_runDirectBoundaryWitnessPlanObserve
                    intro nextContext remaining value laterCandidates
                    apply evalDist_outcome_canonicalizeDirectBoundaryWitnessPlanObserve
                    intro finalContext finalRemaining finalValue finalCandidates
                    exact ih finalValue.1 finalCandidates finalContext finalRemaining finalValue.2
                _ = _ := by
                  symm
                  exact evalDist_runDirectDetailedObserve_probingHashQuery_eq_afterPlan
                    parameter input context fuel table cache nextDetailed (by
                      cases hprobe : decodeProbe? parameter input with
                      | some candidate =>
                          cases hposition : decodePosition? parameter input with
                          | none =>
                              exact probingHashQuery_eq_plan_then_afterPlan_of_probe_some_nonleaf
                                parameter input candidate hprobe (by
                                  rintro ⟨lay, tree, leafIdx, heq⟩
                                  simp [hposition] at heq)
                          | some position =>
                              cases position with
                              | leaf lay tree leafIdx =>
                                  exact probingHashQuery_eq_plan_then_afterPlan_leaf parameter input
                                    candidate lay tree leafIdx hprobe hposition
                              | chain | node | ftsLeaf | ftsNode | ftsRoots =>
                                  exact probingHashQuery_eq_plan_then_afterPlan_of_probe_some_nonleaf
                                    parameter input candidate hprobe (by
                                      rintro ⟨lay, tree, leafIdx, heq⟩
                                      simp [hposition] at heq)
                      | none =>
                          cases hposition : decodePosition? parameter input with
                          | none =>
                              exact probingHashQuery_eq_plan_then_afterPlan_of_probe_none_nonnode
                                parameter input hprobe (by
                                  rintro ⟨lay, tree, level, nodeIdx, heq⟩
                                  simp [hposition] at heq)
                          | some position =>
                              cases position with
                              | node lay tree level nodeIdx =>
                                  exact probingHashQuery_eq_plan_then_afterPlan_node parameter input
                                    lay tree level nodeIdx hprobe hposition
                              | chain | leaf | ftsLeaf | ftsNode | ftsRoots =>
                                  exact probingHashQuery_eq_plan_then_afterPlan_of_probe_none_nonnode
                                    parameter input hprobe (by
                                      rintro ⟨lay, tree, level, nodeIdx, heq⟩
                                      simp [hposition] at heq))
      | inr message =>
          apply evalDist_outcome_runDirectBoundaryWitnessPlanObserve
          intro nextContext remaining value nextCandidates
          apply evalDist_outcome_canonicalizeDirectBoundaryWitnessPlanObserve
          intro finalContext finalRemaining finalValue finalCandidates
          exact ih finalValue.1 finalCandidates finalContext finalRemaining finalValue.2

theorem evalDist_outcome_retainedFinalizationBoundaryWitnessPlan
    (table : OtsSecretIndex → HashOutput) (root : Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : RetainedRestResult × SplitHashCache) (candidates : List Probe) :
    evalDist (BoundaryWitnessPlanOutput.outcome <$>
        retainedResolvedFinalizationBoundaryWitnessPlanObserve table root context fuel value
          candidates) =
      evalDist (retainedResolvedFinalizationDetailedObserve table root context fuel value) := by
  classical
  unfold retainedResolvedFinalizationBoundaryWitnessPlanObserve
    retainedResolvedFinalizationDetailedObserve classifyDirectObserve
  by_cases hhit : PrivateStructuralHit context
  · simp [hhit]
  · simp only [hhit, ↓reduceDIte]
    by_cases hcompletable : DeferredCompletable table context
    · simp [hcompletable, Functor.map_map]
    · simp [hcompletable]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem evalDist_outcome_granularDetailedRetainedRestNormalizedBoundaryWitnessPlanObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (candidates : List Probe) :
    evalDist (BoundaryWitnessPlanOutput.outcome <$>
        granularDetailedRetainedRestNormalizedBoundaryWitnessPlanObserve adversary parameter table
          ftsSecret context fuel value candidates) =
      evalDist (granularDetailedRetainedRestObserve adversary parameter table ftsSecret
        context fuel value) := by
  unfold granularDetailedRetainedRestNormalizedBoundaryWitnessPlanObserve
    granularDetailedRetainedRestObserve
  apply evalDist_outcome_directDetailedBoundaryNormalizedBoundaryWitnessPlanObserve
  intro nextContext remaining nextValue nextCandidates
  exact evalDist_outcome_retainedFinalizationBoundaryWitnessPlan table value.1 nextContext
    remaining nextValue nextCandidates

noncomputable def sampledGranularAllCanonicalBoundaryWitnessPlan
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp BoundaryWitnessPlanOutput := do
  let table ← sampleOtsHashTable
  granularAllCanonicalBoundaryWitnessPlan adversary parameter table ftsSecret fuel

noncomputable def sampledRootAwareMaterializedBoundaryDetailedRetainedOutcome
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp DirectBoundaryOutcome := do
  let table ← sampleOtsHashTable
  rootAwareMaterializedBoundaryDetailedRetainedOutcome adversary parameter table ftsSecret fuel

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
theorem evalDist_witnessPlan_sampledGranularAllCanonicalBoundaryWitnessPlan
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (BoundaryWitnessPlanOutput.witnessPlan <$>
        sampledGranularAllCanonicalBoundaryWitnessPlan adversary parameter ftsSecret fuel) =
      evalDist
        (sampledGranularAllCanonicalPrivateWitnessPlan adversary parameter ftsSecret fuel) := by
  unfold sampledGranularAllCanonicalBoundaryWitnessPlan
    sampledGranularAllCanonicalPrivateWitnessPlan
  rw [map_bind]
  apply evalDist_bind_congr
  intro table _htable
  exact evalDist_witnessPlan_granularAllCanonicalBoundaryWitnessPlan adversary parameter table
    ftsSecret fuel

set_option maxRecDepth 100000 in
theorem relTriple_finishBoundaryWitnessPlan_detailed_of_materializedStable
    (table : OtsSecretIndex → HashOutput)
    (leftRun : ProbComp (DirectWitnessResult (α × SplitHashCache)))
    (rightRun : ProbComp (DirectDetailedResult (α × SplitHashCache)))
    (leftObserve : DeferredContext → Nat → (α × SplitHashCache) → List Probe →
      ProbComp BoundaryWitnessPlanOutput)
    (rightObserve : DeferredContext → Nat → (α × SplitHashCache) →
      ProbComp DirectBoundaryOutcome)
    (candidates : List Probe)
    (hstep : RelTriple leftRun rightRun (DirectWitnessMaterializedStableRunEq table))
    (hclean : ∀ left right,
      DirectWitnessResult.done left ∈ support leftRun →
      DirectDetailedResult.done right ∈ support rightRun →
      OrdinaryMaterializedRunEq table left right →
      RelTriple
        (leftObserve left.context left.remaining left.value candidates)
        (rightObserve right.context right.remaining right.value)
        BoundaryWitnessCovers)
    (hdoomed : ∀ (left : ProbComp BoundaryWitnessPlanOutput) right,
      DirectDetailedResult.done right ∈ support rightRun →
      OrdinaryMaterializedDoomedRun table right →
      RelTriple left (rightObserve right.context right.remaining right.value)
        BoundaryWitnessCovers) :
    RelTriple
      (leftRun >>= finishDirectBoundaryWitnessPlanObserve leftObserve candidates)
      (rightRun >>= finishDirectDetailedObserve rightObserve)
      BoundaryWitnessCovers := by
  have hleftSupport :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hstep
      (fun result ↦ result ∈ support leftRun) (fun _ hresult ↦ hresult)
  have hbothSupport :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleftSupport
  apply relTriple_bind hbothSupport
  intro left right hrelation
  rcases hrelation with ⟨⟨hrelation, hleftMem⟩, hrightMem⟩
  cases left with
  | stoppedFuel =>
      cases right with
      | stopped reason =>
          cases reason with
          | privateStructuralHit => contradiction
          | ordinaryHit => simp [finishDirectBoundaryWitnessPlanObserve,
              finishDirectDetailedObserve, BoundaryWitnessCovers]
          | fuelExhausted => simp [finishDirectBoundaryWitnessPlanObserve,
              finishDirectDetailedObserve, BoundaryWitnessCovers]
      | done right =>
          exact hdoomed (pure ⟨.ordinaryFailure, none, candidates⟩) right hrightMem hrelation
  | stoppedOrdinary =>
      cases right with
      | stopped reason =>
          cases reason with
          | privateStructuralHit => contradiction
          | ordinaryHit => simp [finishDirectBoundaryWitnessPlanObserve,
              finishDirectDetailedObserve, BoundaryWitnessCovers]
          | fuelExhausted => simp [finishDirectBoundaryWitnessPlanObserve,
              finishDirectDetailedObserve, BoundaryWitnessCovers]
      | done right =>
          exact hdoomed (pure ⟨.ordinaryFailure, none, candidates⟩) right hrightMem hrelation
  | stoppedPrivate witness =>
      have hbase := relTriple_true
        (pure ⟨.privateStructuralFailure, some witness, candidates⟩ :
          ProbComp BoundaryWitnessPlanOutput)
        (finishDirectDetailedObserve rightObserve right)
      have hleft :=
        SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
          (fun source ↦ source = ⟨.privateStructuralFailure, some witness, candidates⟩) (by simp)
      apply relTriple_post_mono hleft
      intro source outcome hsource
      rw [hsource.2]
      intro _
      exact Or.inl rfl
  | done left =>
      cases right with
      | stopped reason =>
          cases reason with
          | privateStructuralHit => contradiction
          | ordinaryHit => exact relTriple_any_ordinaryFailure_boundaryWitnessCovers _
          | fuelExhausted => exact relTriple_any_ordinaryFailure_boundaryWitnessCovers _
      | done right =>
          rcases hrelation with hcleanRelation | hdoomedRelation
          · exact hclean left right hleftMem hrightMem hcleanRelation
          · exact hdoomed
              (leftObserve left.context left.remaining left.value candidates)
              right hrightMem hdoomedRelation

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem relTriple_normalizedBoundaryWitness_rootAwareMaterializedDetailed
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (leftObserve : DeferredContext → Nat → (α × SplitHashCache) → List Probe →
      ProbComp BoundaryWitnessPlanOutput)
    (rightObserve : DeferredContext → Nat → (α × SplitHashCache) →
      ProbComp DirectBoundaryOutcome)
    (candidates : List Probe)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (leftCache rightCache : SplitHashCache) (q bound : Nat)
    (hbound :
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        computation).IsQueryBoundP (fun query => query matches Sum.inr _) bound)
    (hcontext : FinalizationContextLE table left right)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state)
    (hcanonical : CanonicalMaterializedValues table left)
    (hleftLower : bound ≤ leftFuel) (hleftUpper : leftFuel ≤ q)
    (hrightLower : q + bound ≤ rightFuel)
    (hterminal : ∀ value nextLeft nextRight nextLeftFuel nextRightFuel
        nextLeftCache nextRightCache nextCandidates,
      FinalizationContextLE table nextLeft nextRight →
      nextLeftFuel ≤ nextRightFuel →
      ordinaryQueryCache nextLeftCache = ordinaryQueryCache nextRightCache →
      nextLeft.state.revealed = nextRight.state.revealed →
      LazyRevealProbe.ValuesLE nextLeft.state nextRight.state →
      PublishedValues nextLeft.state →
      nextRight = directDeferredContext nextRight.state →
      CanonicalMaterializedValues table nextLeft →
      RelTriple
        (leftObserve nextLeft nextLeftFuel (value, nextLeftCache) nextCandidates)
        (rightObserve nextRight nextRightFuel (value, nextRightCache))
        BoundaryWitnessCovers) :
    RelTriple
      (directDetailedBoundaryNormalizedBoundaryWitnessPlanObserve parameter root ftsSecret
        computation leftObserve candidates left leftFuel table leftCache)
      (rootAwareMaterializedDetailedBoundaryObserve parameter root ftsSecret computation
        rightObserve right rightFuel table rightCache)
      BoundaryWitnessCovers := by
  induction computation using OracleComp.inductionOn generalizing
      candidates left right leftFuel rightFuel leftCache rightCache bound with
  | pure value =>
      simp only [directDetailedBoundaryNormalizedBoundaryWitnessPlanObserve,
        rootAwareMaterializedDetailedBoundaryObserve, OracleComp.construct_pure]
      exact hterminal value left right leftFuel rightFuel leftCache rightCache candidates
        hcontext (by omega) hcache hrevealed hvalues hpublished hrightMaterialized hcanonical
  | query_bind query next ih =>
      rw [directDetailedBoundaryNormalizedBoundaryWitnessPlanObserve,
        OracleComp.construct_query_bind, rootAwareMaterializedDetailedBoundaryObserve,
        OracleComp.construct_query_bind]
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              rw [simulateQ_expandedAdversaryImpl_query_bind_inl,
                OracleComp.isQueryBoundP_query_bind_iff] at hbound
              simp only
              let nextLeftObserve : DeferredContext → Nat →
                  (Fin (n + 1) × SplitHashCache) → List Probe →
                    ProbComp BoundaryWitnessPlanOutput :=
                fun nextContext remaining value nextCandidates =>
                  directDetailedBoundaryNormalizedBoundaryWitnessPlanObserve parameter root
                    ftsSecret (next value.1) leftObserve nextCandidates nextContext remaining
                    table value.2
              let nextRightObserve : DeferredContext → Nat →
                  (Fin (n + 1) × SplitHashCache) → ProbComp DirectBoundaryOutcome :=
                fun nextContext remaining value =>
                  rootAwareMaterializedDetailedBoundaryObserve parameter root ftsSecret
                    (next value.1) rightObserve nextContext remaining table value.2
              apply relTriple_finishBoundaryWitnessPlan_detailed_of_materializedStable table
              · exact (witnessMaterializedStableCouples_splitUniformImpl table n)
                  left right leftFuel rightFuel leftCache rightCache hcontext (by omega) hcache
                  hrevealed hvalues hpublished hrightMaterialized
              · intro nextLeft nextRight hleftSupport hrightSupport hclean
                have hcanonicalRun := hclean.canonicalize_left
                let canonical := canonicalizeMaterializedValues table nextLeft.context
                have hleftCompletable := hcanonicalRun.context_le.leftCompletable
                have hleftNotPrivate :=
                  not_privateStructuralHit_of_deferredCompletable hleftCompletable
                have hrightNotPrivate :=
                  not_privateStructuralHit_of_deferredCompletable
                    hcanonicalRun.context_le.rightCompletable
                simp only [canonicalizeDirectBoundaryWitnessPlanObserve, hleftNotPrivate,
                  ↓reduceDIte, hclean.left_published, ↓reduceIte,
                  classifyDirectBoundaryWitnessPlanObserve, hleftCompletable,
                  classifyDirectDetailedObserve, hrightNotPrivate,
                  hcanonicalRun.context_le.rightCompletable]
                rw [← hclean.value_eq]
                have hleftFuelPreserved : leftFuel ≤ nextLeft.remaining := by
                  have := fuel_le_remaining_add_of_done_runDirectResolvedWitnessFromTable
                    ((splitUniformImpl n).run leftCache) left leftFuel table nextLeft 0
                    (splitUniformImpl_probeFree n leftCache) hleftSupport
                  omega
                have hrightFuelPreserved : rightFuel ≤ nextRight.remaining := by
                  have := fuel_le_remaining_add_of_done_runDirectResolvedDetailedFromTable
                    ((splitUniformImpl n).run rightCache) right rightFuel table nextRight 0
                    (splitUniformImpl_probeFree n rightCache) hrightSupport
                  omega
                have hleftRemainingUpper : nextLeft.remaining ≤ leftFuel :=
                  remaining_le_fuel_of_done_runDirectResolvedDetailedFromTable
                    ((splitUniformImpl n).run leftCache) left leftFuel table nextLeft (by
                      rw [← map_erase_runDirectResolvedWitnessFromTable
                        ((splitUniformImpl n).run leftCache) left leftFuel table, support_map]
                      exact ⟨.done nextLeft, hleftSupport, rfl⟩)
                exact ih nextLeft.value.1 candidates canonical nextRight.context
                  nextLeft.remaining nextRight.remaining nextLeft.value.2 nextRight.value.2 bound
                  (hbound.2 nextLeft.value.1) hcanonicalRun.context_le hcanonicalRun.cache_eq
                  hcanonicalRun.revealed_eq hcanonicalRun.values_le
                  hcanonicalRun.left_published hcanonicalRun.right_materialized
                  (canonicalizeMaterializedValues_canonical table nextLeft.context
                    hclean.context_le.view.leftConsistent)
                  (by omega) (by omega) (by omega)
              · intro leftRun nextRight _hrightSupport hdoomed
                have hnotPrivate := not_privateStructuralHit_of_directDeferredContext
                  nextRight.context hdoomed.2
                have hnotCompletable : ¬DeferredCompletable table nextRight.context :=
                  hdoomed.1.2.2.2
                simpa [classifyDirectDetailedObserve, hnotPrivate, hnotCompletable] using
                  (relTriple_any_ordinaryFailure_boundaryWitnessCovers leftRun)
          | inr input =>
              rw [simulateQ_expandedAdversaryImpl_query_bind_inl,
                OracleComp.isQueryBoundP_query_bind_iff] at hbound
              simp only
              have hrightValues :
                  (materializedCanonicalContext table right.state).state.values =
                    left.state.values := by
                unfold materializedCanonicalContext
                rw [← hrightMaterialized]
                exact canonicalized_right_values_eq_of_finalizationContextLE hcontext
                  hrevealed hcanonical
              have hplanEq :
                  purePlanProbingHashQuery parameter input
                      (materializedCanonicalContext table right.state).state =
                    purePlanProbingHashQuery parameter input left.state :=
                purePlanProbingHashQuery_eq_of_values_eq hrightValues parameter input
              rw [hplanEq]
              let plan := purePlanProbingHashQuery parameter input left.state
              have hpublicExecutor :
                  probingHashQueryAfterRootAwarePublicPlan parameter input
                      (materializedCanonicalContext table right.state).state plan =
                    probingHashQueryAfterRootAwarePublicPlan parameter input left.state plan :=
                probingHashQueryAfterRootAwarePublicPlan_eq_of_values_eq parameter input
                  hrightValues plan
              rw [hpublicExecutor]
              let nextCandidates := appendPlannedCandidate candidates
                (rootAwarePlannedCandidate? parameter input left.state)
              let nextLeftObserve : DeferredContext → Nat →
                  (HashOutput × SplitHashCache) → List Probe →
                    ProbComp BoundaryWitnessPlanOutput :=
                fun nextContext remaining value laterCandidates =>
                  directDetailedBoundaryNormalizedBoundaryWitnessPlanObserve parameter root
                    ftsSecret (next value.1) leftObserve laterCandidates nextContext remaining
                    table value.2
              let nextRightObserve : DeferredContext → Nat →
                  (HashOutput × SplitHashCache) → ProbComp DirectBoundaryOutcome :=
                fun nextContext remaining value =>
                  rootAwareMaterializedDetailedBoundaryObserve parameter root ftsSecret
                    (next value.1) rightObserve nextContext remaining table value.2
              have hboundPositive : 0 < bound := by
                rcases hbound.1 with hnot | hpositive
                · exact (hnot (by simp)).elim
                · exact hpositive
              apply relTriple_finishBoundaryWitnessPlan_detailed_of_materializedStable table
              · exact relTriple_runDirectResolvedWitness_afterPlan_rootAwarePublic table parameter
                  input left.state plan left right leftFuel rightFuel leftCache rightCache rfl
                  (by omega) (by omega) hcontext hcache hrevealed hvalues hpublished
                  hrightMaterialized
              · intro nextLeft nextRight hleftSupport hrightSupport hclean
                have hcanonicalRun := hclean.canonicalize_left
                let canonical := canonicalizeMaterializedValues table nextLeft.context
                have hleftCompletable := hcanonicalRun.context_le.leftCompletable
                have hleftNotPrivate :=
                  not_privateStructuralHit_of_deferredCompletable hleftCompletable
                have hrightNotPrivate :=
                  not_privateStructuralHit_of_deferredCompletable
                    hcanonicalRun.context_le.rightCompletable
                simp only [canonicalizeDirectBoundaryWitnessPlanObserve, hleftNotPrivate,
                  ↓reduceDIte, hclean.left_published, ↓reduceIte,
                  classifyDirectBoundaryWitnessPlanObserve, hleftCompletable,
                  classifyDirectDetailedObserve, hrightNotPrivate,
                  hcanonicalRun.context_le.rightCompletable]
                rw [← hclean.value_eq]
                have hleftSpent : leftFuel ≤ nextLeft.remaining + 1 :=
                  fuel_le_remaining_add_of_done_runDirectResolvedWitnessFromTable
                    ((probingHashQueryAfterPlan parameter input plan).run leftCache)
                    left leftFuel table nextLeft 1
                    (probingHashQueryAfterPlan_isProbeBound_one parameter input plan leftCache)
                    hleftSupport
                have hrightSpent : rightFuel ≤ nextRight.remaining + 1 :=
                  fuel_le_remaining_add_of_done_runDirectResolvedDetailedFromTable
                    ((probingHashQueryAfterRootAwarePublicPlan parameter input left.state plan).run
                      rightCache)
                    right rightFuel table nextRight 1
                    (probingHashQueryAfterRootAwarePublicPlan_isProbeBound_one parameter input
                      left.state plan rightCache)
                    hrightSupport
                have htail :
                    (simulateQ
                      (SphincsSecurity.expandedAdversaryImpl
                        (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
                          SecretKey))
                      (next nextLeft.value.1)).IsQueryBoundP
                        (fun query => query matches Sum.inr _) (bound - 1) := by
                  simpa [IsOuterHash] using hbound.2 nextLeft.value.1
                exact ih nextLeft.value.1 nextCandidates canonical nextRight.context
                  nextLeft.remaining nextRight.remaining nextLeft.value.2 nextRight.value.2
                  (bound - 1) htail hcanonicalRun.context_le hcanonicalRun.cache_eq
                  hcanonicalRun.revealed_eq hcanonicalRun.values_le
                  hcanonicalRun.left_published hcanonicalRun.right_materialized
                  (canonicalizeMaterializedValues_canonical table nextLeft.context
                    hclean.context_le.view.leftConsistent)
                  (by omega)
                  ((remaining_le_fuel_of_done_runDirectResolvedDetailedFromTable
                    ((probingHashQueryAfterPlan parameter input plan).run leftCache)
                    left leftFuel table nextLeft (by
                      rw [← map_erase_runDirectResolvedWitnessFromTable
                        ((probingHashQueryAfterPlan parameter input plan).run leftCache)
                        left leftFuel table, support_map]
                      exact ⟨.done nextLeft, hleftSupport, rfl⟩)).trans hleftUpper)
                  (by omega)
              · intro leftRun nextRight _hrightSupport hdoomed
                have hnotPrivate := not_privateStructuralHit_of_directDeferredContext
                  nextRight.context hdoomed.2
                have hnotCompletable : ¬DeferredCompletable table nextRight.context :=
                  hdoomed.1.2.2.2
                simpa [classifyDirectDetailedObserve, hnotPrivate, hnotCompletable] using
                  (relTriple_any_ordinaryFailure_boundaryWitnessCovers leftRun)
      | inr message =>
          rw [simulateQ_expandedAdversaryImpl_query_bind_inr] at hbound
          simp only
          let nextLeftObserve : DeferredContext → Nat →
              (Option Signature × SplitHashCache) → List Probe →
                ProbComp BoundaryWitnessPlanOutput :=
            fun nextContext remaining value nextCandidates =>
              directDetailedBoundaryNormalizedBoundaryWitnessPlanObserve parameter root ftsSecret
                (next value.1) leftObserve nextCandidates nextContext remaining table value.2
          let nextRightObserve : DeferredContext → Nat →
              (Option Signature × SplitHashCache) → ProbComp DirectBoundaryOutcome :=
            fun nextContext remaining value =>
              rootAwareMaterializedDetailedBoundaryObserve parameter root ftsSecret
                (next value.1) rightObserve nextContext remaining table value.2
          apply relTriple_finishBoundaryWitnessPlan_detailed_of_materializedStable table
          · exact (witnessMaterializedStableCouples_maskedSign table parameter root ftsSecret
                message) left right leftFuel rightFuel leftCache rightCache hcontext (by omega)
                hcache hrevealed hvalues hpublished hrightMaterialized
          · intro nextLeft nextRight hleftSupport hrightSupport hclean
            have hcanonicalRun := hclean.canonicalize_left
            let canonical := canonicalizeMaterializedValues table nextLeft.context
            have hleftCompletable := hcanonicalRun.context_le.leftCompletable
            have hleftNotPrivate :=
              not_privateStructuralHit_of_deferredCompletable hleftCompletable
            have hrightNotPrivate :=
              not_privateStructuralHit_of_deferredCompletable
                hcanonicalRun.context_le.rightCompletable
            simp only [canonicalizeDirectBoundaryWitnessPlanObserve, hleftNotPrivate,
              ↓reduceDIte, hclean.left_published, ↓reduceIte,
              classifyDirectBoundaryWitnessPlanObserve, hleftCompletable,
              classifyDirectDetailedObserve, hrightNotPrivate,
              hcanonicalRun.context_le.rightCompletable]
            rw [← hclean.value_eq]
            have hleftPreserved : leftFuel ≤ nextLeft.remaining := by
              have := fuel_le_remaining_add_of_done_runDirectResolvedWitnessFromTable
                ((maskedSign parameter root ftsSecret message).run leftCache)
                left leftFuel table nextLeft 0
                (maskedSign_probeFree parameter root ftsSecret message leftCache)
                hleftSupport
              omega
            have hrightPreserved : rightFuel ≤ nextRight.remaining := by
              have := fuel_le_remaining_add_of_done_runDirectResolvedDetailedFromTable
                ((maskedSign parameter root ftsSecret message).run rightCache)
                right rightFuel table nextRight 0
                (maskedSign_probeFree parameter root ftsSecret message rightCache)
                hrightSupport
              omega
            have hdetailed : DirectDetailedResult.done nextLeft ∈ support
                (runDirectResolvedDetailedFromTable left leftFuel table
                  ((maskedSign parameter root ftsSecret message).run leftCache)) := by
              rw [← map_erase_runDirectResolvedWitnessFromTable
                ((maskedSign parameter root ftsSecret message).run leftCache)
                left leftFuel table, support_map]
              exact ⟨.done nextLeft, hleftSupport, rfl⟩
            have hdirect := mem_support_runDirectResolvedFromTable_of_done_detailed
              ((maskedSign parameter root ftsSecret message).run leftCache)
              left leftFuel table nextLeft hdetailed
            have hraw := raw_done_of_mem_runDirectResolvedFromTable
              ((maskedSign parameter root ftsSecret message).run leftCache)
              left leftFuel table nextLeft hdirect
            have houtput : nextLeft.value.1 ∈ support
                (scheme.sign
                  (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
                    SecretKey) message) :=
              maskedSign_done_output_mem_support parameter root table ftsSecret message
                left.state nextLeft.context.state leftCache nextLeft.value.2 leftFuel
                nextLeft.remaining nextLeft.value.1 hclean.context_le.view.leftStarts (by
                  simpa only [SigningSpec, maskedExpandedAdversaryImpl, maskedSigningImpl]
                    using hraw)
            have htail := isQueryBoundP_of_bind hbound nextLeft.value.1 houtput
            exact ih nextLeft.value.1 candidates canonical nextRight.context
              nextLeft.remaining nextRight.remaining nextLeft.value.2 nextRight.value.2 bound
              (htail.mono (by omega)) hcanonicalRun.context_le hcanonicalRun.cache_eq
              hcanonicalRun.revealed_eq hcanonicalRun.values_le
              hcanonicalRun.left_published hcanonicalRun.right_materialized
              (canonicalizeMaterializedValues_canonical table nextLeft.context
                hclean.context_le.view.leftConsistent)
              (by omega)
              ((remaining_le_fuel_of_done_runDirectResolvedDetailedFromTable
                ((maskedSign parameter root ftsSecret message).run leftCache)
                left leftFuel table nextLeft hdetailed).trans hleftUpper)
              (by omega)
          · intro leftRun nextRight _hrightSupport hdoomed
            have hnotPrivate := not_privateStructuralHit_of_directDeferredContext
              nextRight.context hdoomed.2
            have hnotCompletable : ¬DeferredCompletable table nextRight.context :=
              hdoomed.1.2.2.2
            simpa [classifyDirectDetailedObserve, hnotPrivate, hnotCompletable] using
              (relTriple_any_ordinaryFailure_boundaryWitnessCovers leftRun)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem relTriple_granularBoundaryWitnessPlan_rootAwareMaterializedDetailedRetainedRest
    (adversary : Adversary) (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (left right : DeferredContext) (leftFuel rightFuel q : Nat)
    (leftCache rightCache : SplitHashCache)
    (hbound :
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hcontext : FinalizationContextLE table left right)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state)
    (hcanonical : CanonicalMaterializedValues table left)
    (hqLeft : q ≤ leftFuel) (hleftUpper : leftFuel ≤ q)
    (hrightLower : q + q ≤ rightFuel) :
    RelTriple
      (granularDetailedRetainedRestNormalizedBoundaryWitnessPlanObserve adversary parameter table
        ftsSecret left leftFuel (root, leftCache) [])
      (rootAwareMaterializedDetailedRetainedRestObserve adversary parameter table ftsSecret
        right rightFuel (root, rightCache))
      BoundaryWitnessCovers := by
  unfold granularDetailedRetainedRestNormalizedBoundaryWitnessPlanObserve
    rootAwareMaterializedDetailedRetainedRestObserve
  apply relTriple_normalizedBoundaryWitness_rootAwareMaterializedDetailed parameter root ftsSecret
    (retainedGameRestComputation adversary ⟨root, parameter⟩)
      (retainedResolvedFinalizationBoundaryWitnessPlanObserve table root)
      (retainedResolvedFinalizationDetailedObserve table root) [] left right leftFuel rightFuel
      table leftCache rightCache q q hbound hcontext hcache hrevealed hvalues hpublished
      hrightMaterialized hcanonical hqLeft hleftUpper hrightLower
  intro value nextLeft nextRight nextLeftFuel nextRightFuel nextLeftCache nextRightCache
    nextCandidates hnextContext _hnextFuel _hnextCache _hnextRevealed _hnextValues
    _hnextPublished _hnextMaterialized _hnextCanonical
  simpa only using
    (relTriple_retainedFinalizationBoundaryWitnessPlan_detailed table root value nextLeft nextRight
      nextLeftFuel nextRightFuel nextLeftCache nextRightCache nextCandidates hnextContext)

attribute [local irreducible] maskedPublishedTreeRoot

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem relTriple_granularAllCanonicalBoundaryWitnessPlan_rootAwareMaterializedBoundary
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q) :
    RelTriple
      (granularAllCanonicalBoundaryWitnessPlan adversary parameter table ftsSecret q)
      (rootAwareMaterializedBoundaryDetailedRetainedOutcome adversary parameter table ftsSecret q)
      BoundaryWitnessCovers := by
  let initial : DeferredContext := emptyWitnessDeferredContext
  let materializedInitial : DeferredContext :=
    directDeferredContext
      (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
  have hcontext : FinalizationContextLE table initial materializedInitial :=
    finalizationContextLE_empty table
  have hstep := (witnessMaterializedStableCouples_maskedPublishedTreeRoot table)
    initial materializedInitial q (2 * q) emptySplitHashCache emptySplitHashCache hcontext
      (by omega) rfl rfl (fun _ _ hvalue => hvalue) publishedValues_empty rfl
  unfold granularAllCanonicalBoundaryWitnessPlan
    rootAwareMaterializedBoundaryDetailedRetainedOutcome runDirectBoundaryWitnessPlanObserve
    runDirectDetailedObserve
  apply relTriple_finishBoundaryWitnessPlan_detailed_of_materializedStable table
  · simpa [initial, materializedInitial] using hstep
  · intro leftResult rightResult hleftSupport hrightSupport hclean
    have hcanonicalRun := hclean.canonicalize_left
    let canonical := canonicalizeMaterializedValues table leftResult.context
    have hleftCompletable := hcanonicalRun.context_le.leftCompletable
    have hleftNotPrivate :=
      not_privateStructuralHit_of_deferredCompletable hleftCompletable
    have hrightNotPrivate :=
      not_privateStructuralHit_of_deferredCompletable
        hcanonicalRun.context_le.rightCompletable
    simp only [canonicalizeDirectBoundaryWitnessPlanObserve, hleftNotPrivate, ↓reduceDIte,
      hclean.left_published, ↓reduceIte, classifyDirectBoundaryWitnessPlanObserve,
      hleftCompletable, classifyDirectDetailedObserve, hrightNotPrivate,
      hcanonicalRun.context_le.rightCompletable]
    have hleftFuelPreserved : q ≤ leftResult.remaining := by
      have := fuel_le_remaining_add_of_done_runDirectResolvedWitnessFromTable
        (maskedPublishedTreeRoot.run emptySplitHashCache) initial q table leftResult 0
        (maskedPublishedTreeRoot_probeFree emptySplitHashCache) (by
          simpa [initial] using hleftSupport)
      omega
    have hrightFuelPreserved : 2 * q ≤ rightResult.remaining := by
      have := fuel_le_remaining_add_of_done_runDirectResolvedDetailedFromTable
        (maskedPublishedTreeRoot.run emptySplitHashCache) materializedInitial (2 * q) table
        rightResult 0 (maskedPublishedTreeRoot_probeFree emptySplitHashCache) (by
          simpa [materializedInitial] using hrightSupport)
      omega
    have hleftRemainingUpper : leftResult.remaining ≤ q :=
      remaining_le_fuel_of_done_runDirectResolvedDetailedFromTable
        (maskedPublishedTreeRoot.run emptySplitHashCache) initial q table leftResult (by
          rw [← map_erase_runDirectResolvedWitnessFromTable
            (maskedPublishedTreeRoot.run emptySplitHashCache) initial q table, support_map]
          exact ⟨.done leftResult, by simpa [initial] using hleftSupport, rfl⟩)
    change RelTriple
      (granularDetailedRetainedRestNormalizedBoundaryWitnessPlanObserve adversary parameter table
        ftsSecret canonical leftResult.remaining
          (leftResult.value.1, leftResult.value.2) [])
      (rootAwareMaterializedDetailedRetainedRestObserve adversary parameter table ftsSecret
        rightResult.context rightResult.remaining
          (rightResult.value.1, rightResult.value.2))
      BoundaryWitnessCovers
    rw [← hclean.value_eq]
    exact relTriple_granularBoundaryWitnessPlan_rootAwareMaterializedDetailedRetainedRest
        adversary parameter leftResult.value.1 table ftsSecret canonical rightResult.context
        leftResult.remaining rightResult.remaining q leftResult.value.2 rightResult.value.2
        (hbound leftResult.value.1) hcanonicalRun.context_le hcanonicalRun.cache_eq
        hcanonicalRun.revealed_eq hcanonicalRun.values_le hcanonicalRun.left_published
        hcanonicalRun.right_materialized
        (canonicalizeMaterializedValues_canonical table leftResult.context
          hclean.context_le.view.leftConsistent)
        hleftFuelPreserved hleftRemainingUpper (by omega)
  · intro leftRun rightResult _hrightSupport hdoomed
    have hnotPrivate := not_privateStructuralHit_of_directDeferredContext
      rightResult.context hdoomed.2
    have hnotCompletable : ¬DeferredCompletable table rightResult.context :=
      hdoomed.1.2.2.2
    simpa [classifyDirectDetailedObserve, hnotPrivate, hnotCompletable] using
      (relTriple_any_ordinaryFailure_boundaryWitnessCovers leftRun)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_sampledGranularAllCanonicalBoundaryWitnessPlan_rootAwareMaterializedBoundary
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q) :
    RelTriple
      (sampledGranularAllCanonicalBoundaryWitnessPlan adversary parameter ftsSecret q)
      (sampledRootAwareMaterializedBoundaryDetailedRetainedOutcome adversary parameter
        ftsSecret q)
      BoundaryWitnessCovers := by
  unfold sampledGranularAllCanonicalBoundaryWitnessPlan
    sampledRootAwareMaterializedBoundaryDetailedRetainedOutcome
  apply relTriple_bind (relTriple_refl sampleOtsHashTable)
  intro leftTable rightTable htable
  subst rightTable
  exact relTriple_granularAllCanonicalBoundaryWitnessPlan_rootAwareMaterializedBoundary
    adversary parameter leftTable ftsSecret q (hbound leftTable)

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem probEvent_sampledCanonicalBoundary_failed_le_witness_add_materializedOrdinary
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hbound : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q) :
    Pr[fun output => output.outcome.failed = true |
        sampledGranularAllCanonicalBoundaryWitnessPlan adversary parameter ftsSecret q] ≤
      Pr[fun output => output.witnessPlan.1.isSome = true |
          sampledGranularAllCanonicalBoundaryWitnessPlan adversary parameter ftsSecret q] +
        Pr[fun outcome => outcome.ordinary = true |
          sampledRootAwareMaterializedBoundaryDetailedRetainedOutcome adversary parameter
            ftsSecret q] := by
  let sourceRun :=
    sampledGranularAllCanonicalBoundaryWitnessPlan adversary parameter ftsSecret q
  let materializedRun :=
    sampledRootAwareMaterializedBoundaryDetailedRetainedOutcome adversary parameter ftsSecret q
  have hrel : RelTriple sourceRun materializedRun BoundaryWitnessCovers :=
    relTriple_sampledGranularAllCanonicalBoundaryWitnessPlan_rootAwareMaterializedBoundary
      adversary parameter ftsSecret q hbound
  change Pr[fun output => output.outcome.failed = true | sourceRun] ≤
    Pr[fun output => output.witnessPlan.1.isSome = true | sourceRun] +
      Pr[fun outcome => outcome.ordinary = true | materializedRun]
  calc
    _ ≤ Pr[fun output => output.witnessPlan.1.isSome = true ∨
          (output.outcome.failed = true ∧ output.witnessPlan.1.isSome ≠ true) | sourceRun] := by
      apply probEvent_mono
      intro output _houtput hfailed
      by_cases hwitness : output.witnessPlan.1.isSome = true
      · exact Or.inl hwitness
      · exact Or.inr ⟨hfailed, hwitness⟩
    _ ≤ Pr[fun output => output.witnessPlan.1.isSome = true | sourceRun] +
        Pr[fun output => output.outcome.failed = true ∧
          output.witnessPlan.1.isSome ≠ true | sourceRun] :=
      probEvent_or_le _ _ _
    _ ≤ _ := add_le_add le_rfl (by
      apply probEvent_le_of_relTriple hrel
      intro source materialized hrelation hsource
      rcases hrelation hsource.1 with hwitness | hordinary
      · exact (hsource.2 hwitness).elim
      · exact hordinary)

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
theorem probEvent_witness_sampledGranularAllCanonicalBoundaryWitnessPlan_eq
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[fun output => output.witnessPlan.1.isSome = true |
        sampledGranularAllCanonicalBoundaryWitnessPlan adversary parameter ftsSecret fuel] =
      Pr[fun output => output.1.isSome = true |
        sampledGranularAllCanonicalPrivateWitnessPlan adversary parameter ftsSecret fuel] := by
  calc
    _ = Pr[fun output => output.1.isSome = true |
        BoundaryWitnessPlanOutput.witnessPlan <$>
          sampledGranularAllCanonicalBoundaryWitnessPlan adversary parameter ftsSecret fuel] := by
      rw [probEvent_map]
      rfl
    _ = _ := OracleComp.probEvent_congr' (fun _ _ ↦ Iff.rfl)
      (evalDist_witnessPlan_sampledGranularAllCanonicalBoundaryWitnessPlan adversary parameter
        ftsSecret fuel)


end SphincsSecurity.Concrete.OtsProbeSimulation
