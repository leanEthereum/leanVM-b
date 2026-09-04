import SphincsSecurity.Proof.OtsProbeJointSnapshotProjection

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

set_option linter.constructorNameAsVariable false

attribute [local simp] erasePrivateWitnessSnapshotOutput

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem map_erase_finishDirectBoundaryWitnessSnapshotObserve
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp BoundaryWitnessSnapshotOutput)
    (planObserve : DeferredContext → Nat → α → List Probe →
      ProbComp BoundaryWitnessPlanOutput)
    (snapshots : List PlannedProbeSnapshot) (result : DirectWitnessResult α)
    (hproject : ∀ context fuel value snapshots,
      eraseBoundaryWitnessSnapshotOutput <$> observe context fuel value snapshots =
        planObserve context fuel value
          (snapshots.map PlannedProbeSnapshot.toProbe)) :
    eraseBoundaryWitnessSnapshotOutput <$>
        finishDirectBoundaryWitnessSnapshotObserve observe snapshots result =
      finishDirectBoundaryWitnessPlanObserve planObserve
        (snapshots.map PlannedProbeSnapshot.toProbe) result := by
  cases result with
  | stoppedFuel => simp [finishDirectBoundaryWitnessSnapshotObserve,
      finishDirectBoundaryWitnessPlanObserve, eraseBoundaryWitnessSnapshotOutput]
  | stoppedOrdinary => simp [finishDirectBoundaryWitnessSnapshotObserve,
      finishDirectBoundaryWitnessPlanObserve, eraseBoundaryWitnessSnapshotOutput]
  | stoppedPrivate witness => simp [finishDirectBoundaryWitnessSnapshotObserve,
      finishDirectBoundaryWitnessPlanObserve, eraseBoundaryWitnessSnapshotOutput]
  | done result => exact hproject result.context result.remaining result.value snapshots

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem map_erase_classifyDirectBoundaryWitnessSnapshotObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp BoundaryWitnessSnapshotOutput)
    (planObserve : DeferredContext → Nat → α → List Probe →
      ProbComp BoundaryWitnessPlanOutput)
    (context : DeferredContext) (fuel : Nat) (value : α)
    (snapshots : List PlannedProbeSnapshot)
    (hproject : ∀ nextContext remaining nextValue nextSnapshots,
      eraseBoundaryWitnessSnapshotOutput <$>
          observe nextContext remaining nextValue nextSnapshots =
        planObserve nextContext remaining nextValue
          (nextSnapshots.map PlannedProbeSnapshot.toProbe)) :
    eraseBoundaryWitnessSnapshotOutput <$>
        classifyDirectBoundaryWitnessSnapshotObserve table observe context fuel value snapshots =
      classifyDirectBoundaryWitnessPlanObserve table planObserve context fuel value
        (snapshots.map PlannedProbeSnapshot.toProbe) := by
  classical
  unfold classifyDirectBoundaryWitnessSnapshotObserve classifyDirectBoundaryWitnessPlanObserve
  by_cases hhit : PrivateStructuralHit context
  · simp [hhit, eraseBoundaryWitnessSnapshotOutput]
  · simp only [hhit, ↓reduceDIte]
    by_cases hcompletable : DeferredCompletable table context
    · simp only [hcompletable, ↓reduceIte]
      exact hproject context fuel value snapshots
    · simp [hcompletable, eraseBoundaryWitnessSnapshotOutput]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem map_erase_canonicalizeDirectBoundaryWitnessSnapshotObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp BoundaryWitnessSnapshotOutput)
    (planObserve : DeferredContext → Nat → α → List Probe →
      ProbComp BoundaryWitnessPlanOutput)
    (context : DeferredContext) (fuel : Nat) (value : α)
    (snapshots : List PlannedProbeSnapshot)
    (hproject : ∀ nextContext remaining nextValue nextSnapshots,
      eraseBoundaryWitnessSnapshotOutput <$>
          observe nextContext remaining nextValue nextSnapshots =
        planObserve nextContext remaining nextValue
          (nextSnapshots.map PlannedProbeSnapshot.toProbe)) :
    eraseBoundaryWitnessSnapshotOutput <$>
        canonicalizeDirectBoundaryWitnessSnapshotObserve table observe context fuel value snapshots =
      canonicalizeDirectBoundaryWitnessPlanObserve table planObserve context fuel value
        (snapshots.map PlannedProbeSnapshot.toProbe) := by
  classical
  unfold canonicalizeDirectBoundaryWitnessSnapshotObserve canonicalizeDirectBoundaryWitnessPlanObserve
  let canonical := canonicalizeMaterializedValues table context
  by_cases hhit : PrivateStructuralHit canonical
  · simp [canonical, hhit, eraseBoundaryWitnessSnapshotOutput]
  · simp only [canonical, hhit, ↓reduceDIte]
    by_cases hpublished : PublishedValues context.state
    · simp only [hpublished, ↓reduceIte]
      exact map_erase_classifyDirectBoundaryWitnessSnapshotObserve table observe planObserve canonical
        fuel value snapshots hproject
    · simp [hpublished, eraseBoundaryWitnessSnapshotOutput]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem map_erase_runDirectBoundaryWitnessSnapshotObserve
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp BoundaryWitnessSnapshotOutput)
    (planObserve : DeferredContext → Nat → α → List Probe →
      ProbComp BoundaryWitnessPlanOutput)
    (snapshots : List PlannedProbeSnapshot) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hproject : ∀ nextContext remaining value nextSnapshots,
      eraseBoundaryWitnessSnapshotOutput <$>
          observe nextContext remaining value nextSnapshots =
        planObserve nextContext remaining value
          (nextSnapshots.map PlannedProbeSnapshot.toProbe)) :
    eraseBoundaryWitnessSnapshotOutput <$>
        runDirectBoundaryWitnessSnapshotObserve observe snapshots context fuel table computation =
      runDirectBoundaryWitnessPlanObserve planObserve
        (snapshots.map PlannedProbeSnapshot.toProbe) context fuel table computation := by
  unfold runDirectBoundaryWitnessSnapshotObserve runDirectBoundaryWitnessPlanObserve
  rw [map_bind]
  apply bind_congr
  intro result
  exact map_erase_finishDirectBoundaryWitnessSnapshotObserve observe planObserve snapshots result hproject

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem map_erase_directDetailedBoundaryNormalizedBoundaryWitnessSnapshotObserve
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) →
      List PlannedProbeSnapshot → ProbComp BoundaryWitnessSnapshotOutput)
    (planObserve : DeferredContext → Nat → (α × SplitHashCache) →
      List Probe → ProbComp BoundaryWitnessPlanOutput)
    (snapshots : List PlannedProbeSnapshot) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hproject : ∀ nextContext remaining value nextSnapshots,
      eraseBoundaryWitnessSnapshotOutput <$>
          observe nextContext remaining value nextSnapshots =
        planObserve nextContext remaining value
          (nextSnapshots.map PlannedProbeSnapshot.toProbe)) :
    eraseBoundaryWitnessSnapshotOutput <$>
        directDetailedBoundaryNormalizedBoundaryWitnessSnapshotObserve parameter root ftsSecret
          computation observe snapshots context fuel table cache =
      directDetailedBoundaryNormalizedBoundaryWitnessPlanObserve parameter root ftsSecret
        computation planObserve (snapshots.map PlannedProbeSnapshot.toProbe) context fuel table
          cache := by
  induction computation using OracleComp.inductionOn generalizing snapshots context fuel cache with
  | pure value =>
      rw [directDetailedBoundaryNormalizedBoundaryWitnessSnapshotObserve,
        OracleComp.construct_pure,
        directDetailedBoundaryNormalizedBoundaryWitnessPlanObserve, OracleComp.construct_pure]
      exact hproject context fuel (value, cache) snapshots
  | query_bind query next ih =>
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              rw [directDetailedBoundaryNormalizedBoundaryWitnessSnapshotObserve,
                OracleComp.construct_query_bind]
              rw [directDetailedBoundaryNormalizedBoundaryWitnessPlanObserve,
                OracleComp.construct_query_bind]
              apply map_erase_runDirectBoundaryWitnessSnapshotObserve
              intro nextContext remaining value nextSnapshots
              apply map_erase_canonicalizeDirectBoundaryWitnessSnapshotObserve
              intro finalContext finalRemaining finalValue finalSnapshots
              exact ih finalValue.1 finalSnapshots finalContext finalRemaining finalValue.2
          | inr input =>
              rw [directDetailedBoundaryNormalizedBoundaryWitnessSnapshotObserve,
                OracleComp.construct_query_bind]
              rw [directDetailedBoundaryNormalizedBoundaryWitnessPlanObserve,
                OracleComp.construct_query_bind]
              let plan := purePlanProbingHashQuery parameter input context.state
              let nextSnapshots := appendPlannedSnapshot snapshots
                (rootAwarePlannedCandidate? parameter input context.state) context
              dsimp only
              rw [← map_toProbe_appendPlannedSnapshot]
              apply map_erase_runDirectBoundaryWitnessSnapshotObserve
              intro nextContext remaining value laterSnapshots
              apply map_erase_canonicalizeDirectBoundaryWitnessSnapshotObserve
              intro finalContext finalRemaining finalValue finalSnapshots
              exact ih finalValue.1 finalSnapshots finalContext finalRemaining finalValue.2
      | inr message =>
          rw [directDetailedBoundaryNormalizedBoundaryWitnessSnapshotObserve,
            OracleComp.construct_query_bind]
          rw [directDetailedBoundaryNormalizedBoundaryWitnessPlanObserve,
            OracleComp.construct_query_bind]
          apply map_erase_runDirectBoundaryWitnessSnapshotObserve
          intro nextContext remaining value nextSnapshots
          apply map_erase_canonicalizeDirectBoundaryWitnessSnapshotObserve
          intro finalContext finalRemaining finalValue finalSnapshots
          exact ih finalValue.1 finalSnapshots finalContext finalRemaining finalValue.2

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem map_erase_retainedResolvedFinalizationBoundaryWitnessSnapshotObserve
    (table : OtsSecretIndex → HashOutput) (root : Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : RetainedRestResult × SplitHashCache)
    (snapshots : List PlannedProbeSnapshot) :
    eraseBoundaryWitnessSnapshotOutput <$>
        retainedResolvedFinalizationBoundaryWitnessSnapshotObserve table root context fuel value
          snapshots =
      retainedResolvedFinalizationBoundaryWitnessPlanObserve table root context fuel value
        (snapshots.map PlannedProbeSnapshot.toProbe) := by
  classical
  unfold retainedResolvedFinalizationBoundaryWitnessSnapshotObserve
    retainedResolvedFinalizationBoundaryWitnessPlanObserve
  by_cases hhit : PrivateStructuralHit context <;>
    by_cases hcomplete : DeferredCompletable table context <;>
    simp [hhit, hcomplete, eraseBoundaryWitnessSnapshotOutput]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem map_erase_granularDetailedRetainedRestNormalizedBoundaryWitnessSnapshotObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (snapshots : List PlannedProbeSnapshot) :
    eraseBoundaryWitnessSnapshotOutput <$>
        granularDetailedRetainedRestNormalizedBoundaryWitnessSnapshotObserve adversary parameter
          table ftsSecret context fuel value snapshots =
      granularDetailedRetainedRestNormalizedBoundaryWitnessPlanObserve adversary parameter table
        ftsSecret context fuel value (snapshots.map PlannedProbeSnapshot.toProbe) := by
  unfold granularDetailedRetainedRestNormalizedBoundaryWitnessSnapshotObserve
    granularDetailedRetainedRestNormalizedBoundaryWitnessPlanObserve
  apply map_erase_directDetailedBoundaryNormalizedBoundaryWitnessSnapshotObserve
  intro nextContext remaining nextValue nextSnapshots
  exact map_erase_retainedResolvedFinalizationBoundaryWitnessSnapshotObserve table value.1
    nextContext remaining nextValue nextSnapshots

theorem map_erase_granularAllCanonicalBoundaryWitnessSnapshot
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    eraseBoundaryWitnessSnapshotOutput <$>
        granularAllCanonicalBoundaryWitnessSnapshot adversary parameter table ftsSecret fuel =
      granularAllCanonicalBoundaryWitnessPlan adversary parameter table ftsSecret fuel := by
  unfold granularAllCanonicalBoundaryWitnessSnapshot granularAllCanonicalBoundaryWitnessPlan
  apply map_erase_runDirectBoundaryWitnessSnapshotObserve
  intro context remaining value snapshots
  apply map_erase_canonicalizeDirectBoundaryWitnessSnapshotObserve
  intro nextContext nextRemaining nextValue nextSnapshots
  exact map_erase_granularDetailedRetainedRestNormalizedBoundaryWitnessSnapshotObserve adversary
    parameter table ftsSecret nextContext nextRemaining nextValue nextSnapshots

theorem map_erase_sampledGranularAllCanonicalBoundaryWitnessSnapshot
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    eraseBoundaryWitnessSnapshotOutput <$>
        sampledGranularAllCanonicalBoundaryWitnessSnapshot adversary parameter ftsSecret fuel =
      sampledGranularAllCanonicalBoundaryWitnessPlan adversary parameter ftsSecret fuel := by
  unfold sampledGranularAllCanonicalBoundaryWitnessSnapshot
    sampledGranularAllCanonicalBoundaryWitnessPlan
  rw [map_bind]
  apply bind_congr
  intro table
  exact map_erase_granularAllCanonicalBoundaryWitnessSnapshot adversary parameter table
    ftsSecret fuel

theorem evalDist_failed_sampledGranularAllCanonicalBoundaryWitnessSnapshot
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist ((fun output => output.outcome.failed) <$>
        sampledGranularAllCanonicalBoundaryWitnessSnapshot adversary parameter ftsSecret fuel) =
      evalDist (sampledGranularAllCanonicalBoundaryRetainedFinishIsNone adversary parameter
        ftsSecret fuel) := by
  have h := evalDist_failed_sampledGranularAllCanonicalBoundaryWitnessPlan adversary parameter
    ftsSecret fuel
  rw [← map_erase_sampledGranularAllCanonicalBoundaryWitnessSnapshot] at h
  simpa only [Functor.map_map, Function.comp_def, eraseBoundaryWitnessSnapshotOutput] using h

theorem probEvent_sampledActualRetained_verifyProbe_le_jointBoundaryFailed
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[fun result => WinningRetainedVerifyProbeWitness parameter
        (extendStartTable result.1) ftsSecret result.2 |
      sampledActualRetainedOtsHashTable adversary parameter ftsSecret] ≤
      Pr[fun output => output.outcome.failed = true |
        sampledGranularAllCanonicalBoundaryWitnessSnapshot adversary parameter ftsSecret fuel] := by
  have h := probEvent_sampledActualRetainedOtsHashTable_verifyProbe_le_canonicalDeferred
    adversary parameter ftsSecret fuel
  have heq := evalDist_failed_sampledGranularAllCanonicalBoundaryWitnessSnapshot adversary
    parameter ftsSecret fuel
  rw [evalDist_sampledCanonicalBoundary_eq_deferred] at heq
  rw [← OracleComp.probOutput_congr (show true = true from rfl) heq,
    ← probEvent_eq_eq_probOutput, probEvent_map] at h
  exact h

end SphincsSecurity.Concrete.OtsProbeSimulation
