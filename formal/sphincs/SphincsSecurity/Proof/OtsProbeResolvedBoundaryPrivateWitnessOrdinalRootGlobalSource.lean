import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobal

/-!
# Context-annotated root source trace

The global clean split needs a residual event on the source run. Each planned candidate therefore
retains the deferred context in which it was created. Erasing those contexts recovers the existing
private witness plan exactly.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

structure PlannedProbeSnapshot where
  probe : Probe
  context : DeferredContext

abbrev PrivateWitnessSnapshotOutput :=
  Option PrivateHitWitness × List PlannedProbeSnapshot

@[simp] def PlannedProbeSnapshot.toProbe (snapshot : PlannedProbeSnapshot) : Probe :=
  snapshot.probe

def erasePrivateWitnessSnapshotOutput
    (output : PrivateWitnessSnapshotOutput) : PrivateWitnessPlanOutput :=
  (output.1, output.2.map PlannedProbeSnapshot.toProbe)

def appendPlannedSnapshot
    (snapshots : List PlannedProbeSnapshot) (candidate? : Option Probe)
    (context : DeferredContext) : List PlannedProbeSnapshot :=
  match candidate? with
  | none => snapshots
  | some candidate => snapshots ++ [⟨candidate, context⟩]

@[simp] theorem map_toProbe_appendPlannedSnapshot
    (snapshots : List PlannedProbeSnapshot) (candidate? : Option Probe)
    (context : DeferredContext) :
    (appendPlannedSnapshot snapshots candidate? context).map PlannedProbeSnapshot.toProbe =
      appendPlannedCandidate (snapshots.map PlannedProbeSnapshot.toProbe) candidate? := by
  cases candidate? <;> simp [appendPlannedSnapshot, appendPlannedCandidate]

noncomputable def finishDirectWitnessSnapshotObserve
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp PrivateWitnessSnapshotOutput)
    (snapshots : List PlannedProbeSnapshot) : DirectWitnessResult α →
      ProbComp PrivateWitnessSnapshotOutput
  | .stoppedFuel => pure (none, snapshots)
  | .stoppedOrdinary => pure (none, snapshots)
  | .stoppedPrivate witness => pure (some witness, snapshots)
  | .done result => observe result.context result.remaining result.value snapshots

noncomputable def classifyDirectWitnessSnapshotObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp PrivateWitnessSnapshotOutput)
    (context : DeferredContext) (fuel : Nat) (value : α)
    (snapshots : List PlannedProbeSnapshot) :
    ProbComp PrivateWitnessSnapshotOutput := by
  classical
  exact if hhit : PrivateStructuralHit context then
      pure (some (privateHitWitnessOf context hhit), snapshots)
    else if DeferredCompletable table context then
      observe context fuel value snapshots
    else
      pure (none, snapshots)

noncomputable def canonicalizeDirectWitnessSnapshotObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp PrivateWitnessSnapshotOutput)
    (context : DeferredContext) (fuel : Nat) (value : α)
    (snapshots : List PlannedProbeSnapshot) :
    ProbComp PrivateWitnessSnapshotOutput := by
  classical
  let canonical := canonicalizeMaterializedValues table context
  exact if hhit : PrivateStructuralHit canonical then
      pure (some (privateHitWitnessOf canonical hhit), snapshots)
    else if PublishedValues context.state then
      classifyDirectWitnessSnapshotObserve table observe canonical fuel value snapshots
    else
      pure (none, snapshots)

noncomputable def runDirectWitnessSnapshotObserve
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp PrivateWitnessSnapshotOutput)
    (snapshots : List PlannedProbeSnapshot) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    ProbComp PrivateWitnessSnapshotOutput :=
  runDirectResolvedWitnessFromTable context fuel table computation >>=
    finishDirectWitnessSnapshotObserve observe snapshots

theorem map_erase_finishDirectWitnessSnapshotObserve
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp PrivateWitnessSnapshotOutput)
    (planObserve : DeferredContext → Nat → α → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (snapshots : List PlannedProbeSnapshot) (result : DirectWitnessResult α)
    (hproject : ∀ context fuel value snapshots,
      erasePrivateWitnessSnapshotOutput <$> observe context fuel value snapshots =
        planObserve context fuel value
          (snapshots.map PlannedProbeSnapshot.toProbe)) :
    erasePrivateWitnessSnapshotOutput <$>
        finishDirectWitnessSnapshotObserve observe snapshots result =
      finishDirectWitnessPlanObserve planObserve
        (snapshots.map PlannedProbeSnapshot.toProbe) result := by
  cases result with
  | stoppedFuel => simp [finishDirectWitnessSnapshotObserve,
      finishDirectWitnessPlanObserve, erasePrivateWitnessSnapshotOutput]
  | stoppedOrdinary => simp [finishDirectWitnessSnapshotObserve,
      finishDirectWitnessPlanObserve, erasePrivateWitnessSnapshotOutput]
  | stoppedPrivate witness => simp [finishDirectWitnessSnapshotObserve,
      finishDirectWitnessPlanObserve, erasePrivateWitnessSnapshotOutput]
  | done result => exact hproject result.context result.remaining result.value snapshots

theorem map_erase_classifyDirectWitnessSnapshotObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp PrivateWitnessSnapshotOutput)
    (planObserve : DeferredContext → Nat → α → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (context : DeferredContext) (fuel : Nat) (value : α)
    (snapshots : List PlannedProbeSnapshot)
    (hproject : ∀ nextContext remaining nextValue nextSnapshots,
      erasePrivateWitnessSnapshotOutput <$>
          observe nextContext remaining nextValue nextSnapshots =
        planObserve nextContext remaining nextValue
          (nextSnapshots.map PlannedProbeSnapshot.toProbe)) :
    erasePrivateWitnessSnapshotOutput <$>
        classifyDirectWitnessSnapshotObserve table observe context fuel value snapshots =
      classifyDirectWitnessPlanObserve table planObserve context fuel value
        (snapshots.map PlannedProbeSnapshot.toProbe) := by
  classical
  unfold classifyDirectWitnessSnapshotObserve classifyDirectWitnessPlanObserve
  by_cases hhit : PrivateStructuralHit context
  · simp [hhit, erasePrivateWitnessSnapshotOutput]
  · simp only [hhit, ↓reduceDIte]
    by_cases hcompletable : DeferredCompletable table context
    · simp only [hcompletable, ↓reduceIte]
      exact hproject context fuel value snapshots
    · simp [hcompletable, erasePrivateWitnessSnapshotOutput]

theorem map_erase_canonicalizeDirectWitnessSnapshotObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp PrivateWitnessSnapshotOutput)
    (planObserve : DeferredContext → Nat → α → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (context : DeferredContext) (fuel : Nat) (value : α)
    (snapshots : List PlannedProbeSnapshot)
    (hproject : ∀ nextContext remaining nextValue nextSnapshots,
      erasePrivateWitnessSnapshotOutput <$>
          observe nextContext remaining nextValue nextSnapshots =
        planObserve nextContext remaining nextValue
          (nextSnapshots.map PlannedProbeSnapshot.toProbe)) :
    erasePrivateWitnessSnapshotOutput <$>
        canonicalizeDirectWitnessSnapshotObserve table observe context fuel value snapshots =
      canonicalizeDirectWitnessPlanObserve table planObserve context fuel value
        (snapshots.map PlannedProbeSnapshot.toProbe) := by
  classical
  unfold canonicalizeDirectWitnessSnapshotObserve canonicalizeDirectWitnessPlanObserve
  let canonical := canonicalizeMaterializedValues table context
  by_cases hhit : PrivateStructuralHit canonical
  · simp [canonical, hhit, erasePrivateWitnessSnapshotOutput]
  · simp only [canonical, hhit, ↓reduceDIte]
    by_cases hpublished : PublishedValues context.state
    · simp only [hpublished, ↓reduceIte]
      exact map_erase_classifyDirectWitnessSnapshotObserve table observe planObserve canonical
        fuel value snapshots hproject
    · simp [hpublished, erasePrivateWitnessSnapshotOutput]

theorem map_erase_runDirectWitnessSnapshotObserve
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp PrivateWitnessSnapshotOutput)
    (planObserve : DeferredContext → Nat → α → List Probe →
      ProbComp PrivateWitnessPlanOutput)
    (snapshots : List PlannedProbeSnapshot) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hproject : ∀ nextContext remaining value nextSnapshots,
      erasePrivateWitnessSnapshotOutput <$>
          observe nextContext remaining value nextSnapshots =
        planObserve nextContext remaining value
          (nextSnapshots.map PlannedProbeSnapshot.toProbe)) :
    erasePrivateWitnessSnapshotOutput <$>
        runDirectWitnessSnapshotObserve observe snapshots context fuel table computation =
      runDirectWitnessPlanObserve planObserve
        (snapshots.map PlannedProbeSnapshot.toProbe) context fuel table computation := by
  unfold runDirectWitnessSnapshotObserve runDirectWitnessPlanObserve
  rw [map_bind]
  apply bind_congr
  intro result
  exact map_erase_finishDirectWitnessSnapshotObserve observe planObserve snapshots result hproject

noncomputable def directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) →
      List PlannedProbeSnapshot → ProbComp PrivateWitnessSnapshotOutput)
    (snapshots : List PlannedProbeSnapshot) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ProbComp PrivateWitnessSnapshotOutput := by
  classical
  exact OracleComp.construct
    (C := fun _ : OracleComp (OracleWorld + SigningSpec) α =>
      (DeferredContext → Nat → (α × SplitHashCache) →
        List PlannedProbeSnapshot → ProbComp PrivateWitnessSnapshotOutput) →
      List PlannedProbeSnapshot → DeferredContext → Nat →
        (OtsSecretIndex → HashOutput) → SplitHashCache →
          ProbComp PrivateWitnessSnapshotOutput)
    (fun value observe snapshots context fuel _table cache =>
      observe context fuel (value, cache) snapshots)
    (fun query _next recursivelyRun observe snapshots context fuel table cache =>
      match query with
      | .inl (.inl n) =>
          runDirectWitnessSnapshotObserve
            (canonicalizeDirectWitnessSnapshotObserve table
              (fun nextContext remaining value nextSnapshots =>
                recursivelyRun value.1 observe nextSnapshots nextContext remaining table
                  value.2))
            snapshots context fuel table ((splitUniformImpl n).run cache)
      | .inl (.inr input) =>
          let plan := purePlanProbingHashQuery parameter input context.state
          let nextSnapshots := appendPlannedSnapshot snapshots
            (rootAwarePlannedCandidate? parameter input context.state) context
          runDirectWitnessSnapshotObserve
            (canonicalizeDirectWitnessSnapshotObserve table
              (fun nextContext remaining value laterSnapshots =>
                recursivelyRun value.1 observe laterSnapshots nextContext remaining table
                  value.2))
            nextSnapshots context fuel table
              ((probingHashQueryAfterPlan parameter input plan).run cache)
      | .inr message =>
          runDirectWitnessSnapshotObserve
            (canonicalizeDirectWitnessSnapshotObserve table
              (fun nextContext remaining value nextSnapshots =>
                recursivelyRun value.1 observe nextSnapshots nextContext remaining table
                  value.2))
            snapshots context fuel table
              ((maskedSign parameter root ftsSecret message).run cache))
    computation observe snapshots context fuel table cache

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem map_erase_directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) →
      List PlannedProbeSnapshot → ProbComp PrivateWitnessSnapshotOutput)
    (planObserve : DeferredContext → Nat → (α × SplitHashCache) →
      List Probe → ProbComp PrivateWitnessPlanOutput)
    (snapshots : List PlannedProbeSnapshot) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hproject : ∀ nextContext remaining value nextSnapshots,
      erasePrivateWitnessSnapshotOutput <$>
          observe nextContext remaining value nextSnapshots =
        planObserve nextContext remaining value
          (nextSnapshots.map PlannedProbeSnapshot.toProbe)) :
    erasePrivateWitnessSnapshotOutput <$>
        directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve parameter root ftsSecret
          computation observe snapshots context fuel table cache =
      directDetailedBoundaryNormalizedPrivateWitnessPlanObserve parameter root ftsSecret
        computation planObserve (snapshots.map PlannedProbeSnapshot.toProbe) context fuel table
          cache := by
  induction computation using OracleComp.inductionOn generalizing snapshots context fuel cache with
  | pure value =>
      rw [directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve,
        OracleComp.construct_pure,
        directDetailedBoundaryNormalizedPrivateWitnessPlanObserve, OracleComp.construct_pure]
      exact hproject context fuel (value, cache) snapshots
  | query_bind query next ih =>
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              rw [directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve,
                OracleComp.construct_query_bind]
              rw [directDetailedBoundaryNormalizedPrivateWitnessPlanObserve,
                OracleComp.construct_query_bind]
              apply map_erase_runDirectWitnessSnapshotObserve
              intro nextContext remaining value nextSnapshots
              apply map_erase_canonicalizeDirectWitnessSnapshotObserve
              intro finalContext finalRemaining finalValue finalSnapshots
              exact ih finalValue.1 finalSnapshots finalContext finalRemaining finalValue.2
          | inr input =>
              rw [directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve,
                OracleComp.construct_query_bind]
              rw [directDetailedBoundaryNormalizedPrivateWitnessPlanObserve,
                OracleComp.construct_query_bind]
              let plan := purePlanProbingHashQuery parameter input context.state
              let nextSnapshots := appendPlannedSnapshot snapshots
                (rootAwarePlannedCandidate? parameter input context.state) context
              dsimp only
              rw [← map_toProbe_appendPlannedSnapshot]
              apply map_erase_runDirectWitnessSnapshotObserve
              intro nextContext remaining value laterSnapshots
              apply map_erase_canonicalizeDirectWitnessSnapshotObserve
              intro finalContext finalRemaining finalValue finalSnapshots
              exact ih finalValue.1 finalSnapshots finalContext finalRemaining finalValue.2
      | inr message =>
          rw [directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve,
            OracleComp.construct_query_bind]
          rw [directDetailedBoundaryNormalizedPrivateWitnessPlanObserve,
            OracleComp.construct_query_bind]
          apply map_erase_runDirectWitnessSnapshotObserve
          intro nextContext remaining value nextSnapshots
          apply map_erase_canonicalizeDirectWitnessSnapshotObserve
          intro finalContext finalRemaining finalValue finalSnapshots
          exact ih finalValue.1 finalSnapshots finalContext finalRemaining finalValue.2

noncomputable def retainedResolvedFinalizationPrivateWitnessSnapshotObserve
    (_table : OtsSecretIndex → HashOutput) (_root : Digest)
    (context : DeferredContext) (_fuel : Nat)
    (_value : RetainedRestResult × SplitHashCache)
    (snapshots : List PlannedProbeSnapshot) :
    ProbComp PrivateWitnessSnapshotOutput := by
  classical
  exact if hhit : PrivateStructuralHit context then
    pure (some (privateHitWitnessOf context hhit), snapshots)
  else
    pure (none, snapshots)

theorem map_erase_retainedResolvedFinalizationPrivateWitnessSnapshotObserve
    (table : OtsSecretIndex → HashOutput) (root : Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : RetainedRestResult × SplitHashCache)
    (snapshots : List PlannedProbeSnapshot) :
    erasePrivateWitnessSnapshotOutput <$>
        retainedResolvedFinalizationPrivateWitnessSnapshotObserve table root context fuel value
          snapshots =
      retainedResolvedFinalizationPrivateWitnessPlanObserve table root context fuel value
        (snapshots.map PlannedProbeSnapshot.toProbe) := by
  classical
  unfold retainedResolvedFinalizationPrivateWitnessSnapshotObserve
    retainedResolvedFinalizationPrivateWitnessPlanObserve
  by_cases hhit : PrivateStructuralHit context <;>
    simp [hhit, erasePrivateWitnessSnapshotOutput]

noncomputable def granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (snapshots : List PlannedProbeSnapshot) :
    ProbComp PrivateWitnessSnapshotOutput :=
  directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve parameter value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
    (retainedResolvedFinalizationPrivateWitnessSnapshotObserve table value.1)
    snapshots context fuel table value.2

theorem map_erase_granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (snapshots : List PlannedProbeSnapshot) :
    erasePrivateWitnessSnapshotOutput <$>
        granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve adversary parameter
          table ftsSecret context fuel value snapshots =
      granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve adversary parameter table
        ftsSecret context fuel value (snapshots.map PlannedProbeSnapshot.toProbe) := by
  unfold granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve
    granularDetailedRetainedRestNormalizedPrivateWitnessPlanObserve
  apply map_erase_directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve
  intro nextContext remaining nextValue nextSnapshots
  exact map_erase_retainedResolvedFinalizationPrivateWitnessSnapshotObserve table value.1
    nextContext remaining nextValue nextSnapshots

noncomputable def granularAllDirectBoundaryNormalizedPrivateWitnessSnapshot
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp PrivateWitnessSnapshotOutput :=
  runDirectWitnessSnapshotObserve
    (granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve adversary parameter table
      ftsSecret)
    []
    { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
      values := emptyDeferredStructuralValues }
    fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)

theorem map_erase_granularAllDirectBoundaryNormalizedPrivateWitnessSnapshot
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    erasePrivateWitnessSnapshotOutput <$>
        granularAllDirectBoundaryNormalizedPrivateWitnessSnapshot adversary parameter table
          ftsSecret fuel =
      granularAllDirectBoundaryNormalizedPrivateWitnessPlan adversary parameter table ftsSecret
        fuel := by
  unfold granularAllDirectBoundaryNormalizedPrivateWitnessSnapshot
    granularAllDirectBoundaryNormalizedPrivateWitnessPlan
  apply map_erase_runDirectWitnessSnapshotObserve
  intro nextContext remaining value nextSnapshots
  exact map_erase_granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve adversary
    parameter table ftsSecret nextContext remaining value nextSnapshots

noncomputable def sampledGranularAllDirectBoundaryNormalizedPrivateWitnessSnapshot
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp PrivateWitnessSnapshotOutput := do
  let table ← sampleOtsHashTable
  granularAllDirectBoundaryNormalizedPrivateWitnessSnapshot adversary parameter table ftsSecret
    fuel

theorem map_erase_sampledGranularAllDirectBoundaryNormalizedPrivateWitnessSnapshot
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    erasePrivateWitnessSnapshotOutput <$>
        sampledGranularAllDirectBoundaryNormalizedPrivateWitnessSnapshot adversary parameter
          ftsSecret fuel =
      sampledGranularAllDirectBoundaryNormalizedPrivateWitnessPlan adversary parameter ftsSecret
        fuel := by
  unfold sampledGranularAllDirectBoundaryNormalizedPrivateWitnessSnapshot
    sampledGranularAllDirectBoundaryNormalizedPrivateWitnessPlan
  rw [map_bind]
  apply bind_congr
  intro table
  exact map_erase_granularAllDirectBoundaryNormalizedPrivateWitnessSnapshot adversary parameter
    table ftsSecret fuel

end SphincsSecurity.Concrete.OtsProbeSimulation
