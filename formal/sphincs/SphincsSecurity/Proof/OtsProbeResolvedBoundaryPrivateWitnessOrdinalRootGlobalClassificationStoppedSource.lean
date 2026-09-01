import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStopped

/-!
# Monotone stopped-source snapshots

The source experiment only appends planned snapshots. A snapshot selected when the comparison first
stops therefore remains an exact prefix entry after an arbitrary source continuation.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

def PrivateWitnessSnapshotExtends
    (snapshots : List PlannedProbeSnapshot) (output : PrivateWitnessSnapshotOutput) : Prop :=
  snapshots <+: output.2

theorem privateWitnessSnapshotExtends_of_mem_finishDirectWitnessSnapshotObserve
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp PrivateWitnessSnapshotOutput)
    (snapshots : List PlannedProbeSnapshot) (result : DirectWitnessResult α)
    (hobserve : ∀ resolved : ResolvedRunResult α,
      result = .done resolved →
      ∀ output ∈ support (observe resolved.context resolved.remaining resolved.value snapshots),
        PrivateWitnessSnapshotExtends snapshots output)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (finishDirectWitnessSnapshotObserve observe snapshots result)) :
    PrivateWitnessSnapshotExtends snapshots output := by
  cases result with
  | stoppedFuel =>
      simp [finishDirectWitnessSnapshotObserve] at houtput
      subst output
      simp [PrivateWitnessSnapshotExtends]
  | stoppedOrdinary =>
      simp [finishDirectWitnessSnapshotObserve] at houtput
      subst output
      simp [PrivateWitnessSnapshotExtends]
  | stoppedPrivate witness =>
      simp [finishDirectWitnessSnapshotObserve] at houtput
      subst output
      simp [PrivateWitnessSnapshotExtends]
  | done resolved => exact hobserve resolved rfl output houtput

theorem privateWitnessSnapshotExtends_of_mem_runDirectWitnessSnapshotObserve
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp PrivateWitnessSnapshotOutput)
    (snapshots : List PlannedProbeSnapshot) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hobserve : ∀ result : ResolvedRunResult α,
      DirectWitnessResult.done result ∈ support
        (runDirectResolvedWitnessFromTable context fuel table computation) →
      ∀ output ∈ support (observe result.context result.remaining result.value snapshots),
        PrivateWitnessSnapshotExtends snapshots output)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (runDirectWitnessSnapshotObserve observe snapshots context fuel table computation)) :
    PrivateWitnessSnapshotExtends snapshots output := by
  unfold runDirectWitnessSnapshotObserve at houtput
  rw [mem_support_bind_iff] at houtput
  obtain ⟨result, hresult, hfinish⟩ := houtput
  exact privateWitnessSnapshotExtends_of_mem_finishDirectWitnessSnapshotObserve observe snapshots
    result (by
      intro resolved heq
      subst result
      exact hobserve resolved hresult)
    output hfinish

theorem privateWitnessSnapshotExtends_of_mem_classifyDirectWitnessSnapshotObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp PrivateWitnessSnapshotOutput)
    (context : DeferredContext) (fuel : Nat) (value : α)
    (snapshots : List PlannedProbeSnapshot)
    (hobserve : ∀ output ∈ support (observe context fuel value snapshots),
      PrivateWitnessSnapshotExtends snapshots output)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (classifyDirectWitnessSnapshotObserve table observe context fuel value snapshots)) :
    PrivateWitnessSnapshotExtends snapshots output := by
  unfold classifyDirectWitnessSnapshotObserve at houtput
  by_cases hhit : PrivateStructuralHit context
  · simp [hhit] at houtput
    subst output
    simp [PrivateWitnessSnapshotExtends]
  · simp only [hhit, ↓reduceDIte] at houtput
    by_cases hcompletable : DeferredCompletable table context
    · simp only [hcompletable, ↓reduceIte] at houtput
      exact hobserve output houtput
    · simp [hcompletable] at houtput
      subst output
      simp [PrivateWitnessSnapshotExtends]

theorem privateWitnessSnapshotExtends_of_mem_canonicalizeDirectWitnessSnapshotObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp PrivateWitnessSnapshotOutput)
    (context : DeferredContext) (fuel : Nat) (value : α)
    (snapshots : List PlannedProbeSnapshot)
    (hobserve : ∀ output ∈ support
      (observe (canonicalizeMaterializedValues table context) fuel value snapshots),
      PrivateWitnessSnapshotExtends snapshots output)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (canonicalizeDirectWitnessSnapshotObserve table observe context fuel value snapshots)) :
    PrivateWitnessSnapshotExtends snapshots output := by
  unfold canonicalizeDirectWitnessSnapshotObserve at houtput
  let canonical := canonicalizeMaterializedValues table context
  by_cases hhit : PrivateStructuralHit canonical
  · simp [canonical, hhit] at houtput
    subst output
    simp [PrivateWitnessSnapshotExtends]
  · simp only [canonical, hhit, ↓reduceDIte] at houtput
    by_cases hpublished : PublishedValues context.state
    · simp only [hpublished, ↓reduceIte] at houtput
      exact privateWitnessSnapshotExtends_of_mem_classifyDirectWitnessSnapshotObserve table observe
        canonical fuel value snapshots hobserve output houtput
    · simp [hpublished] at houtput
      subst output
      simp [PrivateWitnessSnapshotExtends]

set_option maxRecDepth 100000 in
theorem privateWitnessSnapshotExtends_of_mem_directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) →
      List PlannedProbeSnapshot → ProbComp PrivateWitnessSnapshotOutput)
    (snapshots : List PlannedProbeSnapshot) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hobserve : ∀ nextContext remaining value nextSnapshots output,
      output ∈ support (observe nextContext remaining value nextSnapshots) →
      PrivateWitnessSnapshotExtends nextSnapshots output)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve parameter root ftsSecret
        computation observe snapshots context fuel table cache)) :
    PrivateWitnessSnapshotExtends snapshots output := by
  induction computation using OracleComp.inductionOn generalizing snapshots context fuel cache output with
  | pure value =>
      rw [directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve,
        OracleComp.construct_pure] at houtput
      exact hobserve context fuel (value, cache) snapshots output houtput
  | query_bind query next ih =>
      rw [directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve,
        OracleComp.construct_query_bind] at houtput
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              apply privateWitnessSnapshotExtends_of_mem_runDirectWitnessSnapshotObserve _
                snapshots context fuel table ((splitUniformImpl n).run cache) (output := output)
                (houtput := houtput)
              intro result _hresult nextOutput hnextOutput
              apply privateWitnessSnapshotExtends_of_mem_canonicalizeDirectWitnessSnapshotObserve
                table _ result.context result.remaining result.value snapshots
                (output := nextOutput) (houtput := hnextOutput)
              intro finalOutput hfinalOutput
              exact ih result.value.1 snapshots
                (canonicalizeMaterializedValues table result.context) result.remaining
                result.value.2 finalOutput hfinalOutput
          | inr input =>
              let plan := purePlanProbingHashQuery parameter input context.state
              let nextSnapshots := appendPlannedSnapshot snapshots
                (rootAwarePlannedCandidate? parameter input context.state) context
              have hprefix : snapshots <+: nextSnapshots := by
                cases hcandidate : rootAwarePlannedCandidate? parameter input context.state <;>
                  simp [nextSnapshots, appendPlannedSnapshot, hcandidate]
              have hnext : PrivateWitnessSnapshotExtends nextSnapshots output := by
                apply privateWitnessSnapshotExtends_of_mem_runDirectWitnessSnapshotObserve _
                  nextSnapshots context fuel table
                  ((probingHashQueryAfterPlan parameter input plan).run cache) (output := output)
                  (houtput := houtput)
                intro result _hresult nextOutput hnextOutput
                apply privateWitnessSnapshotExtends_of_mem_canonicalizeDirectWitnessSnapshotObserve
                  table _ result.context result.remaining result.value nextSnapshots
                  (output := nextOutput) (houtput := hnextOutput)
                intro finalOutput hfinalOutput
                exact ih result.value.1 nextSnapshots
                  (canonicalizeMaterializedValues table result.context) result.remaining
                  result.value.2 finalOutput hfinalOutput
              exact hprefix.trans hnext
      | inr message =>
          apply privateWitnessSnapshotExtends_of_mem_runDirectWitnessSnapshotObserve _ snapshots
            context fuel table ((maskedSign parameter root ftsSecret message).run cache)
            (output := output) (houtput := houtput)
          intro result _hresult nextOutput hnextOutput
          apply privateWitnessSnapshotExtends_of_mem_canonicalizeDirectWitnessSnapshotObserve
            table _ result.context result.remaining result.value snapshots
            (output := nextOutput) (houtput := hnextOutput)
          intro finalOutput hfinalOutput
          exact ih result.value.1 snapshots
            (canonicalizeMaterializedValues table result.context) result.remaining result.value.2
            finalOutput hfinalOutput

theorem privateWitnessSnapshotExtends_of_mem_retainedResolvedFinalizationPrivateWitnessSnapshotObserve
    (table : OtsSecretIndex → HashOutput) (root : Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : RetainedRestResult × SplitHashCache)
    (snapshots : List PlannedProbeSnapshot)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (retainedResolvedFinalizationPrivateWitnessSnapshotObserve table root context fuel value
        snapshots)) :
    PrivateWitnessSnapshotExtends snapshots output := by
  unfold retainedResolvedFinalizationPrivateWitnessSnapshotObserve at houtput
  by_cases hhit : PrivateStructuralHit context <;>
    simp [hhit] at houtput <;> subst output <;> simp [PrivateWitnessSnapshotExtends]

theorem privateWitnessSnapshotExtends_of_mem_granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (snapshots : List PlannedProbeSnapshot)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve adversary parameter
        table ftsSecret context fuel value snapshots)) :
    PrivateWitnessSnapshotExtends snapshots output := by
  unfold granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve at houtput
  apply privateWitnessSnapshotExtends_of_mem_directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve
    parameter value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
    (retainedResolvedFinalizationPrivateWitnessSnapshotObserve table value.1)
    snapshots context fuel table value.2 (output := output) (houtput := houtput)
  intro nextContext remaining nextValue nextSnapshots nextOutput hnextOutput
  exact privateWitnessSnapshotExtends_of_mem_retainedResolvedFinalizationPrivateWitnessSnapshotObserve
    table value.1 nextContext remaining nextValue nextSnapshots nextOutput hnextOutput

