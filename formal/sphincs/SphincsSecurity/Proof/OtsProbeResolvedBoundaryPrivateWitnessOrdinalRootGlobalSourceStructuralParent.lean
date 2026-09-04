import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalTop
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalHiddenRiskBound
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalHiddenFreshSigner

/-!
# Structural parents of source snapshots

Every snapshot recorded by the source interpreter comes from the root-aware candidate planner. This
file records the resulting support invariant needed to exclude the published top root from the
delayed-root exchange.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

def SnapshotsHaveStructuralParents (snapshots : List PlannedProbeSnapshot) : Prop :=
  CandidatesHaveStructuralParent (snapshots.map PlannedProbeSnapshot.toProbe)

theorem snapshotsHaveStructuralParents_nil :
    SnapshotsHaveStructuralParents [] := by
  exact candidatesHaveStructuralParent_nil

theorem SnapshotsHaveStructuralParents.appendPlanned
    {snapshots : List PlannedProbeSnapshot}
    (hparents : SnapshotsHaveStructuralParents snapshots)
    (candidate? : Option Probe) (context : DeferredContext)
    (hcandidate : ∀ candidate, candidate? = some candidate →
      candidate.HasStructuralParent) :
    SnapshotsHaveStructuralParents (appendPlannedSnapshot snapshots candidate? context) := by
  unfold SnapshotsHaveStructuralParents
  rw [map_toProbe_appendPlannedSnapshot]
  exact CandidatesHaveStructuralParent.appendPlanned hparents candidate? hcandidate

theorem snapshotsHaveStructuralParents_of_mem_finishDirectWitnessSnapshotObserve
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp PrivateWitnessSnapshotOutput)
    (snapshots : List PlannedProbeSnapshot) (result : DirectWitnessResult α)
    (hparents : SnapshotsHaveStructuralParents snapshots)
    (hobserve : ∀ resolved : ResolvedRunResult α,
      result = .done resolved →
      ∀ output ∈ support (observe resolved.context resolved.remaining resolved.value snapshots),
        SnapshotsHaveStructuralParents output.2)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (finishDirectWitnessSnapshotObserve observe snapshots result)) :
    SnapshotsHaveStructuralParents output.2 := by
  cases result with
  | stoppedFuel =>
      simp [finishDirectWitnessSnapshotObserve] at houtput
      simpa [houtput] using hparents
  | stoppedOrdinary =>
      simp [finishDirectWitnessSnapshotObserve] at houtput
      simpa [houtput] using hparents
  | stoppedPrivate witness =>
      simp [finishDirectWitnessSnapshotObserve] at houtput
      simpa [houtput] using hparents
  | done resolved => exact hobserve resolved rfl output houtput

theorem snapshotsHaveStructuralParents_of_mem_runDirectWitnessSnapshotObserve
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp PrivateWitnessSnapshotOutput)
    (snapshots : List PlannedProbeSnapshot) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hparents : SnapshotsHaveStructuralParents snapshots)
    (hobserve : ∀ result : ResolvedRunResult α,
      DirectWitnessResult.done result ∈ support
        (runDirectResolvedWitnessFromTable context fuel table computation) →
      ∀ output ∈ support (observe result.context result.remaining result.value snapshots),
        SnapshotsHaveStructuralParents output.2)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (runDirectWitnessSnapshotObserve observe snapshots context fuel table computation)) :
    SnapshotsHaveStructuralParents output.2 := by
  unfold runDirectWitnessSnapshotObserve at houtput
  rw [mem_support_bind_iff] at houtput
  obtain ⟨result, hresult, hfinish⟩ := houtput
  exact snapshotsHaveStructuralParents_of_mem_finishDirectWitnessSnapshotObserve observe snapshots
    result hparents (by
      intro resolved heq
      subst result
      exact hobserve resolved hresult)
    output hfinish

theorem snapshotsHaveStructuralParents_of_mem_classifyDirectWitnessSnapshotObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp PrivateWitnessSnapshotOutput)
    (context : DeferredContext) (fuel : Nat) (value : α)
    (snapshots : List PlannedProbeSnapshot)
    (hparents : SnapshotsHaveStructuralParents snapshots)
    (hobserve : ∀ output ∈ support (observe context fuel value snapshots),
      SnapshotsHaveStructuralParents output.2)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (classifyDirectWitnessSnapshotObserve table observe context fuel value snapshots)) :
    SnapshotsHaveStructuralParents output.2 := by
  unfold classifyDirectWitnessSnapshotObserve at houtput
  by_cases hhit : PrivateStructuralHit context
  · simp [hhit] at houtput
    simpa [houtput] using hparents
  · simp only [hhit, ↓reduceDIte] at houtput
    by_cases hcompletable : DeferredCompletable table context
    · simp only [hcompletable, ↓reduceIte] at houtput
      exact hobserve output houtput
    · simp [hcompletable] at houtput
      simpa [houtput] using hparents

theorem snapshotsHaveStructuralParents_of_mem_canonicalizeDirectWitnessSnapshotObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp PrivateWitnessSnapshotOutput)
    (context : DeferredContext) (fuel : Nat) (value : α)
    (snapshots : List PlannedProbeSnapshot)
    (hparents : SnapshotsHaveStructuralParents snapshots)
    (hobserve : ∀ output ∈ support
      (observe (canonicalizeMaterializedValues table context) fuel value snapshots),
      SnapshotsHaveStructuralParents output.2)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (canonicalizeDirectWitnessSnapshotObserve table observe context fuel value snapshots)) :
    SnapshotsHaveStructuralParents output.2 := by
  unfold canonicalizeDirectWitnessSnapshotObserve at houtput
  let canonical := canonicalizeMaterializedValues table context
  by_cases hhit : PrivateStructuralHit canonical
  · simp [canonical, hhit] at houtput
    simpa [houtput] using hparents
  · simp only [canonical, hhit, ↓reduceDIte] at houtput
    by_cases hpublished : PublishedValues context.state
    · simp only [hpublished, ↓reduceIte] at houtput
      exact snapshotsHaveStructuralParents_of_mem_classifyDirectWitnessSnapshotObserve table
        observe canonical fuel value snapshots hparents hobserve output houtput
    · simp [hpublished] at houtput
      simpa [houtput] using hparents

set_option maxRecDepth 100000 in
theorem snapshotsHaveStructuralParents_of_mem_directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) →
      List PlannedProbeSnapshot → ProbComp PrivateWitnessSnapshotOutput)
    (snapshots : List PlannedProbeSnapshot) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hparents : SnapshotsHaveStructuralParents snapshots)
    (hobserve : ∀ nextContext remaining value nextSnapshots output,
      SnapshotsHaveStructuralParents nextSnapshots →
      output ∈ support (observe nextContext remaining value nextSnapshots) →
      SnapshotsHaveStructuralParents output.2)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve parameter root ftsSecret
        computation observe snapshots context fuel table cache)) :
    SnapshotsHaveStructuralParents output.2 := by
  induction computation using OracleComp.inductionOn generalizing snapshots context fuel cache output with
  | pure value =>
      rw [directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve,
        OracleComp.construct_pure] at houtput
      exact hobserve context fuel (value, cache) snapshots output hparents houtput
  | query_bind query next ih =>
      rw [directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve,
        OracleComp.construct_query_bind] at houtput
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              apply snapshotsHaveStructuralParents_of_mem_runDirectWitnessSnapshotObserve _
                snapshots context fuel table ((splitUniformImpl n).run cache) hparents
                (output := output) (houtput := houtput)
              intro result _hresult nextOutput hnextOutput
              apply snapshotsHaveStructuralParents_of_mem_canonicalizeDirectWitnessSnapshotObserve
                table _ result.context result.remaining result.value snapshots hparents
                (output := nextOutput) (houtput := hnextOutput)
              intro finalOutput hfinalOutput
              exact ih result.value.1 snapshots
                (canonicalizeMaterializedValues table result.context) result.remaining
                result.value.2 hparents finalOutput hfinalOutput
          | inr input =>
              let plan := purePlanProbingHashQuery parameter input context.state
              let candidate? := rootAwarePlannedCandidate? parameter input context.state
              let nextSnapshots := appendPlannedSnapshot snapshots candidate? context
              have hnextParents : SnapshotsHaveStructuralParents nextSnapshots := by
                apply hparents.appendPlanned candidate? context
                intro candidate hcandidate
                exact rootAwarePlannedCandidate?_hasStructuralParent hcandidate
              apply snapshotsHaveStructuralParents_of_mem_runDirectWitnessSnapshotObserve _
                nextSnapshots context fuel table
                ((probingHashQueryAfterPlan parameter input plan).run cache) hnextParents
                (output := output) (houtput := houtput)
              intro result _hresult nextOutput hnextOutput
              apply snapshotsHaveStructuralParents_of_mem_canonicalizeDirectWitnessSnapshotObserve
                table _ result.context result.remaining result.value nextSnapshots hnextParents
                (output := nextOutput) (houtput := hnextOutput)
              intro finalOutput hfinalOutput
              exact ih result.value.1 nextSnapshots
                (canonicalizeMaterializedValues table result.context) result.remaining
                result.value.2 hnextParents finalOutput hfinalOutput
      | inr message =>
          apply snapshotsHaveStructuralParents_of_mem_runDirectWitnessSnapshotObserve _ snapshots
            context fuel table ((maskedSign parameter root ftsSecret message).run cache) hparents
            (output := output) (houtput := houtput)
          intro result _hresult nextOutput hnextOutput
          apply snapshotsHaveStructuralParents_of_mem_canonicalizeDirectWitnessSnapshotObserve
            table _ result.context result.remaining result.value snapshots hparents
            (output := nextOutput) (houtput := hnextOutput)
          intro finalOutput hfinalOutput
          exact ih result.value.1 snapshots
            (canonicalizeMaterializedValues table result.context) result.remaining result.value.2
            hparents finalOutput hfinalOutput

theorem snapshotsHaveStructuralParents_of_mem_retainedResolvedFinalizationPrivateWitnessSnapshotObserve
    (table : OtsSecretIndex → HashOutput) (root : Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : RetainedRestResult × SplitHashCache)
    (snapshots : List PlannedProbeSnapshot)
    (hparents : SnapshotsHaveStructuralParents snapshots)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (retainedResolvedFinalizationPrivateWitnessSnapshotObserve table root context fuel value
        snapshots)) :
    SnapshotsHaveStructuralParents output.2 := by
  unfold retainedResolvedFinalizationPrivateWitnessSnapshotObserve at houtput
  by_cases hhit : PrivateStructuralHit context <;>
    simp [hhit] at houtput <;> simpa [houtput] using hparents

theorem snapshotsHaveStructuralParents_of_mem_granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (snapshots : List PlannedProbeSnapshot)
    (hparents : SnapshotsHaveStructuralParents snapshots)
    (output : PrivateWitnessSnapshotOutput)
    (houtput : output ∈ support
      (granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve adversary parameter
        table ftsSecret context fuel value snapshots)) :
    SnapshotsHaveStructuralParents output.2 := by
  unfold granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve at houtput
  apply snapshotsHaveStructuralParents_of_mem_directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve
    parameter value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
    (retainedResolvedFinalizationPrivateWitnessSnapshotObserve table value.1)
    snapshots context fuel table value.2 hparents (output := output) (houtput := houtput)
  intro nextContext remaining nextValue nextSnapshots nextOutput hnextParents hnextOutput
  exact snapshotsHaveStructuralParents_of_mem_retainedResolvedFinalizationPrivateWitnessSnapshotObserve
    table value.1 nextContext remaining nextValue nextSnapshots hnextParents nextOutput hnextOutput

end SphincsSecurity.Concrete.OtsProbeSimulation
