import SphincsSecurity.Proof.OtsProbeJointSnapshot

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

set_option linter.constructorNameAsVariable false

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem evalDist_witnessSnapshot_retainedFinalizationBoundaryWitnessSnapshot
    (table : OtsSecretIndex → HashOutput) (root : Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : RetainedRestResult × SplitHashCache) (candidates : List PlannedProbeSnapshot) :
    evalDist (BoundaryWitnessSnapshotOutput.witnessSnapshot <$>
        retainedResolvedFinalizationBoundaryWitnessSnapshotObserve table root context fuel value
          candidates) =
      evalDist
        (retainedResolvedFinalizationPrivateWitnessSnapshotObserve table root context fuel value
          candidates) := by
  classical
  unfold retainedResolvedFinalizationBoundaryWitnessSnapshotObserve
    retainedResolvedFinalizationPrivateWitnessSnapshotObserve
  by_cases hhit : PrivateStructuralHit context
  · simp [hhit]
  · simp only [hhit, ↓reduceDIte, map_eq_bind_pure_comp]
    by_cases hcompletable : DeferredCompletable table context
    · simp only [hcompletable, ↓reduceIte]
      simp only [bind_assoc, pure_bind, Function.comp_apply]
      change evalDist
          (resolvedFinalizationObserve table context fuel ((root, value.1), value.2) >>=
            fun _ => pure (none, candidates)) =
        evalDist (pure (none, candidates) : ProbComp PrivateWitnessSnapshotOutput)
      exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        (resolvedFinalizationObserve table context fuel ((root, value.1), value.2))
        (by simp [resolvedFinalizationObserve]) _
    · simp [hcompletable]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem evalDist_witnessSnapshot_finishDirectBoundaryWitnessSnapshotObserve
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp BoundaryWitnessSnapshotOutput)
    (witnessObserve : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp PrivateWitnessSnapshotOutput)
    (candidates : List PlannedProbeSnapshot) (result : DirectWitnessResult α)
    (hproject : ∀ context fuel value nextCandidates,
      evalDist (BoundaryWitnessSnapshotOutput.witnessSnapshot <$>
          observe context fuel value nextCandidates) =
        evalDist (witnessObserve context fuel value nextCandidates)) :
    evalDist (BoundaryWitnessSnapshotOutput.witnessSnapshot <$>
        finishDirectBoundaryWitnessSnapshotObserve observe candidates result) =
      evalDist (finishDirectWitnessSnapshotObserve witnessObserve candidates result) := by
  cases result with
  | stoppedFuel => simp [finishDirectBoundaryWitnessSnapshotObserve, finishDirectWitnessSnapshotObserve]
  | stoppedOrdinary =>
      simp [finishDirectBoundaryWitnessSnapshotObserve, finishDirectWitnessSnapshotObserve]
  | stoppedPrivate witness =>
      simp [finishDirectBoundaryWitnessSnapshotObserve, finishDirectWitnessSnapshotObserve]
  | done result => exact hproject result.context result.remaining result.value candidates

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem evalDist_witnessSnapshot_classifyDirectBoundaryWitnessSnapshotObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp BoundaryWitnessSnapshotOutput)
    (witnessObserve : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp PrivateWitnessSnapshotOutput)
    (context : DeferredContext) (fuel : Nat) (value : α) (candidates : List PlannedProbeSnapshot)
    (hproject : ∀ nextContext remaining nextValue nextCandidates,
      evalDist (BoundaryWitnessSnapshotOutput.witnessSnapshot <$>
          observe nextContext remaining nextValue nextCandidates) =
        evalDist (witnessObserve nextContext remaining nextValue nextCandidates)) :
    evalDist (BoundaryWitnessSnapshotOutput.witnessSnapshot <$>
        classifyDirectBoundaryWitnessSnapshotObserve table observe context fuel value candidates) =
      evalDist
        (classifyDirectWitnessSnapshotObserve table witnessObserve context fuel value candidates) := by
  classical
  unfold classifyDirectBoundaryWitnessSnapshotObserve classifyDirectWitnessSnapshotObserve
  by_cases hhit : PrivateStructuralHit context
  · simp [hhit]
  · simp only [hhit, ↓reduceDIte]
    by_cases hcompletable : DeferredCompletable table context
    · simp only [hcompletable, ↓reduceIte]
      exact hproject context fuel value candidates
    · simp [hcompletable]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem evalDist_witnessSnapshot_canonicalizeDirectBoundaryWitnessSnapshotObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp BoundaryWitnessSnapshotOutput)
    (witnessObserve : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp PrivateWitnessSnapshotOutput)
    (context : DeferredContext) (fuel : Nat) (value : α) (candidates : List PlannedProbeSnapshot)
    (hproject : ∀ nextContext remaining nextValue nextCandidates,
      evalDist (BoundaryWitnessSnapshotOutput.witnessSnapshot <$>
          observe nextContext remaining nextValue nextCandidates) =
        evalDist (witnessObserve nextContext remaining nextValue nextCandidates)) :
    evalDist (BoundaryWitnessSnapshotOutput.witnessSnapshot <$>
        canonicalizeDirectBoundaryWitnessSnapshotObserve table observe context fuel value candidates) =
      evalDist
        (canonicalizeDirectWitnessSnapshotObserve table witnessObserve context fuel value candidates) := by
  classical
  unfold canonicalizeDirectBoundaryWitnessSnapshotObserve canonicalizeDirectWitnessSnapshotObserve
  let canonical := canonicalizeMaterializedValues table context
  by_cases hhit : PrivateStructuralHit canonical
  · simp [canonical, hhit]
  · simp only [canonical, hhit, ↓reduceDIte]
    by_cases hpublished : PublishedValues context.state
    · simp only [hpublished, ↓reduceIte]
      exact evalDist_witnessSnapshot_classifyDirectBoundaryWitnessSnapshotObserve table observe
        witnessObserve canonical fuel value candidates hproject
    · simp [hpublished]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem evalDist_witnessSnapshot_runDirectBoundaryWitnessSnapshotObserve
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp BoundaryWitnessSnapshotOutput)
    (witnessObserve : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp PrivateWitnessSnapshotOutput)
    (candidates : List PlannedProbeSnapshot) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hproject : ∀ nextContext remaining value nextCandidates,
      evalDist (BoundaryWitnessSnapshotOutput.witnessSnapshot <$>
          observe nextContext remaining value nextCandidates) =
        evalDist (witnessObserve nextContext remaining value nextCandidates)) :
    evalDist (BoundaryWitnessSnapshotOutput.witnessSnapshot <$>
        runDirectBoundaryWitnessSnapshotObserve observe candidates context fuel table computation) =
      evalDist
        (runDirectWitnessSnapshotObserve witnessObserve candidates context fuel table computation) := by
  unfold runDirectBoundaryWitnessSnapshotObserve runDirectWitnessSnapshotObserve
  rw [map_bind]
  apply evalDist_bind_congr
  intro result _hresult
  exact evalDist_witnessSnapshot_finishDirectBoundaryWitnessSnapshotObserve observe witnessObserve
    candidates result hproject

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem evalDist_witnessSnapshot_directDetailedBoundaryNormalizedBoundaryWitnessSnapshotObserve
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) → List PlannedProbeSnapshot →
      ProbComp BoundaryWitnessSnapshotOutput)
    (witnessObserve : DeferredContext → Nat → (α × SplitHashCache) → List PlannedProbeSnapshot →
      ProbComp PrivateWitnessSnapshotOutput)
    (candidates : List PlannedProbeSnapshot) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hproject : ∀ nextContext remaining value nextCandidates,
      evalDist (BoundaryWitnessSnapshotOutput.witnessSnapshot <$>
          observe nextContext remaining value nextCandidates) =
        evalDist (witnessObserve nextContext remaining value nextCandidates)) :
    evalDist (BoundaryWitnessSnapshotOutput.witnessSnapshot <$>
        directDetailedBoundaryNormalizedBoundaryWitnessSnapshotObserve parameter root ftsSecret
          computation observe candidates context fuel table cache) =
      evalDist (directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve parameter root ftsSecret
        computation witnessObserve candidates context fuel table cache) := by
  induction computation using OracleComp.inductionOn generalizing candidates context fuel cache with
  | pure value =>
      rw [directDetailedBoundaryNormalizedBoundaryWitnessSnapshotObserve,
        OracleComp.construct_pure,
        directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve, OracleComp.construct_pure]
      exact hproject context fuel (value, cache) candidates
  | query_bind query next ih =>
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              rw [directDetailedBoundaryNormalizedBoundaryWitnessSnapshotObserve,
                OracleComp.construct_query_bind,
                directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve,
                OracleComp.construct_query_bind]
              apply evalDist_witnessSnapshot_runDirectBoundaryWitnessSnapshotObserve
              intro nextContext remaining value nextCandidates
              apply evalDist_witnessSnapshot_canonicalizeDirectBoundaryWitnessSnapshotObserve
              intro finalContext finalRemaining finalValue finalCandidates
              exact ih finalValue.1 finalCandidates finalContext finalRemaining finalValue.2
          | inr input =>
              rw [directDetailedBoundaryNormalizedBoundaryWitnessSnapshotObserve,
                OracleComp.construct_query_bind,
                directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve,
                OracleComp.construct_query_bind]
              apply evalDist_witnessSnapshot_runDirectBoundaryWitnessSnapshotObserve
              intro nextContext remaining value laterCandidates
              apply evalDist_witnessSnapshot_canonicalizeDirectBoundaryWitnessSnapshotObserve
              intro finalContext finalRemaining finalValue finalCandidates
              exact ih finalValue.1 finalCandidates finalContext finalRemaining finalValue.2
      | inr message =>
          rw [directDetailedBoundaryNormalizedBoundaryWitnessSnapshotObserve,
            OracleComp.construct_query_bind,
            directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve,
            OracleComp.construct_query_bind]
          apply evalDist_witnessSnapshot_runDirectBoundaryWitnessSnapshotObserve
          intro nextContext remaining value nextCandidates
          apply evalDist_witnessSnapshot_canonicalizeDirectBoundaryWitnessSnapshotObserve
          intro finalContext finalRemaining finalValue finalCandidates
          exact ih finalValue.1 finalCandidates finalContext finalRemaining finalValue.2

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem evalDist_witnessSnapshot_granularDetailedRetainedRestNormalizedBoundaryWitnessSnapshotObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (candidates : List PlannedProbeSnapshot) :
    evalDist (BoundaryWitnessSnapshotOutput.witnessSnapshot <$>
        granularDetailedRetainedRestNormalizedBoundaryWitnessSnapshotObserve adversary parameter table
          ftsSecret context fuel value candidates) =
      evalDist
        (granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve adversary parameter table
          ftsSecret context fuel value candidates) := by
  unfold granularDetailedRetainedRestNormalizedBoundaryWitnessSnapshotObserve
    granularDetailedRetainedRestNormalizedPrivateWitnessSnapshotObserve
  apply evalDist_witnessSnapshot_directDetailedBoundaryNormalizedBoundaryWitnessSnapshotObserve
  intro nextContext remaining nextValue nextCandidates
  exact evalDist_witnessSnapshot_retainedFinalizationBoundaryWitnessSnapshot table value.1 nextContext
    remaining nextValue nextCandidates

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem evalDist_witnessSnapshot_granularAllCanonicalBoundaryWitnessSnapshot
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (BoundaryWitnessSnapshotOutput.witnessSnapshot <$>
        granularAllCanonicalBoundaryWitnessSnapshot adversary parameter table ftsSecret fuel) =
      evalDist
        (granularAllCanonicalPrivateWitnessSnapshot adversary parameter table ftsSecret fuel) := by
  unfold granularAllCanonicalBoundaryWitnessSnapshot granularAllCanonicalPrivateWitnessSnapshot
  apply evalDist_witnessSnapshot_runDirectBoundaryWitnessSnapshotObserve
  intro context remaining value candidates
  apply evalDist_witnessSnapshot_canonicalizeDirectBoundaryWitnessSnapshotObserve
  intro nextContext nextRemaining nextValue nextCandidates
  exact
    evalDist_witnessSnapshot_granularDetailedRetainedRestNormalizedBoundaryWitnessSnapshotObserve
      adversary parameter table ftsSecret nextContext nextRemaining nextValue nextCandidates

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem evalDist_witnessSnapshot_sampledGranularAllCanonicalBoundaryWitnessSnapshot
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (BoundaryWitnessSnapshotOutput.witnessSnapshot <$>
        sampledGranularAllCanonicalBoundaryWitnessSnapshot adversary parameter ftsSecret fuel) =
      evalDist
        (sampledGranularAllCanonicalPrivateWitnessSnapshot adversary parameter ftsSecret fuel) := by
  unfold sampledGranularAllCanonicalBoundaryWitnessSnapshot
    sampledGranularAllCanonicalPrivateWitnessSnapshot
  rw [map_bind]
  apply evalDist_bind_congr
  intro table _htable
  exact evalDist_witnessSnapshot_granularAllCanonicalBoundaryWitnessSnapshot adversary parameter table
    ftsSecret fuel

end SphincsSecurity.Concrete.OtsProbeSimulation
