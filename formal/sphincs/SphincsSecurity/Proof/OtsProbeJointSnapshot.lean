import SphincsSecurity.Proof.OtsProbeBoundaryCompletion
import SphincsSecurity.Proof.OtsProbeDiagnostic125

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

/-- Retains the boundary outcome and candidate contexts for a joint failure analysis. -/
structure BoundaryWitnessSnapshotOutput where
  outcome : DirectBoundaryOutcome
  witnessSnapshot : PrivateWitnessSnapshotOutput

def eraseBoundaryWitnessSnapshotOutput
    (output : BoundaryWitnessSnapshotOutput) : BoundaryWitnessPlanOutput :=
  ⟨output.outcome, erasePrivateWitnessSnapshotOutput output.witnessSnapshot⟩

noncomputable def finishDirectBoundaryWitnessSnapshotObserve
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp BoundaryWitnessSnapshotOutput)
    (candidates : List PlannedProbeSnapshot) : DirectWitnessResult α →
      ProbComp BoundaryWitnessSnapshotOutput
  | .stoppedFuel => pure ⟨.ordinaryFailure, none, candidates⟩
  | .stoppedOrdinary => pure ⟨.ordinaryFailure, none, candidates⟩
  | .stoppedPrivate witness => pure ⟨.privateStructuralFailure, some witness, candidates⟩
  | .done result => observe result.context result.remaining result.value candidates

noncomputable def classifyDirectBoundaryWitnessSnapshotObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp BoundaryWitnessSnapshotOutput)
    (context : DeferredContext) (fuel : Nat) (value : α) (candidates : List PlannedProbeSnapshot) :
    ProbComp BoundaryWitnessSnapshotOutput := by
  classical
  exact if hhit : PrivateStructuralHit context then
      pure ⟨.privateStructuralFailure, some (privateHitWitnessOf context hhit), candidates⟩
    else if DeferredCompletable table context then
      observe context fuel value candidates
    else
      pure ⟨.ordinaryFailure, none, candidates⟩

noncomputable def canonicalizeDirectBoundaryWitnessSnapshotObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp BoundaryWitnessSnapshotOutput)
    (context : DeferredContext) (fuel : Nat) (value : α) (candidates : List PlannedProbeSnapshot) :
    ProbComp BoundaryWitnessSnapshotOutput := by
  classical
  let canonical := canonicalizeMaterializedValues table context
  exact if hhit : PrivateStructuralHit canonical then
      pure ⟨.privateStructuralFailure, some (privateHitWitnessOf canonical hhit), candidates⟩
    else if PublishedValues context.state then
      classifyDirectBoundaryWitnessSnapshotObserve table observe canonical fuel value candidates
    else
      pure ⟨.ordinaryFailure, none, candidates⟩

noncomputable def runDirectBoundaryWitnessSnapshotObserve
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      ProbComp BoundaryWitnessSnapshotOutput)
    (candidates : List PlannedProbeSnapshot) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    ProbComp BoundaryWitnessSnapshotOutput :=
  runDirectResolvedWitnessFromTable context fuel table computation >>=
    finishDirectBoundaryWitnessSnapshotObserve observe candidates

noncomputable def directDetailedBoundaryNormalizedBoundaryWitnessSnapshotObserve
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) → List PlannedProbeSnapshot →
      ProbComp BoundaryWitnessSnapshotOutput)
    (candidates : List PlannedProbeSnapshot) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ProbComp BoundaryWitnessSnapshotOutput := by
  classical
  exact OracleComp.construct
    (C := fun _ : OracleComp (OracleWorld + SigningSpec) α =>
      (DeferredContext → Nat → (α × SplitHashCache) → List PlannedProbeSnapshot →
        ProbComp BoundaryWitnessSnapshotOutput) →
      List PlannedProbeSnapshot → DeferredContext → Nat → (OtsSecretIndex → HashOutput) →
        SplitHashCache → ProbComp BoundaryWitnessSnapshotOutput)
    (fun value observe candidates context fuel _table cache =>
      observe context fuel (value, cache) candidates)
    (fun query _next recursivelyRun observe candidates context fuel table cache =>
      match query with
      | .inl (.inl n) =>
          runDirectBoundaryWitnessSnapshotObserve
            (canonicalizeDirectBoundaryWitnessSnapshotObserve table
              (fun nextContext remaining value nextCandidates =>
                recursivelyRun value.1 observe nextCandidates nextContext remaining table
                  value.2))
            candidates context fuel table ((splitUniformImpl n).run cache)
      | .inl (.inr input) =>
          let plan := purePlanProbingHashQuery parameter input context.state
          let nextCandidates := appendPlannedSnapshot candidates
            (rootAwarePlannedCandidate? parameter input context.state) context
          runDirectBoundaryWitnessSnapshotObserve
            (canonicalizeDirectBoundaryWitnessSnapshotObserve table
              (fun nextContext remaining value laterCandidates =>
                recursivelyRun value.1 observe laterCandidates nextContext remaining table
                  value.2))
            nextCandidates context fuel table
              ((probingHashQueryAfterPlan parameter input plan).run cache)
      | .inr message =>
          runDirectBoundaryWitnessSnapshotObserve
            (canonicalizeDirectBoundaryWitnessSnapshotObserve table
              (fun nextContext remaining value nextCandidates =>
                recursivelyRun value.1 observe nextCandidates nextContext remaining table
                  value.2))
            candidates context fuel table ((maskedSign parameter root ftsSecret message).run cache))
    computation observe candidates context fuel table cache

noncomputable def retainedResolvedFinalizationBoundaryWitnessSnapshotObserve
    (table : OtsSecretIndex → HashOutput) (root : Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : RetainedRestResult × SplitHashCache) (candidates : List PlannedProbeSnapshot) :
    ProbComp BoundaryWitnessSnapshotOutput := by
  classical
  exact if hhit : PrivateStructuralHit context then
      pure ⟨.privateStructuralFailure, some (privateHitWitnessOf context hhit), candidates⟩
    else if DeferredCompletable table context then do
      let failed ← resolvedFinalizationObserve table context fuel ((root, value.1), value.2)
      pure ⟨DirectBoundaryOutcome.ofFailed failed, none, candidates⟩
    else
      pure ⟨.ordinaryFailure, none, candidates⟩

noncomputable def granularDetailedRetainedRestNormalizedBoundaryWitnessSnapshotObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (candidates : List PlannedProbeSnapshot) :
    ProbComp BoundaryWitnessSnapshotOutput :=
  directDetailedBoundaryNormalizedBoundaryWitnessSnapshotObserve parameter value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
    (retainedResolvedFinalizationBoundaryWitnessSnapshotObserve table value.1)
    candidates context fuel table value.2

noncomputable def granularAllCanonicalBoundaryWitnessSnapshot
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp BoundaryWitnessSnapshotOutput :=
  runDirectBoundaryWitnessSnapshotObserve
    (canonicalizeDirectBoundaryWitnessSnapshotObserve table
      (granularDetailedRetainedRestNormalizedBoundaryWitnessSnapshotObserve adversary parameter table
        ftsSecret))
    [] emptyWitnessDeferredContext fuel table
      (maskedPublishedTreeRoot.run emptySplitHashCache)

noncomputable def sampledGranularAllCanonicalBoundaryWitnessSnapshot
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp BoundaryWitnessSnapshotOutput := do
  let table ← sampleOtsHashTable
  granularAllCanonicalBoundaryWitnessSnapshot adversary parameter table ftsSecret fuel

end SphincsSecurity.Concrete.OtsProbeSimulation
