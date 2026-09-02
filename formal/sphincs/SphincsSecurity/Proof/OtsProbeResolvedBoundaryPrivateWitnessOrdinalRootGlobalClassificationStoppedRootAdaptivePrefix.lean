import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveBridge

/-!
# Adaptive selected-root prefix

This file keeps the deferred prefix and its chronological observations together. When the chosen
ordinal is appended, it resolves that root and hands the complete current query and suffix to the
compiled selected-root bridge.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

noncomputable def delayedSelectedRootIndicator
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (selection : PrivateOrdinalSelection) (fuel : Nat) (cache : SplitHashCache) :
    ProbComp Bool := do
  let resolved ← resolveDeferredPositionValue target selection.context
  match resolved with
  | none => pure false
  | some resolved =>
      (successfulObservedRootComparisonIndicator table ordinal target ∘
          fun observed => (observed, rightRoot)) <$>
        observedMaterializedBoundary parameter root ftsSecret computation observations
          (materializedDeferredState resolved.toDeferredContext) fuel table cache

noncomputable def finishDirectDelayedSelectedRootIndicator
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      List CleanProbeObservation → ProbComp Bool)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation) : DirectWitnessResult α → ProbComp Bool
  | .stoppedFuel => pure false
  | .stoppedOrdinary => pure false
  | .stoppedPrivate _ => pure false
  | .done result =>
      observe result.context result.remaining result.value snapshots observations

noncomputable def canonicalizeDirectDelayedSelectedRootIndicator
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      List CleanProbeObservation → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (value : α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation) : ProbComp Bool := by
  classical
  let canonical := canonicalizeMaterializedValues table context
  exact if PrivateStructuralHit canonical then pure false
    else if PublishedValues context.state then
      if DeferredCompletable table canonical then
        observe canonical fuel value snapshots observations
      else pure false
    else pure false

noncomputable def directDelayedSelectedRootIndicator
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) : ProbComp Bool := by
  classical
  exact OracleComp.construct
    (C := fun _ : OracleComp (OracleWorld + SigningSpec) α =>
      List PlannedProbeSnapshot → List CleanProbeObservation → DeferredContext → Nat →
        SplitHashCache → ProbComp Bool)
    (fun _value snapshots observations context fuel cache =>
      if hselected : ordinal < snapshots.length then
        delayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
          (pure _value) observations
          ⟨(snapshots.get ⟨ordinal, hselected⟩).probe,
            (snapshots.get ⟨ordinal, hselected⟩).context,
            snapshots.map PlannedProbeSnapshot.toProbe⟩ fuel cache
      else pure false)
    (fun query _next recursivelyRun snapshots observations context fuel cache =>
      if hselected : ordinal < snapshots.length then
        delayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
          (liftM (OracleSpec.query query) >>= _next) observations
          ⟨(snapshots.get ⟨ordinal, hselected⟩).probe,
            (snapshots.get ⟨ordinal, hselected⟩).context,
            snapshots.map PlannedProbeSnapshot.toProbe⟩ fuel cache
      else
        match query with
        | .inl (.inl n) =>
            runDirectResolvedWitnessFromTable context fuel table ((splitUniformImpl n).run cache) >>=
              finishDirectDelayedSelectedRootIndicator
                (canonicalizeDirectDelayedSelectedRootIndicator table
                  (fun nextContext remaining value laterSnapshots laterObservations =>
                    recursivelyRun value.1 laterSnapshots laterObservations nextContext remaining
                      value.2)) snapshots observations
        | .inl (.inr input) =>
            let plan := purePlanProbingHashQuery parameter input context.state
            let candidate? := rootAwareCandidateForPlan? parameter input plan
            let nextSnapshots := appendPlannedSnapshot snapshots candidate? context
            let nextObservations := observationsAfterCandidate observations
              (materializedDeferredState context) candidate?
            if hnextSelected : ordinal < nextSnapshots.length then
              delayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
                ((liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
                    (Sum.inl (Sum.inr input))) :
                    OracleComp (OracleWorld + SigningSpec) HashOutput) >>= _next) observations
                ⟨(nextSnapshots.get ⟨ordinal, hnextSelected⟩).probe,
                  (nextSnapshots.get ⟨ordinal, hnextSelected⟩).context,
                  nextSnapshots.map PlannedProbeSnapshot.toProbe⟩ fuel cache
            else
              runDirectResolvedWitnessFromTable context fuel table
                  ((probingHashQueryAfterPlan parameter input plan).run cache) >>=
                finishDirectDelayedSelectedRootIndicator
                  (canonicalizeDirectDelayedSelectedRootIndicator table
                    (fun nextContext remaining value laterSnapshots laterObservations =>
                      recursivelyRun value.1 laterSnapshots laterObservations nextContext remaining
                        value.2)) nextSnapshots nextObservations
        | .inr message =>
            runDirectResolvedWitnessFromTable context fuel table
                ((maskedSign parameter root ftsSecret message).run cache) >>=
              finishDirectDelayedSelectedRootIndicator
                (canonicalizeDirectDelayedSelectedRootIndicator table
                  (fun nextContext remaining value laterSnapshots laterObservations =>
                    recursivelyRun value.1 laterSnapshots laterObservations nextContext remaining
                      value.2)) snapshots observations)
    computation snapshots observations context fuel cache

theorem directDelayedSelectedRootIndicator_eq_selected
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hselected : ordinal < snapshots.length) :
    directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
        computation snapshots observations context fuel cache =
      delayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
        computation observations
        ⟨(snapshots.get ⟨ordinal, hselected⟩).probe,
          (snapshots.get ⟨ordinal, hselected⟩).context,
          snapshots.map PlannedProbeSnapshot.toProbe⟩ fuel cache := by
  induction computation using OracleComp.inductionOn generalizing
      snapshots observations context fuel cache with
  | pure value =>
      rw [directDelayedSelectedRootIndicator, OracleComp.construct_pure]
      simp only [hselected, ↓reduceDIte]
  | query_bind query next ih =>
      rw [directDelayedSelectedRootIndicator, OracleComp.construct_query_bind]
      simp only [hselected, ↓reduceDIte]

end SphincsSecurity.Concrete.OtsProbeSimulation
