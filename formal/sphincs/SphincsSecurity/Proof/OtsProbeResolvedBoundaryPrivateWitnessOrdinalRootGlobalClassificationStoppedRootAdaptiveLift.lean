import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveObservation

/-!
# Adaptive selected-root lift

The first-stopped step relation is consumed without forgetting the shared continuation. Clean
steps recurse, failed materialized steps make the real indicator false, and a persistent missing
chain start contradicts successful finalization.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option maxRecDepth 100000 in
theorem relTriple_observed_finishDirectDelayed_of_firstStopped
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (next : α → OracleComp (OracleWorld + SigningSpec) RetainedRestResult)
    (observe : DeferredContext → Nat → (α × SplitHashCache) →
      List PlannedProbeSnapshot → List CleanProbeObservation → ProbComp Bool)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (leftResult : DirectWitnessResult (α × SplitHashCache))
    (rightResult : Option (ObservedCleanRunResult (α × SplitHashCache)))
    (hrelation : WitnessObservedFirstStoppedStepRel table observations leftResult rightResult)
    (hrecursive : ∀ left right,
      leftResult = .done left →
      rightResult = some (observedResolvedResult observations right) →
      OrdinaryMaterializedRunEq table left right →
      RelTriple
        ((successfulObservedRootComparisonIndicator table ordinal target ∘
            fun observed ↦ (observed, rightRoot)) <$>
          observedMaterializedBoundary parameter publicRoot ftsSecret (next right.value.1)
            observations right.context.state right.remaining table right.value.2)
        (canonicalizeDirectDelayedSelectedRootIndicator table observe left.context left.remaining
          (left.value.1, left.value.2) snapshots observations)
        SuccessfulObservedIndicatorRel) :
    RelTriple
      (match rightResult with
      | none => pure false
      | some result =>
          (successfulObservedRootComparisonIndicator table ordinal target ∘
              fun observed ↦ (observed, rightRoot)) <$>
            observedMaterializedBoundary parameter publicRoot ftsSecret (next result.value.1)
              result.observations result.state result.remaining table result.value.2)
      (finishDirectDelayedSelectedRootIndicator
        (canonicalizeDirectDelayedSelectedRootIndicator table observe)
        snapshots observations leftResult)
      SuccessfulObservedIndicatorRel := by
  rcases hrelation with hfailed | haligned | hmissing
  · subst rightResult
    have hbase := relTriple_true (pure false : ProbComp Bool)
      (finishDirectDelayedSelectedRootIndicator
        (canonicalizeDirectDelayedSelectedRootIndicator table observe)
        snapshots observations leftResult)
    have hsupported :=
      SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
        (fun result ↦ result = false) (by intro result hresult; simpa using hresult)
    apply relTriple_post_mono hsupported
    intro real delayed hrelation hreal
    exact (Bool.false_ne_true (hrelation.2.symm.trans hreal)).elim
  · obtain ⟨left, right, hleft, hright, hclean⟩ := haligned
    subst leftResult
    subst rightResult
    simp only [finishDirectDelayedSelectedRootIndicator, observedResolvedResult]
    exact hrecursive left right rfl rfl hclean
  · obtain ⟨right, hright, hdoomed, hmissing⟩ := hmissing
    subst rightResult
    let realRun :=
      (successfulObservedRootComparisonIndicator table ordinal target ∘
          fun observed ↦ (observed, rightRoot)) <$>
        observedMaterializedBoundary parameter publicRoot ftsSecret (next right.value.1)
          observations right.context.state right.remaining table right.value.2
    let delayedRun := finishDirectDelayedSelectedRootIndicator
      (canonicalizeDirectDelayedSelectedRootIndicator table observe)
      snapshots observations leftResult
    have hbase := relTriple_true realRun delayedRun
    have hsupported :=
      SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
        (fun result ↦ result ∈ support realRun) (fun _ hresult ↦ hresult)
    apply relTriple_post_mono hsupported
    intro real delayed hsupport hreal
    exfalso
    have hrealSupport : true ∈ support realRun := by simpa [hreal] using hsupport.2
    unfold realRun at hrealSupport
    rw [support_map] at hrealSupport
    obtain ⟨observed, hobserved, hindicator⟩ := hrealSupport
    have hgood : ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
        table ordinal target rightRoot observed := by
      change successfulObservedRootComparisonIndicator table ordinal target
        (observed, rightRoot) = true at hindicator
      rw [successfulObservedRootComparisonIndicator_eq_true_iff] at hindicator
      exact hindicator
    cases observed with
    | none =>
        simp [ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt,
          ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget,
          ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt] at hgood
    | some result =>
        obtain ⟨finalResult, hfinish⟩ := hgood.1.1.1
        exact not_missingChainStartHit_of_successful_observedMaterializedBoundary parameter
          publicRoot ftsSecret (next right.value.1) observations right.context.state
          right.remaining table right.value.2 result finalResult hobserved hfinish
          (by rw [hdoomed.2] at hmissing; exact hmissing)

set_option maxRecDepth 100000 in
theorem relTriple_bind_observed_finishDirectDelayed_of_firstStopped
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (next : α → OracleComp (OracleWorld + SigningSpec) RetainedRestResult)
    (observe : DeferredContext → Nat → (α × SplitHashCache) →
      List PlannedProbeSnapshot → List CleanProbeObservation → ProbComp Bool)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (leftStep : ProbComp (DirectWitnessResult (α × SplitHashCache)))
    (rightStep : ProbComp (Option (ObservedCleanRunResult (α × SplitHashCache))))
    (hstep : RelTriple leftStep rightStep
      (WitnessObservedFirstStoppedStepRel table observations))
    (hrecursive : ∀ left right,
      DirectWitnessResult.done left ∈ support leftStep →
      some (observedResolvedResult observations right) ∈ support rightStep →
      OrdinaryMaterializedRunEq table left right →
      RelTriple
        ((successfulObservedRootComparisonIndicator table ordinal target ∘
            fun observed ↦ (observed, rightRoot)) <$>
          observedMaterializedBoundary parameter publicRoot ftsSecret (next right.value.1)
            observations right.context.state right.remaining table right.value.2)
        (canonicalizeDirectDelayedSelectedRootIndicator table observe left.context left.remaining
          (left.value.1, left.value.2) snapshots observations)
        SuccessfulObservedIndicatorRel) :
    RelTriple
      (rightStep >>= fun result =>
        match result with
        | none => pure false
        | some result =>
            (successfulObservedRootComparisonIndicator table ordinal target ∘
                fun observed ↦ (observed, rightRoot)) <$>
              observedMaterializedBoundary parameter publicRoot ftsSecret (next result.value.1)
                result.observations result.state result.remaining table result.value.2)
      (leftStep >>= finishDirectDelayedSelectedRootIndicator
        (canonicalizeDirectDelayedSelectedRootIndicator table observe)
        snapshots observations)
      SuccessfulObservedIndicatorRel := by
  have hleftSupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hstep
      (fun result ↦ result ∈ support leftStep) (fun _ hresult ↦ hresult)
  have hbothSupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleftSupported
  apply relTriple_bind (relTriple_symm hbothSupported)
  intro rightResult leftResult hrelation
  rcases hrelation with ⟨⟨hrelation, hrightSupport⟩, hleftSupport⟩
  exact relTriple_observed_finishDirectDelayed_of_firstStopped ordinal parameter publicRoot
    rightRoot ftsSecret table target next observe snapshots observations leftResult rightResult
    hrelation (by
      intro left right hleft hright hclean
      subst leftResult
      subst rightResult
      exact hrecursive left right hrightSupport hleftSupport hclean)

end SphincsSecurity.Concrete.OtsProbeSimulation
