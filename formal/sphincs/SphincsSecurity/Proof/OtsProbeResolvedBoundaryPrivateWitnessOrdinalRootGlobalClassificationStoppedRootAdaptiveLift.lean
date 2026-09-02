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

theorem relTriple_indicator_observedMaterializedBoundary_pure_false
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (value : α) (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat) (cache : SplitHashCache)
    (hnoHit : ∀ observation ∈ observations, ¬observation.ExistingHiddenHit) :
    RelTriple
      ((successfulObservedRootComparisonIndicator table ordinal target ∘
          fun observed ↦ (observed, rightRoot)) <$>
        observedMaterializedBoundary parameter publicRoot ftsSecret
          (pure value : OracleComp (OracleWorld + SigningSpec) α) observations state fuel table
          cache)
      (pure false : ProbComp Bool)
      SuccessfulObservedIndicatorRel := by
  rw [observedMaterializedBoundary, OracleComp.construct_pure]
  simp only [map_pure]
  apply relTriple_pure_pure
  intro hgood
  change successfulObservedRootComparisonIndicator table ordinal target
    (some ⟨state, fuel, (value, cache), table, observations⟩, rightRoot) = true at hgood
  rw [successfulObservedRootComparisonIndicator_eq_true_iff] at hgood
  obtain ⟨⟨⟨⟨_finalResult, _hfinish⟩, _hdoomed,
    selected, _hselected, hfirst, _hroot⟩, _hposition⟩, _hcomparison⟩ := hgood
  obtain ⟨first, _hfirstOrdinal, hfirstHit, _hbefore⟩ := hfirst
  exact (hnoHit (observations.get first) (List.get_mem observations first) hfirstHit).elim

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

set_option maxRecDepth 100000 in
theorem relTriple_bind_observed_finishDirectDelayed_of_probeFree
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (next : α → OracleComp (OracleWorld + SigningSpec) RetainedRestResult)
    (observe : DeferredContext → Nat → (α × SplitHashCache) →
      List PlannedProbeSnapshot → List CleanProbeObservation → ProbComp Bool)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftComputation rightComputation :
      OracleComp (LazyRevealProbe.World Coordinate) (α × SplitHashCache))
    (hbase : RelTriple
      (runDirectResolvedWitnessFromTable left leftFuel table leftComputation)
      (runDirectResolvedDetailedFromTable right rightFuel table rightComputation)
      (DirectWitnessMaterializedStableRunEq table))
    (hleftProbeFree : leftComputation.IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 0)
    (hrightProbeFree : rightComputation.IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 0)
    (hleftValid : left.Valid) (hleftCompletable : DeferredCompletable table left)
    (hrightMaterialized : right = directDeferredContext right.state)
    (htracked : CleanProbeObservationsTrackedBy observations right.state)
    (hcovered : CleanProbeObservationsCoverPending observations right.state)
    (hnoHit : ∀ observation ∈ observations, ¬observation.ExistingHiddenHit)
    (hbudget : rightFuel + right.state.pending.card < Fintype.card Digest)
    (hrecursive : ∀ leftResult rightResult,
      DirectWitnessResult.done leftResult ∈ support
        (runDirectResolvedWitnessFromTable left leftFuel table leftComputation) →
      some (observedResolvedResult observations rightResult) ∈ support
        (runObservedCleanFromTable observations right.state rightFuel table rightComputation) →
      OrdinaryMaterializedRunEq table leftResult rightResult →
      RelTriple
        ((successfulObservedRootComparisonIndicator table ordinal target ∘
            fun observed ↦ (observed, rightRoot)) <$>
          observedMaterializedBoundary parameter publicRoot ftsSecret
            (next rightResult.value.1) observations rightResult.context.state
            rightResult.remaining table rightResult.value.2)
        (canonicalizeDirectDelayedSelectedRootIndicator table observe leftResult.context
          leftResult.remaining (leftResult.value.1, leftResult.value.2) snapshots observations)
        SuccessfulObservedIndicatorRel) :
    RelTriple
      (runObservedCleanFromTable observations right.state rightFuel table rightComputation >>=
        fun result =>
          match result with
          | none => pure false
          | some result =>
              (successfulObservedRootComparisonIndicator table ordinal target ∘
                  fun observed ↦ (observed, rightRoot)) <$>
                observedMaterializedBoundary parameter publicRoot ftsSecret
                  (next result.value.1) result.observations result.state result.remaining table
                  result.value.2)
      (runDirectResolvedWitnessFromTable left leftFuel table leftComputation >>=
        finishDirectDelayedSelectedRootIndicator
          (canonicalizeDirectDelayedSelectedRootIndicator table observe)
          snapshots observations)
      SuccessfulObservedIndicatorRel := by
  have hstep := relTriple_runDirectResolvedWitness_observed_firstStopped_of_probeFree table
    leftComputation rightComputation observations left right leftFuel rightFuel hbase
    hleftProbeFree hrightProbeFree hleftValid hleftCompletable hrightMaterialized htracked hcovered
    hnoHit hbudget
  exact relTriple_bind_observed_finishDirectDelayed_of_firstStopped ordinal parameter publicRoot
    rightRoot ftsSecret table target next observe snapshots observations
    (runDirectResolvedWitnessFromTable left leftFuel table leftComputation)
    (runObservedCleanFromTable observations right.state rightFuel table rightComputation)
    hstep hrecursive

set_option maxRecDepth 100000 in
theorem relTriple_uniform_finishDirectDelayed
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (n : unifSpec.Domain)
    (next : Fin (n + 1) → OracleComp (OracleWorld + SigningSpec) RetainedRestResult)
    (observe : DeferredContext → Nat → (Fin (n + 1) × SplitHashCache) →
      List PlannedProbeSnapshot → List CleanProbeObservation → ProbComp Bool)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextLE table left right)
    (hfuel : leftFuel ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state)
    (htracked : CleanProbeObservationsTrackedBy observations right.state)
    (hcovered : CleanProbeObservationsCoverPending observations right.state)
    (hnoHit : ∀ observation ∈ observations, ¬observation.ExistingHiddenHit)
    (hbudget : rightFuel + right.state.pending.card < Fintype.card Digest)
    (hrecursive : ∀ leftResult rightResult,
      DirectWitnessResult.done leftResult ∈ support
        (runDirectResolvedWitnessFromTable left leftFuel table
          ((splitUniformImpl n).run leftCache)) →
      some (observedResolvedResult observations rightResult) ∈ support
        (runObservedCleanFromTable observations right.state rightFuel table
          ((splitUniformImpl n).run rightCache)) →
      OrdinaryMaterializedRunEq table leftResult rightResult →
      RelTriple
        ((successfulObservedRootComparisonIndicator table ordinal target ∘
            fun observed ↦ (observed, rightRoot)) <$>
          observedMaterializedBoundary parameter publicRoot ftsSecret
            (next rightResult.value.1) observations rightResult.context.state
            rightResult.remaining table rightResult.value.2)
        (canonicalizeDirectDelayedSelectedRootIndicator table observe leftResult.context
          leftResult.remaining (leftResult.value.1, leftResult.value.2) snapshots observations)
        SuccessfulObservedIndicatorRel) :
    RelTriple
      (runObservedCleanFromTable observations right.state rightFuel table
          ((splitUniformImpl n).run rightCache) >>= fun result ↦
        match result with
        | none => pure false
        | some result =>
            (successfulObservedRootComparisonIndicator table ordinal target ∘
                fun observed ↦ (observed, rightRoot)) <$>
              observedMaterializedBoundary parameter publicRoot ftsSecret
                (next result.value.1) result.observations result.state result.remaining table
                result.value.2)
      (runDirectResolvedWitnessFromTable left leftFuel table
          ((splitUniformImpl n).run leftCache) >>=
        finishDirectDelayedSelectedRootIndicator
          (canonicalizeDirectDelayedSelectedRootIndicator table observe)
          snapshots observations)
      SuccessfulObservedIndicatorRel := by
  apply relTriple_bind_observed_finishDirectDelayed_of_probeFree ordinal parameter publicRoot
    rightRoot ftsSecret table target next observe snapshots observations left right leftFuel
    rightFuel ((splitUniformImpl n).run leftCache) ((splitUniformImpl n).run rightCache)
  · exact (witnessMaterializedStableCouples_splitUniformImpl table n) left right leftFuel
      rightFuel leftCache rightCache hcontext hfuel hcache hrevealed hvalues hpublished
      hrightMaterialized
  · exact splitUniformImpl_probeFree n leftCache
  · exact splitUniformImpl_probeFree n rightCache
  · exact hcontext.leftValid
  · exact hcontext.leftCompletable
  · exact hrightMaterialized
  · exact htracked
  · exact hcovered
  · exact hnoHit
  · exact hbudget
  · exact hrecursive

set_option maxRecDepth 100000 in
theorem relTriple_sign_finishDirectDelayed
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (message : Message)
    (next : Option Signature →
      OracleComp (OracleWorld + SigningSpec) RetainedRestResult)
    (observe : DeferredContext → Nat →
      (Option Signature × SplitHashCache) →
      List PlannedProbeSnapshot → List CleanProbeObservation → ProbComp Bool)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcontext : FinalizationContextLE table left right)
    (hfuel : leftFuel ≤ rightFuel)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state)
    (htracked : CleanProbeObservationsTrackedBy observations right.state)
    (hcovered : CleanProbeObservationsCoverPending observations right.state)
    (hnoHit : ∀ observation ∈ observations, ¬observation.ExistingHiddenHit)
    (hbudget : rightFuel + right.state.pending.card < Fintype.card Digest)
    (hrecursive : ∀ leftResult rightResult,
      DirectWitnessResult.done leftResult ∈ support
        (runDirectResolvedWitnessFromTable left leftFuel table
          ((maskedSign parameter publicRoot ftsSecret message).run leftCache)) →
      some (observedResolvedResult observations rightResult) ∈ support
        (runObservedCleanFromTable observations right.state rightFuel table
          ((maskedSign parameter publicRoot ftsSecret message).run rightCache)) →
      OrdinaryMaterializedRunEq table leftResult rightResult →
      RelTriple
        ((successfulObservedRootComparisonIndicator table ordinal target ∘
            fun observed ↦ (observed, rightRoot)) <$>
          observedMaterializedBoundary parameter publicRoot ftsSecret
            (next rightResult.value.1) observations rightResult.context.state
            rightResult.remaining table rightResult.value.2)
        (canonicalizeDirectDelayedSelectedRootIndicator table observe leftResult.context
          leftResult.remaining (leftResult.value.1, leftResult.value.2) snapshots observations)
        SuccessfulObservedIndicatorRel) :
    RelTriple
      (runObservedCleanFromTable observations right.state rightFuel table
          ((maskedSign parameter publicRoot ftsSecret message).run rightCache) >>= fun result ↦
        match result with
        | none => pure false
        | some result =>
            (successfulObservedRootComparisonIndicator table ordinal target ∘
                fun observed ↦ (observed, rightRoot)) <$>
              observedMaterializedBoundary parameter publicRoot ftsSecret
                (next result.value.1) result.observations result.state result.remaining table
                result.value.2)
      (runDirectResolvedWitnessFromTable left leftFuel table
          ((maskedSign parameter publicRoot ftsSecret message).run leftCache) >>=
        finishDirectDelayedSelectedRootIndicator
          (canonicalizeDirectDelayedSelectedRootIndicator table observe)
          snapshots observations)
      SuccessfulObservedIndicatorRel := by
  have hresult := relTriple_bind_observed_finishDirectDelayed_of_probeFree ordinal parameter
    publicRoot rightRoot ftsSecret table target next observe snapshots observations left right
    leftFuel rightFuel ((maskedSign parameter publicRoot ftsSecret message).run leftCache)
    ((maskedSign parameter publicRoot ftsSecret message).run rightCache)
    ((witnessMaterializedStableCouples_maskedSign table parameter publicRoot ftsSecret message)
      left right leftFuel rightFuel leftCache rightCache hcontext hfuel hcache hrevealed hvalues
      hpublished hrightMaterialized)
    (maskedSign_probeFree parameter publicRoot ftsSecret message leftCache)
    (maskedSign_probeFree parameter publicRoot ftsSecret message rightCache)
    hcontext.leftValid hcontext.leftCompletable hrightMaterialized htracked hcovered hnoHit hbudget
    hrecursive
  convert hresult using 1 <;>
    try (apply bind_congr; intro result; cases result <;> rfl)

end SphincsSecurity.Concrete.OtsProbeSimulation
