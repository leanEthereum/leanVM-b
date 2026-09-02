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

theorem cleanProbeObservation_materializedDeferredState_eq_of_position
    (table : OtsSecretIndex → HashOutput) (left right : DeferredContext)
    (position : Position) (candidate : Digest)
    (hcontext : FinalizationContextLE table left right)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hrightMaterialized : right = directDeferredContext right.state) :
    cleanProbeObservation (materializedDeferredState left) (.position position) candidate =
      cleanProbeObservation right.state (.position position) candidate := by
  unfold cleanProbeObservation
  have hvalue := congrFun hcontext.view.valueEq (.position position)
  simp only [resolvedCompletionValue] at hvalue
  rw [hrightMaterialized] at hvalue
  simp only [directDeferredContext, directDeferredValues, DeferredContext.positionValue] at hvalue
  have hvalue' : left.positionValue position =
      right.state.values (.position position) := by
    cases hrightValue : right.state.values (.position position) <;>
      simpa [DeferredContext.positionValue, hrightValue] using hvalue
  simp only [materializedDeferredState_position, hvalue', materializedDeferredState_revealed,
    hrevealed]

set_option maxRecDepth 100000 in
theorem selectedHash_goodForRoots
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (input : HashInput)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (left right : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (candidate : Probe)
    (hcandidate : rootAwareCandidateForPlan? parameter input
      (purePlanProbingHashQuery parameter input left.state) = some candidate)
    (hordinal : snapshots.length = ordinal)
    (hcontext : FinalizationContextLE table left right)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hrightMaterialized : right = directDeferredContext right.state)
    (hcanonical : CanonicalMaterializedValues table left)
    (haligned : SnapshotsObservedAt table snapshots observations)
    (hbefore : SnapshotsBefore snapshots left)
    (htracked : CleanProbeObservationsTrackedBy observations right.state)
    (hnoHit : ∀ observation ∈ observations, ¬observation.ExistingHiddenHit)
    (hleftCovered : PendingCoveredBy
      (snapshots.map PlannedProbeSnapshot.toProbe) left)
    (result : ObservedCleanRunResult (α × SplitHashCache))
    (hresult : some result ∈ support
      (observedMaterializedBoundary parameter publicRoot ftsSecret
        (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
          (Sum.inl (Sum.inr input))) >>= next)
        observations right.state fuel table cache))
    (hgood : ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
      table ordinal target rightRoot (some result)) :
    ∃ output,
      let selection : PrivateOrdinalSelection :=
        ⟨candidate, left,
          (snapshots ++ [(⟨candidate, left⟩ : PlannedProbeSnapshot)]).map
            PlannedProbeSnapshot.toProbe⟩
      selection.GoodForRoots target output rightRoot ordinal ∧
        PendingCoveredBy (selection.candidates.take ordinal) selection.context := by
  have hobservationLength : observations.length = ordinal :=
    haligned.length_eq.symm.trans hordinal
  have hrightValues :
      (materializedCanonicalContext table right.state).state.values = left.state.values := by
    unfold materializedCanonicalContext
    rw [← hrightMaterialized]
    exact canonicalized_right_values_eq_of_finalizationContextLE hcontext hrevealed hcanonical
  have hplanEq :
      purePlanProbingHashQuery parameter input
          (materializedCanonicalContext table right.state).state =
        purePlanProbingHashQuery parameter input left.state :=
    purePlanProbingHashQuery_eq_of_values_eq hrightValues parameter input
  have hqueryCandidate : rootAwareCandidateForPlan? parameter input
      (purePlanProbingHashQuery parameter input
        (materializedCanonicalContext table right.state).state) = some candidate := by
    rw [hplanEq]
    exact hcandidate
  obtain ⟨⟨⟨⟨_finalResult, _hfinish⟩, _hdoomed,
    selected, hselected, hfirst, _hroot⟩, hposition⟩, hcomparison⟩ := hgood
  have hobservation :=
    selected_observation_eq_of_mem_observedMaterializedBoundary_hash_query ordinal parameter
      publicRoot ftsSecret input next observations right.state fuel table cache candidate
      hobservationLength hqueryCandidate result hresult selected hselected
  obtain ⟨first, hfirstOrdinal, hfirstHit, _hbeforeFirst⟩ := hfirst
  have hfirstSelected : first = selected :=
    Fin.ext (hfirstOrdinal.trans hselected.symm)
  subst first
  rw [ExistingHiddenHitAtOrdinal, hobservation] at hfirstHit
  obtain ⟨hselectedHidden, output, hselectedValue, hselectedCandidate⟩ := hfirstHit
  have hrightValue : right.state.values candidate.coordinate = some output := by
    simpa [cleanProbeObservation] using hselectedValue
  have hcandidateDigest : truncateHash output = candidate.candidate := by
    simpa [cleanProbeObservation] using hselectedCandidate
  have hselectedLt : ordinal < result.observations.length := by
    rw [← hselected]
    exact selected.isLt
  have hselectedIndex :
      (⟨ordinal, hselectedLt⟩ : Fin result.observations.length) = selected :=
    Fin.ext hselected.symm
  have htargetData :
      (result.observations.get selected).coordinate = .position target ∧ IsLayerRoot target := by
    simp only [observedFirstLayerRootPosition?, hselectedLt, ↓reduceDIte] at hposition
    rw [candidateLayerRootPosition?_eq_some_iff, hselectedIndex] at hposition
    exact hposition
  have hcandidateCoordinate : candidate.coordinate = .position target := by
    rw [hobservation] at htargetData
    simpa [cleanProbeObservation] using htargetData.1
  have hcandidateEq : candidate = ⟨.position target, truncateHash output⟩ := by
    cases candidate
    simp only [Probe.mk.injEq]
    exact ⟨hcandidateCoordinate, hcandidateDigest.symm⟩
  have hrightHidden : candidate.coordinate ∉ right.state.revealed := by
    simpa [cleanProbeObservation, decide_eq_false_iff_not] using hselectedHidden
  have hleftHidden : Coordinate.position target ∉ left.state.revealed := by
    rw [← hcandidateCoordinate, hrevealed]
    exact hrightHidden
  have hleftState : left.state.values (.position target) = none :=
    canonical_value_none_of_not_revealed hcanonical hleftHidden
  have hrightPositionValue : right.state.values (.position target) = some output := by
    rw [← hcandidateCoordinate]
    exact hrightValue
  have hleftPrivate : left.values target = some output :=
    hcontext.view.privateValue_of_left_hidden_of_right_materialized target output hleftState
      hrightPositionValue
  have hleftCandidateHidden : candidate.coordinate ∉ left.state.revealed := by
    simpa [hcandidateCoordinate] using hleftHidden
  have hactualAvoid := candidatesAvoidRoot_of_aligned_tracked table snapshots observations
    candidate left right hbefore hcontext hrightMaterialized hnoHit haligned htracked target output
    hcandidateEq hleftState hleftPrivate hleftCandidateHidden
  have hprefix := observations_prefix_of_mem_observedMaterializedBoundary parameter publicRoot
    ftsSecret
    (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
      (Sum.inl (Sum.inr input))) >>= next)
    observations right.state fuel table cache result hresult
  have htake : result.observations.take ordinal = observations := by
    obtain ⟨tail, htail⟩ := hprefix
    rw [← htail, List.take_append_of_le_length]
    · simpa [hobservationLength]
    · omega
  have hcomparison' : CandidatesAvoidRoot target rightRoot
      (snapshots.map PlannedProbeSnapshot.toProbe) := by
    simpa [observedPrefixProbes, htake, haligned.map_toProbe_eq] using hcomparison
  let selection : PrivateOrdinalSelection :=
    ⟨candidate, left,
      (snapshots ++ [(⟨candidate, left⟩ : PlannedProbeSnapshot)]).map
        PlannedProbeSnapshot.toProbe⟩
  refine ⟨output, ?_, ?_⟩
  · refine ⟨hcandidateEq, hleftState, hleftHidden, hleftPrivate, ?_⟩
    intro earlier hearlier
    have hearlier' : earlier ∈ snapshots.map PlannedProbeSnapshot.toProbe := by
      simpa [selection, hordinal] using hearlier
    exact ⟨hactualAvoid earlier hearlier', hcomparison' earlier hearlier'⟩
  · simpa [selection, hordinal] using hleftCovered

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
theorem relTriple_indicator_observedMaterializedBoundary_false_of_ordinal_lt
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat) (cache : SplitHashCache)
    (other : ProbComp Bool)
    (hordinal : ordinal < observations.length)
    (hnoHit : ∀ observation ∈ observations, ¬observation.ExistingHiddenHit) :
    RelTriple
      ((successfulObservedRootComparisonIndicator table ordinal target ∘
          fun observed ↦ (observed, rightRoot)) <$>
        observedMaterializedBoundary parameter publicRoot ftsSecret computation observations
          state fuel table cache)
      other SuccessfulObservedIndicatorRel := by
  let real :=
    (successfulObservedRootComparisonIndicator table ordinal target ∘
        fun observed ↦ (observed, rightRoot)) <$>
      observedMaterializedBoundary parameter publicRoot ftsSecret computation observations
        state fuel table cache
  have hbase := relTriple_true real other
  have hsupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun result ↦ result ∈ support real) (fun _ hresult ↦ hresult)
  apply relTriple_post_mono hsupported
  intro realResult _otherResult hsupport htrue
  have hrealSupport : true ∈ support real := by simpa [htrue] using hsupport.2
  unfold real at hrealSupport
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
      obtain ⟨⟨⟨⟨_finalResult, _hfinish⟩, _hdoomed,
        _selected, _hselected, hfirst, _hroot⟩, _hposition⟩, _hcomparison⟩ := hgood
      obtain ⟨first, hfirstOrdinal, hfirstHit, _hbefore⟩ := hfirst
      have hprefix := observations_prefix_of_mem_observedMaterializedBoundary parameter
        publicRoot ftsSecret computation observations state fuel table cache result hobserved
      let initial : Fin observations.length := ⟨ordinal, hordinal⟩
      have hresultOrdinal : ordinal < result.observations.length :=
        hordinal.trans_le hprefix.length_le
      let resultIndex : Fin result.observations.length := ⟨ordinal, hresultOrdinal⟩
      have hfirstEq : first = resultIndex := Fin.ext hfirstOrdinal
      subst first
      have hget : observations[initial.val] = result.observations[resultIndex.val] :=
        hprefix.getElem hordinal
      have hinitialHit : (observations.get initial).ExistingHiddenHit := by
        simpa [ExistingHiddenHitAtOrdinal, initial, resultIndex, ← hget] using hfirstHit
      exact (hnoHit (observations.get initial) (List.get_mem observations initial)
        hinitialHit).elim

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
