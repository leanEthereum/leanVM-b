import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveNormalizeSupport

/-!
# Structural adaptive normalization

This module lifts eager target resolution through an arbitrary outer computation. The delayed
indicator can only succeed when every observation preceding its selected ordinal is hit-free, which
supplies the invariant needed by the nonselected hash step.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

theorem no_existingHiddenHit_of_prefix_of_firstExistingHiddenHitAt
    (before : List CleanProbeObservation) (result : ObservedCleanRunResult α)
    (ordinal : Nat) (hprefix : before <+: result.observations)
    (hlength : before.length ≤ ordinal)
    (hfirst : FirstExistingHiddenHitAt result ordinal) :
    ∀ observation ∈ before, ¬observation.ExistingHiddenHit := by
  intro observation hobservation
  obtain ⟨beforeIndex, hget⟩ := List.mem_iff_get.mp hobservation
  obtain ⟨selected, hselected, _hhit, hearlier⟩ := hfirst
  let resultIndex : Fin result.observations.length :=
    ⟨beforeIndex.val, beforeIndex.isLt.trans_le hprefix.length_le⟩
  have hresultGet : result.observations.get resultIndex = observation := by
    rw [← hget]
    exact (hprefix.getElem beforeIndex.isLt).symm
  have hbeforeOrdinal : resultIndex.val < ordinal := beforeIndex.isLt.trans_le hlength
  rw [← hresultGet]
  exact hearlier resultIndex hbeforeOrdinal

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem no_existingHiddenHit_of_true_mem_directDelayedSelectedRootIndicator
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (haligned : observations.length = snapshots.length)
    (hlength : snapshots.length ≤ ordinal)
    (htrue : true ∈ support
      (directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
        computation snapshots observations context fuel cache)) :
    ∀ observation ∈ observations, ¬observation.ExistingHiddenHit := by
  classical
  induction computation using OracleComp.inductionOn generalizing
      snapshots observations context fuel cache with
  | pure value =>
      have hbefore : ¬ordinal < snapshots.length := by omega
      simp [directDelayedSelectedRootIndicator, hbefore] at htrue
  | query_bind query next ih =>
      have hbefore : ¬ordinal < snapshots.length := by omega
      have continueAfter
          (runComputation : OracleComp (LazyRevealProbe.World Coordinate)
            ((OracleWorld + SigningSpec).Range query × SplitHashCache))
          (nextSnapshots : List PlannedProbeSnapshot)
          (nextObservations : List CleanProbeObservation)
          (hnextAligned : nextObservations.length = nextSnapshots.length)
          (hnextLength : nextSnapshots.length ≤ ordinal)
          (hnextTrue : true ∈ support
            (runDirectResolvedWitnessFromTable context fuel table runComputation >>=
              finishDirectDelayedSelectedRootIndicator
                (canonicalizeDirectDelayedSelectedRootIndicator table
                  (fun nextContext remaining value laterSnapshots laterObservations ↦
                    directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table
                      target rightRoot (next value.1) laterSnapshots laterObservations nextContext
                      remaining value.2))
                nextSnapshots nextObservations)) :
          ∀ observation ∈ nextObservations, ¬observation.ExistingHiddenHit := by
        rw [mem_support_bind_iff] at hnextTrue
        obtain ⟨result, hresult, hfinish⟩ := hnextTrue
        cases result with
        | stoppedFuel => simp [finishDirectDelayedSelectedRootIndicator] at hfinish
        | stoppedOrdinary => simp [finishDirectDelayedSelectedRootIndicator] at hfinish
        | stoppedPrivate witness => simp [finishDirectDelayedSelectedRootIndicator] at hfinish
        | done result =>
            let canonical := canonicalizeMaterializedValues table result.context
            unfold finishDirectDelayedSelectedRootIndicator at hfinish
            unfold canonicalizeDirectDelayedSelectedRootIndicator at hfinish
            change true ∈ support
              (if PrivateStructuralHit canonical then pure false
                else if PublishedValues result.context.state then
                  if DeferredCompletable table canonical then
                    directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table
                      target rightRoot (next result.value.1) nextSnapshots nextObservations
                      canonical result.remaining result.value.2
                  else pure false
                else pure false) at hfinish
            by_cases hhit : PrivateStructuralHit canonical
            · simp [hhit] at hfinish
            · by_cases hpublished : PublishedValues result.context.state
              · by_cases hcompletable : DeferredCompletable table canonical
                · simp only [hhit, hpublished, hcompletable, ↓reduceIte] at hfinish
                  exact ih result.value.1 nextSnapshots nextObservations canonical
                    result.remaining result.value.2 hnextAligned hnextLength hfinish
                · simp [hhit, hpublished, hcompletable] at hfinish
              · simp [hhit, hpublished] at hfinish
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              rw [directDelayedSelectedRootIndicator_uniform_eq ordinal parameter root ftsSecret
                table target rightRoot n next snapshots observations context fuel cache hbefore]
                at htrue
              exact continueAfter ((splitUniformImpl n).run cache) snapshots observations haligned
                hlength htrue
          | inr input =>
              let plan := purePlanProbingHashQuery parameter input context.state
              let candidate? := rootAwareCandidateForPlan? parameter input plan
              let nextSnapshots := appendPlannedSnapshot snapshots candidate? context
              let nextObservations := observationsAfterCandidate observations
                (materializedDeferredState context) candidate?
              have hnextAligned : nextObservations.length = nextSnapshots.length := by
                cases hcandidate : candidate? <;>
                  simp [nextSnapshots, nextObservations, observationsAfterCandidate,
                    appendPlannedSnapshot, hcandidate, haligned]
              by_cases hselected : ordinal < nextSnapshots.length
              · rw [directDelayedSelectedRootIndicator_hash_eq_selected ordinal parameter root
                  ftsSecret table target rightRoot input next snapshots observations context fuel
                  cache hbefore (by simpa [nextSnapshots, candidate?, plan] using hselected)] at htrue
                unfold delayedSelectedRootIndicator at htrue
                rw [mem_support_bind_iff] at htrue
                obtain ⟨resolvedOption, _hresolvedOption, hrest⟩ := htrue
                cases resolvedOption with
                | none => simp at hrest
                | some resolved =>
                    simp only at hrest
                    split at hrest
                    · rw [support_map] at hrest
                      obtain ⟨observed, hobserved, hindicator⟩ := hrest
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
                            ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt]
                            at hgood
                      | some result =>
                          obtain ⟨⟨⟨⟨_finalResult, _hfinish⟩, _hdoomed,
                            _selected, _hselected, hfirst, _hroot⟩, _hposition⟩,
                            _hcomparison⟩ := hgood
                          have hprefix := observations_prefix_of_mem_observedMaterializedBoundary
                            parameter root ftsSecret
                            (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
                              (Sum.inl (Sum.inr input))) >>= next)
                            observations
                            (materializedDeferredState resolved.toDeferredContext) fuel table cache
                            result hobserved
                          exact no_existingHiddenHit_of_prefix_of_firstExistingHiddenHitAt
                            observations result ordinal hprefix (by omega) hfirst
                    · simp at hrest
              · have hnextLength : nextSnapshots.length ≤ ordinal := by omega
                rw [directDelayedSelectedRootIndicator_hash_eq_not_selected ordinal parameter root
                  ftsSecret table target rightRoot input next snapshots observations context fuel
                  cache hbefore (by simpa [nextSnapshots, candidate?, plan] using hselected)] at htrue
                have hnextClean := continueAfter
                  ((probingHashQueryAfterPlan parameter input plan).run cache)
                  nextSnapshots nextObservations hnextAligned hnextLength htrue
                intro observation hobservation
                apply hnextClean observation
                cases hcandidate : candidate? with
                | none => simpa [nextObservations, observationsAfterCandidate, hcandidate]
                    using hobservation
                | some candidate =>
                    simp only [nextObservations, observationsAfterCandidate, hcandidate,
                      List.mem_append, List.mem_singleton]
                    exact Or.inl hobservation
      | inr message =>
          rw [directDelayedSelectedRootIndicator_signing_eq ordinal parameter root ftsSecret table
            target rightRoot message next snapshots observations context fuel cache hbefore] at htrue
          exact continueAfter ((maskedSign parameter root ftsSecret message).run cache) snapshots
            observations haligned hlength htrue

set_option maxRecDepth 100000 in
theorem no_existingHiddenHit_afterCandidate_of_true_mem_hash_not_selected
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (input : HashInput)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hbefore : ¬ordinal < snapshots.length)
    (hnotSelected : ¬ordinal <
      (appendPlannedSnapshot snapshots
        (rootAwareCandidateForPlan? parameter input
          (purePlanProbingHashQuery parameter input context.state)) context).length)
    (haligned : observations.length = snapshots.length)
    (htrue : true ∈ support
      (directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
        (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
          (Sum.inl (Sum.inr input))) >>= next)
        snapshots observations context fuel cache)) :
    ∀ observation ∈
      observationsAfterCandidate observations (materializedDeferredState context)
        (rootAwareCandidateForPlan? parameter input
          (purePlanProbingHashQuery parameter input context.state)),
      ¬observation.ExistingHiddenHit := by
  classical
  let plan := purePlanProbingHashQuery parameter input context.state
  let candidate? := rootAwareCandidateForPlan? parameter input plan
  let nextSnapshots := appendPlannedSnapshot snapshots candidate? context
  let nextObservations := observationsAfterCandidate observations
    (materializedDeferredState context) candidate?
  have hnextAligned : nextObservations.length = nextSnapshots.length := by
    cases hcandidate : candidate? <;>
      simp [nextSnapshots, nextObservations, observationsAfterCandidate,
        appendPlannedSnapshot, hcandidate, haligned]
  have hnextLength : nextSnapshots.length ≤ ordinal := by
    simpa [nextSnapshots, candidate?, plan] using Nat.le_of_not_gt hnotSelected
  rw [directDelayedSelectedRootIndicator_hash_eq_not_selected ordinal parameter root ftsSecret
    table target rightRoot input next snapshots observations context fuel cache hbefore
    hnotSelected] at htrue
  rw [mem_support_bind_iff] at htrue
  obtain ⟨result, hresult, hfinish⟩ := htrue
  cases result with
  | stoppedFuel => simp [finishDirectDelayedSelectedRootIndicator] at hfinish
  | stoppedOrdinary => simp [finishDirectDelayedSelectedRootIndicator] at hfinish
  | stoppedPrivate witness => simp [finishDirectDelayedSelectedRootIndicator] at hfinish
  | done result =>
      let canonical := canonicalizeMaterializedValues table result.context
      unfold finishDirectDelayedSelectedRootIndicator at hfinish
      unfold canonicalizeDirectDelayedSelectedRootIndicator at hfinish
      change true ∈ support
        (if PrivateStructuralHit canonical then pure false
          else if PublishedValues result.context.state then
            if DeferredCompletable table canonical then
              directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
                rightRoot (next result.value.1) nextSnapshots nextObservations canonical
                result.remaining result.value.2
            else pure false
          else pure false) at hfinish
      by_cases hhit : PrivateStructuralHit canonical
      · simp [hhit] at hfinish
      · by_cases hpublished : PublishedValues result.context.state
        · by_cases hcompletable : DeferredCompletable table canonical
          · simp only [hhit, hpublished, hcompletable, ↓reduceIte] at hfinish
            exact no_existingHiddenHit_of_true_mem_directDelayedSelectedRootIndicator ordinal
              parameter root ftsSecret table target rightRoot (next result.value.1)
              nextSnapshots nextObservations canonical result.remaining result.value.2
              hnextAligned hnextLength hfinish
          · simp [hhit, hpublished, hcompletable] at hfinish
        · simp [hhit, hpublished] at hfinish

theorem resolveDeferredPositionValue_output_eq_of_positionValue
    (position : Position) (context : DeferredContext) (known : HashOutput)
    (resolved : DeferredResolution)
    (hknown : context.positionValue position = some known)
    (hresolved : some resolved ∈ support
      (resolveDeferredPositionValue position context)) :
    resolved.output = known := by
  cases hstate : context.state.values (.position position) with
  | some output =>
      have hknownOutput : output = known := by
        simpa [DeferredContext.positionValue, hstate] using hknown
      unfold resolveDeferredPositionValue at hresolved
      simp only [hstate] at hresolved
      by_cases hhit : context.state.hitAt (.position position) output
      · simp [hhit] at hresolved
      · simp [hhit] at hresolved
        subst resolved
        exact hknownOutput
  | none =>
      cases hprivate : context.values position with
      | some output =>
          have hknownOutput : output = known := by
            simpa [DeferredContext.positionValue, hstate, hprivate] using hknown
          unfold resolveDeferredPositionValue at hresolved
          simp only [hstate, hprivate] at hresolved
          by_cases hhit : context.state.hitAt (.position position) output
          · simp [hhit] at hresolved
          · simp [hhit] at hresolved
            subst resolved
            exact hknownOutput
      | none =>
          simp [DeferredContext.positionValue, hstate, hprivate] at hknown

theorem existingHiddenHit_cleanProbeObservation_materializedDeferredState_resolved
    (target : Position) (context : DeferredContext) (resolved : DeferredResolution)
    (hresolved : some resolved ∈ support
      (resolveDeferredPositionValue target context))
    (candidate : Probe)
    (hhit : (cleanProbeObservation (materializedDeferredState context)
      candidate.coordinate candidate.candidate).ExistingHiddenHit) :
    (cleanProbeObservation (materializedDeferredState resolved.toDeferredContext)
      candidate.coordinate candidate.candidate).ExistingHiddenHit := by
  rw [cleanProbeObservation_materializedDeferredState_resolved target context resolved hresolved]
  by_cases hcoordinate : candidate.coordinate = .position target
  · rw [installPositionValueAtProbe_existingHiddenHit_iff_of_target target resolved.output _
      hcoordinate]
    unfold CleanProbeObservation.ExistingHiddenHit at hhit
    simp only [cleanProbeObservation, decide_eq_false_iff_not] at hhit ⊢
    refine ⟨hhit.1, ?_⟩
    obtain ⟨known, hknown, hdigest⟩ := hhit.2
    have hpositionValue : context.positionValue target = some known := by
      simpa [materializedDeferredState_position, hcoordinate] using hknown
    have houtput := resolveDeferredPositionValue_output_eq_of_positionValue target context known
      resolved hpositionValue hresolved
    simpa [houtput] using hdigest
  · rw [installPositionValueAtProbe_existingHiddenHit_iff_of_ne target resolved.output _
      hcoordinate]
    exact hhit

theorem not_clean_observationsAfterCandidate_resolved
    (target : Position) (context : DeferredContext) (resolved : DeferredResolution)
    (hresolved : some resolved ∈ support
      (resolveDeferredPositionValue target context))
    (observations : List CleanProbeObservation) (candidate? : Option Probe)
    (hclean : ∀ observation ∈ observations, ¬observation.ExistingHiddenHit)
    (hdirty : ¬∀ observation ∈
      observationsAfterCandidate observations (materializedDeferredState context) candidate?,
        ¬observation.ExistingHiddenHit) :
    ¬∀ observation ∈
      observationsAfterCandidate observations
        (materializedDeferredState resolved.toDeferredContext) candidate?,
        ¬observation.ExistingHiddenHit := by
  cases candidate? with
  | none => simpa [observationsAfterCandidate] using hdirty
  | some candidate =>
      intro hresolvedClean
      apply hdirty
      intro observation hobservation
      simp only [observationsAfterCandidate, List.mem_append, List.mem_singleton] at hobservation
      rcases hobservation with hold | rfl
      · exact hclean observation hold
      · intro hhit
        exact hresolvedClean
          (cleanProbeObservation (materializedDeferredState resolved.toDeferredContext)
            candidate.coordinate candidate.candidate)
          (by simp [observationsAfterCandidate])
          (existingHiddenHit_cleanProbeObservation_materializedDeferredState_resolved
            target context resolved hresolved candidate hhit)

theorem relTriple_eq_false_of_true_not_mem
    (run : ProbComp Bool) (hfalse : true ∉ support run) :
    RelTriple run (pure false : ProbComp Bool) (EqRel Bool) := by
  have hleft := SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support
    (relTriple_true run (pure false : ProbComp Bool))
    (fun value ↦ value ∈ support run) (fun _ hvalue ↦ hvalue)
  have hboth :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleft
  apply relTriple_post_mono hboth
  intro left right hrelation
  have hright : right = false := by simpa using hrelation.2
  subst right
  cases left with
  | false => rfl
  | true => exact (hfalse hrelation.1.2).elim

set_option maxRecDepth 100000 in
theorem true_not_mem_eagerDirectDelayed_hash_of_dirty_not_selected
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (input : HashInput)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hbefore : ¬ordinal < snapshots.length)
    (hnotSelected : ¬ordinal <
      (appendPlannedSnapshot snapshots
        (rootAwareCandidateForPlan? parameter input
          (purePlanProbingHashQuery parameter input context.state)) context).length)
    (haligned : observations.length = snapshots.length)
    (hclean : ∀ observation ∈ observations, ¬observation.ExistingHiddenHit)
    (hdirty : ¬∀ observation ∈
      observationsAfterCandidate observations (materializedDeferredState context)
        (rootAwareCandidateForPlan? parameter input
          (purePlanProbingHashQuery parameter input context.state)),
        ¬observation.ExistingHiddenHit) :
    true ∉ support
      (eagerDirectDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
        rightRoot
        (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
          (Sum.inl (Sum.inr input))) >>= next)
        snapshots observations context fuel cache) := by
  intro htrue
  unfold eagerDirectDelayedSelectedRootIndicator at htrue
  simp only [hbefore, ↓reduceIte] at htrue
  rw [mem_support_bind_iff] at htrue
  obtain ⟨resolvedOption, hresolvedOption, hrest⟩ := htrue
  cases resolvedOption with
  | none => simp at hrest
  | some resolved =>
      have hvalues := resolveDeferredPositionValue_preserves_state_values target context resolved
        hresolvedOption
      have hplan : purePlanProbingHashQuery parameter input resolved.state =
          purePlanProbingHashQuery parameter input context.state :=
        purePlanProbingHashQuery_eq_of_values_eq hvalues parameter input
      have hnotSelectedResolved : ¬ordinal <
          (appendPlannedSnapshot snapshots
            (rootAwareCandidateForPlan? parameter input
              (purePlanProbingHashQuery parameter input resolved.state))
            resolved.toDeferredContext).length := by
        rw [hplan]
        have hlength :
            (appendPlannedSnapshot snapshots
                (rootAwareCandidateForPlan? parameter input
                  (purePlanProbingHashQuery parameter input context.state))
                resolved.toDeferredContext).length =
              (appendPlannedSnapshot snapshots
                (rootAwareCandidateForPlan? parameter input
                  (purePlanProbingHashQuery parameter input context.state)) context).length := by
          cases rootAwareCandidateForPlan? parameter input
              (purePlanProbingHashQuery parameter input context.state) <;>
            simp [appendPlannedSnapshot]
        rw [hlength]
        exact hnotSelected
      have hresolvedDirty := not_clean_observationsAfterCandidate_resolved target context resolved
        hresolvedOption observations
        (rootAwareCandidateForPlan? parameter input
          (purePlanProbingHashQuery parameter input context.state)) hclean hdirty
      have hresolvedClean :=
        no_existingHiddenHit_afterCandidate_of_true_mem_hash_not_selected ordinal parameter root
          ftsSecret table target rightRoot input next snapshots observations
          resolved.toDeferredContext fuel cache hbefore hnotSelectedResolved haligned (by
            simpa [hplan] using hrest)
      apply hresolvedDirty
      simpa [hplan] using hresolvedClean

set_option maxRecDepth 100000 in
theorem relTriple_directDelayed_eagerDirectDelayed_hash_not_selected_general
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (input : HashInput)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hbefore : ¬ordinal < snapshots.length)
    (hnotSelected : ¬ordinal <
      (appendPlannedSnapshot snapshots
        (rootAwareCandidateForPlan? parameter input
          (purePlanProbingHashQuery parameter input context.state)) context).length)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (haligned : observations.map CleanProbeObservation.toProbe =
      snapshots.map PlannedProbeSnapshot.toProbe)
    (hclean : ∀ observation ∈ observations, ¬observation.ExistingHiddenHit)
    (hsynchronized :
      (∀ observation ∈
          observationsAfterCandidate observations (materializedDeferredState context)
            (rootAwareCandidateForPlan? parameter input
              (purePlanProbingHashQuery parameter input context.state)),
          ¬observation.ExistingHiddenHit) →
        ObserverSynchronized table
          (negatedDirectDelayedObserve
            (fun nextContext remaining (value : HashOutput × SplitHashCache)
                laterSnapshots laterObservations ↦
              directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
                rightRoot (next value.1) laterSnapshots laterObservations nextContext remaining
                value.2)
            (appendPlannedSnapshot snapshots
              (rootAwareCandidateForPlan? parameter input
                (purePlanProbingHashQuery parameter input context.state)) context)
            (observationsAfterCandidate observations (materializedDeferredState context)
              (rootAwareCandidateForPlan? parameter input
                (purePlanProbingHashQuery parameter input context.state)))))
    (hneutral :
      (∀ observation ∈
          observationsAfterCandidate observations (materializedDeferredState context)
            (rootAwareCandidateForPlan? parameter input
              (purePlanProbingHashQuery parameter input context.state)),
          ¬observation.ExistingHiddenHit) →
        ObserverPositionNeutral table
          (negatedDirectDelayedObserve
            (fun nextContext remaining (value : HashOutput × SplitHashCache)
                laterSnapshots laterObservations ↦
              directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
                rightRoot (next value.1) laterSnapshots laterObservations nextContext remaining
                value.2)
            (appendPlannedSnapshot snapshots
              (rootAwareCandidateForPlan? parameter input
                (purePlanProbingHashQuery parameter input context.state)) context)
            (observationsAfterCandidate observations (materializedDeferredState context)
              (rootAwareCandidateForPlan? parameter input
                (purePlanProbingHashQuery parameter input context.state))))) :
    RelTriple
      (directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
        (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
          (Sum.inl (Sum.inr input))) >>= next)
        snapshots observations context fuel cache)
      (eagerDirectDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
        rightRoot
        (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
          (Sum.inl (Sum.inr input))) >>= next)
        snapshots observations context fuel cache)
      (EqRel Bool) := by
  have hlength : observations.length = snapshots.length := by
    simpa only [List.length_map] using congrArg List.length haligned
  let nextObservations := observationsAfterCandidate observations
    (materializedDeferredState context)
    (rootAwareCandidateForPlan? parameter input
      (purePlanProbingHashQuery parameter input context.state))
  by_cases hnextClean : ∀ observation ∈ nextObservations,
      ¬observation.ExistingHiddenHit
  · letI := hsynchronized (by simpa [nextObservations] using hnextClean)
    letI := hneutral (by simpa [nextObservations] using hnextClean)
    have hnextAligned :
        nextObservations.map CleanProbeObservation.toProbe =
          (appendPlannedSnapshot snapshots
            (rootAwareCandidateForPlan? parameter input
              (purePlanProbingHashQuery parameter input context.state)) context).map
              PlannedProbeSnapshot.toProbe := by
      cases hcandidate : rootAwareCandidateForPlan? parameter input
          (purePlanProbingHashQuery parameter input context.state) <;>
        simp [nextObservations, observationsAfterCandidate, appendPlannedSnapshot, hcandidate,
          CleanProbeObservation.toProbe, cleanProbeObservation, haligned]
    exact relTriple_directDelayed_eagerDirectDelayed_hash_not_selected ordinal parameter root
      ftsSecret table target rightRoot input next snapshots observations context fuel cache
      hbefore hnotSelected hvalid hcompletable hnextAligned
      (by simpa [nextObservations] using hnextClean)
  · have hdirectFalse : true ∉ support
        (directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
          (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
            (Sum.inl (Sum.inr input))) >>= next)
          snapshots observations context fuel cache) := by
      intro htrue
      apply hnextClean
      exact no_existingHiddenHit_afterCandidate_of_true_mem_hash_not_selected ordinal parameter
        root ftsSecret table target rightRoot input next snapshots observations context fuel cache
        hbefore hnotSelected hlength htrue
    have hleft := relTriple_eq_false_of_true_not_mem _ hdirectFalse
    have hright := relTriple_eq_false_of_true_not_mem _
      (true_not_mem_eagerDirectDelayed_hash_of_dirty_not_selected ordinal parameter root ftsSecret
        table target rightRoot input next snapshots observations context fuel cache hbefore
        hnotSelected hlength hclean (by simpa [nextObservations] using hnextClean))
    have hglued := SphincsSecurity.relTriple_trans_exists hleft (relTriple_symm hright)
    apply relTriple_post_mono hglued
    intro left right hrelation
    obtain ⟨middle, hleftEq, hrightEq⟩ := hrelation
    exact hleftEq.trans hrightEq.symm

end SphincsSecurity.Concrete.OtsProbeSimulation
