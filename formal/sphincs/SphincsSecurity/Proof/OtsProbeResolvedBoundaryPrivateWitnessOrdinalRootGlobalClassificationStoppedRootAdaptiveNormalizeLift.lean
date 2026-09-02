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

noncomputable def negatedDirectDelayedComputationObserve
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) : ProbComp Bool :=
  Bool.not <$> directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
    rightRoot computation snapshots observations context fuel cache

theorem negatedDirectDelayedComputationObserve_pure_eq_true
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (value : α) (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hbefore : snapshots.length ≤ ordinal) :
    negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table target
        rightRoot (pure value) snapshots observations context fuel cache =
      pure true := by
  have hnotSelected : ¬ordinal < snapshots.length := by omega
  simp [negatedDirectDelayedComputationObserve, directDelayedSelectedRootIndicator,
    hnotSelected]

theorem negatedDirectDelayedComputationObserve_pure_observerSynchronized
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (value : α) (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (hbefore : snapshots.length ≤ ordinal) :
    ObserverSynchronized table
      (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table target
        rightRoot (pure value) snapshots observations) where
  eq_of_synchronized left right fuel cache _hcontext _hvalues _hrevealed := by
    rw [negatedDirectDelayedComputationObserve_pure_eq_true ordinal parameter root ftsSecret table
      target rightRoot value snapshots observations left fuel cache hbefore]
    rw [negatedDirectDelayedComputationObserve_pure_eq_true ordinal parameter root ftsSecret table
      target rightRoot value snapshots observations right fuel cache hbefore]

theorem negatedDirectDelayedComputationObserve_pure_observerPositionNeutral
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (value : α) (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (hbefore : snapshots.length ≤ ordinal) :
    ObserverPositionNeutral table
      (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table target
        rightRoot (pure value) snapshots observations) where
  eq_resolve position context fuel cache _hvalid _hcompletable _hensured := by
    rw [negatedDirectDelayedComputationObserve_pure_eq_true ordinal parameter root ftsSecret table
      target rightRoot value snapshots observations context fuel cache hbefore]
    calc
      _ = evalDist (resolveDeferredPositionValue position context >>= fun _ ↦
            (pure true : ProbComp Bool)) := by
          apply evalDist_bind_congr
          intro resolved _hresolved
          cases resolved with
          | none => rfl
          | some resolved =>
              simp only
              rw [negatedDirectDelayedComputationObserve_pure_eq_true ordinal parameter root
                ftsSecret table target rightRoot value snapshots observations
                resolved.toDeferredContext fuel cache hbefore]
      _ = _ := OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        (resolveDeferredPositionValue position context)
        (by simp [resolveDeferredPositionValue, LazyRevealProbe.sampleHashOutput])
        (pure true)

set_option maxRecDepth 100000 in
theorem evalDist_resolve_then_complement_runDirectWitness_finish_false
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      List CleanProbeObservation → ProbComp Bool)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    [ObserverSynchronized table
      (negatedDirectDelayedObserve observe snapshots observations)]
    [ObserverPositionNeutral table
      (negatedDirectDelayedObserve observe snapshots observations)] :
    evalDist (resolveDeferredPositionValue position context >>= fun resolved ↦
        match resolved with
        | none => pure true
        | some resolved => Bool.not <$>
            (runDirectResolvedWitnessFromTable resolved.toDeferredContext fuel table computation >>=
              finishDirectDelayedSelectedRootIndicator
                (canonicalizeDirectDelayedSelectedRootIndicator table observe)
                snapshots observations)) =
      evalDist (Bool.not <$>
        (runDirectResolvedWitnessFromTable context fuel table computation >>=
          finishDirectDelayedSelectedRootIndicator
            (canonicalizeDirectDelayedSelectedRootIndicator table observe)
            snapshots observations)) := by
  have hmove := evalDist_resolve_then_runDirectWitness_finish_false table position observe
    snapshots observations computation context fuel hvalid hcompletable
  calc
    _ = evalDist (Bool.not <$> (resolveDeferredPositionValue position context >>= fun resolved ↦
          match resolved with
          | none => pure false
          | some resolved =>
              runDirectResolvedWitnessFromTable resolved.toDeferredContext fuel table computation >>=
                finishDirectDelayedSelectedRootIndicator
                  (canonicalizeDirectDelayedSelectedRootIndicator table observe)
                  snapshots observations)) := by
        rw [map_bind]
        apply evalDist_bind_congr
        intro resolved _hresolved
        cases resolved <;> rfl
    _ = _ := by
      rw [evalDist_map, evalDist_map]
      exact congrArg (fun distribution => Bool.not <$> distribution) hmove

set_option maxRecDepth 100000 in
theorem negatedDirectDelayedComputationObserve_uniform_observerSynchronized
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (n : Nat) (next : Fin (n + 1) → OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (hbefore : snapshots.length ≤ ordinal)
    (hsynchronized : ∀ output,
      ObserverSynchronized table
        (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table target
          rightRoot (next output) snapshots observations))
    (hneutral : ∀ output,
      ObserverPositionNeutral table
        (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table target
          rightRoot (next output) snapshots observations)) :
    ObserverSynchronized table
      (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table target
        rightRoot
        (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
          (Sum.inl (Sum.inl n))) >>= next)
        snapshots observations) where
  eq_of_synchronized left right fuel cache hcontext hvalues hrevealed := by
    let observe := fun nextContext remaining (value : Fin (n + 1) × SplitHashCache)
        laterSnapshots laterObservations ↦
      directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
        (next value.1) laterSnapshots laterObservations nextContext remaining value.2
    letI : ObserverSynchronized table
        (negatedDirectDelayedObserve observe snapshots observations) := ⟨by
      intro nextLeft nextRight remaining value hnextContext hnextValues hnextRevealed
      simpa [negatedDirectDelayedObserve, negatedDirectDelayedComputationObserve, observe] using
        ObserverSynchronized.eq_of_synchronized
          (table := table)
          (observe := negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret
            table target rightRoot (next value.1) snapshots observations)
          nextLeft nextRight remaining value.2 hnextContext hnextValues hnextRevealed⟩
    letI : ObserverPositionNeutral table
        (negatedDirectDelayedObserve observe snapshots observations) := ⟨by
      intro position nextContext remaining value hvalid hcompletable hensured
      simpa [negatedDirectDelayedObserve, negatedDirectDelayedComputationObserve, observe] using
        ObserverPositionNeutral.eq_resolve
          (table := table)
          (observe := negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret
            table target rightRoot (next value.1) snapshots observations)
          position nextContext remaining value.2 hvalid hcompletable hensured⟩
    have hnotSelected : ¬ordinal < snapshots.length := by omega
    unfold negatedDirectDelayedComputationObserve
    rw [directDelayedSelectedRootIndicator_uniform_eq ordinal parameter root ftsSecret table
      target rightRoot n next snapshots observations left fuel cache hnotSelected]
    rw [directDelayedSelectedRootIndicator_uniform_eq ordinal parameter root ftsSecret table
      target rightRoot n next snapshots observations right fuel cache hnotSelected]
    exact evalDist_complement_runDirectWitness_finish_false_eq_of_synchronized table observe
      snapshots observations ((splitUniformImpl n).run cache) left right fuel hcontext hvalues
      hrevealed

set_option maxRecDepth 100000 in
theorem negatedDirectDelayedComputationObserve_uniform_observerPositionNeutral
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (n : Nat) (next : Fin (n + 1) → OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (hbefore : snapshots.length ≤ ordinal)
    (hsynchronized : ∀ output,
      ObserverSynchronized table
        (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table target
          rightRoot (next output) snapshots observations))
    (hneutral : ∀ output,
      ObserverPositionNeutral table
        (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table target
          rightRoot (next output) snapshots observations)) :
    ObserverPositionNeutral table
      (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table target
        rightRoot
        (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
          (Sum.inl (Sum.inl n))) >>= next)
        snapshots observations) where
  eq_resolve position context fuel cache hvalid hcompletable _hensured := by
    let observe := fun nextContext remaining (value : Fin (n + 1) × SplitHashCache)
        laterSnapshots laterObservations ↦
      directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
        (next value.1) laterSnapshots laterObservations nextContext remaining value.2
    letI : ObserverSynchronized table
        (negatedDirectDelayedObserve observe snapshots observations) := ⟨by
      intro nextLeft nextRight remaining value hnextContext hnextValues hnextRevealed
      simpa [negatedDirectDelayedObserve, negatedDirectDelayedComputationObserve, observe] using
        ObserverSynchronized.eq_of_synchronized
          (table := table)
          (observe := negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret
            table target rightRoot (next value.1) snapshots observations)
          nextLeft nextRight remaining value.2 hnextContext hnextValues hnextRevealed⟩
    letI : ObserverPositionNeutral table
        (negatedDirectDelayedObserve observe snapshots observations) := ⟨by
      intro nextPosition nextContext remaining value hnextValid hnextCompletable hensured
      simpa [negatedDirectDelayedObserve, negatedDirectDelayedComputationObserve, observe] using
        ObserverPositionNeutral.eq_resolve
          (table := table)
          (observe := negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret
            table target rightRoot (next value.1) snapshots observations)
          nextPosition nextContext remaining value.2 hnextValid hnextCompletable hensured⟩
    have hnotSelected : ¬ordinal < snapshots.length := by omega
    unfold negatedDirectDelayedComputationObserve
    simp_rw [directDelayedSelectedRootIndicator_uniform_eq ordinal parameter root ftsSecret table
      target rightRoot n next snapshots observations _ fuel cache hnotSelected]
    exact evalDist_resolve_then_complement_runDirectWitness_finish_false table position observe
      snapshots observations ((splitUniformImpl n).run cache) context fuel hvalid hcompletable

set_option maxRecDepth 100000 in
theorem negatedDirectDelayedComputationObserve_signing_observerSynchronized
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (message : Message)
    (next : Option Signature → OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (hbefore : snapshots.length ≤ ordinal)
    (hsynchronized : ∀ output,
      ObserverSynchronized table
        (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table target
          rightRoot (next output) snapshots observations))
    (hneutral : ∀ output,
      ObserverPositionNeutral table
        (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table target
          rightRoot (next output) snapshots observations)) :
    ObserverSynchronized table
      (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table target
        rightRoot
        (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec) (Sum.inr message)) >>= next)
        snapshots observations) where
  eq_of_synchronized left right fuel cache hcontext hvalues hrevealed := by
    let observe := fun nextContext remaining (value : Option Signature × SplitHashCache)
        laterSnapshots laterObservations ↦
      directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
        (next value.1) laterSnapshots laterObservations nextContext remaining value.2
    letI : ObserverSynchronized table
        (negatedDirectDelayedObserve observe snapshots observations) := ⟨by
      intro nextLeft nextRight remaining value hnextContext hnextValues hnextRevealed
      simpa [negatedDirectDelayedObserve, negatedDirectDelayedComputationObserve, observe] using
        ObserverSynchronized.eq_of_synchronized
          (table := table)
          (observe := negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret
            table target rightRoot (next value.1) snapshots observations)
          nextLeft nextRight remaining value.2 hnextContext hnextValues hnextRevealed⟩
    letI : ObserverPositionNeutral table
        (negatedDirectDelayedObserve observe snapshots observations) := ⟨by
      intro position nextContext remaining value hvalid hcompletable hensured
      simpa [negatedDirectDelayedObserve, negatedDirectDelayedComputationObserve, observe] using
        ObserverPositionNeutral.eq_resolve
          (table := table)
          (observe := negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret
            table target rightRoot (next value.1) snapshots observations)
          position nextContext remaining value.2 hvalid hcompletable hensured⟩
    have hnotSelected : ¬ordinal < snapshots.length := by omega
    unfold negatedDirectDelayedComputationObserve
    rw [directDelayedSelectedRootIndicator_signing_eq ordinal parameter root ftsSecret table
      target rightRoot message next snapshots observations left fuel cache hnotSelected]
    rw [directDelayedSelectedRootIndicator_signing_eq ordinal parameter root ftsSecret table
      target rightRoot message next snapshots observations right fuel cache hnotSelected]
    exact evalDist_complement_runDirectWitness_finish_false_eq_of_synchronized table observe
      snapshots observations ((maskedSign parameter root ftsSecret message).run cache)
      left right fuel hcontext hvalues hrevealed

set_option maxRecDepth 100000 in
theorem negatedDirectDelayedComputationObserve_signing_observerPositionNeutral
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (message : Message)
    (next : Option Signature → OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (hbefore : snapshots.length ≤ ordinal)
    (hsynchronized : ∀ output,
      ObserverSynchronized table
        (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table target
          rightRoot (next output) snapshots observations))
    (hneutral : ∀ output,
      ObserverPositionNeutral table
        (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table target
          rightRoot (next output) snapshots observations)) :
    ObserverPositionNeutral table
      (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table target
        rightRoot
        (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec) (Sum.inr message)) >>= next)
        snapshots observations) where
  eq_resolve position context fuel cache hvalid hcompletable _hensured := by
    let observe := fun nextContext remaining (value : Option Signature × SplitHashCache)
        laterSnapshots laterObservations ↦
      directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
        (next value.1) laterSnapshots laterObservations nextContext remaining value.2
    letI : ObserverSynchronized table
        (negatedDirectDelayedObserve observe snapshots observations) := ⟨by
      intro nextLeft nextRight remaining value hnextContext hnextValues hnextRevealed
      simpa [negatedDirectDelayedObserve, negatedDirectDelayedComputationObserve, observe] using
        ObserverSynchronized.eq_of_synchronized
          (table := table)
          (observe := negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret
            table target rightRoot (next value.1) snapshots observations)
          nextLeft nextRight remaining value.2 hnextContext hnextValues hnextRevealed⟩
    letI : ObserverPositionNeutral table
        (negatedDirectDelayedObserve observe snapshots observations) := ⟨by
      intro nextPosition nextContext remaining value hnextValid hnextCompletable hensured
      simpa [negatedDirectDelayedObserve, negatedDirectDelayedComputationObserve, observe] using
        ObserverPositionNeutral.eq_resolve
          (table := table)
          (observe := negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret
            table target rightRoot (next value.1) snapshots observations)
          nextPosition nextContext remaining value.2 hnextValid hnextCompletable hensured⟩
    have hnotSelected : ¬ordinal < snapshots.length := by omega
    unfold negatedDirectDelayedComputationObserve
    simp_rw [directDelayedSelectedRootIndicator_signing_eq ordinal parameter root ftsSecret table
      target rightRoot message next snapshots observations _ fuel cache hnotSelected]
    exact evalDist_resolve_then_complement_runDirectWitness_finish_false table position observe
      snapshots observations ((maskedSign parameter root ftsSecret message).run cache)
      context fuel hvalid hcompletable

theorem cleanProbeObservation_materializedDeferredState_eq_of_finalizationContextEq
    (table : OtsSecretIndex → HashOutput) (left right : DeferredContext)
    (coordinate : Coordinate) (candidate : Digest)
    (hcontext : FinalizationContextEq table (some left) (some right))
    (hvalues : left.state.values = right.state.values)
    (hrevealed : left.state.revealed = right.state.revealed) :
    cleanProbeObservation (materializedDeferredState left) coordinate candidate =
      cleanProbeObservation (materializedDeferredState right) coordinate candidate := by
  rcases hcontext with ⟨hview, _hleftValid, _hrightValid, _hleftCompletable⟩
  have hvalueAt :
      (materializedDeferredState left).values coordinate =
        (materializedDeferredState right).values coordinate := by
    cases coordinate with
    | chainStart lay tree leafIdx chainIdx =>
        simpa only [materializedDeferredState_chainStart] using
          congrFun hvalues (.chainStart lay tree leafIdx chainIdx)
    | position position =>
        have hvalueEq := congrFun hview.valueEq (.position position)
        simpa only [resolvedCompletionValue, materializedDeferredState_position] using hvalueEq
  by_cases hleftRevealed : coordinate ∈ left.state.revealed
  · have hrightRevealed : coordinate ∈ right.state.revealed := by
      simpa [hrevealed] using hleftRevealed
    simp [cleanProbeObservation, hvalueAt, hleftRevealed, hrightRevealed]
  · have hrightRevealed : coordinate ∉ right.state.revealed := by
      simpa [hrevealed] using hleftRevealed
    simp [cleanProbeObservation, hvalueAt, hleftRevealed, hrightRevealed]

theorem observationsAfterCandidate_materializedDeferredState_eq_of_finalizationContextEq
    (table : OtsSecretIndex → HashOutput) (left right : DeferredContext)
    (observations : List CleanProbeObservation) (candidate? : Option Probe)
    (hcontext : FinalizationContextEq table (some left) (some right))
    (hvalues : left.state.values = right.state.values)
    (hrevealed : left.state.revealed = right.state.revealed) :
    observationsAfterCandidate observations (materializedDeferredState left) candidate? =
      observationsAfterCandidate observations (materializedDeferredState right) candidate? := by
  cases candidate? with
  | none => rfl
  | some candidate =>
      simp only [observationsAfterCandidate]
      rw [cleanProbeObservation_materializedDeferredState_eq_of_finalizationContextEq table
        left right candidate.coordinate candidate.candidate hcontext hvalues hrevealed]

structure CompletionSafeStateEq
    (table : OtsSecretIndex → HashOutput)
    (left right : LazyRevealProbe.State Coordinate) : Prop where
  forward : CompletionSafeStateLE table left right
  backward : CompletionSafeStateLE table right left

theorem CompletionSafeStateEq.ensure
    {table : OtsSecretIndex → HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hstate : CompletionSafeStateEq table left right) (coordinate : Coordinate) :
    CompletionSafeStateEq table (left.ensure coordinate) (right.ensure coordinate) :=
  ⟨hstate.forward.ensure coordinate, hstate.backward.ensure coordinate⟩

theorem CompletionSafeStateEq.publish
    {table : OtsSecretIndex → HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hstate : CompletionSafeStateEq table left right) (coordinate : Coordinate) :
    CompletionSafeStateEq table (left.publish coordinate) (right.publish coordinate) :=
  ⟨hstate.forward.publish coordinate, hstate.backward.publish coordinate⟩

theorem CompletionSafeStateEq.addPending
    {table : OtsSecretIndex → HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hstate : CompletionSafeStateEq table left right)
    (coordinate : Coordinate) (candidate : Digest) :
    CompletionSafeStateEq table
      (left.addPending coordinate candidate) (right.addPending coordinate candidate) :=
  ⟨hstate.forward.addPending coordinate candidate,
    hstate.backward.addPending coordinate candidate⟩

theorem CompletionSafeStateEq.materialize
    {table : OtsSecretIndex → HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hstate : CompletionSafeStateEq table left right)
    (coordinate : Coordinate) (output : HashOutput) :
    CompletionSafeStateEq table
      (left.materialize coordinate output) (right.materialize coordinate output) :=
  ⟨hstate.forward.materialize coordinate output,
    hstate.backward.materialize coordinate output⟩

theorem CompletionSafeStateEq.hitAt_iff_of_value_none
    {table : OtsSecretIndex → HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hstate : CompletionSafeStateEq table left right)
    (coordinate : Coordinate) (output : HashOutput)
    (hleftValue : left.values coordinate = none)
    (hcompletion : ∀ index : OtsSecretIndex,
      coordinate = index.coordinate → output = table index) :
    left.hitAt coordinate output ↔ right.hitAt coordinate output := by
  have hrightValue : right.values coordinate = none := by
    rw [← hstate.forward.values]
    exact hleftValue
  constructor
  · intro hleft
    by_contra hright
    exact hstate.forward.not_hitAt_left_of_right coordinate output hleftValue hcompletion
      hright hleft
  · intro hright
    by_contra hleft
    exact hstate.backward.not_hitAt_left_of_right coordinate output hrightValue hcompletion
      hleft hright

theorem CompletionSafeStateLE.directDeferredCompletable_of_right
    {table : OtsSecretIndex → HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hstate : CompletionSafeStateLE table left right)
    (hcompletable : DeferredCompletable table (directDeferredContext right)) :
    DeferredCompletable table (directDeferredContext left) := by
  obtain ⟨completion, hcompletion⟩ := hcompletable
  refine ⟨completion, ?_⟩
  refine ⟨?_, ?_, ?_, hcompletion.2.2.2⟩
  · intro coordinate output hvalue
    apply hcompletion.1 coordinate output
    simpa [directDeferredContext, hstate.values] using hvalue
  · intro position output hvalue
    apply hcompletion.2.1 position output
    simpa [directDeferredContext, directDeferredValues, hstate.values] using hvalue
  · intro coordinate candidate hentry
    have hentry' : (coordinate, candidate) ∈ left.pending := by
      simpa [directDeferredContext] using hentry
    rcases hstate.pending coordinate candidate hentry' with hright | hknown | hchain
    · apply hcompletion.2.2.1 coordinate candidate
      simpa [directDeferredContext] using hright
    · obtain ⟨output, hvalue, hmiss⟩ := hknown
      have hcompletionValue : completion coordinate = output :=
        hcompletion.1 coordinate output (by
          simpa [directDeferredContext] using
            (show right.values coordinate = some output by rw [← hstate.values]; exact hvalue))
      simpa [hcompletionValue] using Ne.symm hmiss
    · obtain ⟨index, hcoordinate, hmiss⟩ := hchain
      have hcompletionValue : completion coordinate = table index := by
        rw [hcoordinate]
        exact hcompletion.2.2.2 index
      simpa [hcompletionValue] using Ne.symm hmiss

theorem CompletionSafeStateEq.directDeferredCompletable_iff
    {table : OtsSecretIndex → HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hstate : CompletionSafeStateEq table left right) :
    DeferredCompletable table (directDeferredContext left) ↔
      DeferredCompletable table (directDeferredContext right) := by
  exact ⟨hstate.backward.directDeferredCompletable_of_right,
    hstate.forward.directDeferredCompletable_of_right⟩

def ObservedCompletionSafeEqRel
    (table : OtsSecretIndex → HashOutput)
    (leftPrefix rightPrefix : List CleanProbeObservation) :
    Option (ObservedCleanRunResult α) → Option (ObservedCleanRunResult α) → Prop
  | none, none => True
  | some left, some right =>
      left.value = right.value ∧ left.table = right.table ∧
        left.remaining = right.remaining ∧
        (∃ suffix,
          left.observations = leftPrefix ++ suffix ∧
            right.observations = rightPrefix ++ suffix) ∧
        CompletionSafeStateEq table left.state right.state
  | _, _ => False

theorem ObservedCompletionSafeEqRel.pure
    (table : OtsSecretIndex → HashOutput)
    (leftPrefix rightPrefix : List CleanProbeObservation)
    (leftState rightState : LazyRevealProbe.State Coordinate)
    (fuel : Nat) (value : α)
    (hstate : CompletionSafeStateEq table leftState rightState) :
    ObservedCompletionSafeEqRel table leftPrefix rightPrefix
      (some ⟨leftState, fuel, value, table, leftPrefix⟩)
      (some ⟨rightState, fuel, value, table, rightPrefix⟩) := by
  exact ⟨rfl, rfl, rfl, ⟨[], by simp, by simp⟩, hstate⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_runObservedCleanFromTable_completionSafeEq
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (leftPrefix rightPrefix : List CleanProbeObservation)
    (leftState rightState : LazyRevealProbe.State Coordinate)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hstate : CompletionSafeStateEq table leftState rightState) :
    RelTriple
      (runObservedCleanFromTable leftPrefix leftState fuel table computation)
      (runObservedCleanFromTable rightPrefix rightState fuel table computation)
      (ObservedCompletionSafeEqRel table leftPrefix rightPrefix) := by
  induction computation using OracleComp.inductionOn generalizing
      leftPrefix rightPrefix leftState rightState fuel with
  | pure value =>
      rw [runObservedCleanFromTable, OracleComp.construct_pure,
        runObservedCleanFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure
        (ObservedCompletionSafeEqRel.pure table leftPrefix rightPrefix leftState rightState fuel
          value hstate)
  | query_bind query next ih =>
      rw [runObservedCleanFromTable, OracleComp.construct_query_bind,
        runObservedCleanFromTable, OracleComp.construct_query_bind]
      have extendObservation
          (leftObservation rightObservation : CleanProbeObservation)
          (hobservation : leftObservation = rightObservation)
          (leftRun rightRun : ProbComp (Option (ObservedCleanRunResult α)))
          (hrun : RelTriple leftRun rightRun
            (ObservedCompletionSafeEqRel table
              (leftPrefix ++ [leftObservation]) (rightPrefix ++ [rightObservation]))) :
          RelTriple leftRun rightRun
            (ObservedCompletionSafeEqRel table leftPrefix rightPrefix) := by
        apply relTriple_post_mono hrun
        intro leftResult rightResult hresult
        cases leftResult with
        | none =>
            cases rightResult with
            | none => trivial
            | some rightResult =>
                simp [ObservedCompletionSafeEqRel] at hresult
        | some leftResult =>
            cases rightResult with
            | none => simp [ObservedCompletionSafeEqRel] at hresult
            | some rightResult =>
                rcases hresult with ⟨hvalue, htable, hremaining,
                  ⟨suffix, hleft, hright⟩, hnextState⟩
                refine ⟨hvalue, htable, hremaining,
                  ⟨leftObservation :: suffix, ?_, ?_⟩, hnextState⟩
                · simpa [List.append_assoc] using hleft
                · simpa [List.append_assoc, hobservation] using hright
      cases query with
      | uniform n =>
          apply relTriple_bind (relTriple_refl (liftM (unifSpec.query n)))
          intro leftValue rightValue hvalue
          subst rightValue
          exact ih leftValue leftPrefix rightPrefix leftState rightState fuel hstate
      | hashOutput =>
          apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
          intro leftValue rightValue hvalue
          subst rightValue
          exact ih leftValue leftPrefix rightPrefix leftState rightState fuel hstate
      | ensure coordinate =>
          exact ih () leftPrefix rightPrefix (leftState.ensure coordinate)
            (rightState.ensure coordinate) fuel (hstate.ensure coordinate)
      | probe coordinate candidate =>
          cases fuel with
          | zero => exact relTriple_pure_pure (by trivial)
          | succ remaining =>
              let leftObservation := cleanProbeObservation leftState coordinate candidate
              let rightObservation := cleanProbeObservation rightState coordinate candidate
              have hobservation : leftObservation = rightObservation := by
                unfold leftObservation rightObservation cleanProbeObservation
                simp [hstate.forward.values, hstate.forward.revealed]
              have hrevealed : coordinate ∈ leftState.revealed ↔
                  coordinate ∈ rightState.revealed := by
                rw [hstate.forward.revealed]
              by_cases hleftRevealed : coordinate ∈ leftState.revealed
              · have hrightRevealed : coordinate ∈ rightState.revealed :=
                  hrevealed.mp hleftRevealed
                simp only [hleftRevealed, hrightRevealed, ↓reduceIte]
                exact extendObservation leftObservation rightObservation hobservation _ _
                  (ih () (leftPrefix ++ [leftObservation])
                    (rightPrefix ++ [rightObservation]) leftState rightState remaining hstate)
              · have hrightRevealed : coordinate ∉ rightState.revealed := by
                  simpa [hrevealed] using hleftRevealed
                simp only [hleftRevealed, hrightRevealed, ↓reduceIte]
                exact extendObservation leftObservation rightObservation hobservation _ _
                  (ih () (leftPrefix ++ [leftObservation])
                    (rightPrefix ++ [rightObservation])
                    (leftState.addPending coordinate candidate)
                    (rightState.addPending coordinate candidate) remaining
                    (hstate.addPending coordinate candidate))
      | peek coordinate =>
          simp only
          have hvalue : leftState.values coordinate = rightState.values coordinate := by
            rw [hstate.forward.values]
          rw [hvalue]
          exact ih (rightState.values coordinate) leftPrefix rightPrefix leftState rightState fuel
            hstate
      | publish coordinate =>
          simp only
          exact ih () leftPrefix rightPrefix (leftState.publish coordinate)
            (rightState.publish coordinate) fuel (hstate.publish coordinate)
      | reveal coordinate =>
          simp only
          have hvalue : leftState.values coordinate = rightState.values coordinate := by
            rw [hstate.forward.values]
          cases hrightValue : rightState.values coordinate with
          | some output =>
              have hleftValue : leftState.values coordinate = some output := by
                rw [hvalue, hrightValue]
              simp only [hleftValue]
              exact ih output leftPrefix rightPrefix leftState rightState fuel hstate
          | none =>
              have hleftValue : leftState.values coordinate = none := by
                rw [hvalue, hrightValue]
              simp only [hleftValue]
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let output := table ⟨lay, tree, leafIdx, chainIdx⟩
                  have hhit : leftState.hitAt (.chainStart lay tree leafIdx chainIdx) output ↔
                      rightState.hitAt (.chainStart lay tree leafIdx chainIdx) output :=
                    hstate.hitAt_iff_of_value_none _ output hleftValue (by
                      intro index hcoordinate
                      rcases index with ⟨otherLay, otherTree, otherLeaf, otherChain⟩
                      simp [OtsSecretIndex.coordinate] at hcoordinate
                      obtain ⟨rfl, rfl, rfl, rfl⟩ := hcoordinate
                      rfl)
                  by_cases hleftHit : leftState.hitAt
                      (.chainStart lay tree leafIdx chainIdx) output
                  · have hrightHit := hhit.mp hleftHit
                    simp only [output, hleftHit, hrightHit, ↓reduceIte]
                    exact relTriple_pure_pure (by trivial)
                  · have hrightHit : ¬rightState.hitAt
                        (.chainStart lay tree leafIdx chainIdx) output := by
                      rwa [← hhit]
                    simp only [output, hleftHit, hrightHit, ↓reduceIte]
                    exact ih output leftPrefix rightPrefix
                      (leftState.materialize (.chainStart lay tree leafIdx chainIdx) output)
                      (rightState.materialize (.chainStart lay tree leafIdx chainIdx) output)
                      fuel (hstate.materialize _ output)
              | position position =>
                  apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
                  intro leftOutput rightOutput houtput
                  subst rightOutput
                  have hhit : leftState.hitAt (.position position) leftOutput ↔
                      rightState.hitAt (.position position) leftOutput :=
                    hstate.hitAt_iff_of_value_none _ leftOutput hleftValue
                      (by intro index hcoordinate; cases hcoordinate)
                  by_cases hleftHit : leftState.hitAt (.position position) leftOutput
                  · have hrightHit := hhit.mp hleftHit
                    simp only [hleftHit, hrightHit, ↓reduceIte]
                    exact relTriple_pure_pure (by trivial)
                  · have hrightHit : ¬rightState.hitAt (.position position) leftOutput := by
                      rwa [← hhit]
                    simp only [hleftHit, hrightHit, ↓reduceIte]
                    exact ih leftOutput leftPrefix rightPrefix
                      (leftState.materialize (.position position) leftOutput)
                      (rightState.materialize (.position position) leftOutput) fuel
                      (hstate.materialize _ leftOutput)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_observedMaterializedBoundary_completionSafeEq
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (leftPrefix rightPrefix : List CleanProbeObservation)
    (leftState rightState : LazyRevealProbe.State Coordinate)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (cache : SplitHashCache)
    (hstate : CompletionSafeStateEq table leftState rightState) :
    RelTriple
      (observedMaterializedBoundary parameter root ftsSecret computation leftPrefix leftState
        fuel table cache)
      (observedMaterializedBoundary parameter root ftsSecret computation rightPrefix rightState
        fuel table cache)
      (ObservedCompletionSafeEqRel table leftPrefix rightPrefix) := by
  induction computation using OracleComp.inductionOn generalizing
      leftPrefix rightPrefix leftState rightState fuel cache with
  | pure value =>
      rw [observedMaterializedBoundary, OracleComp.construct_pure,
        observedMaterializedBoundary, OracleComp.construct_pure]
      exact relTriple_pure_pure
        (ObservedCompletionSafeEqRel.pure table leftPrefix rightPrefix leftState rightState fuel
          (value, cache) hstate)
  | query_bind query next ih =>
      rw [observedMaterializedBoundary, OracleComp.construct_query_bind,
        observedMaterializedBoundary, OracleComp.construct_query_bind]
      have continueAfter
          (leftRun rightRun : ProbComp (Option (ObservedCleanRunResult
            ((OracleWorld + SigningSpec).Range query × SplitHashCache))))
          (hrun : RelTriple leftRun rightRun
            (ObservedCompletionSafeEqRel table leftPrefix rightPrefix)) :
          RelTriple
            (leftRun >>= fun result ↦
              match result with
              | none => pure none
              | some result =>
                  observedMaterializedBoundary parameter root ftsSecret
                    (next result.value.1) result.observations result.state result.remaining table
                    result.value.2)
            (rightRun >>= fun result ↦
              match result with
              | none => pure none
              | some result =>
                  observedMaterializedBoundary parameter root ftsSecret
                    (next result.value.1) result.observations result.state result.remaining table
                    result.value.2)
            (ObservedCompletionSafeEqRel table leftPrefix rightPrefix) := by
        apply relTriple_bind hrun
        intro leftResult rightResult hresult
        cases leftResult with
        | none =>
            cases rightResult with
            | none => exact relTriple_pure_pure (by trivial)
            | some rightResult => simp [ObservedCompletionSafeEqRel] at hresult
        | some leftResult =>
            cases rightResult with
            | none => simp [ObservedCompletionSafeEqRel] at hresult
            | some rightResult =>
                rcases hresult with ⟨hvalue, htable, hremaining,
                  ⟨suffix, hleftObservations, hrightObservations⟩, hnextState⟩
                simp only
                have houtput : leftResult.value.1 = rightResult.value.1 :=
                  congrArg Prod.fst hvalue
                have hnextCache : leftResult.value.2 = rightResult.value.2 :=
                  congrArg Prod.snd hvalue
                rw [← houtput, ← hnextCache, ← hremaining]
                have hnext := ih leftResult.value.1 leftResult.observations
                  rightResult.observations leftResult.state rightResult.state
                  leftResult.remaining leftResult.value.2 hnextState
                apply relTriple_post_mono hnext
                intro laterLeft laterRight hlater
                cases laterLeft with
                | none =>
                    cases laterRight with
                    | none => trivial
                    | some laterRight => simp [ObservedCompletionSafeEqRel] at hlater
                | some laterLeft =>
                    cases laterRight with
                    | none => simp [ObservedCompletionSafeEqRel] at hlater
                    | some laterRight =>
                        rcases hlater with ⟨hlaterValue, hlaterTable, hlaterRemaining,
                          ⟨laterSuffix, hlaterLeft, hlaterRight⟩, hlaterState⟩
                        refine ⟨hlaterValue, hlaterTable, hlaterRemaining,
                          ⟨suffix ++ laterSuffix, ?_, ?_⟩, hlaterState⟩
                        · rw [hlaterLeft, hleftObservations, List.append_assoc]
                        · rw [hlaterRight, hrightObservations, List.append_assoc]
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              change Fin (n + 1) → OracleComp (OracleWorld + SigningSpec) α at next
              simp only
              have hstep := relTriple_runObservedCleanFromTable_completionSafeEq
                ((splitUniformImpl n).run cache) leftPrefix rightPrefix leftState rightState fuel
                table hstate
              convert continueAfter _ _ hstep using 1 <;>
                apply bind_congr <;> intro result <;> cases result <;> rfl
          | inr input =>
              change HashOutput → OracleComp (OracleWorld + SigningSpec) α at next
              simp only
              let leftPublic := materializedCanonicalContext table leftState
              let rightPublic := materializedCanonicalContext table rightState
              have hpublicValues : leftPublic.state.values = rightPublic.state.values :=
                materializedCanonicalContext_values_eq_of_completionSafe table hstate.forward
              have hplan : purePlanProbingHashQuery parameter input leftPublic.state =
                  purePlanProbingHashQuery parameter input rightPublic.state :=
                purePlanProbingHashQuery_eq_of_values_eq hpublicValues parameter input
              let plan := purePlanProbingHashQuery parameter input leftPublic.state
              have hexecutor :
                  probingHashQueryAfterRootAwarePublicPlan parameter input leftPublic.state plan =
                    probingHashQueryAfterRootAwarePublicPlan parameter input rightPublic.state
                      plan :=
                probingHashQueryAfterRootAwarePublicPlan_eq_of_values_eq parameter input
                  hpublicValues plan
              rw [← hplan, ← hexecutor]
              have hstep := relTriple_runObservedCleanFromTable_completionSafeEq
                ((probingHashQueryAfterRootAwarePublicPlan parameter input leftPublic.state
                  plan).run cache)
                leftPrefix rightPrefix leftState rightState fuel table hstate
              convert continueAfter _ _ hstep using 1 <;>
                simp only [leftPublic, plan, observedMaterializedBoundary] <;>
                apply bind_congr <;> intro result <;> cases result <;> rfl
      | inr message =>
          change Option Signature → OracleComp (OracleWorld + SigningSpec) α at next
          simp only
          have hstep := relTriple_runObservedCleanFromTable_completionSafeEq
            ((maskedSign parameter root ftsSecret message).run cache)
            leftPrefix rightPrefix leftState rightState fuel table hstate
          convert continueAfter _ _ hstep using 1 <;>
            simp only [observedMaterializedBoundary] <;>
            apply bind_congr <;> intro result <;> cases result <;> rfl

set_option maxRecDepth 100000 in
theorem evalDist_negatedDirectDelayedComputationObserve_eq_of_eventEq
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (leftSnapshots rightSnapshots : List PlannedProbeSnapshot)
    (leftObservations rightObservations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hleftBefore : ¬ordinal < leftSnapshots.length)
    (hrightBefore : ¬ordinal < rightSnapshots.length)
    (hsnapshots : leftSnapshots.map PlannedProbeSnapshot.toProbe =
      rightSnapshots.map PlannedProbeSnapshot.toProbe)
    (htrace : CleanProbeObservationsEventEq leftObservations rightObservations) :
    evalDist
        (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table target
          rightRoot computation leftSnapshots leftObservations context fuel cache) =
      evalDist
        (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table target
          rightRoot computation rightSnapshots rightObservations context fuel cache) := by
  unfold negatedDirectDelayedComputationObserve
  rw [evalDist_map, evalDist_map]
  exact congrArg (fun distribution => Bool.not <$> distribution)
    (evalDist_directDelayedSelectedRootIndicator_eq_of_eventEq ordinal parameter root ftsSecret
      table target rightRoot computation leftSnapshots rightSnapshots leftObservations
      rightObservations context fuel cache hleftBefore hrightBefore hsnapshots htrace)

set_option maxRecDepth 100000 in
theorem evalDist_complement_runDirectWitness_finish_false_eq_of_eventEq
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (next : α → OracleComp (OracleWorld + SigningSpec) β)
    (leftSnapshots rightSnapshots : List PlannedProbeSnapshot)
    (leftObservations rightObservations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) (α × SplitHashCache))
    (hleftBefore : ¬ordinal < leftSnapshots.length)
    (hrightBefore : ¬ordinal < rightSnapshots.length)
    (hsnapshots : leftSnapshots.map PlannedProbeSnapshot.toProbe =
      rightSnapshots.map PlannedProbeSnapshot.toProbe)
    (htrace : CleanProbeObservationsEventEq leftObservations rightObservations) :
    evalDist (Bool.not <$>
        (runDirectResolvedWitnessFromTable context fuel table computation >>=
          finishDirectDelayedSelectedRootIndicator
            (canonicalizeDirectDelayedSelectedRootIndicator table
              (fun nextContext remaining value laterSnapshots laterObservations ↦
                directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
                  rightRoot (next value.1) laterSnapshots laterObservations nextContext remaining
                  value.2))
            leftSnapshots leftObservations)) =
      evalDist (Bool.not <$>
        (runDirectResolvedWitnessFromTable context fuel table computation >>=
          finishDirectDelayedSelectedRootIndicator
            (canonicalizeDirectDelayedSelectedRootIndicator table
              (fun nextContext remaining value laterSnapshots laterObservations ↦
                directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
                  rightRoot (next value.1) laterSnapshots laterObservations nextContext remaining
                  value.2))
            rightSnapshots rightObservations)) := by
  rw [evalDist_map, evalDist_map]
  apply congrArg (fun distribution => Bool.not <$> distribution)
  apply evalDist_bind_congr
  intro result _hresult
  cases result with
  | stoppedFuel => rfl
  | stoppedOrdinary => rfl
  | stoppedPrivate witness => rfl
  | done result =>
      unfold finishDirectDelayedSelectedRootIndicator
      unfold canonicalizeDirectDelayedSelectedRootIndicator
      let canonical := canonicalizeMaterializedValues table result.context
      by_cases hhit : PrivateStructuralHit canonical
      · simp [canonical, hhit]
      · by_cases hpublished : PublishedValues result.context.state
        · by_cases hcompletable : DeferredCompletable table canonical
          · simp only [canonical, hhit, hpublished, hcompletable, ↓reduceIte]
            exact evalDist_directDelayedSelectedRootIndicator_eq_of_eventEq ordinal parameter root
              ftsSecret table target rightRoot (next result.value.1) leftSnapshots rightSnapshots
              leftObservations rightObservations canonical result.remaining result.value.2
              hleftBefore hrightBefore hsnapshots htrace
          · simp [canonical, hhit, hpublished, hcompletable]
        · simp [canonical, hhit, hpublished]


end SphincsSecurity.Concrete.OtsProbeSimulation
