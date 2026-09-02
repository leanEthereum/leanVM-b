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

theorem negatedDirectDelayedComputationObserve_pure_observerPositionNeutralAt
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target position : Position)
    (rightRoot : Digest) (value : α) (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (hbefore : snapshots.length ≤ ordinal) :
    ObserverPositionNeutralAt table position
      (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table target
        rightRoot (pure value) snapshots observations) := by
  letI := negatedDirectDelayedComputationObserve_pure_observerPositionNeutral ordinal parameter
    root ftsSecret table target rightRoot value snapshots observations hbefore
  exact ObserverPositionNeutral.at table position _

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
theorem evalDist_resolve_then_complement_runDirectWitness_finish_false_at
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      List CleanProbeObservation → ProbComp Bool)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hensured : Coordinate.position position ∈ context.state.ensured)
    (hneutral : ObserverPositionNeutralAt table position
      (negatedDirectDelayedObserve observe snapshots observations)) :
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
  have hmove := evalDist_resolve_then_runDirectWitness_finish_false_at table position observe
    snapshots observations computation context fuel hvalid hcompletable hensured hneutral
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
theorem negatedDirectDelayedComputationObserve_uniform_observerPositionNeutralAt
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (position : Position) (n : Nat)
    (next : Fin (n + 1) → OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (hbefore : snapshots.length ≤ ordinal)
    (hneutral : ∀ output, ObserverPositionNeutralAt table position
      (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table target
        rightRoot (next output) snapshots observations)) :
    ObserverPositionNeutralAt table position
      (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table target
        rightRoot
        (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
          (Sum.inl (Sum.inl n))) >>= next)
        snapshots observations) := by
  intro context fuel cache hvalid hcompletable hensured
  let observe := fun nextContext remaining (value : Fin (n + 1) × SplitHashCache)
      laterSnapshots laterObservations ↦
    directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
      (next value.1) laterSnapshots laterObservations nextContext remaining value.2
  have hnextNeutral : ObserverPositionNeutralAt table position
      (negatedDirectDelayedObserve observe snapshots observations) := by
    intro nextContext remaining value hnextValid hnextCompletable hnextEnsured
    simpa [negatedDirectDelayedObserve, negatedDirectDelayedComputationObserve, observe] using
      hneutral value.1 nextContext remaining value.2 hnextValid hnextCompletable hnextEnsured
  have hnotSelected : ¬ordinal < snapshots.length := by omega
  unfold negatedDirectDelayedComputationObserve
  simp_rw [directDelayedSelectedRootIndicator_uniform_eq ordinal parameter root ftsSecret table
    target rightRoot n next snapshots observations _ fuel cache hnotSelected]
  exact evalDist_resolve_then_complement_runDirectWitness_finish_false_at table position observe
    snapshots observations ((splitUniformImpl n).run cache) context fuel hvalid hcompletable
    hensured hnextNeutral

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

set_option maxRecDepth 100000 in
theorem negatedDirectDelayedComputationObserve_signing_observerPositionNeutralAt
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (position : Position) (message : Message)
    (next : Option Signature → OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (hbefore : snapshots.length ≤ ordinal)
    (hneutral : ∀ output, ObserverPositionNeutralAt table position
      (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table target
        rightRoot (next output) snapshots observations)) :
    ObserverPositionNeutralAt table position
      (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table target
        rightRoot
        (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec) (Sum.inr message)) >>= next)
        snapshots observations) := by
  intro context fuel cache hvalid hcompletable hensured
  let observe := fun nextContext remaining (value : Option Signature × SplitHashCache)
      laterSnapshots laterObservations ↦
    directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
      (next value.1) laterSnapshots laterObservations nextContext remaining value.2
  have hnextNeutral : ObserverPositionNeutralAt table position
      (negatedDirectDelayedObserve observe snapshots observations) := by
    intro nextContext remaining value hnextValid hnextCompletable hnextEnsured
    simpa [negatedDirectDelayedObserve, negatedDirectDelayedComputationObserve, observe] using
      hneutral value.1 nextContext remaining value.2 hnextValid hnextCompletable hnextEnsured
  have hnotSelected : ¬ordinal < snapshots.length := by omega
  unfold negatedDirectDelayedComputationObserve
  simp_rw [directDelayedSelectedRootIndicator_signing_eq ordinal parameter root ftsSecret table
    target rightRoot message next snapshots observations _ fuel cache hnotSelected]
  exact evalDist_resolve_then_complement_runDirectWitness_finish_false_at table position observe
    snapshots observations ((maskedSign parameter root ftsSecret message).run cache)
    context fuel hvalid hcompletable hensured hnextNeutral

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem evalDist_directDelayed_eagerDirectDelayed_hash_not_selected_at
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
    (hensured : Coordinate.position target ∈ context.state.ensured)
    (haligned :
      (observationsAfterCandidate observations (materializedDeferredState context)
        (rootAwareCandidateForPlan? parameter input
          (purePlanProbingHashQuery parameter input context.state))).map
          CleanProbeObservation.toProbe =
        (appendPlannedSnapshot snapshots
          (rootAwareCandidateForPlan? parameter input
            (purePlanProbingHashQuery parameter input context.state)) context).map
          PlannedProbeSnapshot.toProbe)
    (hclean : ∀ observation ∈
      observationsAfterCandidate observations (materializedDeferredState context)
        (rootAwareCandidateForPlan? parameter input
          (purePlanProbingHashQuery parameter input context.state)),
        ¬observation.ExistingHiddenHit)
    (hneutral : ObserverPositionNeutralAt table target
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
    evalDist
        (directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
          (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
            (Sum.inl (Sum.inr input))) >>= next)
          snapshots observations context fuel cache) =
      evalDist
        (eagerDirectDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot
          (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
            (Sum.inl (Sum.inr input))) >>= next)
          snapshots observations context fuel cache) := by
  let candidate? := rootAwareCandidateForPlan? parameter input
    (purePlanProbingHashQuery parameter input context.state)
  let rightSnapshots := appendPlannedSnapshot snapshots candidate? context
  let rightObservations := observationsAfterCandidate observations
    (materializedDeferredState context) candidate?
  let runComputation :=
    (probingHashQueryAfterPlan parameter input
      (purePlanProbingHashQuery parameter input context.state)).run cache
  let observe := fun nextContext remaining (value : HashOutput × SplitHashCache)
      laterSnapshots laterObservations ↦
    directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
      (next value.1) laterSnapshots laterObservations nextContext remaining value.2
  let delayedResolved : Option DeferredResolution → ProbComp Bool
    | none => pure false
    | some resolved =>
        runDirectResolvedWitnessFromTable resolved.toDeferredContext fuel table runComputation >>=
          finishDirectDelayedSelectedRootIndicator
            (canonicalizeDirectDelayedSelectedRootIndicator table observe)
            rightSnapshots rightObservations
  let eagerResolved : Option DeferredResolution → ProbComp Bool
    | none => pure false
    | some resolved =>
        runDirectResolvedWitnessFromTable resolved.toDeferredContext fuel table runComputation >>=
          finishDirectDelayedSelectedRootIndicator
            (canonicalizeDirectDelayedSelectedRootIndicator table observe)
            (appendPlannedSnapshot snapshots candidate? resolved.toDeferredContext)
            (observationsAfterCandidate observations
              (materializedDeferredState resolved.toDeferredContext) candidate?)
  have hdelayed : evalDist
      (directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
        (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
          (Sum.inl (Sum.inr input))) >>= next)
        snapshots observations context fuel cache) =
      evalDist (resolveDeferredPositionValue target context >>= delayedResolved) := by
    rw [directDelayedSelectedRootIndicator_hash_eq_not_selected ordinal parameter root ftsSecret
      table target rightRoot input next snapshots observations context fuel cache hbefore
      hnotSelected]
    exact (evalDist_resolve_then_runDirectWitness_finish_false_at table target observe rightSnapshots
      rightObservations runComputation context fuel hvalid hcompletable hensured (by
        simpa [observe, rightSnapshots, rightObservations, candidate?] using hneutral)).symm
  have heager : evalDist
      (eagerDirectDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
        rightRoot
        (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
          (Sum.inl (Sum.inr input))) >>= next)
        snapshots observations context fuel cache) =
      evalDist (resolveDeferredPositionValue target context >>= eagerResolved) := by
    unfold eagerDirectDelayedSelectedRootIndicator
    simp only [hbefore, ↓reduceIte]
    apply evalDist_bind_congr
    intro resolvedOption hresolvedOption
    cases resolvedOption with
    | none => rfl
    | some resolved =>
        simp only
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
              (appendPlannedSnapshot snapshots candidate? resolved.toDeferredContext).length =
                rightSnapshots.length := by
            cases hcandidate : candidate? <;>
              simp [rightSnapshots, appendPlannedSnapshot, hcandidate]
          rw [hlength]
          simpa [rightSnapshots, candidate?] using hnotSelected
        rw [directDelayedSelectedRootIndicator_hash_eq_not_selected ordinal parameter root
          ftsSecret table target rightRoot input next snapshots observations
          resolved.toDeferredContext fuel cache hbefore hnotSelectedResolved]
        rw [hplan]
  calc
    _ = evalDist (resolveDeferredPositionValue target context >>= delayedResolved) := hdelayed
    _ = evalDist (resolveDeferredPositionValue target context >>= eagerResolved) := by
      apply evalDist_bind_congr
      intro resolvedOption hresolvedOption
      cases resolvedOption with
      | none => rfl
      | some resolved =>
          have hresolvedPrivate : resolved.values target = some resolved.output :=
            resolveDeferredPositionValue_installs target context resolved hresolvedOption
          let leftSnapshots := appendPlannedSnapshot snapshots candidate?
            resolved.toDeferredContext
          let leftObservations := observationsAfterCandidate observations
            (materializedDeferredState resolved.toDeferredContext) candidate?
          have hsnapshots : leftSnapshots.map PlannedProbeSnapshot.toProbe =
              rightSnapshots.map PlannedProbeSnapshot.toProbe := by
            cases hcandidate : candidate? <;>
              simp [leftSnapshots, rightSnapshots, appendPlannedSnapshot, hcandidate]
          have hlength : rightSnapshots.length ≤ ordinal := by
            simpa [rightSnapshots, candidate?] using Nat.le_of_not_gt hnotSelected
          apply evalDist_eq_of_relTriple_eqRel
          apply relTriple_runDirectWitness_finishDirectDelayed_of_safe_trace ordinal parameter root
            ftsSecret table target resolved.output rightRoot HashOutput next runComputation
            leftSnapshots rightSnapshots leftObservations rightObservations
            resolved.toDeferredContext fuel hresolvedPrivate
            (by rwa [plannedProbeSnapshots_length_eq_of_toProbe_eq hsnapshots]) hlength hsnapshots
          intro hsafe
          apply observationsAfterCandidate_eventEq_resolved_current_of_clean_of_avoids target
            context resolved hresolvedOption observations candidate?
          · simpa [rightObservations, candidate?] using hclean
          · intro probe hprobe
            have hprobeSnapshots : probe ∈ rightSnapshots.map PlannedProbeSnapshot.toProbe := by
              rw [← haligned]
              simpa [rightObservations, candidate?] using hprobe
            exact (hsafe probe hprobeSnapshots).1
    _ = _ := heager.symm

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem evalDist_directDelayed_eagerDirectDelayed_hash_not_selected_general_at
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
    (hensured : Coordinate.position target ∈ context.state.ensured)
    (haligned : observations.map CleanProbeObservation.toProbe =
      snapshots.map PlannedProbeSnapshot.toProbe)
    (hclean : ∀ observation ∈ observations, ¬observation.ExistingHiddenHit)
    (hneutral :
      (∀ observation ∈
          observationsAfterCandidate observations (materializedDeferredState context)
            (rootAwareCandidateForPlan? parameter input
              (purePlanProbingHashQuery parameter input context.state)),
          ¬observation.ExistingHiddenHit) →
        ObserverPositionNeutralAt table target
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
    evalDist
        (directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
          (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
            (Sum.inl (Sum.inr input))) >>= next)
          snapshots observations context fuel cache) =
      evalDist
        (eagerDirectDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot
          (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
            (Sum.inl (Sum.inr input))) >>= next)
          snapshots observations context fuel cache) := by
  have hlength : observations.length = snapshots.length := by
    simpa only [List.length_map] using congrArg List.length haligned
  let nextObservations := observationsAfterCandidate observations
    (materializedDeferredState context)
    (rootAwareCandidateForPlan? parameter input
      (purePlanProbingHashQuery parameter input context.state))
  by_cases hnextClean : ∀ observation ∈ nextObservations,
      ¬observation.ExistingHiddenHit
  · have hnextAligned :
        nextObservations.map CleanProbeObservation.toProbe =
          (appendPlannedSnapshot snapshots
            (rootAwareCandidateForPlan? parameter input
              (purePlanProbingHashQuery parameter input context.state)) context).map
            PlannedProbeSnapshot.toProbe := by
      cases hcandidate : rootAwareCandidateForPlan? parameter input
          (purePlanProbingHashQuery parameter input context.state) <;>
        simp [nextObservations, observationsAfterCandidate, appendPlannedSnapshot, hcandidate,
          CleanProbeObservation.toProbe, cleanProbeObservation, haligned]
    exact evalDist_directDelayed_eagerDirectDelayed_hash_not_selected_at ordinal parameter root
      ftsSecret table target rightRoot input next snapshots observations context fuel cache hbefore
      hnotSelected hvalid hcompletable hensured hnextAligned
      (by simpa [nextObservations] using hnextClean)
      (hneutral (by simpa [nextObservations] using hnextClean))
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
    have heagerFalse : true ∉ support
        (eagerDirectDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot
          (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
            (Sum.inl (Sum.inr input))) >>= next)
          snapshots observations context fuel cache) :=
      true_not_mem_eagerDirectDelayed_hash_of_dirty_not_selected ordinal parameter root ftsSecret
        table target rightRoot input next snapshots observations context fuel cache hbefore
        hnotSelected hlength hclean (by simpa [nextObservations] using hnextClean)
    exact (evalDist_eq_of_relTriple_eqRel (relTriple_eq_false_of_true_not_mem _ hdirectFalse)).trans
      (evalDist_eq_of_relTriple_eqRel
        (relTriple_eq_false_of_true_not_mem _ heagerFalse)).symm

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

theorem materializedDeferredState_values_eq_of_finalizationContextEq
    (table : OtsSecretIndex → HashOutput) (left right : DeferredContext)
    (hcontext : FinalizationContextEq table (some left) (some right))
    (hvalues : left.state.values = right.state.values) :
    (materializedDeferredState left).values =
      (materializedDeferredState right).values := by
  rcases hcontext with ⟨hview, _hleftValid, _hrightValid, _hleftCompletable⟩
  funext coordinate
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      simpa only [materializedDeferredState_chainStart] using
        congrFun hvalues (.chainStart lay tree leafIdx chainIdx)
  | position position =>
      have hvalueEq := congrFun hview.valueEq (.position position)
      simpa only [resolvedCompletionValue, materializedDeferredState_position] using hvalueEq

structure CompletionSafeStateEq
    (table : OtsSecretIndex → HashOutput)
    (left right : LazyRevealProbe.State Coordinate) : Prop where
  forward : CompletionSafeStateLE table left right
  backward : CompletionSafeStateLE table right left

theorem completionSafeStateEq_materialized_of_finalizationContextEq
    (table : OtsSecretIndex → HashOutput) (left right : DeferredContext)
    (hcontext : FinalizationContextEq table (some left) (some right))
    (hvalues : left.state.values = right.state.values)
    (hrevealed : left.state.revealed = right.state.revealed) :
    CompletionSafeStateEq table
      (materializedDeferredState left) (materializedDeferredState right) := by
  rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
  have hrightCompletable : DeferredCompletable table right := by
    obtain ⟨completion, hcompletion⟩ := hleftCompletable
    exact ⟨completion, (hview.deferredCompletion_iff completion).mp hcompletion⟩
  have hmaterializedValues :=
    materializedDeferredState_values_eq_of_finalizationContextEq table left right
      ⟨hview, hleftValid, hrightValid, hleftCompletable⟩ hvalues
  have forwardContext : FinalizationContextLE table left (materializedDeferredContext right) := by
    have hrightMaterialized :=
      finalizationContextLE_materializedDeferredContext hrightValid hrightCompletable
    exact
      { view := (FinalizationContextLE.of_eq
          (⟨hview, hleftValid, hrightValid, hleftCompletable⟩ :
            FinalizationContextEq table (some left) (some right))).view.trans
          hrightMaterialized.view
        leftValid := hleftValid
        rightValid := hrightMaterialized.rightValid
        rightCompletable := hrightMaterialized.rightCompletable }
  have backwardContext : FinalizationContextLE table right (materializedDeferredContext left) := by
    have hleftMaterialized :=
      finalizationContextLE_materializedDeferredContext hleftValid hleftCompletable
    have hreverse : FinalizationContextEq table (some right) (some left) :=
      ⟨hview.symm, hrightValid, hleftValid, hrightCompletable⟩
    exact
      { view := (FinalizationContextLE.of_eq hreverse).view.trans hleftMaterialized.view
        leftValid := hrightValid
        rightValid := hleftMaterialized.rightValid
        rightCompletable := hleftMaterialized.rightCompletable }
  refine ⟨?_, ?_⟩
  · exact completionSafeStateLE_materialized_of_finalizationContextLE table left
      (materializedDeferredContext right) forwardContext (by
        change left.state.revealed = (materializedDeferredState right).revealed
        simpa using hrevealed)
      (by
        change (materializedDeferredState left).values =
          (materializedDeferredState right).values
        exact hmaterializedValues)
  · exact completionSafeStateLE_materialized_of_finalizationContextLE table right
      (materializedDeferredContext left) backwardContext (by
        change right.state.revealed = (materializedDeferredState left).revealed
        simpa using hrevealed.symm)
      (by
        change (materializedDeferredState right).values =
          (materializedDeferredState left).values
        exact hmaterializedValues.symm)

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

theorem CompletionSafeStateEq.pendingAt_eq_of_position_value_none
    {table : OtsSecretIndex → HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hstate : CompletionSafeStateEq table left right)
    (position : Position) (hleftValue : left.values (.position position) = none) :
    left.pendingAt (.position position) = right.pendingAt (.position position) := by
  have hrightValue : right.values (.position position) = none := by
    rw [← hstate.forward.values]
    exact hleftValue
  apply Finset.Subset.antisymm
  · intro candidate hcandidate
    have hentry : (Coordinate.position position, candidate) ∈ left.pending :=
      (LazyRevealProbe.State.mem_pendingAt_iff left (.position position) candidate).1 hcandidate
    rcases hstate.forward.pending (.position position) candidate hentry with
      hright | ⟨output, hvalue, _hmiss⟩ | ⟨index, hcoordinate, _hmiss⟩
    · exact (LazyRevealProbe.State.mem_pendingAt_iff right
        (.position position) candidate).2 hright
    · rw [hleftValue] at hvalue
      simp at hvalue
    · cases hcoordinate
  · intro candidate hcandidate
    have hentry : (Coordinate.position position, candidate) ∈ right.pending :=
      (LazyRevealProbe.State.mem_pendingAt_iff right (.position position) candidate).1 hcandidate
    rcases hstate.backward.pending (.position position) candidate hentry with
      hleft | ⟨output, hvalue, _hmiss⟩ | ⟨index, hcoordinate, _hmiss⟩
    · exact (LazyRevealProbe.State.mem_pendingAt_iff left
        (.position position) candidate).2 hleft
    · rw [hrightValue] at hvalue
      simp at hvalue
    · cases hcoordinate

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

set_option maxRecDepth 100000 in
theorem pendingAt_position_card_lt_of_mem_finalizeCleanFromTable
    (state : LazyRevealProbe.State Coordinate)
    (table : OtsSecretIndex → HashOutput)
    (position : Position)
    (hvalue : state.values (.position position) = none)
    (finalState : LazyRevealProbe.State Coordinate)
    (finalTable : OtsSecretIndex → HashOutput)
    (hfinal : some (finalState, finalTable) ∈ support
      (finalizeCleanFromTable state.coordinates.toList state table)) :
    (state.pendingAt (.position position)).card < Fintype.card Digest := by
  by_cases hempty : state.pendingAt (.position position) = ∅
  · rw [hempty, Finset.card_empty]
    exact Fintype.card_pos
  · obtain ⟨candidate, hcandidate⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hentry : (Coordinate.position position, candidate) ∈ state.pending :=
      (LazyRevealProbe.State.mem_pendingAt_iff state (.position position) candidate).1 hcandidate
    have hcoordinate : Coordinate.position position ∈ state.coordinates := by
      simp only [LazyRevealProbe.State.coordinates, Finset.mem_union, Finset.mem_image]
      exact Or.inr ⟨(.position position, candidate), hentry, rfl⟩
    have hexpose := evalDist_finalizeCleanFromTable_finset_expose_missing
      (.position position) state.coordinates state table hcoordinate hvalue
    have hfinalEval : some (finalState, finalTable) ∈
        support  (do
          let output ← completionOutputFromTable (.position position) table
          if state.hitAt (.position position) output then
            pure none
          else
            finalizeCleanFromTable (state.coordinates.toList.erase (.position position))
              (state.complete (.position position) output) table) := by
      rw [mem_support_iff_evalDist_apply_ne_zero] at hfinal ⊢
      rw [← hexpose]
      exact hfinal
    rw [mem_support_bind_iff] at hfinalEval
    obtain ⟨output, _houtput, hrest⟩ := hfinalEval
    have hmiss : ¬state.hitAt (.position position) output := by
      intro hhit
      simp [hhit] at hrest
    have hnotMem : truncateHash output ∉ state.pendingAt (.position position) := by
      simpa [LazyRevealProbe.State.hitAt] using hmiss
    exact (Finset.card_lt_iff_ne_univ _).2 (by
      intro huniv
      apply hnotMem
      rw [huniv]
      simp)

set_option maxRecDepth 100000 in
theorem exists_successful_finishObservedCleanRunFromTable_of_completionSafeEq
    {table : OtsSecretIndex → HashOutput}
    {left right : ObservedCleanRunResult α}
    (hstate : CompletionSafeStateEq table left.state right.state)
    (hleftTable : left.table = table) (hrightTable : right.table = table)
    (hfinish : ∃ finalResult, some finalResult ∈ support
      (finishObservedCleanRunFromTable (some left))) :
    ∃ finalResult, some finalResult ∈ support
      (finishObservedCleanRunFromTable (some right)) := by
  obtain ⟨leftFinal, hleftFinal⟩ := hfinish
  unfold finishObservedCleanRunFromTable at hleftFinal
  rw [mem_support_bind_iff] at hleftFinal
  obtain ⟨finalized, hfinalized, hreturn⟩ := hleftFinal
  cases finalized with
  | none => simp at hreturn
  | some finalized =>
      rcases finalized with ⟨finalState, finalTable⟩
      have hfinalizedTable : some (finalState, finalTable) ∈ support
          (finalizeCleanFromTable left.state.coordinates.toList left.state table) := by
        simpa [hleftTable] using hfinalized
      have hleftStart : ¬MissingChainStartHit table
          (directDeferredContext left.state) := by
        rw [← hleftTable]
        exact not_missingChainStartHit_of_mem_finishObservedCleanRunFromTable left leftFinal
          (by
            unfold finishObservedCleanRunFromTable
            rw [mem_support_bind_iff]
            exact ⟨some (finalState, finalTable), hfinalized, hreturn⟩)
      have hrightStart : ¬MissingChainStartHit table
          (directDeferredContext right.state) :=
        hstate.backward.not_missingChainStartHit_left_of_right hleftStart
      obtain ⟨rightFinal, hrightFinal⟩ := exists_successful_finalizeCleanFromTable table
        right.state.coordinates.toList right.state right.state.coordinates.nodup_toList (by
          intro entry hentry
          simp only [Finset.mem_toList, LazyRevealProbe.State.coordinates,
            Finset.mem_union, Finset.mem_image]
          exact Or.inr ⟨entry, hentry, rfl⟩) hrightStart (by
          intro position hrightValue
          have hleftValue : left.state.values (.position position) = none := by
            rw [hstate.forward.values, hrightValue]
          have hcard := pendingAt_position_card_lt_of_mem_finalizeCleanFromTable left.state table
            position hleftValue finalState finalTable hfinalizedTable
          rw [← hstate.pendingAt_eq_of_position_value_none position hleftValue]
          exact hcard)
      rcases rightFinal with ⟨rightFinalState, rightFinalTable⟩
      let result : ObservedCleanRunResult α :=
        ⟨rightFinalState, right.remaining, right.value, rightFinalTable, right.observations⟩
      refine ⟨result, ?_⟩
      unfold finishObservedCleanRunFromTable
      rw [mem_support_bind_iff]
      refine ⟨some (rightFinalState, rightFinalTable), ?_, by simp [result]⟩
      simpa [hrightTable] using hrightFinal

theorem successful_finishObservedCleanRunFromTable_iff_of_completionSafeEq
    {table : OtsSecretIndex → HashOutput}
    {left right : ObservedCleanRunResult α}
    (hstate : CompletionSafeStateEq table left.state right.state)
    (hleftTable : left.table = table) (hrightTable : right.table = table) :
    (∃ finalResult, some finalResult ∈ support
        (finishObservedCleanRunFromTable (some left))) ↔
      ∃ finalResult, some finalResult ∈ support
        (finishObservedCleanRunFromTable (some right)) := by
  constructor
  · exact exists_successful_finishObservedCleanRunFromTable_of_completionSafeEq hstate
      hleftTable hrightTable
  · exact exists_successful_finishObservedCleanRunFromTable_of_completionSafeEq
      ⟨hstate.backward, hstate.forward⟩ hrightTable hleftTable

theorem successfulDoomedFirstRootGoodForComparisonAt_iff_of_completionSafeEq
    {table : OtsSecretIndex → HashOutput} (ordinal : Nat) (target : Position)
    (rightRoot : Digest) (left right : ObservedCleanRunResult α)
    (hstate : CompletionSafeStateEq table left.state right.state)
    (hleftTable : left.table = table) (hrightTable : right.table = table)
    (hobservations : left.observations = right.observations) :
    ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
        table ordinal target rightRoot (some left) ↔
      ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
        table ordinal target rightRoot (some right) := by
  have hfinish := successful_finishObservedCleanRunFromTable_iff_of_completionSafeEq hstate
    hleftTable hrightTable
  have hdoomed :
      (¬DeferredCompletable table (directDeferredContext left.state)) ↔
        ¬DeferredCompletable table (directDeferredContext right.state) :=
    not_congr hstate.directDeferredCompletable_iff
  have hfirst :
      ObservedCleanRunOption.FirstExistingHiddenRootHitAt ordinal (some left) ↔
        ObservedCleanRunOption.FirstExistingHiddenRootHitAt ordinal (some right) := by
    rcases left with ⟨leftState, leftRemaining, leftValue, leftTable, leftObservations⟩
    rcases right with ⟨rightState, rightRemaining, rightValue, rightTable, rightObservations⟩
    simp only at hobservations ⊢
    subst rightObservations
    rfl
  have hposition := observedFirstLayerRootPosition?_eq_of_observations_eq ordinal left right
    hobservations
  have hprefix := observedPrefixProbes_eq_of_observations_eq ordinal left right hobservations
  simp only [ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt,
    ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget,
    ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt]
  rw [hfinish, hdoomed, hfirst, hposition, hprefix]

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
theorem relTriple_indicator_observedMaterializedBoundary_completionSafeEq
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (leftState rightState : LazyRevealProbe.State Coordinate)
    (fuel : Nat) (cache : SplitHashCache)
    (hstate : CompletionSafeStateEq table leftState rightState)
    (hleftStarts : StartTableAgrees leftState table) :
    RelTriple
      ((successfulObservedRootComparisonIndicator table ordinal target ∘
          fun observed ↦ (observed, rightRoot)) <$>
        observedMaterializedBoundary parameter publicRoot ftsSecret computation observations
          leftState fuel table cache)
      ((successfulObservedRootComparisonIndicator table ordinal target ∘
          fun observed ↦ (observed, rightRoot)) <$>
        observedMaterializedBoundary parameter publicRoot ftsSecret computation observations
          rightState fuel table cache)
      (EqRel Bool) := by
  let leftRun := observedMaterializedBoundary parameter publicRoot ftsSecret computation
    observations leftState fuel table cache
  let rightRun := observedMaterializedBoundary parameter publicRoot ftsSecret computation
    observations rightState fuel table cache
  have hbase := relTriple_observedMaterializedBoundary_completionSafeEq parameter publicRoot
    ftsSecret computation observations observations leftState rightState fuel table cache hstate
  have hleftSupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun result ↦ result ∈ support leftRun) (by
        intro result hresult
        simpa [leftRun] using hresult)
  have hbothSupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleftSupported
  apply relTriple_map
  apply relTriple_post_mono hbothSupported
  intro leftResult rightResult hrelation
  rcases hrelation with ⟨⟨hcompletion, hleftSupport⟩, hrightSupport⟩
  cases leftResult with
  | none =>
      cases rightResult with
      | none => rfl
      | some rightResult => simp [ObservedCompletionSafeEqRel] at hcompletion
  | some leftResult =>
      cases rightResult with
      | none => simp [ObservedCompletionSafeEqRel] at hcompletion
      | some rightResult =>
          rcases hcompletion with ⟨_hvalue, htable, _hremaining,
            ⟨suffix, hleftObservations, hrightObservations⟩, hfinalState⟩
          have hobservations : leftResult.observations = rightResult.observations := by
            rw [hleftObservations, hrightObservations]
          have hleftTable : leftResult.table = table :=
            (startTableAgrees_of_mem_observedMaterializedBoundary parameter publicRoot ftsSecret
              computation observations leftState fuel table cache hleftStarts leftResult
              (by simpa [leftRun] using hleftSupport)).1
          have hrightTable : rightResult.table = table := htable.symm.trans hleftTable
          apply Bool.eq_iff_iff.mpr
          simp only [Function.comp_apply, successfulObservedRootComparisonIndicator_eq_true_iff]
          exact successfulDoomedFirstRootGoodForComparisonAt_iff_of_completionSafeEq ordinal
            target rightRoot leftResult rightResult hfinalState hleftTable hrightTable
            hobservations

set_option maxRecDepth 100000 in
theorem evalDist_delayedSelectedRootIndicator_eq_of_finalizationContextEq
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (probe : Probe) (candidates : List Probe)
    (left right : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hcontext : FinalizationContextEq table (some left) (some right))
    (hvalues : left.state.values = right.state.values)
    (hrevealed : left.state.revealed = right.state.revealed) :
    evalDist
        (delayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
          computation observations ⟨probe, left, candidates⟩ fuel cache) =
      evalDist
        (delayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
          computation observations ⟨probe, right, candidates⟩ fuel cache) := by
  rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
  have hbase := relTriple_resolveDeferredPositionValue_of_finalizationViewEq table target
    left right hview hleftValid hrightValid hleftCompletable
  have hleftSupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun result ↦ result ∈ support (resolveDeferredPositionValue target left))
      (fun _ hresult ↦ hresult)
  have hbothSupported :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleftSupported
  unfold delayedSelectedRootIndicator
  apply evalDist_eq_of_relTriple_eqRel
  apply relTriple_bind hbothSupported
  intro leftResolved rightResolved hrelation
  rcases hrelation with ⟨⟨hresolution, hleftSupport⟩, hrightSupport⟩
  cases leftResolved with
  | none =>
      cases rightResolved with
      | none => exact relTriple_pure_pure rfl
      | some rightResolved => simp [FinalizationResolutionEq] at hresolution
  | some leftResolved =>
      cases rightResolved with
      | none => simp [FinalizationResolutionEq] at hresolution
      | some rightResolved =>
          rcases hresolution with
            ⟨houtput, hresolvedView, hleftResolvedValid, hrightResolvedValid,
              hleftResolvedCompletable⟩
          simp only
          rw [← houtput]
          by_cases hsafe : CandidatesAvoidRoots target (truncateHash leftResolved.output)
              rightRoot (candidates.take ordinal)
          · simp only [hsafe, ↓reduceIte]
            have hresolvedValues : leftResolved.state.values = rightResolved.state.values := by
              rw [resolveDeferredPositionValue_preserves_state_values target left leftResolved
                hleftSupport,
                resolveDeferredPositionValue_preserves_state_values target right rightResolved
                  hrightSupport]
              exact hvalues
            have hleftState := resolveDeferredPositionValue_state_eq_clearPending target left
              leftResolved hleftSupport
            have hrightState := resolveDeferredPositionValue_state_eq_clearPending target right
              rightResolved hrightSupport
            have hresolvedRevealed :
                leftResolved.state.revealed = rightResolved.state.revealed := by
              rw [hleftState, hrightState]
              simpa [LazyRevealProbe.State.clearPending] using hrevealed
            have hresolvedContext : FinalizationContextEq table
                (some leftResolved.toDeferredContext) (some rightResolved.toDeferredContext) :=
              ⟨hresolvedView, hleftResolvedValid, hrightResolvedValid,
                hleftResolvedCompletable⟩
            have hstate := completionSafeStateEq_materialized_of_finalizationContextEq table
              leftResolved.toDeferredContext rightResolved.toDeferredContext hresolvedContext
              hresolvedValues hresolvedRevealed
            have hstarts : StartTableAgrees
                (materializedDeferredState leftResolved.toDeferredContext) table := by
              intro index output hvalue
              rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
              apply hresolvedView.leftStarts ⟨lay, tree, leafIdx, chainIdx⟩ output
              simpa [materializedDeferredState, OtsSecretIndex.coordinate] using hvalue
            exact relTriple_indicator_observedMaterializedBoundary_completionSafeEq ordinal
              parameter root rightRoot ftsSecret table target computation observations
              (materializedDeferredState leftResolved.toDeferredContext)
              (materializedDeferredState rightResolved.toDeferredContext) fuel cache hstate hstarts
          · simp only [hsafe, ↓reduceIte]
            exact relTriple_pure_pure rfl

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

theorem evalDist_negated_eq_pure_true_of_true_not_mem
    (run : ProbComp Bool) (hfalse : true ∉ support run) :
    evalDist (Bool.not <$> run) = evalDist (pure true : ProbComp Bool) := by
  have heq := evalDist_eq_of_relTriple_eqRel (relTriple_eq_false_of_true_not_mem run hfalse)
  rw [evalDist_map]
  simpa using congrArg (fun distribution => Bool.not <$> distribution) heq

set_option maxRecDepth 100000 in
theorem evalDist_resolve_self_then_negated_delayedSelectedRootIndicator
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (probe : Probe) (candidates : List Probe)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) :
    evalDist (resolveDeferredPositionValue target context >>= fun resolved ↦
        match resolved with
        | none => pure true
        | some resolved => Bool.not <$>
            delayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
              computation observations ⟨probe, resolved.toDeferredContext, candidates⟩ fuel cache) =
      evalDist (Bool.not <$>
        delayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
          computation observations ⟨probe, context, candidates⟩ fuel cache) := by
  unfold delayedSelectedRootIndicator
  rw [map_bind]
  apply evalDist_bind_congr
  intro resolved hresolved
  cases resolved with
  | none => rfl
  | some resolved =>
      simp only
      rw [resolveDeferredPositionValue_of_resolved target context resolved hresolved]
      rfl

set_option maxRecDepth 1000000 in
theorem evalDist_hash_selected_self_positionNeutral
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (input : HashInput)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hbefore : ¬ordinal < snapshots.length)
    (hselected : ordinal <
      (appendPlannedSnapshot snapshots
        (rootAwareCandidateForPlan? parameter input
          (purePlanProbingHashQuery parameter input context.state)) context).length) :
    evalDist (resolveDeferredPositionValue target context >>= fun resolved ↦
        match resolved with
        | none => pure true
        | some resolved =>
            negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table target
              rightRoot
              (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
                (Sum.inl (Sum.inr input))) >>= next)
              snapshots observations resolved.toDeferredContext fuel cache) =
      evalDist
        (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table target
          rightRoot
          (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
            (Sum.inl (Sum.inr input))) >>= next)
          snapshots observations context fuel cache) := by
  let candidate? := rootAwareCandidateForPlan? parameter input
    (purePlanProbingHashQuery parameter input context.state)
  obtain ⟨candidate, hcandidate⟩ : ∃ candidate, candidate? = some candidate := by
    cases hcandidate : candidate? with
    | none =>
        simp [candidate?, hcandidate, appendPlannedSnapshot] at hselected
        omega
    | some candidate => exact ⟨candidate, rfl⟩
  have hlength : snapshots.length = ordinal := by
    simp [candidate?, hcandidate, appendPlannedSnapshot] at hselected
    omega
  let candidates :=
    (snapshots ++ [(⟨candidate, context⟩ : PlannedProbeSnapshot)]).map
      PlannedProbeSnapshot.toProbe
  unfold negatedDirectDelayedComputationObserve
  have hleft : evalDist (resolveDeferredPositionValue target context >>= fun resolved ↦
      match resolved with
      | none => pure true
      | some resolved => Bool.not <$>
          delayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
            (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
              (Sum.inl (Sum.inr input))) >>= next)
            observations ⟨candidate, resolved.toDeferredContext, candidates⟩ fuel cache) =
      evalDist (resolveDeferredPositionValue target context >>= fun resolved ↦
        match resolved with
        | none => pure true
        | some resolved => Bool.not <$>
            directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
              rightRoot
              (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
                (Sum.inl (Sum.inr input))) >>= next)
              snapshots observations resolved.toDeferredContext fuel cache) := by
    apply evalDist_bind_congr
    intro resolved hresolved
    cases resolved with
    | none => rfl
    | some resolved =>
        simp only
        have hvalues := resolveDeferredPositionValue_preserves_state_values target context resolved
          hresolved
        have hplan : purePlanProbingHashQuery parameter input resolved.state =
            purePlanProbingHashQuery parameter input context.state :=
          purePlanProbingHashQuery_eq_of_values_eq hvalues parameter input
        have hcandidateResolved : rootAwareCandidateForPlan? parameter input
            (purePlanProbingHashQuery parameter input resolved.state) = some candidate := by
          rw [hplan]
          simpa [candidate?] using hcandidate
        have hselectedResolved : ordinal <
            (appendPlannedSnapshot snapshots
              (rootAwareCandidateForPlan? parameter input
                (purePlanProbingHashQuery parameter input resolved.state))
              resolved.toDeferredContext).length := by
          simp [appendPlannedSnapshot, hcandidateResolved, hlength]
        rw [directDelayedSelectedRootIndicator_hash_eq_selected ordinal parameter root ftsSecret
          table target rightRoot input next snapshots observations resolved.toDeferredContext fuel
          cache hbefore hselectedResolved]
        simp [appendPlannedSnapshot, hcandidateResolved, hlength, candidates,
          List.get_eq_getElem]
  rw [← hleft]
  rw [directDelayedSelectedRootIndicator_hash_eq_selected ordinal parameter root ftsSecret table
    target rightRoot input next snapshots observations context fuel cache hbefore hselected]
  have hbase := evalDist_resolve_self_then_negated_delayedSelectedRootIndicator ordinal
    parameter root ftsSecret table target rightRoot
    (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
      (Sum.inl (Sum.inr input))) >>= next)
    observations candidate candidates context fuel cache
  simpa [candidate?, hcandidate, appendPlannedSnapshot, hlength, candidates,
    List.get_eq_getElem] using hbase

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem negatedDirectDelayedComputationObserve_hash_observerPositionNeutralAt
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (input : HashInput)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (hbefore : snapshots.length ≤ ordinal)
    (haligned : observations.map CleanProbeObservation.toProbe =
      snapshots.map PlannedProbeSnapshot.toProbe)
    (hclean : ∀ observation ∈ observations, ¬observation.ExistingHiddenHit)
    (hneutral : ∀ output laterSnapshots laterObservations,
      laterSnapshots.length ≤ ordinal →
      laterObservations.map CleanProbeObservation.toProbe =
        laterSnapshots.map PlannedProbeSnapshot.toProbe →
      (∀ observation ∈ laterObservations, ¬observation.ExistingHiddenHit) →
      ObserverPositionNeutralAt table target
        (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table target
          rightRoot (next output) laterSnapshots laterObservations)) :
    ObserverPositionNeutralAt table target
      (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table target
        rightRoot
        (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
          (Sum.inl (Sum.inr input))) >>= next)
        snapshots observations) := by
  intro context fuel cache hvalid hcompletable hensured
  have hnotSelectedBefore : ¬ordinal < snapshots.length := by omega
  let plan := purePlanProbingHashQuery parameter input context.state
  let candidate? := rootAwareCandidateForPlan? parameter input plan
  let nextSnapshots := appendPlannedSnapshot snapshots candidate? context
  let nextObservations := observationsAfterCandidate observations
    (materializedDeferredState context) candidate?
  have hnextAligned : nextObservations.map CleanProbeObservation.toProbe =
      nextSnapshots.map PlannedProbeSnapshot.toProbe := by
    cases hcandidate : candidate? <;>
      simp [nextObservations, nextSnapshots, observationsAfterCandidate, appendPlannedSnapshot,
        hcandidate, CleanProbeObservation.toProbe, cleanProbeObservation, haligned]
  by_cases hselected : ordinal < nextSnapshots.length
  · exact evalDist_hash_selected_self_positionNeutral ordinal parameter root ftsSecret table
      target rightRoot input next snapshots observations context fuel cache hnotSelectedBefore (by
        simpa [nextSnapshots, candidate?, plan] using hselected)
  · have hnextBefore : nextSnapshots.length ≤ ordinal := by omega
    have hnextNeutral :
        (∀ observation ∈ nextObservations, ¬observation.ExistingHiddenHit) →
          ObserverPositionNeutralAt table target
            (negatedDirectDelayedObserve
              (fun nextContext remaining (value : HashOutput × SplitHashCache)
                  laterSnapshots laterObservations ↦
                directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
                  rightRoot (next value.1) laterSnapshots laterObservations nextContext remaining
                  value.2)
              nextSnapshots nextObservations) := by
      intro hnextClean nextContext remaining value hnextValid hnextCompletable hnextEnsured
      simpa [negatedDirectDelayedObserve, negatedDirectDelayedComputationObserve] using
        hneutral value.1 nextSnapshots nextObservations hnextBefore hnextAligned hnextClean
          nextContext remaining value.2 hnextValid hnextCompletable hnextEnsured
    have heq := evalDist_directDelayed_eagerDirectDelayed_hash_not_selected_general_at ordinal
      parameter root ftsSecret table target rightRoot input next snapshots observations context fuel
      cache hnotSelectedBefore (by simpa [nextSnapshots, candidate?, plan] using hselected)
      hvalid hcompletable hensured haligned hclean (by
        simpa [nextSnapshots, nextObservations, candidate?, plan] using hnextNeutral)
    unfold negatedDirectDelayedComputationObserve
    calc
      _ = evalDist (Bool.not <$>
          eagerDirectDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
            rightRoot
            (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
              (Sum.inl (Sum.inr input))) >>= next)
            snapshots observations context fuel cache) := by
          unfold eagerDirectDelayedSelectedRootIndicator
          rw [if_neg hnotSelectedBefore, map_bind]
          apply evalDist_bind_congr
          intro resolved _hresolved
          cases resolved <;> rfl
      _ = _ := by
        rw [evalDist_map, evalDist_map]
        exact congrArg (fun distribution => Bool.not <$> distribution) heq.symm

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem negatedDirectDelayedComputationObserve_hash_observerSynchronized
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (input : HashInput)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (hbefore : snapshots.length ≤ ordinal)
    (haligned : observations.map CleanProbeObservation.toProbe =
      snapshots.map PlannedProbeSnapshot.toProbe)
    (hclean : ∀ observation ∈ observations, ¬observation.ExistingHiddenHit)
    (hsynchronized : ∀ output laterSnapshots laterObservations,
      laterSnapshots.length ≤ ordinal →
      laterObservations.map CleanProbeObservation.toProbe =
        laterSnapshots.map PlannedProbeSnapshot.toProbe →
      (∀ observation ∈ laterObservations, ¬observation.ExistingHiddenHit) →
      ObserverSynchronized table
        (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table target
          rightRoot (next output) laterSnapshots laterObservations))
    (hneutral : ∀ output laterSnapshots laterObservations,
      laterSnapshots.length ≤ ordinal →
      laterObservations.map CleanProbeObservation.toProbe =
        laterSnapshots.map PlannedProbeSnapshot.toProbe →
      (∀ observation ∈ laterObservations, ¬observation.ExistingHiddenHit) →
      ObserverPositionNeutral table
        (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table target
          rightRoot (next output) laterSnapshots laterObservations)) :
    ObserverSynchronized table
      (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table target
        rightRoot
        (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
          (Sum.inl (Sum.inr input))) >>= next)
        snapshots observations) where
  eq_of_synchronized left right fuel cache hcontext hvalues hrevealed := by
    have hnotSelected : ¬ordinal < snapshots.length := by omega
    let plan := purePlanProbingHashQuery parameter input left.state
    have hplan : purePlanProbingHashQuery parameter input right.state = plan := by
      rw [purePlanProbingHashQuery_eq_of_values_eq hvalues.symm parameter input]
    let candidate? := rootAwareCandidateForPlan? parameter input plan
    have hrightCandidate : rootAwareCandidateForPlan? parameter input
        (purePlanProbingHashQuery parameter input right.state) = candidate? := by
      rw [hplan]
    let nextLeftSnapshots := appendPlannedSnapshot snapshots candidate? left
    let nextRightSnapshots := appendPlannedSnapshot snapshots candidate? right
    let nextLeftObservations := observationsAfterCandidate observations
      (materializedDeferredState left) candidate?
    let nextRightObservations := observationsAfterCandidate observations
      (materializedDeferredState right) candidate?
    have hnextSnapshots : nextLeftSnapshots.map PlannedProbeSnapshot.toProbe =
        nextRightSnapshots.map PlannedProbeSnapshot.toProbe := by
      cases hcandidate : candidate? <;>
        simp [nextLeftSnapshots, nextRightSnapshots, appendPlannedSnapshot, hcandidate]
    have hnextLength : nextLeftSnapshots.length = nextRightSnapshots.length :=
      plannedProbeSnapshots_length_eq_of_toProbe_eq hnextSnapshots
    have hnextObservations : nextLeftObservations = nextRightObservations :=
      observationsAfterCandidate_materializedDeferredState_eq_of_finalizationContextEq table
        left right observations candidate? hcontext hvalues hrevealed
    have hnextAligned : nextLeftObservations.map CleanProbeObservation.toProbe =
        nextLeftSnapshots.map PlannedProbeSnapshot.toProbe := by
      cases hcandidate : candidate? <;>
        simp [nextLeftObservations, nextLeftSnapshots, observationsAfterCandidate,
          appendPlannedSnapshot, hcandidate, CleanProbeObservation.toProbe,
          cleanProbeObservation, haligned]
    by_cases hselected : ordinal < nextLeftSnapshots.length
    · have hselectedRight : ordinal < nextRightSnapshots.length := by
        rwa [← hnextLength]
      obtain ⟨candidate, hcandidate⟩ : ∃ candidate, candidate? = some candidate := by
        cases hcandidate : candidate? with
        | none =>
            simp [nextLeftSnapshots, appendPlannedSnapshot, hcandidate] at hselected
            omega
        | some candidate => exact ⟨candidate, rfl⟩
      have hlength : snapshots.length = ordinal := by
        simp [nextLeftSnapshots, appendPlannedSnapshot, hcandidate] at hselected
        omega
      have hcandidateLeft : rootAwareCandidateForPlan? parameter input
          (purePlanProbingHashQuery parameter input left.state) = some candidate := by
        simpa [candidate?, plan] using hcandidate
      have hcandidateRight : rootAwareCandidateForPlan? parameter input
          (purePlanProbingHashQuery parameter input right.state) = some candidate :=
        hrightCandidate.trans hcandidate
      unfold negatedDirectDelayedComputationObserve
      rw [evalDist_map, evalDist_map]
      apply congrArg (fun distribution => Bool.not <$> distribution)
      rw [directDelayedSelectedRootIndicator_hash_eq_selected ordinal parameter root ftsSecret
        table target rightRoot input next snapshots observations left fuel cache hnotSelected (by
          simpa [nextLeftSnapshots, candidate?, plan] using hselected)]
      rw [directDelayedSelectedRootIndicator_hash_eq_selected ordinal parameter root ftsSecret
        table target rightRoot input next snapshots observations right fuel cache hnotSelected (by
          simpa [nextRightSnapshots, candidate?, hrightCandidate] using hselectedRight)]
      simpa [hcandidateLeft, hcandidateRight, appendPlannedSnapshot, hlength,
        List.get_eq_getElem] using
        (evalDist_delayedSelectedRootIndicator_eq_of_finalizationContextEq ordinal parameter root
          ftsSecret table target rightRoot
          (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
            (Sum.inl (Sum.inr input))) >>= next)
          observations candidate
          ((snapshots ++ [(⟨candidate, left⟩ : PlannedProbeSnapshot)]).map
            PlannedProbeSnapshot.toProbe)
          left right fuel cache hcontext hvalues hrevealed)
    · have hnotSelectedRight : ¬ordinal < nextRightSnapshots.length := by
        rwa [← hnextLength]
      have hnextBefore : nextLeftSnapshots.length ≤ ordinal := by omega
      by_cases hnextClean : ∀ observation ∈ nextLeftObservations,
          ¬observation.ExistingHiddenHit
      · let observe := fun nextContext remaining
            (value : HashOutput × SplitHashCache) laterSnapshots laterObservations ↦
          directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
            rightRoot (next value.1) laterSnapshots laterObservations nextContext remaining
            value.2
        letI : ObserverSynchronized table
            (negatedDirectDelayedObserve observe nextLeftSnapshots nextLeftObservations) := ⟨by
          intro nextLeft nextRight remaining value hnextContext hnextValues hnextRevealed
          exact (hsynchronized value.1 nextLeftSnapshots nextLeftObservations hnextBefore
            hnextAligned hnextClean).eq_of_synchronized nextLeft nextRight remaining value.2
              hnextContext hnextValues hnextRevealed⟩
        letI : ObserverPositionNeutral table
            (negatedDirectDelayedObserve observe nextLeftSnapshots nextLeftObservations) := ⟨by
          intro position nextContext remaining value hvalid hcompletable hensured
          exact (hneutral value.1 nextLeftSnapshots nextLeftObservations hnextBefore hnextAligned
            hnextClean).eq_resolve position nextContext remaining value.2 hvalid hcompletable
              hensured⟩
        unfold negatedDirectDelayedComputationObserve
        rw [directDelayedSelectedRootIndicator_hash_eq_not_selected ordinal parameter root
          ftsSecret table target rightRoot input next snapshots observations left fuel cache
          hnotSelected (by simpa [nextLeftSnapshots, candidate?, plan] using hselected)]
        rw [directDelayedSelectedRootIndicator_hash_eq_not_selected ordinal parameter root
          ftsSecret table target rightRoot input next snapshots observations right fuel cache
          hnotSelected (by
            simpa [nextRightSnapshots, candidate?, hrightCandidate] using hnotSelectedRight)]
        have hsync :=
          evalDist_complement_runDirectWitness_finish_false_eq_of_synchronized table
            observe nextLeftSnapshots nextLeftObservations
            ((probingHashQueryAfterPlan parameter input plan).run cache) left right fuel
            hcontext hvalues hrevealed
        have htrace : CleanProbeObservationsEventEq nextLeftObservations
            nextRightObservations := by
          rw [hnextObservations]
          exact CleanProbeObservationsEventEq.refl nextRightObservations
        have hevent :=
          evalDist_complement_runDirectWitness_finish_false_eq_of_eventEq ordinal
            parameter root ftsSecret table target rightRoot next nextLeftSnapshots
            nextRightSnapshots nextLeftObservations nextRightObservations right fuel
            ((probingHashQueryAfterPlan parameter input plan).run cache) hselected
            hnotSelectedRight hnextSnapshots htrace
        rw [hsync]
        rw [hevent, hplan]
      · have hleftFalse : true ∉ support
            (directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
              rightRoot
              (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
                (Sum.inl (Sum.inr input))) >>= next)
              snapshots observations left fuel cache) := by
          intro htrue
          apply hnextClean
          have hleftStep : ¬ordinal <
              (appendPlannedSnapshot snapshots
                (rootAwareCandidateForPlan? parameter input
                  (purePlanProbingHashQuery parameter input left.state)) left).length := by
            simpa [nextLeftSnapshots, candidate?, plan] using hselected
          have hlength : observations.length = snapshots.length := by
            simpa only [List.length_map] using congrArg List.length haligned
          have hleftClean :=
            no_existingHiddenHit_afterCandidate_of_true_mem_hash_not_selected ordinal
              parameter root ftsSecret table target rightRoot input next snapshots observations
              left fuel cache hnotSelected hleftStep hlength htrue
          change ∀ observation ∈ observationsAfterCandidate observations
            (materializedDeferredState left) candidate?, ¬observation.ExistingHiddenHit
          exact hleftClean
        have hrightDirty : ¬∀ observation ∈ nextRightObservations,
            ¬observation.ExistingHiddenHit := by
          rwa [← hnextObservations]
        have hrightFalse : true ∉ support
            (directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
              rightRoot
              (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
                (Sum.inl (Sum.inr input))) >>= next)
              snapshots observations right fuel cache) := by
          intro htrue
          apply hrightDirty
          have hrightStep : ¬ordinal <
              (appendPlannedSnapshot snapshots
                (rootAwareCandidateForPlan? parameter input
                  (purePlanProbingHashQuery parameter input right.state)) right).length := by
            simpa [nextRightSnapshots, candidate?, hrightCandidate] using hnotSelectedRight
          have hlength : observations.length = snapshots.length := by
            simpa only [List.length_map] using congrArg List.length haligned
          have hrightClean :=
            no_existingHiddenHit_afterCandidate_of_true_mem_hash_not_selected ordinal
              parameter root ftsSecret table target rightRoot input next snapshots observations
              right fuel cache hnotSelected hrightStep hlength htrue
          change ∀ observation ∈ observationsAfterCandidate observations
            (materializedDeferredState right) candidate?, ¬observation.ExistingHiddenHit
          rw [← hrightCandidate]
          exact hrightClean
        unfold negatedDirectDelayedComputationObserve
        exact (evalDist_negated_eq_pure_true_of_true_not_mem _ hleftFalse).trans
          (evalDist_negated_eq_pure_true_of_true_not_mem _ hrightFalse).symm


end SphincsSecurity.Concrete.OtsProbeSimulation
