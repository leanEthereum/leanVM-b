import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveNormalize

/-!
# Support invariants for adaptive root normalization

A successful delayed selected-root execution certifies that every candidate already recorded before
the selected ordinal avoids both comparison roots. This is the unsafe half of eager normalization:
when an earlier candidate does not avoid the eagerly resolved root, the delayed indicator cannot be
true.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local instance] Classical.propDecidable

theorem positionValue_eq_of_private_of_deferredCompletable
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (context : DeferredContext) (output : HashOutput)
    (hprivate : context.values target = some output)
    (hcompletable : DeferredCompletable table context) :
    context.positionValue target = some output := by
  obtain ⟨completion, hcompletion⟩ := hcompletable
  unfold DeferredContext.positionValue
  cases hstate : context.state.values (.position target) with
  | none => simpa [hstate] using hprivate
  | some cached =>
      have hcached : completion (.position target) = cached :=
        hcompletion.1 (.position target) cached hstate
      have houtput : completion (.position target) = output :=
        hcompletion.2.1 target output hprivate
      have : cached = output := hcached.symm.trans houtput
      simpa [hstate, this]

theorem resolveDeferredPositionValue_output_eq_of_private_of_deferredCompletable
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (context : DeferredContext) (output : HashOutput)
    (hprivate : context.values target = some output)
    (hcompletable : DeferredCompletable table context)
    (resolved : DeferredResolution)
    (hresolved : some resolved ∈ support
      (resolveDeferredPositionValue target context)) :
    resolved.output = output := by
  have hknown := positionValue_eq_of_private_of_deferredCompletable table target context output
    hprivate hcompletable
  have hpreserved := resolveDeferredPositionValue_preserves_positionValue target target context
    resolved output hknown hresolved
  have hresolvedValue := resolveDeferredPositionValue_resolves target context resolved hresolved
  exact Option.some.inj (hresolvedValue.symm.trans hpreserved)

theorem privateValuesLE_of_done_runDirectResolvedWitnessFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult α)
    (hresult : DirectWitnessResult.done result ∈ support
      (runDirectResolvedWitnessFromTable context fuel table computation)) :
    PrivateValuesLE context result.context := by
  have hdetailed : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table computation) := by
    rw [← map_erase_runDirectResolvedWitnessFromTable computation context fuel table,
      support_map]
    exact ⟨DirectWitnessResult.done result, hresult, rfl⟩
  exact privateValuesLE_of_done_runDirectResolvedDetailedFromTable computation context fuel table
    result hdetailed

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem candidatesAvoidRoots_of_true_mem_directDelayedSelectedRootIndicator
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (output : HashOutput)
    (rightRoot : Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hprivate : context.values target = some output)
    (hcompletable : DeferredCompletable table context)
    (hlength : snapshots.length ≤ ordinal)
    (htrue : true ∈ support
      (directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
        computation snapshots observations context fuel cache)) :
    CandidatesAvoidRoots target (truncateHash output) rightRoot
      (snapshots.map PlannedProbeSnapshot.toProbe) := by
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
          CandidatesAvoidRoots target (truncateHash output) rightRoot
            (nextSnapshots.map PlannedProbeSnapshot.toProbe) := by
        rw [mem_support_bind_iff] at hnextTrue
        obtain ⟨result, hresult, hfinish⟩ := hnextTrue
        cases result with
        | stoppedFuel => simp [finishDirectDelayedSelectedRootIndicator] at hfinish
        | stoppedOrdinary => simp [finishDirectDelayedSelectedRootIndicator] at hfinish
        | stoppedPrivate witness => simp [finishDirectDelayedSelectedRootIndicator] at hfinish
        | done result =>
            let canonical := canonicalizeMaterializedValues table result.context
            have hprivateLE := privateValuesLE_of_done_runDirectResolvedWitnessFromTable
              runComputation context fuel table result hresult
            have hnextPrivate : canonical.values target = some output := by
              exact (hprivateLE.canonicalize_right table) target output hprivate
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
              · by_cases hnextCompletable : DeferredCompletable table canonical
                · simp only [hhit, hpublished, hnextCompletable, ↓reduceIte] at hfinish
                  exact ih result.value.1 nextSnapshots nextObservations canonical result.remaining
                    result.value.2 hnextPrivate hnextCompletable hnextLength hfinish
                · simp [hhit, hpublished, hnextCompletable] at hfinish
              · simp [hhit, hpublished] at hfinish
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              rw [directDelayedSelectedRootIndicator_uniform_eq ordinal parameter root ftsSecret
                table target rightRoot n next snapshots observations context fuel cache hbefore]
                at htrue
              exact continueAfter ((splitUniformImpl n).run cache) snapshots observations hlength
                htrue
          | inr input =>
              let plan := purePlanProbingHashQuery parameter input context.state
              let candidate? := rootAwareCandidateForPlan? parameter input plan
              let nextSnapshots := appendPlannedSnapshot snapshots candidate? context
              let nextObservations := observationsAfterCandidate observations
                (materializedDeferredState context) candidate?
              by_cases hselected : ordinal < nextSnapshots.length
              · rw [directDelayedSelectedRootIndicator_hash_eq_selected ordinal parameter root
                  ftsSecret table target rightRoot input next snapshots observations context fuel
                  cache hbefore (by simpa [nextSnapshots, candidate?, plan] using hselected)] at htrue
                have hnextLength : nextSnapshots.length = ordinal + 1 := by
                  have : nextSnapshots.length ≤ snapshots.length + 1 := by
                    cases hcandidate : candidate? <;>
                      simp [nextSnapshots, appendPlannedSnapshot, hcandidate]
                  omega
                have htake :
                    (nextSnapshots.map PlannedProbeSnapshot.toProbe).take ordinal =
                      snapshots.map PlannedProbeSnapshot.toProbe := by
                  cases hcandidate : candidate? with
                  | none =>
                      simp [nextSnapshots, appendPlannedSnapshot, hcandidate] at hselected
                      omega
                  | some candidate =>
                      have hsnapshotLength : snapshots.length = ordinal := by
                        simp [nextSnapshots, appendPlannedSnapshot, hcandidate] at hnextLength
                        omega
                      simp [nextSnapshots, appendPlannedSnapshot, hcandidate, hsnapshotLength]
                unfold delayedSelectedRootIndicator at htrue
                rw [mem_support_bind_iff] at htrue
                obtain ⟨resolvedOption, hresolvedOption, hrest⟩ := htrue
                cases resolvedOption with
                | none => simp at hrest
                | some resolved =>
                    have hselectedContext :
                        (nextSnapshots.get ⟨ordinal, hselected⟩).context = context := by
                      cases hcandidate : candidate? with
                      | none =>
                          exfalso
                          apply hbefore
                          simpa [nextSnapshots, appendPlannedSnapshot, hcandidate] using hselected
                      | some candidate =>
                          have hsnapshotLength : snapshots.length = ordinal := by
                            simp [nextSnapshots, appendPlannedSnapshot, hcandidate] at hnextLength
                            omega
                          simp [nextSnapshots, appendPlannedSnapshot, hcandidate,
                            hsnapshotLength, List.get_eq_getElem]
                    rw [hselectedContext] at hresolvedOption
                    have houtput :=
                      resolveDeferredPositionValue_output_eq_of_private_of_deferredCompletable
                        table target context output hprivate hcompletable resolved hresolvedOption
                    simp only at hrest
                    rw [houtput] at hrest
                    by_cases hsafe : CandidatesAvoidRoots target (truncateHash output) rightRoot
                        ((nextSnapshots.map PlannedProbeSnapshot.toProbe).take ordinal)
                    · simpa [htake] using hsafe
                    · have hunsafe : ¬CandidatesAvoidRoots target (truncateHash output) rightRoot
                        (((appendPlannedSnapshot snapshots
                          (rootAwareCandidateForPlan? parameter input
                            (purePlanProbingHashQuery parameter input context.state))
                          context).map PlannedProbeSnapshot.toProbe).take ordinal) := by
                        simpa [nextSnapshots, candidate?, plan] using hsafe
                      rw [map_toProbe_appendPlannedSnapshot] at hunsafe
                      simp [hunsafe] at hrest
              · have hnextLength : nextSnapshots.length ≤ ordinal := by omega
                rw [directDelayedSelectedRootIndicator_hash_eq_not_selected ordinal parameter root
                  ftsSecret table target rightRoot input next snapshots observations context fuel
                  cache hbefore (by simpa [nextSnapshots, candidate?, plan] using hselected)] at htrue
                have hnextAvoid := continueAfter
                  ((probingHashQueryAfterRootAwarePlan parameter input plan).run cache)
                  nextSnapshots nextObservations hnextLength htrue
                intro probe hprobe
                apply hnextAvoid probe
                cases hcandidate : candidate? with
                | none =>
                    simpa [nextSnapshots, appendPlannedSnapshot, hcandidate] using hprobe
                | some candidate =>
                    simp only [nextSnapshots, appendPlannedSnapshot, hcandidate, List.map_append,
                      List.map_singleton, List.mem_append]
                    exact Or.inl hprobe
      | inr message =>
          rw [directDelayedSelectedRootIndicator_signing_eq ordinal parameter root ftsSecret table
            target rightRoot message next snapshots observations context fuel cache hbefore] at htrue
          exact continueAfter ((maskedSign parameter root ftsSecret message).run cache) snapshots
            observations hlength htrue

theorem candidatesAvoidRoots_of_true_mem_runDirectWitness_finishDirectDelayed
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (output : HashOutput)
    (rightRoot : Digest) (β : Type)
    (next : β → OracleComp (OracleWorld + SigningSpec) α)
    (runComputation : OracleComp (LazyRevealProbe.World Coordinate) (β × SplitHashCache))
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat)
    (hprivate : context.values target = some output)
    (hlength : snapshots.length ≤ ordinal)
    (htrue : true ∈ support
      (runDirectResolvedWitnessFromTable context fuel table runComputation >>=
        finishDirectDelayedSelectedRootIndicator
          (canonicalizeDirectDelayedSelectedRootIndicator table
            (fun nextContext remaining value laterSnapshots laterObservations ↦
              directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
                rightRoot (next value.1) laterSnapshots laterObservations nextContext remaining
                value.2)) snapshots observations)) :
    CandidatesAvoidRoots target (truncateHash output) rightRoot
      (snapshots.map PlannedProbeSnapshot.toProbe) := by
  rw [mem_support_bind_iff] at htrue
  obtain ⟨result, hresult, hfinish⟩ := htrue
  cases result with
  | stoppedFuel => simp [finishDirectDelayedSelectedRootIndicator] at hfinish
  | stoppedOrdinary => simp [finishDirectDelayedSelectedRootIndicator] at hfinish
  | stoppedPrivate witness => simp [finishDirectDelayedSelectedRootIndicator] at hfinish
  | done result =>
      let canonical := canonicalizeMaterializedValues table result.context
      have hprivateLE := privateValuesLE_of_done_runDirectResolvedWitnessFromTable runComputation
        context fuel table result hresult
      have hnextPrivate : canonical.values target = some output := by
        exact (hprivateLE.canonicalize_right table) target output hprivate
      unfold finishDirectDelayedSelectedRootIndicator at hfinish
      unfold canonicalizeDirectDelayedSelectedRootIndicator at hfinish
      change true ∈ support
        (if PrivateStructuralHit canonical then pure false
          else if PublishedValues result.context.state then
            if DeferredCompletable table canonical then
              directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
                rightRoot (next result.value.1) snapshots observations canonical result.remaining
                result.value.2
            else pure false
          else pure false) at hfinish
      by_cases hhit : PrivateStructuralHit canonical
      · simp [hhit] at hfinish
      · by_cases hpublished : PublishedValues result.context.state
        · by_cases hnextCompletable : DeferredCompletable table canonical
          · simp only [hhit, hpublished, hnextCompletable, ↓reduceIte] at hfinish
            exact candidatesAvoidRoots_of_true_mem_directDelayedSelectedRootIndicator ordinal
              parameter root ftsSecret table target output rightRoot (next result.value.1)
              snapshots observations canonical result.remaining result.value.2 hnextPrivate
              hnextCompletable hlength hfinish
          · simp [hhit, hpublished, hnextCompletable] at hfinish
        · simp [hhit, hpublished] at hfinish

open OracleComp.ProgramLogic.Relational

set_option maxRecDepth 100000 in
theorem relTriple_runDirectWitness_finishDirectDelayed_of_safe_trace
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (output : HashOutput)
    (rightRoot : Digest) (β : Type)
    (next : β → OracleComp (OracleWorld + SigningSpec) α)
    (runComputation : OracleComp (LazyRevealProbe.World Coordinate) (β × SplitHashCache))
    (leftSnapshots rightSnapshots : List PlannedProbeSnapshot)
    (leftObservations rightObservations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat)
    (hprivate : context.values target = some output)
    (hleftLength : leftSnapshots.length ≤ ordinal)
    (hrightLength : rightSnapshots.length ≤ ordinal)
    (hsnapshots : leftSnapshots.map PlannedProbeSnapshot.toProbe =
      rightSnapshots.map PlannedProbeSnapshot.toProbe)
    (hsafeTrace : CandidatesAvoidRoots target (truncateHash output) rightRoot
        (rightSnapshots.map PlannedProbeSnapshot.toProbe) →
      CleanProbeObservationsEventEq leftObservations rightObservations) :
    RelTriple
      (runDirectResolvedWitnessFromTable context fuel table runComputation >>=
        finishDirectDelayedSelectedRootIndicator
          (canonicalizeDirectDelayedSelectedRootIndicator table
            (fun nextContext remaining value laterSnapshots laterObservations ↦
              directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
                rightRoot (next value.1) laterSnapshots laterObservations nextContext remaining
                value.2)) rightSnapshots rightObservations)
      (runDirectResolvedWitnessFromTable context fuel table runComputation >>=
        finishDirectDelayedSelectedRootIndicator
          (canonicalizeDirectDelayedSelectedRootIndicator table
            (fun nextContext remaining value laterSnapshots laterObservations ↦
              directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
                rightRoot (next value.1) laterSnapshots laterObservations nextContext remaining
                value.2)) leftSnapshots leftObservations)
      (EqRel Bool) := by
  let leftRun := runDirectResolvedWitnessFromTable context fuel table runComputation >>=
    finishDirectDelayedSelectedRootIndicator
      (canonicalizeDirectDelayedSelectedRootIndicator table
        (fun nextContext remaining value laterSnapshots laterObservations ↦
          directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
            rightRoot (next value.1) laterSnapshots laterObservations nextContext remaining
            value.2)) rightSnapshots rightObservations
  let rightRun := runDirectResolvedWitnessFromTable context fuel table runComputation >>=
    finishDirectDelayedSelectedRootIndicator
      (canonicalizeDirectDelayedSelectedRootIndicator table
        (fun nextContext remaining value laterSnapshots laterObservations ↦
          directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
            rightRoot (next value.1) laterSnapshots laterObservations nextContext remaining
            value.2)) leftSnapshots leftObservations
  by_cases hsafe : CandidatesAvoidRoots target (truncateHash output) rightRoot
      (rightSnapshots.map PlannedProbeSnapshot.toProbe)
  · have htrace := hsafeTrace hsafe
    have heval : evalDist leftRun = evalDist rightRun := by
      dsimp [leftRun, rightRun]
      apply evalDist_bind_congr
      intro result _hresult
      cases result with
      | stoppedFuel => rfl
      | stoppedOrdinary => rfl
      | stoppedPrivate witness => rfl
      | done result =>
          simp only [finishDirectDelayedSelectedRootIndicator,
            canonicalizeDirectDelayedSelectedRootIndicator]
          split
          · rfl
          · split
            · split
              · exact evalDist_directDelayedSelectedRootIndicator_eq_of_eventEq ordinal parameter
                  root ftsSecret table target rightRoot (next result.value.1) rightSnapshots
                  leftSnapshots rightObservations leftObservations
                  (canonicalizeMaterializedValues table result.context) result.remaining
                  result.value.2 (by omega) (by omega) hsnapshots.symm htrace.symm
              · rfl
            · rfl
    exact relTriple_eqRel_of_evalDist_eq heval
  · have hbase := relTriple_true leftRun rightRun
    have hleftSupported :=
      SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
        (fun value ↦ value ∈ support leftRun) (fun _ hvalue ↦ hvalue)
    have hbothSupported :=
      SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleftSupported
    apply relTriple_post_mono hbothSupported
    intro leftValue rightValue hrelation
    have hleftFalse : leftValue = false := by
      cases hleft : leftValue with
      | false => rfl
      | true =>
          have havoid := candidatesAvoidRoots_of_true_mem_runDirectWitness_finishDirectDelayed
            ordinal parameter root ftsSecret table target output rightRoot β next runComputation
            rightSnapshots rightObservations context fuel hprivate hrightLength (by
              simpa [leftRun, hleft] using hrelation.1.2)
          exact (hsafe havoid).elim
    have hrightFalse : rightValue = false := by
      cases hright : rightValue with
      | false => rfl
      | true =>
          have havoid := candidatesAvoidRoots_of_true_mem_runDirectWitness_finishDirectDelayed
            ordinal parameter root ftsSecret table target output rightRoot β next runComputation
            leftSnapshots leftObservations context fuel hprivate hleftLength (by
              simpa [rightRun, hright] using hrelation.2)
          have havoidRight : CandidatesAvoidRoots target (truncateHash output) rightRoot
              (rightSnapshots.map PlannedProbeSnapshot.toProbe) := by
            rwa [hsnapshots] at havoid
          exact (hsafe havoidRight).elim
    exact hleftFalse.trans hrightFalse.symm

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem relTriple_directDelayed_eagerDirectDelayed_hash_not_selected
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
    [ObserverSynchronized table
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
            (purePlanProbingHashQuery parameter input context.state))))]
    [ObserverPositionNeutral table
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
            (purePlanProbingHashQuery parameter input context.state))))]
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
        ¬observation.ExistingHiddenHit) :
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
  let candidate? := rootAwareCandidateForPlan? parameter input
    (purePlanProbingHashQuery parameter input context.state)
  let rightSnapshots := appendPlannedSnapshot snapshots candidate? context
  let rightObservations := observationsAfterCandidate observations
    (materializedDeferredState context) candidate?
  let runComputation :=
    (probingHashQueryAfterRootAwarePlan parameter input
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
    exact (evalDist_resolve_then_runDirectWitness_finish_false table target observe rightSnapshots
      rightObservations runComputation context fuel hvalid hcompletable).symm
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
  apply relTriple_of_evalDist_eq_left hdelayed
  apply relTriple_of_evalDist_eq_right heager.symm
  have hresolve := SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support
    (relTriple_refl (resolveDeferredPositionValue target context))
    (fun resolved ↦ resolved ∈ support (resolveDeferredPositionValue target context))
    (fun _ hresolved ↦ hresolved)
  apply relTriple_bind hresolve
  intro leftResolved rightResolved hrelation
  obtain ⟨rfl, hresolved⟩ := hrelation
  cases leftResolved with
  | none =>
      exact relTriple_pure_pure rfl
  | some resolved =>
      have hresolvedPrivate : resolved.values target = some resolved.output :=
        resolveDeferredPositionValue_installs target context resolved hresolved
      have hresolvedCompletable : DeferredCompletable table resolved.toDeferredContext :=
        hcompletable.of_resolveDeferredPositionValue hvalid target resolved hresolved
      let leftSnapshots := appendPlannedSnapshot snapshots candidate? resolved.toDeferredContext
      let leftObservations := observationsAfterCandidate observations
        (materializedDeferredState resolved.toDeferredContext) candidate?
      have hsnapshots : leftSnapshots.map PlannedProbeSnapshot.toProbe =
          rightSnapshots.map PlannedProbeSnapshot.toProbe := by
        cases hcandidate : candidate? <;>
          simp [leftSnapshots, rightSnapshots, appendPlannedSnapshot, hcandidate]
      have hlength : rightSnapshots.length ≤ ordinal := by
        simpa [rightSnapshots, candidate?] using Nat.le_of_not_gt hnotSelected
      apply relTriple_runDirectWitness_finishDirectDelayed_of_safe_trace ordinal parameter root
        ftsSecret table target resolved.output rightRoot HashOutput next runComputation
        leftSnapshots rightSnapshots leftObservations rightObservations resolved.toDeferredContext
        fuel hresolvedPrivate (by rwa [plannedProbeSnapshots_length_eq_of_toProbe_eq hsnapshots])
        hlength hsnapshots
      intro hsafe
      apply observationsAfterCandidate_eventEq_resolved_current_of_clean_of_avoids target context
        resolved hresolved observations candidate?
      · simpa [rightObservations, candidate?] using hclean
      · intro probe hprobe
        have hprobeSnapshots : probe ∈ rightSnapshots.map PlannedProbeSnapshot.toProbe := by
          rw [← haligned]
          simpa [rightObservations, candidate?] using hprobe
        exact (hsafe probe hprobeSnapshots).1

end SphincsSecurity.Concrete.OtsProbeSimulation
