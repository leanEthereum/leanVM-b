import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveAfterRoot

/-!
# Adaptive chronological trace invariance

The normalization may materialize a structural value before a probe that does not select the
tracked ordinal. The two executions then share all operational state and differ only in historical
observation fields. This file records the exact observation semantics used by the terminal event
and proves that the observed interpreter preserves them.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def CleanProbeObservation.EventEq
    (left right : CleanProbeObservation) : Prop :=
  left.toProbe = right.toProbe ∧
    (left.ExistingHiddenHit ↔ right.ExistingHiddenHit)

def CleanProbeObservationsEventEq
    (left right : List CleanProbeObservation) : Prop :=
  List.Forall₂ CleanProbeObservation.EventEq left right

theorem CleanProbeObservationsEventEq.length_eq
    {left right : List CleanProbeObservation}
    (htrace : CleanProbeObservationsEventEq left right) :
    left.length = right.length :=
  List.Forall₂.length_eq htrace

theorem CleanProbeObservationsEventEq.refl
    (observations : List CleanProbeObservation) :
    CleanProbeObservationsEventEq observations observations := by
  induction observations with
  | nil => exact .nil
  | cons observation observations ih =>
      exact .cons ⟨rfl, Iff.rfl⟩ ih

theorem CleanProbeObservationsEventEq.symm
    {left right : List CleanProbeObservation}
    (htrace : CleanProbeObservationsEventEq left right) :
    CleanProbeObservationsEventEq right left := by
  induction htrace with
  | nil => exact .nil
  | cons hhead _htail ih =>
      exact .cons ⟨hhead.1.symm, hhead.2.symm⟩ ih

theorem CleanProbeObservationsEventEq.append_same
    {left right : List CleanProbeObservation}
    (htrace : CleanProbeObservationsEventEq left right)
    (suffix : List CleanProbeObservation) :
    CleanProbeObservationsEventEq (left ++ suffix) (right ++ suffix) := by
  exact List.rel_append htrace (CleanProbeObservationsEventEq.refl suffix)

theorem CleanProbeObservation.eventEq_installPositionValueAtProbe_of_clean_of_avoids
    (target : Position) (output : HashOutput) (observation : CleanProbeObservation)
    (hclean : ¬observation.ExistingHiddenHit)
    (havoid : observation.toProbe ≠
      ⟨.position target, truncateHash output⟩) :
    (installPositionValueAtProbe target output observation).EventEq observation := by
  refine ⟨installPositionValueAtProbe_toProbe target output observation, ?_⟩
  have hinstalled := not_existingHiddenHit_installPositionValueAtProbe_of_avoids target output
    observation hclean havoid
  constructor
  · exact fun hhit => (hinstalled hhit).elim
  · exact fun hhit => (hclean hhit).elim

theorem CleanProbeObservationsEventEq.map_installPositionValueAtProbe_of_clean_of_avoids
    (target : Position) (output : HashOutput)
    (observations : List CleanProbeObservation)
    (hclean : ∀ observation ∈ observations, ¬observation.ExistingHiddenHit)
    (havoid : CandidatesAvoidRoot target (truncateHash output)
      (observations.map CleanProbeObservation.toProbe)) :
    CleanProbeObservationsEventEq
      (observations.map (installPositionValueAtProbe target output)) observations := by
  induction observations with
  | nil => exact .nil
  | cons observation observations ih =>
      apply List.Forall₂.cons
      · apply CleanProbeObservation.eventEq_installPositionValueAtProbe_of_clean_of_avoids
        · exact hclean observation (by simp)
        · intro heq
          exact havoid observation.toProbe (by simp) heq
      · apply ih
        · intro other hother
          exact hclean other (by simp [hother])
        · intro candidate hcandidate
          exact havoid candidate (by simp [hcandidate])

theorem CleanProbeObservationsEventEq.toProbe_eq
    {left right : List CleanProbeObservation}
    (htrace : CleanProbeObservationsEventEq left right) :
    left.map CleanProbeObservation.toProbe =
      right.map CleanProbeObservation.toProbe := by
  induction htrace with
  | nil => rfl
  | cons hhead _htail ih => simp [hhead.1, ih]

theorem CleanProbeObservationsEventEq.get
    {left right : List CleanProbeObservation}
    (htrace : CleanProbeObservationsEventEq left right)
    (index : Nat) (hleft : index < left.length) (hright : index < right.length) :
    (left.get ⟨index, hleft⟩).EventEq (right.get ⟨index, hright⟩) :=
  List.Forall₂.get htrace hleft hright

def ObservedCleanRunOption.EventEq
    (left right : Option (ObservedCleanRunResult α)) : Prop :=
  match left, right with
  | none, none => True
  | some left, some right =>
      left.state = right.state ∧
        left.remaining = right.remaining ∧
        left.value = right.value ∧
        left.table = right.table ∧
        CleanProbeObservationsEventEq left.observations right.observations
  | _, _ => False

theorem ObservedCleanRunOption.EventEq.pure
    (leftObservations rightObservations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (value : α) (table : OtsSecretIndex → HashOutput)
    (htrace : CleanProbeObservationsEventEq leftObservations rightObservations) :
    ObservedCleanRunOption.EventEq
      (some ⟨state, fuel, value, table, leftObservations⟩)
      (some ⟨state, fuel, value, table, rightObservations⟩) := by
  exact ⟨rfl, rfl, rfl, rfl, htrace⟩

set_option maxRecDepth 100000 in
theorem relTriple_runObservedCleanFromTable_eventEq
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (leftObservations rightObservations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (htrace : CleanProbeObservationsEventEq leftObservations rightObservations) :
    RelTriple
      (runObservedCleanFromTable leftObservations state fuel table computation)
      (runObservedCleanFromTable rightObservations state fuel table computation)
      ObservedCleanRunOption.EventEq := by
  induction computation using OracleComp.inductionOn generalizing
      leftObservations rightObservations state fuel with
  | pure value =>
      rw [runObservedCleanFromTable, OracleComp.construct_pure,
        runObservedCleanFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure
        (ObservedCleanRunOption.EventEq.pure leftObservations rightObservations state fuel value
          table htrace)
  | query_bind query next ih =>
      rw [runObservedCleanFromTable, OracleComp.construct_query_bind,
        runObservedCleanFromTable, OracleComp.construct_query_bind]
      cases query with
      | uniform n =>
          apply relTriple_bind (relTriple_refl (liftM (unifSpec.query n)))
          intro leftValue rightValue hvalue
          subst rightValue
          exact ih leftValue leftObservations rightObservations state fuel htrace
      | hashOutput =>
          apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
          intro leftValue rightValue hvalue
          subst rightValue
          exact ih leftValue leftObservations rightObservations state fuel htrace
      | ensure coordinate =>
          exact ih () leftObservations rightObservations (state.ensure coordinate) fuel htrace
      | probe coordinate candidate =>
          cases fuel with
          | zero =>
              exact relTriple_pure_pure (by simp [ObservedCleanRunOption.EventEq])
          | succ remaining =>
              let observation := cleanProbeObservation state coordinate candidate
              have hnextTrace : CleanProbeObservationsEventEq
                  (leftObservations ++ [observation])
                  (rightObservations ++ [observation]) :=
                htrace.append_same [observation]
              by_cases hrevealed : coordinate ∈ state.revealed
              · simp only [hrevealed, ↓reduceIte]
                exact ih () (leftObservations ++ [observation])
                  (rightObservations ++ [observation]) state remaining hnextTrace
              · simp only [hrevealed, ↓reduceIte]
                exact ih () (leftObservations ++ [observation])
                  (rightObservations ++ [observation])
                  (state.addPending coordinate candidate) remaining hnextTrace
      | peek coordinate =>
          exact ih (state.values coordinate) leftObservations rightObservations state fuel htrace
      | publish coordinate =>
          exact ih () leftObservations rightObservations (state.publish coordinate) fuel htrace
      | reveal coordinate =>
          cases hvalue : state.values coordinate with
          | some value =>
              simp only [hvalue]
              exact ih value leftObservations rightObservations state fuel htrace
          | none =>
              simp only [hvalue]
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let value := table ⟨lay, tree, leafIdx, chainIdx⟩
                  by_cases hhit : state.hitAt (.chainStart lay tree leafIdx chainIdx) value
                  · simp only [value, hhit, ↓reduceIte]
                    exact relTriple_pure_pure (by simp [ObservedCleanRunOption.EventEq])
                  · simp only [value, hhit, ↓reduceIte]
                    exact ih value leftObservations rightObservations
                      (state.materialize (.chainStart lay tree leafIdx chainIdx) value) fuel htrace
              | position position =>
                  apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
                  intro leftOutput rightOutput houtput
                  subst rightOutput
                  by_cases hhit : state.hitAt (.position position) leftOutput
                  · simp only [hhit, ↓reduceIte]
                    exact relTriple_pure_pure (by simp [ObservedCleanRunOption.EventEq])
                  · simp only [hhit, ↓reduceIte]
                    exact ih leftOutput leftObservations rightObservations
                      (state.materialize (.position position) leftOutput) fuel htrace

set_option maxRecDepth 100000 in
theorem relTriple_observedMaterializedBoundary_eventEq
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (leftObservations rightObservations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (htrace : CleanProbeObservationsEventEq leftObservations rightObservations) :
    RelTriple
      (observedMaterializedBoundary parameter root ftsSecret computation leftObservations state
        fuel table cache)
      (observedMaterializedBoundary parameter root ftsSecret computation rightObservations state
        fuel table cache)
      ObservedCleanRunOption.EventEq := by
  induction computation using OracleComp.inductionOn generalizing
      leftObservations rightObservations state fuel cache with
  | pure value =>
      rw [observedMaterializedBoundary, OracleComp.construct_pure,
        observedMaterializedBoundary, OracleComp.construct_pure]
      exact relTriple_pure_pure
        (ObservedCleanRunOption.EventEq.pure leftObservations rightObservations state fuel
          (value, cache) table htrace)
  | query_bind query next ih =>
      rw [observedMaterializedBoundary, OracleComp.construct_query_bind,
        observedMaterializedBoundary, OracleComp.construct_query_bind]
      have continueAfter
          (leftRun rightRun : ProbComp (Option (ObservedCleanRunResult
            ((OracleWorld + SigningSpec).Range query × SplitHashCache))))
          (hrun : RelTriple leftRun rightRun ObservedCleanRunOption.EventEq) :
          RelTriple
            (leftRun >>= fun result =>
              match result with
              | none => pure none
              | some result =>
                  observedMaterializedBoundary parameter root ftsSecret
                    (next result.value.1) result.observations result.state result.remaining table
                    result.value.2)
            (rightRun >>= fun result =>
              match result with
              | none => pure none
              | some result =>
                  observedMaterializedBoundary parameter root ftsSecret
                    (next result.value.1) result.observations result.state result.remaining table
                    result.value.2)
            ObservedCleanRunOption.EventEq := by
        apply relTriple_bind hrun
        intro leftResult rightResult hresult
        cases leftResult with
        | none =>
            cases rightResult with
            | none => exact relTriple_pure_pure (by trivial)
            | some rightResult => simp [ObservedCleanRunOption.EventEq] at hresult
        | some leftResult =>
            cases rightResult with
            | none => simp [ObservedCleanRunOption.EventEq] at hresult
            | some rightResult =>
                simp only
                rcases hresult with
                  ⟨hstate, hremaining, hvalue, _htable, hnextTrace⟩
                have hnextValue : leftResult.value.1 = rightResult.value.1 :=
                  congrArg Prod.fst hvalue
                have hnextCache : leftResult.value.2 = rightResult.value.2 :=
                  congrArg Prod.snd hvalue
                rw [← hstate, ← hremaining, ← hnextValue, ← hnextCache]
                exact ih leftResult.value.1 leftResult.observations rightResult.observations
                  leftResult.state leftResult.remaining leftResult.value.2 hnextTrace
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              change Fin (n + 1) → OracleComp (OracleWorld + SigningSpec) α at next
              have hstep := relTriple_runObservedCleanFromTable_eventEq
                ((splitUniformImpl n).run cache) leftObservations rightObservations state fuel
                table htrace
              convert continueAfter _ _ hstep using 1 <;>
                apply bind_congr <;> intro result <;> cases result <;> rfl
          | inr input =>
              change HashOutput → OracleComp (OracleWorld + SigningSpec) α at next
              let publicContext := materializedCanonicalContext table state
              let plan := purePlanProbingHashQuery parameter input publicContext.state
              have hstep := relTriple_runObservedCleanFromTable_eventEq
                ((probingHashQueryAfterRootAwarePublicPlan parameter input publicContext.state
                  plan).run cache)
                leftObservations rightObservations state fuel table htrace
              convert continueAfter _ _ hstep using 1 <;>
                simp only [publicContext, plan, observedMaterializedBoundary] <;>
                apply bind_congr <;> intro result <;> cases result <;> rfl
      | inr message =>
          change Option Signature → OracleComp (OracleWorld + SigningSpec) α at next
          have hstep := relTriple_runObservedCleanFromTable_eventEq
            ((maskedSign parameter root ftsSecret message).run cache)
            leftObservations rightObservations state fuel table htrace
          convert continueAfter _ _ hstep using 1 <;>
            simp only [observedMaterializedBoundary] <;>
            apply bind_congr <;> intro result <;> cases result <;> rfl

theorem firstExistingHiddenHitAt_of_eventEq
    (left right : ObservedCleanRunResult α) (ordinal : Nat)
    (htrace : CleanProbeObservationsEventEq left.observations right.observations)
    (hfirst : FirstExistingHiddenHitAt left ordinal) :
    FirstExistingHiddenHitAt right ordinal := by
  obtain ⟨selected, hselected, hhit, hearlier⟩ := hfirst
  have hlength := htrace.length_eq
  let rightSelected : Fin right.observations.length :=
    ⟨selected.val, by rw [← hlength]; exact selected.isLt⟩
  refine ⟨rightSelected, hselected, ?_, ?_⟩
  · have hget := htrace.get selected.val selected.isLt rightSelected.isLt
    exact hget.2.mp hhit
  · intro rightEarlier hearlierLt hrightHit
    let leftEarlier : Fin left.observations.length :=
      ⟨rightEarlier.val, by rw [hlength]; exact rightEarlier.isLt⟩
    apply hearlier leftEarlier hearlierLt
    have hget := htrace.get rightEarlier.val leftEarlier.isLt rightEarlier.isLt
    exact hget.2.mpr hrightHit

theorem firstExistingHiddenHitAt_iff_of_eventEq
    (left right : ObservedCleanRunResult α) (ordinal : Nat)
    (htrace : CleanProbeObservationsEventEq left.observations right.observations) :
    FirstExistingHiddenHitAt left ordinal ↔ FirstExistingHiddenHitAt right ordinal := by
  exact ⟨firstExistingHiddenHitAt_of_eventEq left right ordinal htrace,
    firstExistingHiddenHitAt_of_eventEq right left ordinal htrace.symm⟩

theorem observedFirstLayerRootPosition?_eq_of_eventEq
    (ordinal : Nat) (left right : ObservedCleanRunResult α)
    (htrace : CleanProbeObservationsEventEq left.observations right.observations) :
    observedFirstLayerRootPosition? ordinal (some left) =
      observedFirstLayerRootPosition? ordinal (some right) := by
  have hlength := htrace.length_eq
  unfold observedFirstLayerRootPosition?
  by_cases hleft : ordinal < left.observations.length
  · have hright : ordinal < right.observations.length := by omega
    simp only [hleft, hright, ↓reduceDIte]
    have hget := htrace.get ordinal hleft hright
    rw [hget.1]
  · have hright : ¬ordinal < right.observations.length := by omega
    simp [hleft, hright]

theorem observedPrefixProbes_eq_of_eventEq
    (ordinal : Nat) (left right : ObservedCleanRunResult α)
    (htrace : CleanProbeObservationsEventEq left.observations right.observations) :
    observedPrefixProbes ordinal (some left) =
      observedPrefixProbes ordinal (some right) := by
  simp only [observedPrefixProbes]
  rw [List.map_take, List.map_take, htrace.toProbe_eq]

theorem finishObservedCleanRunFromTable_some_of_eventEq
    (left right : ObservedCleanRunResult α)
    (hrel : ObservedCleanRunOption.EventEq (some left) (some right))
    (hfinish : ∃ finalResult, some finalResult ∈ support
      (finishObservedCleanRunFromTable (some left))) :
    ∃ finalResult, some finalResult ∈ support
      (finishObservedCleanRunFromTable (some right)) := by
  rcases hrel with ⟨hstate, _hremaining, _hvalue, htable, _htrace⟩
  obtain ⟨finalResult, hfinal⟩ := hfinish
  unfold finishObservedCleanRunFromTable at hfinal
  simp only at hfinal
  rw [mem_support_bind_iff] at hfinal
  obtain ⟨finalized, hfinalized, hreturn⟩ := hfinal
  cases finalized with
  | none => simp at hreturn
  | some finalized =>
      rcases finalized with ⟨finalState, finalTable⟩
      let rightFinal : ObservedCleanRunResult α :=
        ⟨finalState, right.remaining, right.value, finalTable, right.observations⟩
      refine ⟨rightFinal, ?_⟩
      unfold finishObservedCleanRunFromTable
      rw [mem_support_bind_iff]
      refine ⟨some (finalState, finalTable), ?_, ?_⟩
      · simpa [← hstate, ← htable] using hfinalized
      · simp [rightFinal]

theorem finishObservedCleanRunFromTable_some_iff_of_eventEq
    (left right : ObservedCleanRunResult α)
    (hrel : ObservedCleanRunOption.EventEq (some left) (some right)) :
    (∃ finalResult, some finalResult ∈ support
        (finishObservedCleanRunFromTable (some left))) ↔
      ∃ finalResult, some finalResult ∈ support
        (finishObservedCleanRunFromTable (some right)) := by
  rcases hrel with ⟨hstate, hremaining, hvalue, htable, htrace⟩
  exact ⟨
    finishObservedCleanRunFromTable_some_of_eventEq left right
      ⟨hstate, hremaining, hvalue, htable, htrace⟩,
    finishObservedCleanRunFromTable_some_of_eventEq right left
      ⟨hstate.symm, hremaining.symm, hvalue.symm, htable.symm, htrace.symm⟩⟩

theorem firstExistingHiddenRootHitAt_of_eventEq
    (ordinal : Nat) (left right : ObservedCleanRunResult α)
    (htrace : CleanProbeObservationsEventEq left.observations right.observations)
    (hfirst : ObservedCleanRunOption.FirstExistingHiddenRootHitAt ordinal (some left)) :
    ObservedCleanRunOption.FirstExistingHiddenRootHitAt ordinal (some right) := by
  obtain ⟨selected, hselected, hfirst, hroot⟩ := hfirst
  have hlength := htrace.length_eq
  let rightSelected : Fin right.observations.length :=
    ⟨selected.val, by rw [← hlength]; exact selected.isLt⟩
  have hget := htrace.get selected.val selected.isLt rightSelected.isLt
  exact ⟨rightSelected, hselected,
    firstExistingHiddenHitAt_of_eventEq left right ordinal htrace hfirst, by
      rw [← hget.1]
      exact hroot⟩

theorem firstExistingHiddenRootHitAt_iff_of_eventEq
    (ordinal : Nat) (left right : ObservedCleanRunResult α)
    (htrace : CleanProbeObservationsEventEq left.observations right.observations) :
    ObservedCleanRunOption.FirstExistingHiddenRootHitAt ordinal (some left) ↔
      ObservedCleanRunOption.FirstExistingHiddenRootHitAt ordinal (some right) := by
  exact ⟨firstExistingHiddenRootHitAt_of_eventEq ordinal left right htrace,
    firstExistingHiddenRootHitAt_of_eventEq ordinal right left htrace.symm⟩

theorem successfulDoomedFirstRootGoodForComparisonAt_iff_of_eventEq
    (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (target : Position) (rightRoot : Digest)
    (left right : Option (ObservedCleanRunResult α))
    (hrel : ObservedCleanRunOption.EventEq left right) :
    ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
        table ordinal target rightRoot left ↔
      ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
        table ordinal target rightRoot right := by
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some right => simp [ObservedCleanRunOption.EventEq] at hrel
  | some left =>
      cases right with
      | none => simp [ObservedCleanRunOption.EventEq] at hrel
      | some right =>
          rcases hrel with ⟨hstate, hremaining, hvalue, htable, htrace⟩
          have hfinish := finishObservedCleanRunFromTable_some_iff_of_eventEq left right
            ⟨hstate, hremaining, hvalue, htable, htrace⟩
          have hfirst := firstExistingHiddenRootHitAt_iff_of_eventEq ordinal left right htrace
          have hposition := observedFirstLayerRootPosition?_eq_of_eventEq ordinal left right htrace
          have hprefix := observedPrefixProbes_eq_of_eventEq ordinal left right htrace
          simp only [ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt,
            ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget,
            ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt]
          rw [hfinish, hstate, hfirst, hposition, hprefix]

set_option maxRecDepth 100000 in
theorem evalDist_delayedSelectedRootIndicator_eq_of_eventEq
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (leftObservations rightObservations : List CleanProbeObservation)
    (selection : PrivateOrdinalSelection) (fuel : Nat) (cache : SplitHashCache)
    (htrace : CleanProbeObservationsEventEq leftObservations rightObservations) :
    evalDist
        (delayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
          computation leftObservations selection fuel cache) =
      evalDist
        (delayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
          computation rightObservations selection fuel cache) := by
  classical
  unfold delayedSelectedRootIndicator
  apply evalDist_bind_congr
  intro resolved hresolved
  cases resolved with
  | none => rfl
  | some resolved =>
      by_cases hsafe : CandidatesAvoidRoots target (truncateHash resolved.output) rightRoot
          (selection.candidates.take ordinal)
      · simp only [hsafe, ↓reduceIte]
        apply evalDist_eq_of_relTriple_eqRel
        apply relTriple_map
        apply relTriple_post_mono
          (relTriple_observedMaterializedBoundary_eventEq parameter root ftsSecret computation
            leftObservations rightObservations
            (materializedDeferredState resolved.toDeferredContext)
            fuel table cache htrace)
        intro left right hrel
        apply Bool.eq_iff_iff.mpr
        simp only [Function.comp_apply, successfulObservedRootComparisonIndicator_eq_true_iff]
        exact successfulDoomedFirstRootGoodForComparisonAt_iff_of_eventEq table ordinal target
          rightRoot left right hrel
      · simp [hsafe]

theorem plannedProbeSnapshots_length_eq_of_toProbe_eq
    {left right : List PlannedProbeSnapshot}
    (hsnapshots : left.map PlannedProbeSnapshot.toProbe =
      right.map PlannedProbeSnapshot.toProbe) :
    left.length = right.length := by
  simpa using congrArg List.length hsnapshots

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem evalDist_directDelayedSelectedRootIndicator_eq_of_eventEq
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
        (directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot computation leftSnapshots leftObservations context fuel cache) =
      evalDist
        (directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot computation rightSnapshots rightObservations context fuel cache) := by
  induction computation using OracleComp.inductionOn generalizing
      leftSnapshots rightSnapshots leftObservations rightObservations context fuel cache with
  | pure value =>
      simp [directDelayedSelectedRootIndicator, hleftBefore, hrightBefore]
  | query_bind query next ih =>
      rw [directDelayedSelectedRootIndicator, OracleComp.construct_query_bind,
        directDelayedSelectedRootIndicator, OracleComp.construct_query_bind]
      simp only [hleftBefore, hrightBefore, ↓reduceDIte]
      have continueAfter
          (run : ProbComp (DirectWitnessResult
            ((OracleWorld + SigningSpec).Range query × SplitHashCache)))
          (nextLeftSnapshots nextRightSnapshots : List PlannedProbeSnapshot)
          (nextLeftObservations nextRightObservations : List CleanProbeObservation)
          (hnextLeftBefore : ¬ordinal < nextLeftSnapshots.length)
          (hnextRightBefore : ¬ordinal < nextRightSnapshots.length)
          (hnextSnapshots : nextLeftSnapshots.map PlannedProbeSnapshot.toProbe =
            nextRightSnapshots.map PlannedProbeSnapshot.toProbe)
          (hnextTrace : CleanProbeObservationsEventEq
            nextLeftObservations nextRightObservations) :
          evalDist
              (run >>= finishDirectDelayedSelectedRootIndicator
                (canonicalizeDirectDelayedSelectedRootIndicator table
                  (fun nextContext remaining value laterSnapshots laterObservations ↦
                    directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table
                      target rightRoot (next value.1) laterSnapshots laterObservations
                      nextContext remaining value.2))
                nextLeftSnapshots nextLeftObservations) =
            evalDist
              (run >>= finishDirectDelayedSelectedRootIndicator
                (canonicalizeDirectDelayedSelectedRootIndicator table
                  (fun nextContext remaining value laterSnapshots laterObservations ↦
                    directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table
                      target rightRoot (next value.1) laterSnapshots laterObservations
                      nextContext remaining value.2))
                nextRightSnapshots nextRightObservations) := by
        apply evalDist_bind_congr
        intro result _hresult
        cases result with
        | stoppedFuel => rfl
        | stoppedOrdinary => rfl
        | stoppedPrivate output => rfl
        | done result =>
            simp only [finishDirectDelayedSelectedRootIndicator,
              canonicalizeDirectDelayedSelectedRootIndicator]
            split
            · rfl
            · split
              · split
                · exact ih result.value.1 nextLeftSnapshots nextRightSnapshots
                    nextLeftObservations nextRightObservations
                    (canonicalizeMaterializedValues table result.context) result.remaining
                    result.value.2 hnextLeftBefore hnextRightBefore hnextSnapshots hnextTrace
                · rfl
              · rfl
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              change Fin (n + 1) → OracleComp (OracleWorld + SigningSpec) α at next
              simp only
              exact continueAfter
                (runDirectResolvedWitnessFromTable context fuel table
                  ((splitUniformImpl n).run cache)) leftSnapshots rightSnapshots
                leftObservations rightObservations hleftBefore hrightBefore hsnapshots htrace
          | inr input =>
              change HashOutput → OracleComp (OracleWorld + SigningSpec) α at next
              simp only
              let plan := purePlanProbingHashQuery parameter input context.state
              let candidate? := rootAwareCandidateForPlan? parameter input plan
              let nextLeftSnapshots := appendPlannedSnapshot leftSnapshots candidate? context
              let nextRightSnapshots := appendPlannedSnapshot rightSnapshots candidate? context
              let nextLeftObservations := observationsAfterCandidate leftObservations
                (materializedDeferredState context) candidate?
              let nextRightObservations := observationsAfterCandidate rightObservations
                (materializedDeferredState context) candidate?
              have hnextSnapshots : nextLeftSnapshots.map PlannedProbeSnapshot.toProbe =
                  nextRightSnapshots.map PlannedProbeSnapshot.toProbe := by
                cases hcandidate : candidate? <;>
                  simp [nextLeftSnapshots, nextRightSnapshots, appendPlannedSnapshot,
                    hcandidate, hsnapshots]
              have hnextLength : nextLeftSnapshots.length = nextRightSnapshots.length :=
                plannedProbeSnapshots_length_eq_of_toProbe_eq hnextSnapshots
              have hnextTrace : CleanProbeObservationsEventEq
                  nextLeftObservations nextRightObservations := by
                cases hcandidate : candidate? with
                | none =>
                    simpa [nextLeftObservations, nextRightObservations,
                      observationsAfterCandidate, hcandidate] using htrace
                | some candidate =>
                    simpa [nextLeftObservations, nextRightObservations,
                      observationsAfterCandidate, hcandidate] using
                      htrace.append_same
                        [cleanProbeObservation (materializedDeferredState context)
                          candidate.coordinate candidate.candidate]
              by_cases hnextSelected : ordinal < nextLeftSnapshots.length
              · have hnextSelectedRight : ordinal < nextRightSnapshots.length := by
                  rw [← hnextLength]
                  exact hnextSelected
                obtain ⟨candidate, hcandidate⟩ : ∃ candidate, candidate? = some candidate := by
                  cases hcandidate : candidate? with
                  | none =>
                      simp [nextLeftSnapshots, appendPlannedSnapshot, hcandidate] at hnextSelected
                      omega
                  | some candidate => exact ⟨candidate, rfl⟩
                have hleftLength : leftSnapshots.length = ordinal := by
                  have hnextLength' : nextLeftSnapshots.length = leftSnapshots.length + 1 := by
                    simp [nextLeftSnapshots, appendPlannedSnapshot, hcandidate]
                  omega
                have hrightLength : rightSnapshots.length = ordinal := by
                  have hlength := plannedProbeSnapshots_length_eq_of_toProbe_eq hsnapshots
                  omega
                have hleftGet : nextLeftSnapshots.get ⟨ordinal, hnextSelected⟩ =
                    (⟨candidate, context⟩ : PlannedProbeSnapshot) := by
                  simp [nextLeftSnapshots, appendPlannedSnapshot, hcandidate, ← hleftLength,
                    List.get_eq_getElem]
                have hrightGet : nextRightSnapshots.get ⟨ordinal, hnextSelectedRight⟩ =
                    (⟨candidate, context⟩ : PlannedProbeSnapshot) := by
                  simp [nextRightSnapshots, appendPlannedSnapshot, hcandidate, ← hrightLength,
                    List.get_eq_getElem]
                have hselection :
                    (⟨(nextLeftSnapshots.get ⟨ordinal, hnextSelected⟩).probe,
                      (nextLeftSnapshots.get ⟨ordinal, hnextSelected⟩).context,
                      nextLeftSnapshots.map PlannedProbeSnapshot.toProbe⟩ :
                        PrivateOrdinalSelection) =
                      ⟨(nextRightSnapshots.get ⟨ordinal, hnextSelectedRight⟩).probe,
                        (nextRightSnapshots.get ⟨ordinal, hnextSelectedRight⟩).context,
                        nextRightSnapshots.map PlannedProbeSnapshot.toProbe⟩ := by
                  rw [hleftGet, hrightGet, hnextSnapshots]
                have hactualLeft : ordinal <
                    (appendPlannedSnapshot leftSnapshots
                      (rootAwareCandidateForPlan? parameter input
                        (purePlanProbingHashQuery parameter input context.state)) context).length := by
                  simpa [nextLeftSnapshots, candidate?, plan] using hnextSelected
                have hactualRight : ordinal <
                    (appendPlannedSnapshot rightSnapshots
                      (rootAwareCandidateForPlan? parameter input
                        (purePlanProbingHashQuery parameter input context.state)) context).length := by
                  simpa [nextRightSnapshots, candidate?, plan] using hnextSelectedRight
                rw [dif_pos hactualLeft, dif_pos hactualRight]
                rw [hselection]
                exact evalDist_delayedSelectedRootIndicator_eq_of_eventEq ordinal parameter root
                  ftsSecret table target rightRoot
                  ((liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
                    (Sum.inl (Sum.inr input))) :
                      OracleComp (OracleWorld + SigningSpec) HashOutput) >>= next)
                  leftObservations rightObservations _ fuel cache htrace
              · have hnextSelectedRight : ¬ordinal < nextRightSnapshots.length := by
                  rw [← hnextLength]
                  exact hnextSelected
                have hactualLeft : ¬ordinal <
                    (appendPlannedSnapshot leftSnapshots
                      (rootAwareCandidateForPlan? parameter input
                        (purePlanProbingHashQuery parameter input context.state)) context).length := by
                  simpa [nextLeftSnapshots, candidate?, plan] using hnextSelected
                have hactualRight : ¬ordinal <
                    (appendPlannedSnapshot rightSnapshots
                      (rootAwareCandidateForPlan? parameter input
                        (purePlanProbingHashQuery parameter input context.state)) context).length := by
                  simpa [nextRightSnapshots, candidate?, plan] using hnextSelectedRight
                rw [dif_neg hactualLeft, dif_neg hactualRight]
                convert continueAfter
                  (runDirectResolvedWitnessFromTable context fuel table
                    ((probingHashQueryAfterRootAwarePlan parameter input plan).run cache))
                  nextLeftSnapshots nextRightSnapshots nextLeftObservations nextRightObservations
                  hnextSelected hnextSelectedRight hnextSnapshots hnextTrace using 1 <;> rfl
      | inr message =>
          change Option Signature → OracleComp (OracleWorld + SigningSpec) α at next
          simp only
          exact continueAfter
            (runDirectResolvedWitnessFromTable context fuel table
              ((maskedSign parameter root ftsSecret message).run cache))
            leftSnapshots rightSnapshots leftObservations rightObservations hleftBefore
            hrightBefore hsnapshots htrace

end SphincsSecurity.Concrete.OtsProbeSimulation
