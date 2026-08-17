import XmssSecurity.CappedUnifiedStructuralCollision
import XmssSecurity.CappedEncodingMonitor

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

set_option maxRecDepth 100000

structure UnifiedOutputObservation where
  address : EncodingSampleAddress
  output : HashOutput
deriving DecidableEq

abbrev UnifiedOutputTrace := List UnifiedOutputObservation

def unifiedOutputTraceFragment
    (input : EncodingSamplingWorld.Domain)
    (output : EncodingSamplingWorld.Range input) : UnifiedOutputTrace :=
  match input with
  | .inl _ => []
  | .inr address => [⟨address, output⟩]

noncomputable def unifiedOutputSamplingTraceImpl :
    QueryImpl EncodingSamplingWorld (WriterT UnifiedOutputTrace ProbComp) :=
  QueryImpl.withTraceAppend encodingSamplingWorldImpl unifiedOutputTraceFragment

def UnifiedOutputObservation.encodingAction? :
    UnifiedOutputObservation → Option EncodingMonitor.ObservedAction
  | ⟨⟨.query, some epoch, _⟩, output⟩ => some (.query epoch output)
  | ⟨⟨.sign, some epoch, _⟩, output⟩ => some (.sign epoch output)
  | _ => none

def UnifiedOutputTrace.encodingActions
    (trace : UnifiedOutputTrace) : EncodingActionTrace :=
  trace.filterMap UnifiedOutputObservation.encodingAction?

@[simp]
theorem unifiedOutputTraceFragment_encodingActions
    (input : EncodingSamplingWorld.Domain)
    (output : EncodingSamplingWorld.Range input) :
    (unifiedOutputTraceFragment input output).encodingActions =
      encodingSamplingTraceFragment input output := by
  cases input with
  | inl index => rfl
  | inr address =>
      rcases address with ⟨kind, epoch, sampledInput⟩
      cases kind <;> cases epoch <;> rfl

noncomputable def projectUnifiedOutputWriter
    (computation : WriterT UnifiedOutputTrace ProbComp α) :
    WriterT EncodingActionTrace ProbComp α :=
  computation.adapt UnifiedOutputTrace.encodingActions

@[simp]
theorem projectUnifiedOutputWriter_run
    (computation : WriterT UnifiedOutputTrace ProbComp α) :
    (projectUnifiedOutputWriter computation).run =
      (fun result => (result.1, result.2.encodingActions)) <$> computation.run :=
  rfl

@[simp]
theorem projectUnifiedOutputWriter_pure (value : α) :
    projectUnifiedOutputWriter (pure value) = pure value := by
  apply WriterT.ext
  change Prod.map id UnifiedOutputTrace.encodingActions <$>
      (pure value : WriterT UnifiedOutputTrace ProbComp α).run =
    (pure value : WriterT EncodingActionTrace ProbComp α).run
  simp [UnifiedOutputTrace.encodingActions]

theorem projectUnifiedOutputWriter_bind
    (computation : WriterT UnifiedOutputTrace ProbComp α)
    (next : α → WriterT UnifiedOutputTrace ProbComp β) :
    projectUnifiedOutputWriter (computation >>= next) =
      projectUnifiedOutputWriter computation >>= fun value =>
        projectUnifiedOutputWriter (next value) := by
  apply WriterT.ext
  change Prod.map id UnifiedOutputTrace.encodingActions <$>
      (computation >>= next).run =
    (projectUnifiedOutputWriter computation >>= fun value =>
      projectUnifiedOutputWriter (next value)).run
  rw [WriterT.run_bind', WriterT.run_bind', map_bind]
  unfold projectUnifiedOutputWriter
  simp only [WriterT.adapt, WriterT.run_mk]
  rw [bind_map_left]
  apply bind_congr
  intro result
  rcases result with ⟨value, trace⟩
  simp only [Prod.map_apply, id_eq, Functor.map_map]
  congr 1
  funext tailResult
  rcases tailResult with ⟨tailValue, tailTrace⟩
  simp [UnifiedOutputTrace.encodingActions, List.filterMap_append]

theorem unifiedOutputSamplingTraceImpl_query_run
    (input : EncodingSamplingWorld.Domain) :
    (unifiedOutputSamplingTraceImpl input).run =
      (fun output => (output, unifiedOutputTraceFragment input output)) <$>
        encodingSamplingWorldImpl input := by
  unfold unifiedOutputSamplingTraceImpl
  rw [QueryImpl.withTraceAppend_apply, WriterT.run_bind']
  rw [WriterT.run_monadLift']
  simp [WriterT.run_tell]

theorem unifiedOutputSamplingTraceImpl_support_trace_any
    (input : EncodingSamplingWorld.Domain)
    (result : EncodingSamplingWorld.Range input × UnifiedOutputTrace)
    (hmem : result ∈ support (unifiedOutputSamplingTraceImpl input).run) :
    result.2 = unifiedOutputTraceFragment input result.1 := by
  rw [unifiedOutputSamplingTraceImpl_query_run, support_map] at hmem
  obtain ⟨output, _houtput, heq⟩ := hmem
  subst result
  rfl

theorem projectUnifiedOutputWriter_unifiedOutputSamplingTraceImpl
    (input : EncodingSamplingWorld.Domain) :
    projectUnifiedOutputWriter (unifiedOutputSamplingTraceImpl input) =
      encodingSamplingTraceImpl input := by
  apply WriterT.ext
  rw [projectUnifiedOutputWriter_run,
    unifiedOutputSamplingTraceImpl_query_run]
  unfold encodingSamplingTraceImpl
  rw [QueryImpl.withTraceAppend_apply, WriterT.run_bind']
  rw [WriterT.run_monadLift']
  simp [WriterT.run_tell, Functor.map_map,
    unifiedOutputTraceFragment_encodingActions]

theorem projectUnifiedOutputWriter_simulateQ
    (computation : OracleComp EncodingSamplingWorld α) :
    projectUnifiedOutputWriter
        (simulateQ unifiedOutputSamplingTraceImpl computation) =
      simulateQ encodingSamplingTraceImpl computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_bind,
        projectUnifiedOutputWriter_bind, simulateQ_spec_query,
        simulateQ_spec_query,
        projectUnifiedOutputWriter_unifiedOutputSamplingTraceImpl]
      exact bind_congr ih

theorem unifiedOutputSamplingTrace_encodingProjection
    (computation : OracleComp EncodingSamplingWorld α) :
    (fun result => (result.1, result.2.encodingActions)) <$>
        (simulateQ unifiedOutputSamplingTraceImpl computation).run =
      (simulateQ encodingSamplingTraceImpl computation).run := by
  exact congrArg WriterT.run
    (projectUnifiedOutputWriter_simulateQ computation)

def UnifiedOutputObservation.IsStructuralHit
    (initialCache : QueryCache HashSpec)
    (targetInput : HashInput → HashInput)
    (observation : UnifiedOutputObservation) : Prop :=
  observation.address.epoch = none ∧
    truncateHash observation.output =
      Concrete.CacheView.digestAt initialCache
        (targetInput observation.address.input)

noncomputable instance
    (initialCache : QueryCache HashSpec)
    (targetInput : HashInput → HashInput) :
    DecidablePred (UnifiedOutputObservation.IsStructuralHit initialCache targetInput) :=
  Classical.decPred _

noncomputable def applyUnifiedOutputObserved
    (initialCache : QueryCache HashSpec)
    (targetInput : HashInput → HashInput)
    (state : EncodingMonitor.State)
    (observation : UnifiedOutputObservation) :
    Option (EncodingMonitor.State × Bool) :=
  if observation.IsStructuralHit initialCache targetInput then
    some (state, true)
  else
    match observation.encodingAction? with
    | none => some (state, false)
    | some action => CappedEncodingMonitor.State.applyObserved state action

noncomputable def runUnifiedOutputObserved
    (initialCache : QueryCache HashSpec)
    (targetInput : HashInput → HashInput) :
    EncodingMonitor.State → UnifiedOutputTrace → Bool
  | _state, [] => false
  | state, observation :: observations =>
      match applyUnifiedOutputObserved initialCache targetInput state observation with
      | none => false
      | some (nextState, hit) =>
          hit || runUnifiedOutputObserved initialCache targetInput nextState observations

@[simp]
theorem runUnifiedOutputObserved_nil
    (initialCache : QueryCache HashSpec)
    (targetInput : HashInput → HashInput)
    (state : EncodingMonitor.State) :
    runUnifiedOutputObserved initialCache targetInput state [] = false := rfl

@[simp]
theorem runUnifiedOutputObserved_cons
    (initialCache : QueryCache HashSpec)
    (targetInput : HashInput → HashInput)
    (state : EncodingMonitor.State)
    (observation : UnifiedOutputObservation)
    (observations : UnifiedOutputTrace) :
    runUnifiedOutputObserved initialCache targetInput state
        (observation :: observations) =
      match applyUnifiedOutputObserved initialCache targetInput state observation with
      | none => false
      | some (nextState, hit) =>
          hit || runUnifiedOutputObserved initialCache targetInput nextState observations :=
  rfl

theorem runUnifiedOutputObserved_of_encodingActions
    (initialCache : QueryCache HashSpec)
    (targetInput : HashInput → HashInput)
    (state : EncodingMonitor.State)
    (trace : UnifiedOutputTrace)
    (hhit : CappedEncodingMonitor.runObserved state trace.encodingActions = true) :
    runUnifiedOutputObserved initialCache targetInput state trace = true := by
  induction trace generalizing state with
  | nil =>
      simp [UnifiedOutputTrace.encodingActions,
        CappedEncodingMonitor.runObserved] at hhit
  | cons observation trace ih =>
      by_cases hstructural :
          observation.IsStructuralHit initialCache targetInput
      · simp [runUnifiedOutputObserved, applyUnifiedOutputObserved, hstructural]
      · cases haction : observation.encodingAction? with
        | none =>
            simp [UnifiedOutputTrace.encodingActions, haction] at hhit
            simp [runUnifiedOutputObserved, applyUnifiedOutputObserved,
              hstructural, haction, ih state hhit]
        | some action =>
            simp only [UnifiedOutputTrace.encodingActions,
              List.filterMap_cons, haction] at hhit
            cases happly : CappedEncodingMonitor.State.applyObserved state action with
            | none =>
                simp [CappedEncodingMonitor.runObserved, happly] at hhit
            | some result =>
                rcases result with ⟨nextState, hit⟩
                cases hit with
                | false =>
                    simp [CappedEncodingMonitor.runObserved, happly] at hhit
                    simp [runUnifiedOutputObserved, applyUnifiedOutputObserved,
                      hstructural, haction, happly, ih nextState hhit]
                | true =>
                    simp [runUnifiedOutputObserved, applyUnifiedOutputObserved,
                      hstructural, haction, happly]

noncomputable def runUnifiedOutputTraced
    (initialCache : QueryCache HashSpec)
    (targetInput : HashInput → HashInput)
    (state : EncodingMonitor.State)
    (computation : OracleComp EncodingSamplingWorld α) : ProbComp Bool :=
  (fun result => runUnifiedOutputObserved initialCache targetInput state result.2) <$>
    (simulateQ unifiedOutputSamplingTraceImpl computation).run

theorem runUnifiedOutputTraced_cons_probability_le
    (initialCache : QueryCache HashSpec)
    (targetInput : HashInput → HashInput)
    (state : EncodingMonitor.State)
    (observation : UnifiedOutputObservation)
    (computation : OracleComp EncodingSamplingWorld α)
    (resume : EncodingMonitor.State → ProbComp Bool)
    (hresume : ∀ nextState,
      Pr[(· = true) |
        runUnifiedOutputTraced initialCache targetInput nextState computation] ≤
          Pr[(· = true) | resume nextState]) :
    Pr[(· = true) |
      (fun result => runUnifiedOutputObserved initialCache targetInput state
          (observation :: result.2)) <$>
        (simulateQ unifiedOutputSamplingTraceImpl computation).run] ≤
      Pr[(· = true) |
        match applyUnifiedOutputObserved initialCache targetInput state observation with
        | none => pure false
        | some (nextState, hit) =>
            if hit then pure true else resume nextState] := by
  cases happly : applyUnifiedOutputObserved initialCache targetInput state observation with
  | none => simp [runUnifiedOutputObserved, happly]
  | some result =>
      rcases result with ⟨nextState, hit⟩
      cases hit with
      | false =>
          simpa only [runUnifiedOutputTraced, runUnifiedOutputObserved, happly,
            Bool.false_or, Bool.false_eq_true, ↓reduceIte] using hresume nextState
      | true => simp [runUnifiedOutputObserved, happly]

def IsUnifiedOutputRiskSample : EncodingSamplingWorld.Domain → Prop
  | .inr ⟨.query, some _, _⟩ => True
  | .inr ⟨_, none, _⟩ => True
  | _ => False

noncomputable instance : DecidablePred IsUnifiedOutputRiskSample :=
  Classical.decPred _

noncomputable def applyUnifiedOutputSampleMonitor
    (initialCache : QueryCache HashSpec)
    (targetInput : HashInput → HashInput)
    (address : EncodingSampleAddress)
    (resume : HashOutput → EncodingMonitor.State → ProbComp Bool)
    (state : EncodingMonitor.State) : ProbComp Bool :=
  match address.kind, address.epoch with
  | .query, some epoch =>
      CappedEncodingMonitor.applyProgrammedQueryMonitor epoch resume state
  | .sign, some epoch =>
      CappedEncodingMonitor.applyProgrammedSignAttemptMonitor epoch resume state
  | _, none =>
      uniformHashOutput >>= fun output =>
        if truncateHash output =
            Concrete.CacheView.digestAt initialCache (targetInput address.input) then
          pure true
        else resume output state
  | _, some _ => uniformHashOutput >>= fun output => resume output state

noncomputable def runUnifiedOutputRaw
    (initialCache : QueryCache HashSpec)
    (targetInput : HashInput → HashInput)
    (state : EncodingMonitor.State)
    (computation : OracleComp EncodingSamplingWorld α) : ProbComp Bool :=
  OracleComp.construct
    (C := fun _ => EncodingMonitor.State → ProbComp Bool)
    (fun _result _state => pure false)
    (fun input _next recursivelyMonitor state =>
      match input with
      | .inl index => do
          let output ← (liftM (unifSpec.query index) : ProbComp _)
          recursivelyMonitor output state
      | .inr address =>
          applyUnifiedOutputSampleMonitor initialCache targetInput address
            recursivelyMonitor state)
    computation state

theorem runUnifiedOutputRaw_true_probability_le
    (initialCache : QueryCache HashSpec)
    (targetInput : HashInput → HashInput)
    (state : EncodingMonitor.State)
    (computation : OracleComp EncodingSamplingWorld α) (queryBound : Nat)
    (hbound : computation.IsQueryBoundP IsUnifiedOutputRiskSample queryBound) :
    Pr[(· = true) |
      runUnifiedOutputRaw initialCache targetInput state computation] ≤
      (queryBound : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
        CappedEncodingMonitor.State.pendingRisk state := by
  induction computation using OracleComp.inductionOn generalizing state queryBound with
  | pure result =>
      rw [runUnifiedOutputRaw, OracleComp.construct_pure, probEvent_pure]
      simp
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      cases input with
      | inl index =>
          rw [runUnifiedOutputRaw, OracleComp.construct_query_bind]
          exact probEvent_bind_le_of_forall_le fun output _houtput =>
            ih output state queryBound
              (by simpa [IsUnifiedOutputRiskSample] using hbound.2 output)
      | inr address =>
          rcases address with ⟨kind, taggedEpoch, sampledInput⟩
          cases taggedEpoch with
          | none =>
              cases kind
              all_goals
                cases queryBound with
                | zero => simp [IsUnifiedOutputRiskSample] at hbound
                | succ queryBound =>
                    rw [runUnifiedOutputRaw, OracleComp.construct_query_bind]
                    unfold applyUnifiedOutputSampleMonitor
                    refine (uniformHashOutput_if_truncate_eq_probability_le
                      (Concrete.CacheView.digestAt initialCache
                        (targetInput sampledInput))
                      (fun output => runUnifiedOutputRaw initialCache targetInput state
                        (next output))
                      ((queryBound : ℝ≥0∞) *
                          (Fintype.card Digest : ℝ≥0∞)⁻¹ +
                        CappedEncodingMonitor.State.pendingRisk state) ?_).trans_eq ?_
                    · intro output _hmiss
                      exact ih output state queryBound
                        (by simpa [IsUnifiedOutputRiskSample] using hbound.2 output)
                    · rw [show Fintype.card Digest = 2 ^ digestBits by
                        exact card_bitVec digestBits]
                      push_cast
                      ring
          | some epoch =>
              cases kind with
              | side =>
                  rw [runUnifiedOutputRaw, OracleComp.construct_query_bind]
                  unfold applyUnifiedOutputSampleMonitor
                  exact probEvent_bind_le_of_forall_le fun output _houtput =>
                    ih output state queryBound
                      (by simpa [IsUnifiedOutputRiskSample] using hbound.2 output)
              | query =>
                  cases queryBound with
                  | zero => simp [IsUnifiedOutputRiskSample] at hbound
                  | succ queryBound =>
                      rw [runUnifiedOutputRaw, OracleComp.construct_query_bind]
                      unfold applyUnifiedOutputSampleMonitor
                      exact
                        CappedEncodingMonitor.applyProgrammedQueryMonitor_true_probability_le
                          epoch
                          (fun output nextState =>
                            runUnifiedOutputRaw initialCache targetInput nextState
                              (next output))
                          state queryBound
                          (fun output nextState => ih output nextState queryBound
                            (by simpa [IsUnifiedOutputRiskSample] using
                              hbound.2 output))
              | sign =>
                  rw [runUnifiedOutputRaw, OracleComp.construct_query_bind]
                  unfold applyUnifiedOutputSampleMonitor
                  exact
                    CappedEncodingMonitor.applyProgrammedSignAttemptMonitor_true_probability_le
                      epoch
                      (fun output nextState =>
                        runUnifiedOutputRaw initialCache targetInput nextState
                          (next output))
                      state queryBound
                      (fun output nextState => ih output nextState queryBound
                        (by simpa [IsUnifiedOutputRiskSample] using hbound.2 output))

theorem runUnifiedOutputTraced_probability_le_raw
    (initialCache : QueryCache HashSpec)
    (targetInput : HashInput → HashInput)
    (state : EncodingMonitor.State)
    (computation : OracleComp EncodingSamplingWorld α) :
    Pr[(· = true) |
      runUnifiedOutputTraced initialCache targetInput state computation] ≤
      Pr[(· = true) |
        runUnifiedOutputRaw initialCache targetInput state computation] := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure result =>
      simp [runUnifiedOutputTraced, runUnifiedOutputObserved,
        runUnifiedOutputRaw, unifiedOutputSamplingTraceImpl]
  | query_bind input next ih =>
      simp only [runUnifiedOutputTraced, simulateQ_query_bind, WriterT.run_bind',
        runUnifiedOutputRaw, OracleComp.construct_query_bind]
      cases input with
      | inl index =>
          simp only [OracleQuery.input_query, monadLift_self,
            unifiedOutputSamplingTraceImpl, QueryImpl.withTraceAppend_apply,
            encodingSamplingWorldImpl, QueryImpl.add_apply_inl, uniformWorldImpl,
            unifiedOutputTraceFragment, WriterT.run_bind', WriterT.run_monadLift',
            WriterT.run_tell, WriterT.run_pure', map_eq_bind_pure_comp, bind_assoc,
            pure_bind, List.nil_append, Prod.map_apply, id_eq, Function.comp_apply]
          apply probEvent_bind_mono
          intro output _houtput
          exact ih output state
      | inr address =>
          simp only [OracleQuery.input_query, monadLift_self,
            unifiedOutputSamplingTraceImpl, QueryImpl.withTraceAppend_apply,
            encodingSamplingWorldImpl, QueryImpl.add_apply_inr, encodingOutputImpl,
            unifiedOutputTraceFragment, WriterT.run_bind', WriterT.run_monadLift',
            WriterT.run_tell, WriterT.run_pure', map_eq_bind_pure_comp, bind_assoc,
            pure_bind, Prod.map_apply, id_eq, Function.comp_apply]
          rcases address with ⟨kind, taggedEpoch, sampledInput⟩
          cases taggedEpoch with
          | none =>
              cases kind <;>
                unfold applyUnifiedOutputSampleMonitor <;>
                apply probEvent_bind_mono <;>
                intro output _houtput <;>
                by_cases hhit : truncateHash output =
                  Concrete.CacheView.digestAt initialCache
                    (targetInput sampledInput) <;>
                simp [applyUnifiedOutputObserved, hhit,
                  UnifiedOutputObservation.IsStructuralHit,
                  UnifiedOutputObservation.encodingAction?]
              all_goals
                rw [← encodingSamplingWorldImpl]
                rw [← unifiedOutputSamplingTraceImpl]
                rw [← runUnifiedOutputTraced]
                have hih := ih output state
                rw [runUnifiedOutputRaw] at hih
                simp only [applyUnifiedOutputSampleMonitor] at hih
                rw [probEvent_eq_eq_probOutput, probEvent_eq_eq_probOutput] at hih
                apply hih
          | some epoch =>
              cases kind with
              | side =>
                  unfold applyUnifiedOutputSampleMonitor
                  apply probEvent_bind_mono
                  intro output _houtput
                  simp [applyUnifiedOutputObserved,
                    UnifiedOutputObservation.IsStructuralHit,
                    UnifiedOutputObservation.encodingAction?]
                  rw [← encodingSamplingWorldImpl]
                  rw [← unifiedOutputSamplingTraceImpl]
                  rw [← runUnifiedOutputTraced]
                  have hih := ih output state
                  rw [runUnifiedOutputRaw] at hih
                  simp only [applyUnifiedOutputSampleMonitor] at hih
                  rw [probEvent_eq_eq_probOutput, probEvent_eq_eq_probOutput] at hih
                  apply hih
              | query =>
                  unfold applyUnifiedOutputSampleMonitor
                  change _ ≤ Pr[(· = true) |
                    CappedEncodingMonitor.applyProgrammedQueryMonitor epoch
                      (fun output nextState =>
                        runUnifiedOutputRaw initialCache targetInput nextState
                          (next output)) state]
                  have hprob :
                      Pr[(· = true) |
                        CappedEncodingMonitor.applyProgrammedQueryMonitor epoch
                          (fun output nextState =>
                            runUnifiedOutputRaw initialCache targetInput nextState
                              (next output)) state] =
                      Pr[(· = true) |
                        CappedEncodingMonitor.applyHashOutputQueryMonitor epoch
                          (fun output nextState =>
                            runUnifiedOutputRaw initialCache targetInput nextState
                              (next output)) state] := by
                    rw [probEvent_def, probEvent_def,
                      CappedEncodingMonitor.applyProgrammedQueryMonitor_evalDist_eq]
                  rw [hprob]
                  rw [CappedEncodingMonitor.applyHashOutputQueryMonitor_eq_observed]
                  apply probEvent_bind_mono
                  intro output _houtput
                  convert
                    (runUnifiedOutputTraced_cons_probability_le initialCache
                      targetInput state ⟨⟨.query, some epoch, sampledInput⟩, output⟩
                      (next output)
                      (fun nextState =>
                        runUnifiedOutputRaw initialCache targetInput nextState
                          (next output))
                      (fun nextState => ih output nextState)) using 1
                  all_goals
                    simp [unifiedOutputSamplingTraceImpl,
                      encodingSamplingWorldImpl, map_eq_bind_pure_comp, Prod.map,
                      applyUnifiedOutputObserved,
                      UnifiedOutputObservation.IsStructuralHit,
                      UnifiedOutputObservation.encodingAction?] <;> try rfl
              | sign =>
                  unfold applyUnifiedOutputSampleMonitor
                  change _ ≤ Pr[(· = true) |
                    CappedEncodingMonitor.applyProgrammedSignAttemptMonitor epoch
                      (fun output nextState =>
                        runUnifiedOutputRaw initialCache targetInput nextState
                          (next output)) state]
                  have hprob :
                      Pr[(· = true) |
                        CappedEncodingMonitor.applyProgrammedSignAttemptMonitor epoch
                          (fun output nextState =>
                            runUnifiedOutputRaw initialCache targetInput nextState
                              (next output)) state] =
                      Pr[(· = true) |
                        CappedEncodingMonitor.applyHashOutputSignAttemptMonitor epoch
                          (fun output nextState =>
                            runUnifiedOutputRaw initialCache targetInput nextState
                              (next output)) state] := by
                    rw [probEvent_def, probEvent_def,
                      CappedEncodingMonitor.applyProgrammedSignAttemptMonitor_evalDist_eq]
                  rw [hprob]
                  rw [CappedEncodingMonitor.applyHashOutputSignAttemptMonitor_eq_observed]
                  apply probEvent_bind_mono
                  intro output _houtput
                  convert
                    (runUnifiedOutputTraced_cons_probability_le initialCache
                      targetInput state ⟨⟨.sign, some epoch, sampledInput⟩, output⟩
                      (next output)
                      (fun nextState =>
                        runUnifiedOutputRaw initialCache targetInput nextState
                          (next output))
                      (fun nextState => ih output nextState)) using 1
                  all_goals
                    simp [unifiedOutputSamplingTraceImpl,
                      encodingSamplingWorldImpl, map_eq_bind_pure_comp, Prod.map,
                      applyUnifiedOutputObserved,
                      UnifiedOutputObservation.IsStructuralHit,
                      UnifiedOutputObservation.encodingAction?] <;> try rfl

theorem runUnifiedOutputRaw_empty_true_probability_le
    (initialCache : QueryCache HashSpec)
    (targetInput : HashInput → HashInput)
    (computation : OracleComp EncodingSamplingWorld α) (queryBound : Nat)
    (hbound : computation.IsQueryBoundP IsUnifiedOutputRiskSample queryBound) :
    Pr[(· = true) |
      runUnifiedOutputRaw initialCache targetInput EncodingMonitor.State.empty
        computation] ≤
      (queryBound : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  simpa only [CappedEncodingMonitor.State.pendingRisk_empty, add_zero] using
    runUnifiedOutputRaw_true_probability_le initialCache targetInput
      EncodingMonitor.State.empty computation queryBound hbound

theorem unifiedOutputSamplingTrace_probability_le
    (initialCache : QueryCache HashSpec)
    (targetInput : HashInput → HashInput)
    (computation : OracleComp EncodingSamplingWorld α) (queryBound : Nat)
    (hbound : computation.IsQueryBoundP IsUnifiedOutputRiskSample queryBound) :
    Pr[fun result : α × UnifiedOutputTrace =>
        runUnifiedOutputObserved initialCache targetInput
          EncodingMonitor.State.empty result.2 = true |
      (simulateQ unifiedOutputSamplingTraceImpl computation).run] ≤
      (queryBound : ℝ≥0∞) /
        ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  change Pr[((fun hit : Bool => hit = true) ∘ fun result =>
      runUnifiedOutputObserved initialCache targetInput
        EncodingMonitor.State.empty result.2) |
    (simulateQ unifiedOutputSamplingTraceImpl computation).run] ≤ _
  rw [← probEvent_map]
  refine (runUnifiedOutputTraced_probability_le_raw initialCache targetInput
    EncodingMonitor.State.empty computation).trans ?_
  refine (runUnifiedOutputRaw_empty_true_probability_le initialCache targetInput
    computation queryBound hbound).trans_eq ?_
  rw [show Fintype.card Digest = 2 ^ digestBits by
    exact card_bitVec digestBits]
  rw [div_eq_mul_inv]

end XmssSecurity
