import XmssSecurity.CappedExactFirstLaneTransport
import XmssSecurity.CappedGlobalChainHighPublicExperiment

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000
set_option linter.constructorNameAsVariable false

noncomputable def globalHighDirectExactQueryResult
    (keyView : ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : GlobalHighDirectExactTracedState)
    (result : (OracleWorld + SigningSpec).Range input ×
      GlobalHighDirectTracedState) :
    (OracleWorld + SigningSpec).Range input ×
      GlobalHighDirectExactTracedState :=
  (result.1, GlobalExactTracedState.mk result.2.1 result.2.2
    (encodingActionTraceUpdate keyView.secretKey input
      (initialState.causalState.cache, []) result.1
      (result.2.1.cache, []) initialState.encodingTrace))

theorem globalHighDirectExactTracedLift_eq_map
    (keyView : ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (base : StateT GlobalCausalHashState
      (OracleComp
        (RevealProbeOracleSimulation.World GlobalChainValueIndex))
      ((OracleWorld + SigningSpec).Range input))
    (initialState : GlobalHighDirectExactTracedState) :
    (globalHighDirectExactTracedLift keyView input base).run initialState =
      globalHighDirectExactQueryResult keyView input initialState <$>
        ((fun result => (result.1,
          (result.2, initialState.attackerTrace ++
            attackerActionFragment input result.1))) <$>
          base.run initialState.causalState) := by
  unfold globalHighDirectExactTracedLift globalHighDirectExactQueryResult
    globalExactTracedNextState
  simp [StateT.run_mk, Functor.map_map, Function.comp_def]

theorem globalHighDirectTracedMappedAdversaryImpl_run_eq_map
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalHighDirectTracedState) :
    (globalHighDirectTracedMappedAdversaryImpl keyView edgeHigh input).run
        state =
      (fun result => (result.1,
        (result.2, state.2 ++ attackerActionFragment input result.1))) <$>
        (globalHighDirectBaseMappedAdversaryImpl keyView edgeHigh input).run
          state.1 := by
  unfold globalHighDirectTracedMappedAdversaryImpl
  simp [StateT.run_mk, map_eq_bind_pure_comp]

theorem globalHighDirectBaseMappedAdversaryImpl_sign
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (request : SignRequest) :
    globalHighDirectBaseMappedAdversaryImpl keyView edgeHigh (.inr request) =
      globalHighDirectSigningImpl keyView request := by
  unfold globalHighDirectBaseMappedAdversaryImpl
  exact QueryImpl.add_apply_inr _ _ request

theorem globalHighDirectExactTracedMappedAdversaryImpl_sign
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (request : SignRequest) :
    globalHighDirectExactTracedMappedAdversaryImpl keyView edgeHigh
        (.inr request) =
      globalHighDirectExactTracedSigningImpl keyView request := by
  unfold globalHighDirectExactTracedMappedAdversaryImpl
  exact QueryImpl.add_apply_inr _ _ request

theorem globalHighDirectExactTracedMappedAdversaryImpl_uniform_eq_map
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (n : Nat)
    (initialState : GlobalHighDirectExactTracedState) :
    (globalHighDirectExactTracedMappedAdversaryImpl keyView edgeHigh
      (.inl (.inl n))).run initialState =
      globalHighDirectExactQueryResult keyView (.inl (.inl n)) initialState <$>
        (globalHighDirectTracedMappedAdversaryImpl keyView edgeHigh
          (.inl (.inl n))).run
            (initialState.causalState, initialState.attackerTrace) := by
  change (globalHighDirectExactTracedLift keyView (.inl (.inl n))
    (globalHighDirectUniformImpl n)).run initialState = _
  change _ = globalHighDirectExactQueryResult keyView (.inl (.inl n))
    initialState <$> ((fun result => (result.1,
      (result.2, initialState.attackerTrace ++
        attackerActionFragment (.inl (.inl n)) result.1))) <$>
          (globalHighDirectUniformImpl n).run initialState.causalState)
  exact globalHighDirectExactTracedLift_eq_map keyView (.inl (.inl n))
    (globalHighDirectUniformImpl n) initialState

theorem globalHighDirectExactTracedMappedAdversaryImpl_hash_eq_map
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (hashInput : HashInput)
    (initialState : GlobalHighDirectExactTracedState) :
    (globalHighDirectExactTracedMappedAdversaryImpl keyView edgeHigh
      (.inl (.inr hashInput))).run initialState =
      globalHighDirectExactQueryResult keyView (.inl (.inr hashInput))
        initialState <$>
        (globalHighDirectTracedMappedAdversaryImpl keyView edgeHigh
          (.inl (.inr hashInput))).run
            (initialState.causalState, initialState.attackerTrace) := by
  let base := globalCausalAttackerHashQueryFromHigh
    (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey hashInput
  change (globalHighDirectExactTracedLift keyView (.inl (.inr hashInput))
    base).run initialState = _
  change _ = globalHighDirectExactQueryResult keyView (.inl (.inr hashInput))
    initialState <$> ((fun result => (result.1,
      (result.2, initialState.attackerTrace ++
        attackerActionFragment (.inl (.inr hashInput)) result.1))) <$>
          base.run initialState.causalState)
  exact globalHighDirectExactTracedLift_eq_map keyView
    (.inl (.inr hashInput)) base initialState

theorem globalHighDirectExactTracedMappedAdversaryImpl_sign_eq_map
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (request : SignRequest)
    (initialState : GlobalHighDirectExactTracedState) :
    (globalHighDirectExactTracedMappedAdversaryImpl keyView edgeHigh
      (.inr request)).run initialState =
      globalHighDirectExactQueryResult keyView (.inr request) initialState <$>
        (globalHighDirectTracedMappedAdversaryImpl keyView edgeHigh
          (.inr request)).run
            (initialState.causalState, initialState.attackerTrace) := by
  rw [globalHighDirectExactTracedMappedAdversaryImpl_sign]
  unfold globalHighDirectExactTracedSigningImpl
  rw [globalHighDirectTracedMappedAdversaryImpl_run_eq_map,
    globalHighDirectBaseMappedAdversaryImpl_sign]
  exact globalHighDirectExactTracedLift_eq_map keyView (.inr request)
    (globalHighDirectSigningImpl keyView request) initialState

theorem globalHighDirectExactTracedMappedAdversaryImpl_query_eq_map
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : GlobalHighDirectExactTracedState) :
    (globalHighDirectExactTracedMappedAdversaryImpl keyView edgeHigh input
      ).run initialState =
      globalHighDirectExactQueryResult keyView input initialState <$>
        (globalHighDirectTracedMappedAdversaryImpl keyView edgeHigh input
          ).run (initialState.causalState, initialState.attackerTrace) := by
  rcases input with (worldInput | request)
  · rcases worldInput with n | hashInput
    · exact globalHighDirectExactTracedMappedAdversaryImpl_uniform_eq_map
        keyView edgeHigh n initialState
    · exact globalHighDirectExactTracedMappedAdversaryImpl_hash_eq_map
        keyView edgeHigh hashInput initialState
  · exact globalHighDirectExactTracedMappedAdversaryImpl_sign_eq_map
      keyView edgeHigh request initialState

def globalHighExactFullQueryProjection
    {input : (OracleWorld + SigningSpec).Domain}
    (result : (OracleWorld + SigningSpec).Range input ×
      GlobalHighExactMonitoredState) :
    ((OracleWorld + SigningSpec).Range input ×
      GlobalHighDirectExactTracedState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex :=
  ((result.1, GlobalExactTracedState.mk result.2.1.1.causal
    result.2.1.2 result.2.2), result.2.1.1.trace)

theorem map_globalHighExactMonitored_adversary_full_query
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalHighExactMonitoredState) :
    globalHighExactFullQueryProjection <$>
        (globalHighExactMonitoredMappedAdversaryImpl
          ((keyView, base), edgeHigh) input).run state =
      (fun result : (((OracleWorld + SigningSpec).Range input ×
          GlobalHighDirectExactTracedState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.1.1.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          ((globalHighDirectExactTracedMappedAdversaryImpl keyView edgeHigh
            input).run (GlobalExactTracedState.mk state.1.1.causal
              state.1.2 state.2))).run := by
  let augment := fun result :
      (((OracleWorld + SigningSpec).Range input ×
        GlobalHighDirectTracedState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
    ((result.1.1, GlobalExactTracedState.mk result.1.2.1 result.1.2.2
      (encodingActionTraceUpdate keyView.secretKey input
        (state.1.1.causal.cache, []) result.1.1
        (result.1.2.1.cache, []) state.2)), result.2)
  have hold := map_globalHighMonitored_adversary_full_query keyView base
    edgeHigh input state.1.1 state.1.2
  have hlifted := congrArg (fun candidate => augment <$> candidate) hold
  rw [globalHighExactMonitoredMappedAdversaryImpl_query_eq_map]
  rw [globalHighDirectExactTracedMappedAdversaryImpl_query_eq_map]
  simpa [globalHighExactFullQueryProjection, globalHighExactQueryResult,
    globalHighDirectExactQueryResult, augment, Functor.map_map,
    Function.comp_def, simulateQ_map, bind_map_left] using hlifted

theorem map_simulate_globalHighExact_full_projection_of_query
    {spec : OracleSpec ι}
    (table : GlobalChainValueIndex → Digest)
    (left : QueryImpl spec
      (StateT GlobalHighExactMonitoredState ProbComp))
    (right : QueryImpl spec
      (StateT GlobalHighDirectExactTracedState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))))
    (hquery : ∀ (input : spec.Domain)
      (state : GlobalHighExactMonitoredState),
      (fun result : spec.Range input × GlobalHighExactMonitoredState =>
        ((result.1, GlobalExactTracedState.mk result.2.1.1.causal
          result.2.1.2 result.2.2), result.2.1.1.trace)) <$>
          (left input).run state =
        (fun result : ((spec.Range input ×
            GlobalHighDirectExactTracedState) ×
            RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
          (result.1, state.1.1.trace ++ result.2)) <$>
          (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
            ((right input).run (GlobalExactTracedState.mk state.1.1.causal
              state.1.2 state.2))).run)
    (computation : OracleComp spec α)
    (state : GlobalHighExactMonitoredState) :
    (fun result : α × GlobalHighExactMonitoredState =>
      ((result.1, GlobalExactTracedState.mk result.2.1.1.causal
        result.2.1.2 result.2.2), result.2.1.1.trace)) <$>
        (simulateQ left computation).run state =
      (fun result : ((α × GlobalHighDirectExactTracedState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.1.1.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          ((simulateQ right computation).run
            (GlobalExactTracedState.mk state.1.1.causal
              state.1.2 state.2))).run := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, StateT.run_bind, WriterT.run_bind', map_bind,
        simulateQ_spec_query]
      simp_rw [ih]
      let project := fun result :
          spec.Range input × GlobalHighExactMonitoredState =>
        ((result.1, GlobalExactTracedState.mk result.2.1.1.causal
          result.2.1.2 result.2.2), result.2.1.1.trace)
      let tail := fun head : ((spec.Range input ×
          GlobalHighDirectExactTracedState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (fun result => (result.1, head.2 ++ result.2)) <$>
          (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
            ((simulateQ right (next head.1.1)).run head.1.2)).run
      change (do
        let head ← (left input).run state
        tail (project head)) = _
      rw [← bind_map_left project]
      have hhead := hquery input state
      change project <$> (left input).run state = _ at hhead
      rw [hhead, bind_map_left]
      apply bind_congr
      intro head
      simp [tail, Functor.map_map, List.append_assoc]

theorem map_simulate_globalHighExactMonitored_adversary_full_projection
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : GlobalHighExactMonitoredState) :
    (fun result : α × GlobalHighExactMonitoredState =>
      ((result.1, GlobalExactTracedState.mk result.2.1.1.causal
        result.2.1.2 result.2.2), result.2.1.1.trace)) <$>
        (simulateQ (globalHighExactMonitoredMappedAdversaryImpl
          ((keyView, base), edgeHigh)) computation).run state =
      (fun result : ((α × GlobalHighDirectExactTracedState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.1.1.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          ((simulateQ
            (globalHighDirectExactTracedMappedAdversaryImpl keyView edgeHigh)
            computation).run (GlobalExactTracedState.mk state.1.1.causal
              state.1.2 state.2))).run := by
  apply map_simulate_globalHighExact_full_projection_of_query
  exact map_globalHighExactMonitored_adversary_full_query keyView base edgeHigh

theorem globalHighDirectExactTracedVerifierImpl_run_eq
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp OracleWorld α)
    (initialState : GlobalHighDirectExactTracedState) :
    (simulateQ (globalHighDirectExactTracedVerifierImpl keyView edgeHigh)
        computation).run initialState =
      (fun result => (result.1, GlobalExactTracedState.mk result.2
        initialState.attackerTrace initialState.encodingTrace)) <$>
        (simulateQ (globalHighDirectVerifierImpl keyView edgeHigh)
          computation).run initialState.causalState := by
  induction computation using OracleComp.inductionOn generalizing
      initialState with
  | pure value => simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, StateT.run_bind, map_bind]
      simp only [id_map]
      unfold globalHighDirectExactTracedVerifierImpl
      rw [StateT.run_mk]
      simp only [bind_map_left]
      apply bind_congr
      intro head
      change (simulateQ
        (globalHighDirectExactTracedVerifierImpl keyView edgeHigh)
        (next head.1)).run (GlobalExactTracedState.mk head.2
          initialState.attackerTrace initialState.encodingTrace) = _
      exact ih head.1 (GlobalExactTracedState.mk head.2
        initialState.attackerTrace initialState.encodingTrace)

theorem globalHighDirectExactTracedVerifierImpl_run_eq_map_traced
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp OracleWorld α)
    (initialState : GlobalHighDirectExactTracedState) :
    (simulateQ (globalHighDirectExactTracedVerifierImpl keyView edgeHigh)
        computation).run initialState =
      (fun result => (result.1, GlobalExactTracedState.mk result.2.1
        result.2.2 initialState.encodingTrace)) <$>
        (simulateQ (globalHighDirectTracedVerifierImpl keyView edgeHigh)
          computation).run
            (initialState.causalState, initialState.attackerTrace) := by
  rw [globalHighDirectExactTracedVerifierImpl_run_eq,
    globalHighDirectTracedVerifierImpl_run_eq]
  simp [Functor.map_map, Function.comp_def]

theorem map_simulate_globalHighExactMonitored_verifier_full_projection
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp OracleWorld α)
    (state : GlobalHighExactMonitoredState) :
    (fun result : α × GlobalMonitoredTracedState =>
      ((result.1, GlobalExactTracedState.mk result.2.1.causal
        result.2.2 state.2), result.2.1.trace)) <$>
        (simulateQ (globalHighMonitoredVerifierImpl
          ((keyView, base), edgeHigh)) computation).run state.1 =
      (fun result : ((α × GlobalHighDirectExactTracedState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.1.1.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          ((simulateQ
            (globalHighDirectExactTracedVerifierImpl keyView edgeHigh)
            computation).run (GlobalExactTracedState.mk state.1.1.causal
              state.1.2 state.2))).run := by
  let augment := fun result : ((α × GlobalHighDirectTracedState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
    ((result.1.1, GlobalExactTracedState.mk result.1.2.1 result.1.2.2
      state.2), result.2)
  have hold := map_simulate_globalHighMonitored_verifier_full_projection
    keyView base edgeHigh computation state.1.1 state.1.2
  have hlifted := congrArg (fun candidate => augment <$> candidate) hold
  rw [globalHighDirectExactTracedVerifierImpl_run_eq_map_traced]
  simpa [augment, Functor.map_map, Function.comp_def, simulateQ_map,
    bind_map_left] using hlifted

set_option maxHeartbeats 3000000 in
theorem map_globalHighExactMonitoredDetailedExecution_full_projection
    (adversary : Adversary Concrete.scheme)
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    (fun result : (Forgery × Bool) × GlobalHighExactMonitoredState =>
      ((result.1, GlobalExactTracedState.mk result.2.1.1.causal
        result.2.1.2 result.2.2), result.2.1.1.trace)) <$>
        globalHighExactMonitoredDetailedExecution adversary
          ((keyView, base), edgeHigh) =
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
        ((globalHighDirectExactTracedDetailedExecution adversary keyView
          edgeHigh).run (GlobalExactTracedState.mk
            (globalFilteredCausalKeygenState keyView) [] []))).run := by
  let initial : GlobalHighExactMonitoredState :=
    ((⟨globalFilteredCausalKeygenState keyView,
      some AdaptiveRevealMonitor.State.empty, []⟩, []), [])
  let project := fun result : Forgery × GlobalHighExactMonitoredState =>
    ((result.1, GlobalExactTracedState.mk result.2.1.1.causal
      result.2.1.2 result.2.2), result.2.1.1.trace)
  let tail := fun head : ((Forgery × GlobalHighDirectExactTracedState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
    (fun result : ((Bool × GlobalHighDirectExactTracedState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
      let finalTrace := appendVerificationEncodingObservation
        keyView.secretKey head.1.1 head.1.2.causalState.cache
          result.1.2.causalState.cache result.1.2.encodingTrace
      (((head.1.1, result.1.1),
        { result.1.2 with encodingTrace := finalTrace }),
        head.2 ++ result.2)) <$>
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
        ((simulateQ (globalHighDirectExactTracedVerifierImpl keyView edgeHigh)
          (Concrete.scheme.verify keyView.publicKey head.1.1.epoch
            head.1.1.message head.1.1.signature)).run head.1.2)).run
  have htail (handled : Forgery × GlobalHighExactMonitoredState) :
      (do
        let verified ← (simulateQ (globalHighMonitoredVerifierImpl
          ((keyView, base), edgeHigh))
          (Concrete.scheme.verify keyView.publicKey handled.1.epoch
            handled.1.message handled.1.signature)).run handled.2.1
        let finalTrace := appendVerificationEncodingObservation
          keyView.secretKey handled.1 handled.2.1.1.causal.cache
            verified.2.1.causal.cache handled.2.2
        pure (((handled.1, verified.1),
          GlobalExactTracedState.mk verified.2.1.causal verified.2.2
            finalTrace), verified.2.1.trace)) = tail (project handled) := by
    have hvertifier :=
      map_simulate_globalHighExactMonitored_verifier_full_projection keyView
        base edgeHigh
        (Concrete.scheme.verify keyView.publicKey handled.1.epoch
          handled.1.message handled.1.signature) handled.2
    simpa [tail, project, Functor.map_map] using congrArg
      (fun candidate =>
        (fun result : ((Bool × GlobalHighDirectExactTracedState) ×
            RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
          let finalTrace := appendVerificationEncodingObservation
            keyView.secretKey handled.1 handled.2.1.1.causal.cache
              result.1.2.causalState.cache result.1.2.encodingTrace
          (((handled.1, result.1.1),
            { result.1.2 with encodingTrace := finalTrace }), result.2)) <$>
          candidate)
        hvertifier
  unfold globalHighExactMonitoredDetailedExecution
    globalHighDirectExactTracedDetailedExecution
  simp only [map_bind, StateT.run_mk, simulateQ_bind, WriterT.run_bind',
    map_pure]
  simp_rw [htail]
  change (do
    let handled ← (simulateQ (globalHighExactMonitoredMappedAdversaryImpl
      ((keyView, base), edgeHigh))
        (adversary.main keyView.publicKey)).run initial
    tail (project handled)) = _
  rw [← bind_map_left project]
  have hhead :=
    map_simulate_globalHighExactMonitored_adversary_full_projection keyView
      base edgeHigh (adversary.main keyView.publicKey) initial
  change project <$>
    (simulateQ (globalHighExactMonitoredMappedAdversaryImpl
      ((keyView, base), edgeHigh))
        (adversary.main keyView.publicKey)).run initial = _ at hhead
  simp only [initial, List.nil_append] at hhead
  rw [hhead, bind_map_left]
  apply bind_congr
  intro head
  simp [tail, Functor.map_map]

def globalHighExactMonitoredFullProjection
    (result : GlobalHighExactMonitoredProgramResult) :
    (GlobalChainValueIndex → Digest) ×
      (GlobalHighDirectExactTracedResult ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :=
  (result.1.1.2,
    (((result.1.1.1, result.1.2),
      (result.2.1, GlobalExactTracedState.mk
        result.2.2.1.1.causal result.2.2.1.2 result.2.2.2)),
      result.2.2.1.1.trace))

noncomputable def globalHighDirectExactTracedContinuation
    (adversary : Adversary Concrete.scheme)
    (parameter : PublicParameter)
    (base : GlobalChainValueIndex → Digest) :
    ProbComp ((GlobalChainValueIndex → Digest) ×
      (GlobalHighDirectExactTracedResult ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) := do
  let keyResult ← globalHighDirectKeygenAfterParameter parameter
  let execution ← (simulateQ
    (RevealProbeOracleSimulation.eagerTraceImpl base)
    ((globalHighDirectExactTracedDetailedExecution adversary keyResult.1
      keyResult.2).run (GlobalExactTracedState.mk
        (globalFilteredCausalKeygenState keyResult.1) [] []))).run
  pure (base, ((keyResult, execution.1), execution.2))

theorem globalHighExactMonitored_afterKey_full_projection
    (adversary : Adversary Concrete.scheme)
    (parameter : PublicParameter)
    (base : GlobalChainValueIndex → Digest) :
    (do
      let keyResult ← globalHighDirectKeygenAfterParameter parameter
      let execution ← globalHighExactMonitoredDetailedExecution adversary
        ((keyResult.1, base), keyResult.2)
      pure (globalHighExactMonitoredFullProjection
        (((keyResult.1, base), keyResult.2), execution))) =
      globalHighDirectExactTracedContinuation adversary parameter base := by
  unfold globalHighDirectExactTracedContinuation
  apply bind_congr
  intro keyResult
  have hdetail :=
    map_globalHighExactMonitoredDetailedExecution_full_projection adversary
      keyResult.1 base keyResult.2
  simpa [globalHighExactMonitoredFullProjection, Functor.map_map,
    map_eq_bind_pure_comp] using congrArg
      (fun candidate =>
        (fun execution : ((Forgery × Bool) ×
            GlobalHighDirectExactTracedState) ×
            RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex =>
          (base, ((keyResult, execution.1), execution.2))) <$> candidate)
      hdetail

theorem globalHighExactMonitoredProgram_eq_directKeygen
    (adversary : Adversary Concrete.scheme) :
    globalHighExactMonitoredProgram adversary = (do
      let parameter ← Concrete.samplePublicParameter
      let base ← independentGlobalChainValueTable
      let keyResult ← globalHighDirectKeygenAfterParameter parameter
      let execution ← globalHighExactMonitoredDetailedExecution adversary
        ((keyResult.1, base), keyResult.2)
      pure (((keyResult.1, base), keyResult.2), execution)) := by
  rw [globalHighExactMonitoredProgram]
  rw [coupledGlobalChainKeygenWithBaseHighFull_eq_direct]
  simp only [bind_assoc, pure_bind]

theorem globalHighExactMonitoredProgram_fullProjection_eq_parameterFirst
    (adversary : Adversary Concrete.scheme) :
    globalHighExactMonitoredFullProjection <$>
      globalHighExactMonitoredProgram adversary =
    (do
      let parameter ← Concrete.samplePublicParameter
      let base ← independentGlobalChainValueTable
      globalHighDirectExactTracedContinuation adversary parameter base) := by
  rw [globalHighExactMonitoredProgram_eq_directKeygen]
  simp only [map_eq_bind_pure_comp, bind_assoc]
  apply bind_congr
  intro parameter
  apply bind_congr
  intro base
  exact globalHighExactMonitored_afterKey_full_projection adversary parameter
    base

theorem globalHighDirectExactTracedContinuation_eq_eagerAfterBase
    (adversary : Adversary Concrete.scheme)
    (base : GlobalChainValueIndex → Digest) :
    (do
      let parameter ← Concrete.samplePublicParameter
      globalHighDirectExactTracedContinuation adversary parameter base) = (do
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl base)
        (globalHighDirectExactTracedProgram adversary)).run
      pure (base, result)) := by
  unfold globalHighDirectExactTracedContinuation
    globalHighDirectExactTracedProgram globalHighDirectKeygen
  simpa only [bind_assoc] using
    (eagerTrace_liftProbComp_then_bind base
      (do
        let parameter ← Concrete.samplePublicParameter
        globalHighDirectKeygenAfterParameter parameter)
      (fun keyResult =>
        (globalHighDirectExactTracedDetailedExecution adversary keyResult.1
          keyResult.2).run (GlobalExactTracedState.mk
            (globalFilteredCausalKeygenState keyResult.1) [] [])))

theorem evalDist_globalHighExactMonitoredFullProjection_eq_eagerExperiment
    (adversary : Adversary Concrete.scheme) :
    evalDist (globalHighExactMonitoredFullProjection <$>
      globalHighExactMonitoredProgram adversary) =
    evalDist (RevealProbeOracleSimulation.eagerExperiment
      (globalHighDirectExactTracedProgram adversary)) := by
  rw [globalHighExactMonitoredProgram_fullProjection_eq_parameterFirst]
  calc
    evalDist (do
        let parameter ← Concrete.samplePublicParameter
        let base ← independentGlobalChainValueTable
        globalHighDirectExactTracedContinuation adversary parameter base) =
      evalDist (do
        let base ← independentGlobalChainValueTable
        let parameter ← Concrete.samplePublicParameter
        globalHighDirectExactTracedContinuation adversary parameter base) := by
          exact OracleComp.DeferredSampling.evalDist_bind_comm
            Concrete.samplePublicParameter independentGlobalChainValueTable _
    _ = evalDist (do
        let base ← independentGlobalChainValueTable
        let result ← (simulateQ
          (RevealProbeOracleSimulation.eagerTraceImpl base)
          (globalHighDirectExactTracedProgram adversary)).run
        pure (base, result)) := by
          rw [evalDist_bind, evalDist_bind]
          apply bind_congr
          intro base
          exact congrArg evalDist
            (globalHighDirectExactTracedContinuation_eq_eagerAfterBase
              adversary base)
    _ = _ := by
      unfold RevealProbeOracleSimulation.eagerExperiment
      rw [evalDist_bind, evalDist_bind]
      unfold independentGlobalChainValueTable
        RevealProbeOracleSimulation.eagerTableSample
      rw [evalDist_uniformSample, evalDist_uniformSample]

theorem map_globalFirstLaneExactTracedEagerExperiment_chainProjection
    (adversary : Adversary Concrete.scheme) :
    (fun result =>
        (result.1, (result.2.1, result.2.2.chainActions))) <$>
        FirstLaneOracleSimulation.eagerExperiment
          (globalFirstLaneExactTracedProgram adversary) =
      RevealProbeOracleSimulation.eagerExperiment
        (globalHighDirectExactTracedProgram adversary) := by
  rw [map_globalFirstLaneEagerExperiment_chainProjection]
  rw [(globalFirstLaneErase_exactTracedProgram adversary).eq]

theorem evalDist_globalHighExactMonitoredFullProjection_eq_firstLane
    (adversary : Adversary Concrete.scheme) :
    evalDist (globalHighExactMonitoredFullProjection <$>
      globalHighExactMonitoredProgram adversary) =
    evalDist ((fun result =>
      (result.1, (result.2.1, result.2.2.chainActions))) <$>
        FirstLaneOracleSimulation.eagerExperiment
          (globalFirstLaneExactTracedProgram adversary)) := by
  rw [evalDist_globalHighExactMonitoredFullProjection_eq_eagerExperiment]
  exact congrArg evalDist
    (map_globalFirstLaneExactTracedEagerExperiment_chainProjection
      adversary).symm

def globalHighDirectExactTracedBaseProjection
    (result : GlobalHighDirectExactTracedResult) : GlobalHighDirectResult :=
  (result.1, (result.2.1, result.2.2.causalState))

noncomputable def globalHighDirectExactForgeryPrimaryProbeTrace
    (result : GlobalHighDirectExactTracedResult) :
    RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex :=
  globalHighDirectForgeryPrimaryProbeTrace
    (globalHighDirectExactTracedBaseProjection result)

noncomputable def appendGlobalHighDirectExactPublicTrace
    (result : (GlobalChainValueIndex → Digest) ×
      (GlobalHighDirectExactTracedResult ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) :
    (GlobalChainValueIndex → Digest) ×
      (GlobalHighDirectExactTracedResult ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :=
  (result.1, (result.2.1, result.2.2 ++
    globalHighDirectExactForgeryPrimaryProbeTrace result.2.1))

noncomputable def globalHighDirectExactTracedPublicProgram
    (adversary : Adversary Concrete.scheme) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      GlobalHighDirectExactTracedResult := do
  let result ← globalHighDirectExactTracedProgram adversary
  let _ ← RevealProbeOracleSimulation.emitObservedTrace
    (globalHighDirectExactForgeryPrimaryProbeTrace result)
  pure result

noncomputable def globalFirstLaneExactTracedPublicProgram
    (adversary : Adversary Concrete.scheme) :
    OracleComp GlobalFirstLaneWorld GlobalFirstLaneExactTracedResult := do
  let result ← globalFirstLaneExactTracedProgram adversary
  let _ ← globalFirstLaneLiftRevealProbe
    (RevealProbeOracleSimulation.emitObservedTrace
      (globalHighDirectExactForgeryPrimaryProbeTrace result))
  pure result

theorem globalFirstLaneErase_exactTracedPublicProgram
    (adversary : Adversary Concrete.scheme) :
    GlobalFirstLaneErases
      (globalFirstLaneExactTracedPublicProgram adversary)
      (globalHighDirectExactTracedPublicProgram adversary) := by
  unfold globalFirstLaneExactTracedPublicProgram
    globalHighDirectExactTracedPublicProgram
  apply (globalFirstLaneErase_exactTracedProgram adversary).bind
  intro result
  apply (globalFirstLaneErases_liftRevealProbe
    (RevealProbeOracleSimulation.emitObservedTrace
      (globalHighDirectExactForgeryPrimaryProbeTrace result))).bind
  intro _unit
  exact GlobalFirstLaneErases.pure result

theorem globalHighDirectExactForgeryPrimaryProbeTrace_agrees
    (table : GlobalChainValueIndex → Digest)
    (result : GlobalHighDirectExactTracedResult) :
    RevealProbeOracleSimulation.TraceAgrees table
      (globalHighDirectExactForgeryPrimaryProbeTrace result) := by
  unfold globalHighDirectExactForgeryPrimaryProbeTrace
  exact globalHighDirectForgeryPrimaryProbeTrace_agrees table _

theorem simulate_eagerTrace_bind_emitObservedTrace_keep
    (table : Index → Digest)
    (computation : OracleComp
      (RevealProbeOracleSimulation.World Index) α)
    (suffix : α → RevealProbeOracleSimulation.ActionTrace Index)
    (hagrees : ∀ result, RevealProbeOracleSimulation.TraceAgrees table
      (suffix result)) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table) (do
      let result ← computation
      let _ ← RevealProbeOracleSimulation.emitObservedTrace (suffix result)
      pure result)).run =
    (fun result => (result.1, result.2 ++ suffix result.1)) <$>
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        computation).run := by
  rw [simulateQ_bind, WriterT.run_bind']
  apply bind_congr
  intro result
  rcases result with ⟨result, trace⟩
  simp only [Function.comp_apply]
  rw [simulateQ_bind, WriterT.run_bind']
  rw [RevealProbeOracleSimulation.simulate_eagerTrace_emitObservedTrace]
  · simp only [simulateQ_pure, WriterT.run_pure', map_pure, pure_bind,
      Prod.map_apply, id_eq]
    change (pure (result, trace ++ (suffix result ++ [])) : ProbComp _) =
      pure (result, trace ++ suffix result)
    rw [List.append_nil]
  · exact hagrees result

theorem eagerExperiment_globalHighDirectExactTracedPublicProgram_eq_append
    (adversary : Adversary Concrete.scheme) :
    RevealProbeOracleSimulation.eagerExperiment
      (globalHighDirectExactTracedPublicProgram adversary) =
    appendGlobalHighDirectExactPublicTrace <$>
      RevealProbeOracleSimulation.eagerExperiment
        (globalHighDirectExactTracedProgram adversary) := by
  unfold globalHighDirectExactTracedPublicProgram
    RevealProbeOracleSimulation.eagerExperiment
  simp only [map_bind]
  apply bind_congr
  intro table
  rw [simulate_eagerTrace_bind_emitObservedTrace_keep table
    (globalHighDirectExactTracedProgram adversary)
    globalHighDirectExactForgeryPrimaryProbeTrace
    (globalHighDirectExactForgeryPrimaryProbeTrace_agrees table)]
  simp [appendGlobalHighDirectExactPublicTrace, map_eq_bind_pure_comp,
    bind_assoc]

theorem map_globalFirstLaneExactTracedPublicEager_chainProjection
    (adversary : Adversary Concrete.scheme) :
    (fun result =>
        (result.1, (result.2.1, result.2.2.chainActions))) <$>
        FirstLaneOracleSimulation.eagerExperiment
          (globalFirstLaneExactTracedPublicProgram adversary) =
      RevealProbeOracleSimulation.eagerExperiment
        (globalHighDirectExactTracedPublicProgram adversary) := by
  rw [map_globalFirstLaneEagerExperiment_chainProjection]
  rw [(globalFirstLaneErase_exactTracedPublicProgram adversary).eq]

theorem evalDist_globalHighExactMonitoredPublicProjection_eq_firstLane
    (adversary : Adversary Concrete.scheme) :
    evalDist (appendGlobalHighDirectExactPublicTrace <$>
      (globalHighExactMonitoredFullProjection <$>
        globalHighExactMonitoredProgram adversary)) =
    evalDist ((fun result =>
      (result.1, (result.2.1, result.2.2.chainActions))) <$>
        FirstLaneOracleSimulation.eagerExperiment
          (globalFirstLaneExactTracedPublicProgram adversary)) := by
  calc
    evalDist (appendGlobalHighDirectExactPublicTrace <$>
        (globalHighExactMonitoredFullProjection <$>
          globalHighExactMonitoredProgram adversary)) =
      evalDist (appendGlobalHighDirectExactPublicTrace <$>
        RevealProbeOracleSimulation.eagerExperiment
          (globalHighDirectExactTracedProgram adversary)) := by
            exact evalDist_map_congr_of_evalDist_eq
              appendGlobalHighDirectExactPublicTrace
              (globalHighExactMonitoredFullProjection <$>
                globalHighExactMonitoredProgram adversary)
              (RevealProbeOracleSimulation.eagerExperiment
                (globalHighDirectExactTracedProgram adversary))
              (evalDist_globalHighExactMonitoredFullProjection_eq_eagerExperiment
                adversary)
    _ = evalDist (RevealProbeOracleSimulation.eagerExperiment
        (globalHighDirectExactTracedPublicProgram adversary)) := by
          rw [eagerExperiment_globalHighDirectExactTracedPublicProgram_eq_append]
    _ = _ := congrArg evalDist
      (map_globalFirstLaneExactTracedPublicEager_chainProjection adversary).symm

theorem globalFirstLaneBindLiftRevealProbe_support_baseTrace
    (table : GlobalChainValueIndex → Digest)
    (computation : OracleComp GlobalFirstLaneWorld α)
    (suffix : α → OracleComp
      (RevealProbeOracleSimulation.World GlobalChainValueIndex) Unit)
    (result : α ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (do
          let value ← computation
          let _ ← globalFirstLaneLiftRevealProbe (suffix value)
          pure value)).run)) :
    ∃ baseTrace : FirstLaneOracleSimulation.ActionTrace
        GlobalChainValueIndex,
      (result.1, baseTrace) ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          computation).run) ∧
      result.2.encodingActions = baseTrace.encodingActions := by
  rw [simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hresult
  obtain ⟨head, hhead, hrest⟩ := hresult
  rw [support_map] at hrest
  obtain ⟨tail, htail, hresultEq⟩ := hrest
  rw [simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at htail
  obtain ⟨suffixResult, hsuffix, hfinal⟩ := htail
  simp only [simulateQ_pure, WriterT.run_pure', map_pure, support_pure,
    Set.mem_singleton_iff, Prod.map_apply, id_eq] at hfinal
  subst tail
  subst result
  refine ⟨head.2, hhead, ?_⟩
  have hsuffixNil := globalFirstLaneLiftRevealProbe_encodingActions_eq_nil
    table (suffix head.1) suffixResult hsuffix
  simp [FirstLaneOracleSimulation.ActionTrace.encodingActions_append,
    hsuffixNil]

theorem globalFirstLaneExactTracedPublicProgram_support_baseTrace
    (table : GlobalChainValueIndex → Digest)
    (adversary : Adversary Concrete.scheme)
    (result : GlobalFirstLaneExactTracedResult ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneExactTracedPublicProgram adversary)).run)) :
    ∃ baseTrace : FirstLaneOracleSimulation.ActionTrace
        GlobalChainValueIndex,
      (result.1, baseTrace) ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (globalFirstLaneExactTracedProgram adversary)).run) ∧
      result.2.encodingActions = baseTrace.encodingActions := by
  unfold globalFirstLaneExactTracedPublicProgram at hresult
  exact globalFirstLaneBindLiftRevealProbe_support_baseTrace table
    (globalFirstLaneExactTracedProgram adversary)
    (fun result => RevealProbeOracleSimulation.emitObservedTrace
      (globalHighDirectExactForgeryPrimaryProbeTrace result)) result hresult

abbrev GlobalHighExactPublicResult :=
  (GlobalChainValueIndex → Digest) ×
    (GlobalHighDirectExactTracedResult ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)

def GlobalHighExactProjectedFirstLaneEvent
    (result : GlobalHighExactPublicResult) : Prop :=
  (SigningTranscript.Valid
      result.2.1.2.2.attackerTrace.toSigningLog ∧
    CappedEncodingMonitor.runObserved EncodingMonitor.State.empty
      result.2.1.2.2.encodingTrace = true) ∨
    RevealProbeOracleSimulation.runObserved result.1
      AdaptiveRevealMonitor.State.empty result.2.2 = true

theorem globalHighExactMonitored_publicProjection_eq
    (result : GlobalHighExactMonitoredProgramResult) :
    let projected := appendGlobalHighDirectExactPublicTrace
      (globalHighExactMonitoredFullProjection result)
    (projected.1, ((), projected.2.2)) =
      globalHighMonitoredPublicProjection
        (globalHighExactErasedResult result) := by
  rw [globalHighMonitoredPublicProjection_eq_append_direct]
  rfl

theorem globalHighExactFirstLaneEvent_implies_projected
    (result : GlobalHighExactMonitoredProgramResult)
    (hevent : GlobalHighExactFirstLaneEvent result) :
    GlobalHighExactProjectedFirstLaneEvent
      (appendGlobalHighDirectExactPublicTrace
        (globalHighExactMonitoredFullProjection result)) := by
  rcases hevent with hencoding | hchain
  · exact Or.inl hencoding
  · apply Or.inr
    unfold RevealProbeOracleSimulation.ObservedHit at hchain
    have hprojection := globalHighExactMonitored_publicProjection_eq result
    rw [← hprojection] at hchain
    exact hchain

theorem globalHighExactProjectedFirstLaneEvent_implies_combinedHit_of_run
    (adversary : Adversary Concrete.scheme)
    (table : GlobalChainValueIndex → Digest)
    (runResult : GlobalFirstLaneExactTracedResult ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hrun : runResult ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneExactTracedPublicProgram adversary)).run))
    (hevent : GlobalHighExactProjectedFirstLaneEvent
      (table, (runResult.1, runResult.2.chainActions))) :
    FirstLaneOracleSimulation.CombinedHit table runResult.2 := by
  rcases hevent with hencoding | hchain
  · apply Or.inl
    obtain ⟨baseTrace, hbase, hencodingActions⟩ :=
      globalFirstLaneExactTracedPublicProgram_support_baseTrace table
        adversary runResult hrun
    have htraceSub := globalFirstLaneExactTracedProgram_trace_sublist table
      adversary (runResult.1, baseTrace) hbase
    have hvalidSub :=
      globalFirstLaneExactTracedProgram_validSignEpochs_sublist table
        adversary (runResult.1, baseTrace) hbase
    have htraceSub' : List.Sublist
        runResult.1.2.2.encodingTrace runResult.2.encodingActions := by
      rw [hencodingActions]
      exact htraceSub
    have hvalidSub' : List.Sublist
        (CappedEncodingMonitor.validObservedSignEpochs
          runResult.2.encodingActions)
        (runResult.1.2.2.attackerTrace.toSigningLog.map
          fun entry => entry.1.epoch) := by
      rw [hencodingActions]
      exact hvalidSub
    have hnodup :
        (CappedEncodingMonitor.validObservedSignEpochs
          runResult.2.encodingActions).Nodup := by
      exact hvalidSub'.nodup hencoding.1
    exact CappedEncodingMonitor.runObserved_empty_eq_true_mono_sublist
      htraceSub' hnodup hencoding.2
  · exact Or.inr hchain

abbrev GlobalFirstLaneExactPublicEagerResult :=
  (GlobalChainValueIndex → Digest) ×
    (GlobalFirstLaneExactTracedResult ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)

def GlobalHighExactProjectedFirstLaneEagerEvent
    (result : GlobalFirstLaneExactPublicEagerResult) : Prop :=
  GlobalHighExactProjectedFirstLaneEvent
    (result.1, (result.2.1, result.2.2.chainActions))

def GlobalFirstLaneExactPublicCombinedHit
    (result : GlobalFirstLaneExactPublicEagerResult) : Prop :=
  FirstLaneOracleSimulation.CombinedHit result.1 result.2.2

noncomputable def globalFirstLaneExactPublicEagerExperiment
    (adversary : Adversary Concrete.scheme) :
    ProbComp GlobalFirstLaneExactPublicEagerResult :=
  FirstLaneOracleSimulation.eagerExperiment
    (globalFirstLaneExactTracedPublicProgram adversary)

theorem globalHighExactProjectedFirstLaneEvent_implies_combinedHit
    (adversary : Adversary Concrete.scheme)
    (result : (GlobalChainValueIndex → Digest) ×
      (GlobalFirstLaneExactTracedResult ×
        FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex))
    (hresult : result ∈ support
      (globalFirstLaneExactPublicEagerExperiment adversary))
    (hevent : GlobalHighExactProjectedFirstLaneEvent
      (result.1, (result.2.1, result.2.2.chainActions))) :
    FirstLaneOracleSimulation.CombinedHit result.1 result.2.2 := by
  unfold globalFirstLaneExactPublicEagerExperiment at hresult
  unfold FirstLaneOracleSimulation.eagerExperiment at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨table, _htable, hrest⟩ := hresult
  rw [mem_support_bind_iff] at hrest
  obtain ⟨runResult, hrun, hpure⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  rw [hpure] at hevent ⊢
  exact globalHighExactProjectedFirstLaneEvent_implies_combinedHit_of_run
    adversary table runResult hrun hevent

theorem globalHighExactProjectedFirstLaneEagerEvent_implies_combinedHit
    (adversary : Adversary Concrete.scheme)
    (result : GlobalFirstLaneExactPublicEagerResult)
    (hresult : result ∈ support
      (globalFirstLaneExactPublicEagerExperiment adversary))
    (hevent : GlobalHighExactProjectedFirstLaneEagerEvent result) :
    GlobalFirstLaneExactPublicCombinedHit result := by
  unfold GlobalHighExactProjectedFirstLaneEagerEvent at hevent
  unfold GlobalFirstLaneExactPublicCombinedHit
  unfold globalFirstLaneExactPublicEagerExperiment at hresult
  unfold FirstLaneOracleSimulation.eagerExperiment at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨table, _htable, hrest⟩ := hresult
  rw [mem_support_bind_iff] at hrest
  obtain ⟨runResult, hrun, hpure⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  rw [hpure] at hevent ⊢
  exact globalHighExactProjectedFirstLaneEvent_implies_combinedHit_of_run
    adversary table runResult hrun hevent

theorem globalHighExactProjectedFirstLane_probability_le_combinedHit
    (adversary : Adversary Concrete.scheme) :
    Pr[GlobalHighExactProjectedFirstLaneEagerEvent |
        globalFirstLaneExactPublicEagerExperiment adversary] ≤
      Pr[GlobalFirstLaneExactPublicCombinedHit |
        globalFirstLaneExactPublicEagerExperiment adversary] := by
  apply probEvent_mono
  exact globalHighExactProjectedFirstLaneEagerEvent_implies_combinedHit adversary

theorem globalHighExactFirstLane_probability_le_eagerCombinedHit
    (adversary : Adversary Concrete.scheme) :
    Pr[GlobalHighExactFirstLaneEvent |
        globalHighExactMonitoredProgram adversary] ≤
      Pr[fun result : (GlobalChainValueIndex → Digest) ×
          (GlobalFirstLaneExactTracedResult ×
            FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        FirstLaneOracleSimulation.CombinedHit result.1 result.2.2 |
        FirstLaneOracleSimulation.eagerExperiment
          (globalFirstLaneExactTracedPublicProgram adversary)] := by
  calc
    _ ≤ Pr[fun result => GlobalHighExactProjectedFirstLaneEvent
          (appendGlobalHighDirectExactPublicTrace
            (globalHighExactMonitoredFullProjection result)) |
        globalHighExactMonitoredProgram adversary] := by
      apply probEvent_mono
      intro result _hresult hevent
      exact globalHighExactFirstLaneEvent_implies_projected result hevent
    _ = Pr[GlobalHighExactProjectedFirstLaneEvent |
        appendGlobalHighDirectExactPublicTrace <$>
          (globalHighExactMonitoredFullProjection <$>
            globalHighExactMonitoredProgram adversary)] := by
      rw [probEvent_map, probEvent_map]
      rfl
    _ = Pr[GlobalHighExactProjectedFirstLaneEvent |
        (fun result =>
          (result.1, (result.2.1, result.2.2.chainActions))) <$>
          FirstLaneOracleSimulation.eagerExperiment
            (globalFirstLaneExactTracedPublicProgram adversary)] :=
      probEvent_eq_of_evalDist_eq _
        (evalDist_globalHighExactMonitoredPublicProjection_eq_firstLane
          adversary)
    _ = Pr[fun result => GlobalHighExactProjectedFirstLaneEvent
          (result.1, (result.2.1, result.2.2.chainActions)) |
        FirstLaneOracleSimulation.eagerExperiment
          (globalFirstLaneExactTracedPublicProgram adversary)] := by
      rw [probEvent_map]
      rfl
    _ ≤ _ := globalHighExactProjectedFirstLane_probability_le_combinedHit
      adversary

theorem winningExactFirstLane_probability_le_eagerCombinedHit
    (adversary : Adversary Concrete.scheme) :
    Pr[WinningExactFirstLaneBadEventOccurs |
        cappedDetailedGameWithEncodingTrace adversary] ≤
      Pr[fun result : GlobalFirstLaneExactPublicEagerResult =>
          FirstLaneOracleSimulation.CombinedHit result.1 result.2.2 |
        FirstLaneOracleSimulation.eagerExperiment
          (globalFirstLaneExactTracedPublicProgram adversary)] := by
  calc
    _ = Pr[SourceWinningExactFirstLaneEvent |
        sourceGlobalExactTracedProgram adversary] :=
      cappedExactFirstLane_probability_eq_sourceGlobalExact adversary
    _ ≤ Pr[GlobalHighExactFirstLaneEvent |
        globalHighExactMonitoredProgram adversary] :=
      sourceWinningExactFirstLane_probability_le_globalHighExact adversary
    _ ≤ _ := globalHighExactFirstLane_probability_le_eagerCombinedHit adversary

end XmssSecurity.CappedChain
