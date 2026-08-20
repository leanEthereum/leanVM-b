import XmssSecurity.Proof.CappedExactFirstLaneTransport
import XmssSecurity.Proof.CappedGlobalChainHighPublicProgram
import XmssSecurity.Proof.CappedGlobalChainHighActionTrace
import XmssSecurity.Proof.StateLens

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000
set_option linter.constructorNameAsVariable false

noncomputable def globalHighDirectExactQueryResult
    (_keyView : ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (_initialState : GlobalExactTracedState)
    (result : (OracleWorld + SigningSpec).Range input ×
      GlobalHighDirectTracedState) :
    (OracleWorld + SigningSpec).Range input ×
      GlobalExactTracedState :=
  (result.1, GlobalExactTracedState.mk result.2.1 result.2.2)

theorem globalExactTracedLift_eq_map
    (keyView : ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (base : StateT GlobalCausalHashState
      (OracleComp
        (RevealProbeOracleSimulation.World GlobalChainValueIndex))
      ((OracleWorld + SigningSpec).Range input))
    (initialState : GlobalExactTracedState) :
    (globalExactTracedLift keyView input base).run initialState =
      globalHighDirectExactQueryResult keyView input initialState <$>
        ((fun result => (result.1,
          (result.2, initialState.attackerTrace ++
            attackerActionFragment input result.1))) <$>
          base.run initialState.causalState) := by
  unfold globalExactTracedLift globalHighDirectExactQueryResult
    globalExactTracedNextState
  simp [StateT.run_mk, Functor.map_map]

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
    (initialState : GlobalExactTracedState) :
    (globalHighDirectExactTracedMappedAdversaryImpl keyView edgeHigh
      (.inl (.inl n))).run initialState =
      globalHighDirectExactQueryResult keyView (.inl (.inl n)) initialState <$>
        (globalHighDirectTracedMappedAdversaryImpl keyView edgeHigh
          (.inl (.inl n))).run
            (initialState.causalState, initialState.attackerTrace) := by
  change (globalExactTracedLift keyView (.inl (.inl n))
    (globalHighDirectUniformImpl n)).run initialState = _
  change _ = globalHighDirectExactQueryResult keyView (.inl (.inl n))
    initialState <$> ((fun result => (result.1,
      (result.2, initialState.attackerTrace ++
        attackerActionFragment (.inl (.inl n)) result.1))) <$>
          (globalHighDirectUniformImpl n).run initialState.causalState)
  exact globalExactTracedLift_eq_map keyView (.inl (.inl n))
    (globalHighDirectUniformImpl n) initialState

theorem globalHighDirectExactTracedMappedAdversaryImpl_hash_eq_map
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (hashInput : HashInput)
    (initialState : GlobalExactTracedState) :
    (globalHighDirectExactTracedMappedAdversaryImpl keyView edgeHigh
      (.inl (.inr hashInput))).run initialState =
      globalHighDirectExactQueryResult keyView (.inl (.inr hashInput))
        initialState <$>
        (globalHighDirectTracedMappedAdversaryImpl keyView edgeHigh
          (.inl (.inr hashInput))).run
            (initialState.causalState, initialState.attackerTrace) := by
  let base := globalCausalAttackerHashQueryFromHigh
    (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey hashInput
  change (globalExactTracedLift keyView (.inl (.inr hashInput))
    base).run initialState = _
  change _ = globalHighDirectExactQueryResult keyView (.inl (.inr hashInput))
    initialState <$> ((fun result => (result.1,
      (result.2, initialState.attackerTrace ++
        attackerActionFragment (.inl (.inr hashInput)) result.1))) <$>
          base.run initialState.causalState)
  exact globalExactTracedLift_eq_map keyView
    (.inl (.inr hashInput)) base initialState

theorem globalHighDirectExactTracedMappedAdversaryImpl_sign_eq_map
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (request : SignRequest)
    (initialState : GlobalExactTracedState) :
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
  exact globalExactTracedLift_eq_map keyView (.inr request)
    (globalHighDirectSigningImpl keyView request) initialState

theorem globalHighDirectExactTracedMappedAdversaryImpl_query_eq_map
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : GlobalExactTracedState) :
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

def globalHighExactFullProjection {α : Type}
    (result : α × GlobalHighExactMonitoredState) :
    (α × GlobalExactTracedState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex :=
  ((result.1, globalHighExactStateProjection result.2), result.2.1.1.trace)

theorem map_globalHighExactMonitored_adversary_full_query
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalHighExactMonitoredState) :
    globalHighExactFullProjection <$>
        (globalHighExactMonitoredMappedAdversaryImpl
          ((keyView, base), edgeHigh) input).run state =
      (fun result : (((OracleWorld + SigningSpec).Range input ×
          GlobalExactTracedState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.1.1.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          ((globalHighDirectExactTracedMappedAdversaryImpl keyView edgeHigh
            input).run (globalHighExactStateProjection state))).run := by
  let augment := fun result :
      (((OracleWorld + SigningSpec).Range input ×
        GlobalHighDirectTracedState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
    ((result.1.1, GlobalExactTracedState.mk result.1.2.1 result.1.2.2),
      result.2)
  have hold := map_globalHighMonitored_adversary_full_query keyView base
    edgeHigh input state.1.1 state.1.2
  have hlifted := congrArg (fun candidate => augment <$> candidate) hold
  rw [globalHighExactMonitoredMappedAdversaryImpl_query_eq_map]
  rw [globalHighDirectExactTracedMappedAdversaryImpl_query_eq_map]
  simpa [globalHighExactFullProjection, globalHighExactQueryResult,
    globalHighDirectExactQueryResult, globalHighExactStateProjection, augment,
    Functor.map_map, Function.comp_def, simulateQ_map, bind_map_left] using
      hlifted

theorem map_globalHighMonitored_adversary_exact_query
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalMonitoredTracedState) :
    (fun result => ((result.1, GlobalExactTracedState.mk
      result.2.1.causal result.2.2), result.2.1.trace)) <$>
        (globalHighMonitoredMappedAdversaryImpl
          ((keyView, base), edgeHigh) input).run state =
      (fun result : (((OracleWorld + SigningSpec).Range input ×
          GlobalExactTracedState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.1.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          ((globalHighDirectExactTracedMappedAdversaryImpl keyView edgeHigh
            input).run (GlobalExactTracedState.mk state.1.causal state.2))).run := by
  let augment := fun result :
      (((OracleWorld + SigningSpec).Range input ×
        GlobalHighDirectTracedState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
    ((result.1.1, GlobalExactTracedState.mk result.1.2.1 result.1.2.2),
      result.2)
  have hold := map_globalHighMonitored_adversary_full_query keyView base
    edgeHigh input state.1 state.2
  have hlifted := congrArg (fun candidate => augment <$> candidate) hold
  rw [globalHighDirectExactTracedMappedAdversaryImpl_query_eq_map]
  simpa [augment, globalHighDirectExactQueryResult, Functor.map_map,
    Function.comp_def, simulateQ_map, bind_map_left] using hlifted

theorem map_simulate_globalHighMonitored_exact_of_query
    {spec : OracleSpec ι}
    (table : GlobalChainValueIndex → Digest)
    (left : QueryImpl spec
      (StateT GlobalMonitoredTracedState ProbComp))
    (right : QueryImpl spec
      (StateT GlobalExactTracedState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))))
    (hquery : ∀ (input : spec.Domain)
      (state : GlobalMonitoredTracedState),
      (fun result : spec.Range input × GlobalMonitoredTracedState =>
        ((result.1, GlobalExactTracedState.mk result.2.1.causal result.2.2),
          result.2.1.trace)) <$>
          (left input).run state =
        (fun result : ((spec.Range input ×
            GlobalExactTracedState) ×
            RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
          (result.1, state.1.trace ++ result.2)) <$>
          (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
            ((right input).run
              (GlobalExactTracedState.mk state.1.causal state.2))).run)
    (computation : OracleComp spec α)
    (state : GlobalMonitoredTracedState) :
    (fun result : α × GlobalMonitoredTracedState =>
      ((result.1, GlobalExactTracedState.mk result.2.1.causal result.2.2),
        result.2.1.trace)) <$>
        (simulateQ left computation).run state =
      (fun result : ((α × GlobalExactTracedState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.1.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          ((simulateQ right computation).run
            (GlobalExactTracedState.mk state.1.causal state.2))).run := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, StateT.run_bind, WriterT.run_bind', map_bind,
        simulateQ_spec_query]
      simp_rw [ih]
      let project := fun result :
          spec.Range input × GlobalMonitoredTracedState =>
        ((result.1, GlobalExactTracedState.mk result.2.1.causal result.2.2),
          result.2.1.trace)
      let tail := fun head : ((spec.Range input ×
          GlobalExactTracedState) ×
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

theorem map_simulate_globalHighMonitored_adversary_exact
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : GlobalMonitoredTracedState) :
    (fun result : α × GlobalMonitoredTracedState =>
      ((result.1, GlobalExactTracedState.mk result.2.1.causal result.2.2),
        result.2.1.trace)) <$>
        (simulateQ (globalHighMonitoredMappedAdversaryImpl
          ((keyView, base), edgeHigh)) computation).run state =
      (fun result : ((α × GlobalExactTracedState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.1.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          ((simulateQ
            (globalHighDirectExactTracedMappedAdversaryImpl keyView edgeHigh)
            computation).run
              (GlobalExactTracedState.mk state.1.causal state.2))).run := by
  apply map_simulate_globalHighMonitored_exact_of_query
  exact map_globalHighMonitored_adversary_exact_query keyView base edgeHigh

theorem globalHighDirectExactTracedVerifierImpl_run_eq
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp OracleWorld α)
    (initialState : GlobalExactTracedState) :
    (simulateQ (globalHighDirectExactTracedVerifierImpl keyView edgeHigh)
        computation).run initialState =
      (fun result => (result.1, initialState.withCausalState result.2)) <$>
        (simulateQ (globalHighDirectVerifierImpl keyView edgeHigh)
          computation).run initialState.causalState := by
  apply globalExactTracedCausalLens.simulateQ_run_eq
  intro input state
  rfl

theorem globalHighDirectExactTracedVerifierImpl_run_eq_map_traced
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp OracleWorld α)
    (initialState : GlobalExactTracedState) :
    (simulateQ (globalHighDirectExactTracedVerifierImpl keyView edgeHigh)
        computation).run initialState =
      (fun result => (result.1, GlobalExactTracedState.mk result.2.1
        result.2.2)) <$>
        (simulateQ (globalHighDirectTracedVerifierImpl keyView edgeHigh)
          computation).run
            (initialState.causalState, initialState.attackerTrace) := by
  rw [globalHighDirectExactTracedVerifierImpl_run_eq,
    globalHighDirectTracedVerifierImpl_run_eq]
  simp [Functor.map_map]

theorem map_simulate_globalHighExactMonitored_verifier_full_projection
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp OracleWorld α)
    (state : GlobalHighExactMonitoredState) :
    (fun result : α × GlobalMonitoredTracedState =>
      ((result.1, GlobalExactTracedState.mk result.2.1.causal
        result.2.2), result.2.1.trace)) <$>
        (simulateQ (globalHighMonitoredVerifierImpl
          ((keyView, base), edgeHigh)) computation).run state.1 =
      (fun result : ((α × GlobalExactTracedState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.1.1.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          ((simulateQ
            (globalHighDirectExactTracedVerifierImpl keyView edgeHigh)
            computation).run (globalHighExactStateProjection state))).run := by
  let augment := fun result : ((α × GlobalHighDirectTracedState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
    ((result.1.1, GlobalExactTracedState.mk result.1.2.1 result.1.2.2),
      result.2)
  have hold := map_simulate_globalHighMonitored_verifier_full_projection
    keyView base edgeHigh computation state.1.1 state.1.2
  have hlifted := congrArg (fun candidate => augment <$> candidate) hold
  rw [globalHighDirectExactTracedVerifierImpl_run_eq_map_traced]
  simpa [globalHighExactStateProjection, augment, Functor.map_map,
    Function.comp_def, simulateQ_map, bind_map_left] using hlifted

theorem map_simulate_globalHighMonitored_verifier_exact
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp OracleWorld α)
    (state : GlobalMonitoredTracedState) :
    (fun result : α × GlobalMonitoredTracedState =>
      ((result.1, GlobalExactTracedState.mk result.2.1.causal result.2.2),
        result.2.1.trace)) <$>
        (simulateQ (globalHighMonitoredVerifierImpl
          ((keyView, base), edgeHigh)) computation).run state =
      (fun result : ((α × GlobalExactTracedState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.1.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          ((simulateQ
            (globalHighDirectExactTracedVerifierImpl keyView edgeHigh)
            computation).run
              (GlobalExactTracedState.mk state.1.causal state.2))).run := by
  let augment := fun result : ((α × GlobalHighDirectTracedState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
    ((result.1.1, GlobalExactTracedState.mk result.1.2.1 result.1.2.2),
      result.2)
  have hold := map_simulate_globalHighMonitored_verifier_full_projection
    keyView base edgeHigh computation state.1 state.2
  have hlifted := congrArg (fun candidate => augment <$> candidate) hold
  rw [globalHighDirectExactTracedVerifierImpl_run_eq_map_traced]
  simpa [augment, Functor.map_map, Function.comp_def, simulateQ_map,
    bind_map_left] using hlifted

set_option maxHeartbeats 3000000 in
theorem map_globalHighMonitoredDetailedExecution_full_projection
    (adversary : Adversary)
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    (fun result : (Forgery × Bool) × GlobalMonitoredTracedState =>
      ((result.1, GlobalExactTracedState.mk result.2.1.causal result.2.2),
        result.2.1.trace)) <$>
        globalHighMonitoredDetailedExecution adversary
          ((keyView, base), edgeHigh) =
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
        ((globalHighDirectExactTracedDetailedExecution adversary keyView
          edgeHigh).run (GlobalExactTracedState.initial
            (globalFilteredCausalKeygenState keyView)))).run := by
  let initial : GlobalMonitoredTracedState :=
    (⟨globalFilteredCausalKeygenState keyView,
      some AdaptiveRevealMonitor.State.empty, []⟩, [])
  let project := fun result : Forgery × GlobalMonitoredTracedState =>
    ((result.1, GlobalExactTracedState.mk result.2.1.causal result.2.2),
      result.2.1.trace)
  let tail := fun head : ((Forgery × GlobalExactTracedState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
    (fun result : ((Bool × GlobalExactTracedState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
      (((head.1.1, result.1.1), result.1.2), head.2 ++ result.2)) <$>
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
        ((simulateQ (globalHighDirectExactTracedVerifierImpl keyView edgeHigh)
          (Concrete.scheme.verify keyView.publicKey head.1.1.epoch
            head.1.1.message head.1.1.signature)).run head.1.2)).run
  have htail (handled : Forgery × GlobalMonitoredTracedState) :
      (do
        let verified ← (simulateQ (globalHighMonitoredVerifierImpl
          ((keyView, base), edgeHigh))
          (Concrete.scheme.verify keyView.publicKey handled.1.epoch
            handled.1.message handled.1.signature)).run handled.2
        pure (((handled.1, verified.1),
          GlobalExactTracedState.mk verified.2.1.causal verified.2.2),
            verified.2.1.trace)) = tail (project handled) := by
    have hvertifier :=
      map_simulate_globalHighMonitored_verifier_exact keyView
        base edgeHigh
        (Concrete.scheme.verify keyView.publicKey handled.1.epoch
          handled.1.message handled.1.signature) handled.2
    simpa [tail, project, Functor.map_map] using
      congrArg
      (fun candidate =>
        (fun result : ((Bool × GlobalExactTracedState) ×
            RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
          (((handled.1, result.1.1), result.1.2), result.2)) <$>
          candidate)
        hvertifier
  unfold globalHighMonitoredDetailedExecution
    globalHighDirectExactTracedDetailedExecution
  simp only [map_bind, StateT.run_mk, simulateQ_bind, WriterT.run_bind',
    map_pure]
  simp_rw [htail]
  change (do
    let handled ← (simulateQ (globalHighMonitoredMappedAdversaryImpl
      ((keyView, base), edgeHigh))
        (adversary.main keyView.publicKey)).run initial
    tail (project handled)) = _
  rw [← bind_map_left project]
  have hhead :=
    map_simulate_globalHighMonitored_adversary_exact keyView
      base edgeHigh (adversary.main keyView.publicKey) initial
  change project <$>
    (simulateQ (globalHighMonitoredMappedAdversaryImpl
      ((keyView, base), edgeHigh))
        (adversary.main keyView.publicKey)).run initial = _ at hhead
  simp only [initial, List.nil_append] at hhead
  rw [hhead, bind_map_left]
  apply bind_congr
  intro head
  simp [tail]

def globalHighMonitoredFullProjection
    (result : GlobalHighMonitoredProgramResult) :
    (GlobalChainValueIndex → Digest) ×
      (GlobalExactTracedResult ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :=
  (result.1.1.2,
    (((result.1.1.1, result.1.2),
      (result.2.1, GlobalExactTracedState.mk result.2.2.1.causal
        result.2.2.2)), result.2.2.1.trace))


def globalHighDirectExactTracedBaseProjection
    (result : GlobalExactTracedResult) : GlobalHighDirectResult :=
  (result.1, (result.2.1, result.2.2.causalState))

noncomputable def globalHighDirectExactForgeryPrimaryProbeTrace
    (result : GlobalExactTracedResult) :
    RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex :=
  globalHighDirectForgeryPrimaryProbeTrace
    (globalHighDirectExactTracedBaseProjection result)

noncomputable def appendGlobalHighDirectExactPublicTrace
    (result : (GlobalChainValueIndex → Digest) ×
      (GlobalExactTracedResult ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) :
    (GlobalChainValueIndex → Digest) ×
      (GlobalExactTracedResult ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :=
  (result.1, (result.2.1, result.2.2 ++
    globalHighDirectExactForgeryPrimaryProbeTrace result.2.1))


noncomputable def globalFirstLaneExactTracedPublicProgram
    (adversary : Adversary) :
    OracleComp GlobalFirstLaneWorld GlobalExactTracedResult := do
  let result ← globalFirstLaneExactTracedProgram adversary
  let _ ← globalFirstLaneLiftRevealProbe
    (RevealProbeOracleSimulation.emitObservedTrace
      (globalHighDirectExactForgeryPrimaryProbeTrace result))
  pure result


theorem globalHighDirectExactForgeryPrimaryProbeTrace_agrees
    (table : GlobalChainValueIndex → Digest)
    (result : GlobalExactTracedResult) :
    RevealProbeOracleSimulation.TraceAgrees table
      (globalHighDirectExactForgeryPrimaryProbeTrace result) := by
  unfold globalHighDirectExactForgeryPrimaryProbeTrace
  exact globalHighDirectForgeryPrimaryProbeTrace_agrees table _


theorem globalHighMonitored_fullProjection_public_eq
    (result : GlobalHighMonitoredProgramResult) :
    let projected := appendGlobalHighDirectExactPublicTrace
      (globalHighMonitoredFullProjection result)
    (projected.1, ((), projected.2.2)) =
      globalHighMonitoredPublicProjection result := by
  rw [globalHighMonitoredPublicProjection_eq_append_direct]
  rfl

theorem globalHighExactEncodingEvent_implies_combinedHit
    (table : GlobalChainValueIndex → Digest)
    (encodingTrace : EncodingActionTrace)
    (attackerTrace : AttackerActionTrace)
    (trace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hencodingSub : List.Sublist encodingTrace trace.encodingActions)
    (hvalidSub : List.Sublist
      (CappedEncodingMonitor.validObservedSignEpochs
        trace.encodingActions)
      (attackerTrace.toSigningLog.map
        fun entry => entry.1.epoch))
    (hvalid : SigningTranscript.Valid attackerTrace.toSigningLog)
    (hhit : CappedEncodingMonitor.runObserved EncodingMonitor.State.empty
      encodingTrace = true) :
    FirstLaneOracleSimulation.CombinedHit table trace := by
  apply Or.inl
  have hnodup :
      (CappedEncodingMonitor.validObservedSignEpochs
        trace.encodingActions).Nodup := by
    exact hvalidSub.nodup hvalid
  exact CappedEncodingMonitor.runObserved_empty_eq_true_mono_sublist
    hencodingSub hnodup hhit

abbrev GlobalFirstLaneExactPublicEagerResult :=
  (GlobalChainValueIndex → Digest) ×
    (GlobalExactTracedResult ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)


noncomputable def globalFirstLaneExactPublicEagerExperiment
    (adversary : Adversary) :
    ProbComp GlobalFirstLaneExactPublicEagerResult :=
  FirstLaneOracleSimulation.eagerExperiment
    (globalFirstLaneExactTracedPublicProgram adversary)


end XmssSecurity.CappedChain
