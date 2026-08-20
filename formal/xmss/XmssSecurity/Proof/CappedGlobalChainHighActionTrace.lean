import XmssSecurity.Proof.CappedGlobalChainHighWholeGame
import XmssSecurity.Proof.CappedGlobalChainHighDirectReduction
import XmssSecurity.Proof.StateLens

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

abbrev GlobalHighDirectTracedState :=
  GlobalCausalHashState × AttackerActionTrace

noncomputable def globalHighDirectTracedMappedAdversaryImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT GlobalHighDirectTracedState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  fun input => StateT.mk fun state => do
    let result ←
      (globalHighDirectBaseMappedAdversaryImpl keyView edgeHigh input).run state.1
    pure (result.1,
      (result.2, state.2 ++ attackerActionFragment input result.1))

noncomputable def globalHighDirectTracedVerifierImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    QueryImpl OracleWorld
      (StateT GlobalHighDirectTracedState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  fun input => StateT.mk fun state =>
    (fun result => (result.1, (result.2, state.2))) <$>
      (globalHighDirectVerifierImpl keyView edgeHigh input).run state.1

theorem globalHighMonitoredMappedAdversaryImpl_support_actionTrace_eq
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalMonitoredTracedState)
    (result : (OracleWorld + SigningSpec).Range input ×
      GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((globalHighMonitoredMappedAdversaryImpl right input).run state)) :
    result.2.2 = state.2 ++ attackerActionFragment input result.1 := by
  unfold globalHighMonitoredMappedAdversaryImpl actionTracedStateImpl at hresult
  change result ∈ support (do
    let baseResult ←
      (globalHighMonitoredBaseMappedAdversaryImpl right input).run state.1
    pure (baseResult.1,
      (baseResult.2, state.2 ++ attackerActionFragment input baseResult.1)))
      at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨baseResult, _hbaseResult, hfinal⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  rfl

theorem map_globalHighMonitored_adversary_full_query
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalMonitoredCausalState)
    (attackerTrace : AttackerActionTrace) :
    (fun result : (OracleWorld + SigningSpec).Range input ×
        GlobalMonitoredTracedState =>
      ((result.1, (result.2.1.causal, result.2.2)), result.2.1.trace)) <$>
        (globalHighMonitoredMappedAdversaryImpl
          ((keyView, base), edgeHigh) input).run (state, attackerTrace) =
      (fun result : (((OracleWorld + SigningSpec).Range input ×
          GlobalHighDirectTracedState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          ((globalHighDirectTracedMappedAdversaryImpl keyView edgeHigh input
            ).run (state.causal, attackerTrace))).run := by
  let addAttackerTrace := fun result :
      (((OracleWorld + SigningSpec).Range input × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
    ((result.1.1,
      (result.1.2, attackerTrace ++ attackerActionFragment input result.1.1)),
      result.2)
  have herased :
      (fun result : (OracleWorld + SigningSpec).Range input ×
          GlobalMonitoredTracedState =>
        ((result.1, result.2.1.causal), result.2.1.trace)) <$>
          (globalHighMonitoredMappedAdversaryImpl
            ((keyView, base), edgeHigh) input).run (state, attackerTrace) =
        (fun result : (((OracleWorld + SigningSpec).Range input ×
            GlobalCausalHashState) ×
            RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
          (result.1, state.trace ++ result.2)) <$>
          (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
            ((globalHighDirectBaseMappedAdversaryImpl keyView edgeHigh input
              ).run state.causal)).run := by
    rcases input with (uniformOrHash | request)
    · rcases uniformOrHash with n | hashInput
      · unfold globalHighDirectBaseMappedAdversaryImpl
          globalHighDirectOracleImpl globalHighDirectOracleExecution
          globalHighDirectUniformImpl
        exact map_globalHighMonitored_uniform_erased_projection keyView base
          edgeHigh n state attackerTrace
      · unfold globalHighDirectBaseMappedAdversaryImpl
          globalHighDirectOracleImpl globalHighDirectOracleExecution
        exact map_globalHighMonitored_hash_erased_projection keyView base
          edgeHigh hashInput state attackerTrace
    · unfold globalHighDirectBaseMappedAdversaryImpl
        globalHighDirectSigningImpl
      exact map_globalHighMonitored_sign_erased_projection keyView base
        edgeHigh request state attackerTrace
  have hlifted := congrArg (fun candidate => addAttackerTrace <$> candidate)
    herased
  simpa [addAttackerTrace, globalHighMonitoredMappedAdversaryImpl,
    actionTracedStateImpl, globalHighDirectTracedMappedAdversaryImpl,
    StateT.run_mk, Functor.map_map, Function.comp_def, simulateQ_bind,
    bind_map_left, List.append_assoc] using hlifted

theorem globalHighDirectTracedVerifierImpl_run_eq
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp OracleWorld α)
    (initialState : GlobalHighDirectTracedState) :
    (simulateQ (globalHighDirectTracedVerifierImpl keyView edgeHigh)
        computation).run initialState =
      (fun result => (result.1, (result.2, initialState.2))) <$>
        (simulateQ (globalHighDirectVerifierImpl keyView edgeHigh)
          computation).run initialState.1 := by
  apply (StateLens.fst : StateLens GlobalHighDirectTracedState
    GlobalCausalHashState).simulateQ_run_eq
  intro input state
  rfl

noncomputable def globalHighMonitoredVerifierBaseImpl
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) :
    QueryImpl OracleWorld (StateT GlobalMonitoredCausalState ProbComp) :=
  fun input => globalHighMonitoredBaseMappedAdversaryImpl right (.inl input)

theorem globalHighMonitoredVerifierImpl_run_eq
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (computation : OracleComp OracleWorld α)
    (initialState : GlobalMonitoredTracedState) :
    (simulateQ (globalHighMonitoredVerifierImpl right)
        computation).run initialState =
      (fun result => (result.1, (result.2, initialState.2))) <$>
        (simulateQ (globalHighMonitoredVerifierBaseImpl right)
          computation).run initialState.1 := by
  apply (StateLens.fst : StateLens GlobalMonitoredTracedState
    GlobalMonitoredCausalState).simulateQ_run_eq
  intro input state
  rfl

theorem map_simulate_globalHighMonitored_verifier_full_projection
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp OracleWorld α)
    (state : GlobalMonitoredCausalState)
    (attackerTrace : AttackerActionTrace) :
    (fun result : α × GlobalMonitoredTracedState =>
      ((result.1, (result.2.1.causal, result.2.2)), result.2.1.trace)) <$>
        (simulateQ (globalHighMonitoredVerifierImpl
          ((keyView, base), edgeHigh)) computation).run
            (state, attackerTrace) =
      (fun result : ((α × GlobalHighDirectTracedState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          ((simulateQ
            (globalHighDirectTracedVerifierImpl keyView edgeHigh)
            computation).run (state.causal, attackerTrace))).run := by
  let addAttackerTrace := fun result :
      ((α × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
    ((result.1.1, (result.1.2, attackerTrace)), result.2)
  have herased := map_simulate_globalHighMonitored_verifier_erased_projection
    keyView base edgeHigh computation state attackerTrace
  have hlifted := congrArg (fun candidate => addAttackerTrace <$> candidate)
    herased
  rw [globalHighMonitoredVerifierImpl_run_eq] at hlifted
  rw [globalHighMonitoredVerifierImpl_run_eq]
  rw [globalHighDirectTracedVerifierImpl_run_eq]
  simpa [addAttackerTrace, Functor.map_map, Function.comp_def,
    simulateQ_map, bind_map_left] using hlifted

end XmssSecurity.CappedChain
