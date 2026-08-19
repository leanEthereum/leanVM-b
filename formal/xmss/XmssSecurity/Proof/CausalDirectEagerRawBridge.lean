import XmssSecurity.Proof.CausalDirectLazyRawAdversaryRun

open OracleComp OracleSpec

namespace XmssSecurity

set_option maxRecDepth 100000 in
theorem simulate_eagerTrace_filteredDirectActionTraced_step_eq_map
    (table : ChainValueIndex → Digest)
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (((filteredDirectActionTracedMappedAdversaryImpl
        keyView selected input).run).run state)).run =
    (fun result =>
      (((result.1.1, attackerActionFragment input result.1.1), result.1.2),
        result.2)) <$>
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((filteredDirectMappedAdversaryImpl keyView selected input).run
          state)).run := by
  unfold filteredDirectActionTracedMappedAdversaryImpl
  rw [QueryImpl.withTraceAppend_apply, WriterT.run_bind',
    WriterT.run_monadLift', StateT.run_bind, simulateQ_bind,
    StateT.run_map, simulateQ_map]
  simp [WriterT.run_tell, WriterT.run_pure, simulateQ_pure,
    map_eq_bind_pure_comp]

set_option maxHeartbeats 10000 in
set_option maxRecDepth 100000 in
theorem simulate_eagerTrace_filteredDirectActionTraced_uniform_step_eq_raw
    (table : ChainValueIndex → Digest)
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (n : Nat) (state : CausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (((filteredDirectActionTracedMappedAdversaryImpl
        keyView selected (Sum.inl (Sum.inl n))).run).run state)).run =
    (((filteredDirectEagerRawActionTracedImpl table keyView selected
      (Sum.inl (Sum.inl n))).run).run state).run := by
  rw [simulate_eagerTrace_filteredDirectActionTraced_step_eq_map,
    filteredDirectEagerRawActionTracedImpl_run]
  unfold filteredDirectEagerRawActionTracedStep
  rw [filteredDirectMappedAdversaryImpl.eq_1,
    filteredDirectEagerRawMappedStep.eq_1]
  rfl

set_option maxHeartbeats 10000 in
set_option maxRecDepth 100000 in
theorem simulate_eagerTrace_filteredDirectActionTraced_hash_step_eq_raw
    (table : ChainValueIndex → Digest)
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (input : HashInput) (state : CausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (((filteredDirectActionTracedMappedAdversaryImpl
        keyView selected (Sum.inl (Sum.inr input))).run).run state)).run =
    (((filteredDirectEagerRawActionTracedImpl table keyView selected
      (Sum.inl (Sum.inr input))).run).run state).run := by
  rw [simulate_eagerTrace_filteredDirectActionTraced_step_eq_map,
    filteredDirectEagerRawActionTracedImpl_run]
  unfold filteredDirectEagerRawActionTracedStep
  rw [filteredDirectMappedAdversaryImpl.eq_2,
    filteredDirectEagerRawMappedStep.eq_2, StateT.run_mk,
    map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  apply bind_congr
  intro result
  change pure (((result.1.1, [AttackerAction.hash input]), result.1.2),
    result.2) =
      pure (((result.1.1, [AttackerAction.hash input]), result.1.2), result.2)
  rfl

set_option maxHeartbeats 10000 in
set_option maxRecDepth 100000 in
theorem simulate_eagerTrace_filteredDirectActionTraced_signing_step_eq_raw
    (table : ChainValueIndex → Digest)
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (request : SignRequest) (state : CausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (((filteredDirectActionTracedMappedAdversaryImpl
        keyView selected (Sum.inr request)).run).run state)).run =
    (((filteredDirectEagerRawActionTracedImpl table keyView selected
      (Sum.inr request)).run).run state).run := by
  rw [simulate_eagerTrace_filteredDirectActionTraced_step_eq_map,
    filteredDirectEagerRawActionTracedImpl_run]
  unfold filteredDirectEagerRawActionTracedStep
  rw [filteredDirectMappedAdversaryImpl.eq_3,
    filteredDirectEagerRawMappedStep.eq_3, StateT.run_mk,
    map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  apply bind_congr
  intro result
  change pure (((result.1.1, [AttackerAction.sign request result.1.1]),
    result.1.2), result.2) =
      pure (((result.1.1, [AttackerAction.sign request result.1.1]),
        result.1.2), result.2)
  rfl

theorem simulate_eagerTrace_filteredDirectActionTraced_step_eq_raw
    (table : ChainValueIndex → Digest)
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (((filteredDirectActionTracedMappedAdversaryImpl
        keyView selected input).run).run state)).run =
    (((filteredDirectEagerRawActionTracedImpl table keyView selected input).run).run
      state).run := by
  rcases input with (n | hashInput) | request
  · exact simulate_eagerTrace_filteredDirectActionTraced_uniform_step_eq_raw
      table keyView selected n state
  · exact simulate_eagerTrace_filteredDirectActionTraced_hash_step_eq_raw
      table keyView selected hashInput state
  · exact simulate_eagerTrace_filteredDirectActionTraced_signing_step_eq_raw
      table keyView selected request state

set_option maxHeartbeats 20000 in
set_option maxRecDepth 100000 in
theorem simulate_eagerTrace_simulate_filteredDirectActionTraced_eq_raw
    (table : ChainValueIndex → Digest)
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (((simulateQ (filteredDirectActionTracedMappedAdversaryImpl
        keyView selected) computation).run).run state)).run =
    (((simulateQ
      (filteredDirectEagerRawActionTracedImpl table keyView selected)
        computation).run).run state).run := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure result => rfl
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, WriterT.run_bind', StateT.run_bind]
      rw [simulate_eagerTrace_filteredDirectActionTraced_step_eq_raw]
      apply bind_congr
      intro handled
      rw [StateT.run_map, simulateQ_map, StateT.run_map,
        WriterT.run_map, WriterT.run_map]
      rw [ih handled.1.1.1 handled.1.2]

end XmssSecurity
