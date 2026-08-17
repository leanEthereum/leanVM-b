import XmssSecurity.CappedGlobalCausalStrategyProgram
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

noncomputable def globalCausalCacheXmssRomImpl :
    QueryImpl OracleWorld
      (StateT (QueryCache HashSpec)
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  fun input cache =>
    match input with
    | .inl n =>
        (fun output => (output, cache)) <$>
          RevealProbeOracleSimulation.uniformQuery n
    | .inr hashInput =>
        RevealProbeOracleSimulation.liftProbComp
          ((randomOracle hashInput).run cache)

theorem globalCausalXmssRomImpl_project_cache_step
    (input : OracleWorld.Domain) (state : GlobalCausalHashState) :
    Prod.map id GlobalCausalHashState.cache <$>
        (globalCausalXmssRomImpl input).run state =
      (globalCausalCacheXmssRomImpl input).run state.cache := by
  cases input with
  | inl n =>
      change Prod.map id GlobalCausalHashState.cache <$>
          (globalCausalUniformImpl n).run state =
        (fun output => (output, state.cache)) <$>
          RevealProbeOracleSimulation.uniformQuery n
      unfold globalCausalUniformImpl
      rw [OracleComp.liftM_run_StateT]
      simp [Functor.map_map]
  | inr input =>
      change Prod.map id GlobalCausalHashState.cache <$>
          (globalCausalHashQuery input).run state =
        RevealProbeOracleSimulation.liftProbComp
          ((randomOracle input).run state.cache)
      rw [globalCausalHashQuery_run]
      simp [GlobalCausalHashState.setCache, Functor.map_map]

theorem globalCausalXmssRomImpl_reconstruct_step
    (input : OracleWorld.Domain) (state : GlobalCausalHashState) :
    (globalCausalXmssRomImpl input).run state =
      (fun result => (result.1, { state with cache := result.2 })) <$>
        (globalCausalCacheXmssRomImpl input).run state.cache := by
  cases input with
  | inl n =>
      change (globalCausalUniformImpl n).run state =
        (fun result => (result.1, { state with cache := result.2 })) <$>
          ((fun output => (output, state.cache)) <$>
            RevealProbeOracleSimulation.uniformQuery n)
      unfold globalCausalUniformImpl
      rw [OracleComp.liftM_run_StateT]
      simp [Functor.map_map]
  | inr input =>
      change (globalCausalHashQuery input).run state =
        (fun result => (result.1, { state with cache := result.2 })) <$>
          RevealProbeOracleSimulation.liftProbComp
            ((randomOracle input).run state.cache)
      exact globalCausalHashQuery_run input state

theorem simulate_globalCausalXmssRomImpl_reconstruct
    (computation : OracleComp OracleWorld alpha)
    (state : GlobalCausalHashState) :
    (simulateQ globalCausalXmssRomImpl computation).run state =
      (fun result => (result.1, { state with cache := result.2 })) <$>
        (simulateQ globalCausalCacheXmssRomImpl computation).run
          state.cache := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
      rw [globalCausalXmssRomImpl_reconstruct_step]
      rw [bind_map_left]
      apply bind_congr
      intro handled
      rw [ih]

theorem simulate_globalUniformForwardImpl_xmssRomImpl_step
    (input : OracleWorld.Domain) (cache : QueryCache HashSpec) :
    simulateQ
        (RevealProbeOracleSimulation.uniformForwardImpl
          (Index := GlobalChainValueIndex))
        ((xmssRomImpl input).run cache) =
      (globalCausalCacheXmssRomImpl input).run cache := by
  cases input with
  | inl n =>
      change simulateQ
          (RevealProbeOracleSimulation.uniformForwardImpl
            (Index := GlobalChainValueIndex))
          ((unifFwdImpl HashSpec n).run cache) =
        (fun output => (output, cache)) <$>
          RevealProbeOracleSimulation.uniformQuery n
      rw [show (unifFwdImpl HashSpec n).run cache =
          (fun output => (output, cache)) <$>
            (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) by
        simpa [simulateQ_query] using
          (unifFwdImpl.simulateQ_run
            (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) cache)]
      rw [simulateQ_map]
      rfl
  | inr hashInput => rfl

theorem simulate_globalCausalCacheXmssRomImpl_eq_liftProbComp
    (computation : OracleComp OracleWorld alpha)
    (cache : QueryCache HashSpec) :
    (simulateQ globalCausalCacheXmssRomImpl computation).run cache =
      RevealProbeOracleSimulation.liftProbComp
        ((simulateQ xmssRomImpl computation).run cache) := by
  exact (simulateQ_StateT_compose xmssRomImpl
    (RevealProbeOracleSimulation.uniformForwardImpl
      (Index := GlobalChainValueIndex))
    globalCausalCacheXmssRomImpl
    simulate_globalUniformForwardImpl_xmssRomImpl_step computation cache).symm

theorem simulate_globalCausalXmssRomImpl_project_cache
    (computation : OracleComp OracleWorld alpha)
    (state : GlobalCausalHashState) :
    Prod.map id GlobalCausalHashState.cache <$>
        (simulateQ globalCausalXmssRomImpl computation).run state =
      (simulateQ globalCausalCacheXmssRomImpl computation).run
        state.cache := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
    globalCausalXmssRomImpl globalCausalCacheXmssRomImpl
      GlobalCausalHashState.cache
  exact globalCausalXmssRomImpl_project_cache_step

theorem simulate_eagerImpl_globalCausalCacheXmssRomImpl_step
    (table : GlobalChainValueIndex → Digest)
    (input : OracleWorld.Domain) (cache : QueryCache HashSpec) :
    simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        ((globalCausalCacheXmssRomImpl input).run cache) =
      (xmssRomImpl input).run cache := by
  cases input with
  | inl n =>
      change simulateQ (RevealProbeOracleSimulation.eagerImpl table)
          ((fun output => (output, cache)) <$>
            RevealProbeOracleSimulation.uniformQuery n) =
        (unifFwdImpl HashSpec n).run cache
      rw [simulateQ_map]
      simp [RevealProbeOracleSimulation.uniformQuery,
        RevealProbeOracleSimulation.eagerImpl, unifFwdImpl]
  | inr hashInput =>
      change simulateQ (RevealProbeOracleSimulation.eagerImpl table)
          (RevealProbeOracleSimulation.liftProbComp
            ((randomOracle hashInput).run cache)) =
        (randomOracle hashInput).run cache
      exact RevealProbeOracleSimulation.simulate_eagerImpl_liftProbComp table
        ((randomOracle hashInput).run cache)

theorem simulate_eagerImpl_simulate_globalCausalCacheXmssRomImpl
    (table : GlobalChainValueIndex → Digest)
    (computation : OracleComp OracleWorld alpha)
    (cache : QueryCache HashSpec) :
    simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        ((simulateQ globalCausalCacheXmssRomImpl computation).run cache) =
      (simulateQ xmssRomImpl computation).run cache := by
  exact simulateQ_StateT_compose globalCausalCacheXmssRomImpl
    (RevealProbeOracleSimulation.eagerImpl table) xmssRomImpl
    (simulate_eagerImpl_globalCausalCacheXmssRomImpl_step table)
    computation cache

theorem simulate_eagerTrace_simulate_globalCausalCacheXmssRomImpl
    (table : GlobalChainValueIndex → Digest)
    (computation : OracleComp OracleWorld alpha)
    (cache : QueryCache HashSpec) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((simulateQ globalCausalCacheXmssRomImpl computation).run cache)).run =
      (fun result =>
        (result, ([] : RevealProbeOracleSimulation.ActionTrace
          GlobalChainValueIndex))) <$>
        (simulateQ xmssRomImpl computation).run cache := by
  rw [simulate_globalCausalCacheXmssRomImpl_eq_liftProbComp]
  exact RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp table
    ((simulateQ xmssRomImpl computation).run cache)

theorem simulate_eagerImpl_simulate_globalCausalXmssRomImpl_project_cache
    (table : GlobalChainValueIndex → Digest)
    (computation : OracleComp OracleWorld alpha)
    (state : GlobalCausalHashState) :
    Prod.map id GlobalCausalHashState.cache <$>
        simulateQ (RevealProbeOracleSimulation.eagerImpl table)
          ((simulateQ globalCausalXmssRomImpl computation).run state) =
      (simulateQ xmssRomImpl computation).run state.cache := by
  rw [← simulateQ_map, simulate_globalCausalXmssRomImpl_project_cache,
    simulate_eagerImpl_simulate_globalCausalCacheXmssRomImpl]

theorem simulate_eagerImpl_simulate_globalCausalXmssRomImpl_reconstruct
    (table : GlobalChainValueIndex → Digest)
    (computation : OracleComp OracleWorld alpha)
    (state : GlobalCausalHashState) :
    simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        ((simulateQ globalCausalXmssRomImpl computation).run state) =
      (fun result => (result.1, { state with cache := result.2 })) <$>
        (simulateQ xmssRomImpl computation).run state.cache := by
  rw [simulate_globalCausalXmssRomImpl_reconstruct, simulateQ_map,
    simulate_eagerImpl_simulate_globalCausalCacheXmssRomImpl]

theorem simulate_eagerTrace_simulate_globalCausalXmssRomImpl_reconstruct
    (table : GlobalChainValueIndex → Digest)
    (computation : OracleComp OracleWorld alpha)
    (state : GlobalCausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((simulateQ globalCausalXmssRomImpl computation).run state)).run =
      (fun result =>
        ((result.1, { state with cache := result.2 }),
          ([] : RevealProbeOracleSimulation.ActionTrace
            GlobalChainValueIndex))) <$>
        (simulateQ xmssRomImpl computation).run state.cache := by
  rw [simulate_globalCausalXmssRomImpl_reconstruct, simulateQ_map,
    WriterT.run_map',
    simulate_eagerTrace_simulate_globalCausalCacheXmssRomImpl]
  simp [Functor.map_map]

theorem simulate_eagerImpl_globalCausalKeygen_project_cache
    (table : GlobalChainValueIndex → Digest) :
    Prod.map id GlobalCausalHashState.cache <$>
        simulateQ (RevealProbeOracleSimulation.eagerImpl table)
          ((simulateQ globalCausalXmssRomImpl Concrete.keygen).run
            GlobalCausalHashState.empty) =
      (simulateQ xmssRomImpl Concrete.keygen).run ∅ := by
  simpa [GlobalCausalHashState.empty] using
    (simulate_eagerImpl_simulate_globalCausalXmssRomImpl_project_cache
      table Concrete.keygen GlobalCausalHashState.empty)

theorem simulate_eagerImpl_globalCausalKeygen_reconstruct
    (table : GlobalChainValueIndex → Digest) :
    simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        ((simulateQ globalCausalXmssRomImpl Concrete.keygen).run
          GlobalCausalHashState.empty) =
      (fun result =>
        (result.1,
          { GlobalCausalHashState.empty with cache := result.2 })) <$>
        (simulateQ xmssRomImpl Concrete.keygen).run ∅ := by
  simpa [GlobalCausalHashState.empty] using
    (simulate_eagerImpl_simulate_globalCausalXmssRomImpl_reconstruct
      table Concrete.keygen GlobalCausalHashState.empty)

theorem simulate_eagerTrace_globalCausalKeygen_reconstruct
    (table : GlobalChainValueIndex → Digest) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((simulateQ globalCausalXmssRomImpl Concrete.keygen).run
          GlobalCausalHashState.empty)).run =
      (fun result =>
        ((result.1,
          { GlobalCausalHashState.empty with cache := result.2 }),
          ([] : RevealProbeOracleSimulation.ActionTrace
            GlobalChainValueIndex))) <$>
        (simulateQ xmssRomImpl Concrete.keygen).run ∅ := by
  simpa [GlobalCausalHashState.empty] using
    (simulate_eagerTrace_simulate_globalCausalXmssRomImpl_reconstruct
      table Concrete.keygen GlobalCausalHashState.empty)

end XmssSecurity.CappedChain
