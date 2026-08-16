import XmssSecurity.CappedChain.CausalStateInvariantSimulation
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

noncomputable def causalCacheXmssRomImpl :
    QueryImpl OracleWorld
      (StateT (QueryCache HashSpec)
        (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex))) :=
  fun input cache =>
    match input with
    | .inl n =>
        (fun output => (output, cache)) <$>
          RevealProbeOracleSimulation.uniformQuery n
    | .inr hashInput =>
        RevealProbeOracleSimulation.liftProbComp
          ((randomOracle hashInput).run cache)

theorem causalXmssRomImpl_project_cache_step
    (input : OracleWorld.Domain) (state : CausalHashState) :
    Prod.map id CausalHashState.cache <$> (causalXmssRomImpl input).run state =
      (causalCacheXmssRomImpl input).run state.cache := by
  cases input with
  | inl n =>
      change Prod.map id CausalHashState.cache <$>
          (causalUniformImpl n).run state =
        (fun output => (output, state.cache)) <$>
          RevealProbeOracleSimulation.uniformQuery n
      unfold causalUniformImpl
      rw [OracleComp.liftM_run_StateT]
      simp [Functor.map_map]
  | inr input =>
      change Prod.map id CausalHashState.cache <$>
          (causalHashQuery input).run state =
        RevealProbeOracleSimulation.liftProbComp
          ((randomOracle input).run state.cache)
      rw [causalHashQuery_run]
      simp [Functor.map_map]

theorem causalXmssRomImpl_reconstruct_step
    (input : OracleWorld.Domain) (state : CausalHashState) :
    (causalXmssRomImpl input).run state =
      (fun result => (result.1, { state with cache := result.2 })) <$>
        (causalCacheXmssRomImpl input).run state.cache := by
  cases input with
  | inl n =>
      change (causalUniformImpl n).run state =
        (fun result => (result.1, { state with cache := result.2 })) <$>
          ((fun output => (output, state.cache)) <$>
            RevealProbeOracleSimulation.uniformQuery n)
      unfold causalUniformImpl
      rw [OracleComp.liftM_run_StateT]
      simp [Functor.map_map]
  | inr input =>
      change (causalHashQuery input).run state =
        (fun result => (result.1, { state with cache := result.2 })) <$>
          RevealProbeOracleSimulation.liftProbComp
            ((randomOracle input).run state.cache)
      exact causalHashQuery_run input state

theorem simulate_causalXmssRomImpl_reconstruct
    (computation : OracleComp OracleWorld α) (state : CausalHashState) :
    (simulateQ causalXmssRomImpl computation).run state =
      (fun result => (result.1, { state with cache := result.2 })) <$>
        (simulateQ causalCacheXmssRomImpl computation).run state.cache := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
      rw [causalXmssRomImpl_reconstruct_step]
      rw [bind_map_left]
      apply bind_congr
      intro handled
      rw [ih]

theorem simulate_uniformForwardImpl_xmssRomImpl_step
    (input : OracleWorld.Domain) (cache : QueryCache HashSpec) :
    simulateQ
        (RevealProbeOracleSimulation.uniformForwardImpl
          (Index := ChainValueIndex))
        ((xmssRomImpl input).run cache) =
      (causalCacheXmssRomImpl input).run cache := by
  cases input with
  | inl n =>
      change simulateQ
          (RevealProbeOracleSimulation.uniformForwardImpl
            (Index := ChainValueIndex))
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
  | inr hashInput =>
      rfl

theorem simulate_causalCacheXmssRomImpl_eq_liftProbComp
    (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) :
    (simulateQ causalCacheXmssRomImpl computation).run cache =
      RevealProbeOracleSimulation.liftProbComp
        ((simulateQ xmssRomImpl computation).run cache) := by
  exact (simulateQ_StateT_compose xmssRomImpl
    (RevealProbeOracleSimulation.uniformForwardImpl (Index := ChainValueIndex))
    causalCacheXmssRomImpl simulate_uniformForwardImpl_xmssRomImpl_step
    computation cache).symm

theorem simulate_causalXmssRomImpl_project_cache
    (computation : OracleComp OracleWorld α) (state : CausalHashState) :
    Prod.map id CausalHashState.cache <$>
        (simulateQ causalXmssRomImpl computation).run state =
      (simulateQ causalCacheXmssRomImpl computation).run state.cache := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
    causalXmssRomImpl causalCacheXmssRomImpl CausalHashState.cache
  exact causalXmssRomImpl_project_cache_step

theorem simulate_eagerImpl_causalCacheXmssRomImpl_step
    (table : ChainValueIndex → Digest) (input : OracleWorld.Domain)
    (cache : QueryCache HashSpec) :
    simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        ((causalCacheXmssRomImpl input).run cache) =
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

theorem simulate_eagerImpl_simulate_causalCacheXmssRomImpl
    (table : ChainValueIndex → Digest)
    (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) :
    simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        ((simulateQ causalCacheXmssRomImpl computation).run cache) =
      (simulateQ xmssRomImpl computation).run cache := by
  exact simulateQ_StateT_compose causalCacheXmssRomImpl
    (RevealProbeOracleSimulation.eagerImpl table) xmssRomImpl
    (simulate_eagerImpl_causalCacheXmssRomImpl_step table)
    computation cache

theorem simulate_eagerTrace_simulate_causalCacheXmssRomImpl
    (table : ChainValueIndex → Digest)
    (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((simulateQ causalCacheXmssRomImpl computation).run cache)).run =
      (fun result =>
        (result, ([] : RevealProbeOracleSimulation.ActionTrace
          ChainValueIndex))) <$>
        (simulateQ xmssRomImpl computation).run cache := by
  rw [simulate_causalCacheXmssRomImpl_eq_liftProbComp]
  exact RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp table
    ((simulateQ xmssRomImpl computation).run cache)

theorem simulate_eagerImpl_simulate_causalXmssRomImpl_project_cache
    (table : ChainValueIndex → Digest)
    (computation : OracleComp OracleWorld α) (state : CausalHashState) :
    Prod.map id CausalHashState.cache <$>
        simulateQ (RevealProbeOracleSimulation.eagerImpl table)
          ((simulateQ causalXmssRomImpl computation).run state) =
      (simulateQ xmssRomImpl computation).run state.cache := by
  rw [← simulateQ_map, simulate_causalXmssRomImpl_project_cache,
    simulate_eagerImpl_simulate_causalCacheXmssRomImpl]

theorem simulate_eagerImpl_simulate_causalXmssRomImpl_reconstruct
    (table : ChainValueIndex → Digest)
    (computation : OracleComp OracleWorld α) (state : CausalHashState) :
    simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        ((simulateQ causalXmssRomImpl computation).run state) =
      (fun result => (result.1, { state with cache := result.2 })) <$>
        (simulateQ xmssRomImpl computation).run state.cache := by
  rw [simulate_causalXmssRomImpl_reconstruct, simulateQ_map,
    simulate_eagerImpl_simulate_causalCacheXmssRomImpl]

theorem simulate_eagerTrace_simulate_causalXmssRomImpl_reconstruct
    (table : ChainValueIndex → Digest)
    (computation : OracleComp OracleWorld α) (state : CausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((simulateQ causalXmssRomImpl computation).run state)).run =
      (fun result =>
        ((result.1, { state with cache := result.2 }),
          ([] : RevealProbeOracleSimulation.ActionTrace ChainValueIndex))) <$>
        (simulateQ xmssRomImpl computation).run state.cache := by
  rw [simulate_causalXmssRomImpl_reconstruct, simulateQ_map,
    WriterT.run_map', simulate_eagerTrace_simulate_causalCacheXmssRomImpl]
  simp [Functor.map_map]

theorem simulate_eagerImpl_causalKeygen_project_cache
    (table : ChainValueIndex → Digest) :
    Prod.map id CausalHashState.cache <$>
        simulateQ (RevealProbeOracleSimulation.eagerImpl table)
          ((simulateQ causalXmssRomImpl Concrete.keygen).run
            CausalHashState.empty) =
      (simulateQ xmssRomImpl Concrete.keygen).run ∅ := by
  simpa [CausalHashState.empty] using
    (simulate_eagerImpl_simulate_causalXmssRomImpl_project_cache
      table Concrete.keygen CausalHashState.empty)

theorem simulate_eagerImpl_causalKeygen_reconstruct
    (table : ChainValueIndex → Digest) :
    simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        ((simulateQ causalXmssRomImpl Concrete.keygen).run
          CausalHashState.empty) =
      (fun result =>
        (result.1, { CausalHashState.empty with cache := result.2 })) <$>
        (simulateQ xmssRomImpl Concrete.keygen).run ∅ := by
  simpa [CausalHashState.empty] using
    (simulate_eagerImpl_simulate_causalXmssRomImpl_reconstruct
      table Concrete.keygen CausalHashState.empty)

theorem simulate_eagerTrace_causalKeygen_reconstruct
    (table : ChainValueIndex → Digest) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((simulateQ causalXmssRomImpl Concrete.keygen).run
          CausalHashState.empty)).run =
      (fun result =>
        ((result.1, { CausalHashState.empty with cache := result.2 }),
          ([] : RevealProbeOracleSimulation.ActionTrace ChainValueIndex))) <$>
        (simulateQ xmssRomImpl Concrete.keygen).run ∅ := by
  simpa [CausalHashState.empty] using
    (simulate_eagerTrace_simulate_causalXmssRomImpl_reconstruct
      table Concrete.keygen CausalHashState.empty)

end XmssSecurity.CappedChain
