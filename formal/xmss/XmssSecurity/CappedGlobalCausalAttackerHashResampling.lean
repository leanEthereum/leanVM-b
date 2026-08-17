import XmssSecurity.CappedGlobalCausalStrategyEagerSteps

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

noncomputable local instance globalCausalAttackerHashSampleableChainTable :
    SampleableType (GlobalChainValueIndex → Digest) :=
  SampleableType.ofFintype (GlobalChainValueIndex → Digest)

noncomputable def globalCausalEagerAttackerHashStep
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) :
    ProbComp ((GlobalChainValueIndex → Digest) ×
      ((HashOutput × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) := do
  let table ← $ᵗ (GlobalChainValueIndex → Digest)
  let result ← (simulateQ
    (RevealProbeOracleSimulation.eagerTraceImpl table)
    ((globalCausalAttackerHashQuery secretKey input).run state)).run
  pure (table, result)

noncomputable def globalCausalResampledAttackerHashStep
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) :
    ProbComp ((GlobalChainValueIndex → Digest) ×
      ((HashOutput × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) :=
  match globalCausalAttackerHashPlan secretKey input state with
  | .cached output => do
      let table ← $ᵗ (GlobalChainValueIndex → Digest)
      pure (table, ((output,
        globalCausalRecordedState secretKey input state), []))
  | .redirect output => do
      let table ← $ᵗ (GlobalChainValueIndex → Digest)
      pure (table, ((output,
        { (globalCausalRecordedState secretKey input state) with
          cache := (globalCausalRecordedState secretKey input state).cache.cacheQuery
            input output }), []))
  | .fresh => do
      let table ← $ᵗ (GlobalChainValueIndex → Digest)
      let hashResult ← (randomOracle input).run
        (globalCausalRecordedState secretKey input state).cache
      pure (table, ((hashResult.1,
        { (globalCausalRecordedState secretKey input state) with
          cache := hashResult.2 }), []))
  | .reveal index => do
      let output ← $ᵗ HashOutput
      let base ← $ᵗ (GlobalChainValueIndex → Digest)
      let value := truncateHash output
      let table := Function.update base index value
      pure (table, ((output, globalCausalRevealResultState secretKey input state
        index value output),
        [RevealProbeOracleSimulation.ObservedAction.reveal index value]))

theorem evalDist_uniformGlobalTable_simulate_eagerTrace_globalCausalAttackerHashQuery_eq_resampled
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) :
    𝒟[globalCausalEagerAttackerHashStep secretKey input state] =
    𝒟[globalCausalResampledAttackerHashStep secretKey input state] := by
  unfold globalCausalEagerAttackerHashStep
  generalize hplan : globalCausalAttackerHashPlan secretKey input state = plan
  cases plan with
  | cached output =>
      unfold globalCausalResampledAttackerHashStep
      rw [hplan]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro table
      rw [globalCausalAttackerHashQuery_run, hplan]
      simp
  | redirect output =>
      unfold globalCausalResampledAttackerHashStep
      rw [hplan]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro table
      rw [simulate_eagerTrace_globalCausalAttackerHashQuery_redirect_eq
        table secretKey input state output hplan]
      simp
  | fresh =>
      unfold globalCausalResampledAttackerHashStep
      rw [hplan]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro table
      rw [simulate_eagerTrace_globalCausalAttackerHashQuery_fresh_eq_globalCausalHashQuery
        table secretKey input state hplan,
        simulate_eagerTrace_globalCausalHashQuery]
      simp [GlobalCausalHashState.setCache, map_eq_bind_pure_comp]
  | reveal index =>
      unfold globalCausalResampledAttackerHashStep
      rw [hplan]
      exact
        evalDist_uniformGlobalTable_simulate_eagerTrace_globalCausalAttackerHashQuery_reveal
          secretKey input state index hplan

theorem evalDist_uniformGlobalTable_simulate_eagerTrace_globalCausalAttackerHashQuery_continuation
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (continuation : (GlobalChainValueIndex → Digest) →
      ((HashOutput × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) → ProbComp α) :
    𝒟[globalCausalEagerAttackerHashStep secretKey input state >>=
      fun result => continuation result.1 result.2] =
    𝒟[globalCausalResampledAttackerHashStep secretKey input state >>=
      fun result => continuation result.1 result.2] := by
  rw [evalDist_bind,
    evalDist_uniformGlobalTable_simulate_eagerTrace_globalCausalAttackerHashQuery_eq_resampled,
    ← evalDist_bind]

end XmssSecurity.CappedChain
