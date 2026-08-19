import XmssSecurity.Proof.CausalCacheInvariantGame

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

noncomputable local instance causalAttackerHashSampleableChainTable :
    SampleableType (ChainValueIndex → Digest) :=
  SampleableType.ofFintype (ChainValueIndex → Digest)

noncomputable def causalEagerAttackerHashStep
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState) :
    ProbComp ((ChainValueIndex → Digest) ×
      ((HashOutput × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) := do
  let table ← $ᵗ (ChainValueIndex → Digest)
  let result ← (simulateQ
    (RevealProbeOracleSimulation.eagerTraceImpl table)
    ((causalAttackerHashQuery secretKey chain input).run state)).run
  pure (table, result)

noncomputable def causalResampledAttackerHashStep
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState) :
    ProbComp ((ChainValueIndex → Digest) ×
      ((HashOutput × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) :=
  match causalAttackerHashPlan secretKey chain input state with
  | .cached output => do
      let table ← $ᵗ (ChainValueIndex → Digest)
      pure (table, ((output,
        causalRecordedState secretKey chain input state), []))
  | .redirect output => do
      let table ← $ᵗ (ChainValueIndex → Digest)
      pure (table, ((output,
        { (causalRecordedState secretKey chain input state) with
          cache := (causalRecordedState secretKey chain input state).cache.cacheQuery
            input output }), []))
  | .fresh => do
      let table ← $ᵗ (ChainValueIndex → Digest)
      let hashResult ← (randomOracle input).run
        (causalRecordedState secretKey chain input state).cache
      pure (table, ((hashResult.1,
        { (causalRecordedState secretKey chain input state) with
          cache := hashResult.2 }), []))
  | .reveal index => do
      let output ← $ᵗ HashOutput
      let base ← $ᵗ (ChainValueIndex → Digest)
      let value := truncateHash output
      let table := Function.update base index value
      pure (table, ((output, causalRevealResultState secretKey chain input state
        index value output),
        [RevealProbeOracleSimulation.ObservedAction.reveal index value]))

theorem evalDist_uniformTable_simulate_eagerTrace_causalAttackerHashQuery_eq_resampled
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState) :
    𝒟[causalEagerAttackerHashStep secretKey chain input state] =
    𝒟[causalResampledAttackerHashStep secretKey chain input state] := by
  unfold causalEagerAttackerHashStep
  generalize hplan : causalAttackerHashPlan secretKey chain input state = plan
  cases plan with
  | cached output =>
      unfold causalResampledAttackerHashStep
      rw [hplan]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro table
      rw [causalAttackerHashQuery_run, hplan]
      simp
  | redirect output =>
      unfold causalResampledAttackerHashStep
      rw [hplan]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro table
      rw [simulate_eagerTrace_causalAttackerHashQuery_redirect_eq
        table secretKey chain input state output hplan]
      simp
  | fresh =>
      unfold causalResampledAttackerHashStep
      rw [hplan]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro table
      rw [simulate_eagerTrace_causalAttackerHashQuery_fresh_eq_causalHashQuery
        table secretKey chain input state hplan,
        simulate_eagerTrace_causalHashQuery]
      simp [map_eq_bind_pure_comp]
  | reveal index =>
      unfold causalResampledAttackerHashStep
      rw [hplan]
      exact
        evalDist_uniformTable_simulate_eagerTrace_causalAttackerHashQuery_reveal
          secretKey chain input state index hplan

theorem evalDist_uniformTable_simulate_eagerTrace_causalAttackerHashQuery_continuation
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      ((HashOutput × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    𝒟[causalEagerAttackerHashStep secretKey chain input state >>=
      fun result => continuation result.1 result.2] =
    𝒟[causalResampledAttackerHashStep secretKey chain input state >>=
      fun result => continuation result.1 result.2] := by
  rw [evalDist_bind,
    evalDist_uniformTable_simulate_eagerTrace_causalAttackerHashQuery_eq_resampled,
    ← evalDist_bind]

end XmssSecurity
