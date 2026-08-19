import XmssSecurity.Proof.CappedGlobalCausalStrategyProgram

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

noncomputable local instance globalCausalEagerSampleableChainTable :
    SampleableType (GlobalChainValueIndex → Digest) :=
  SampleableType.ofFintype (GlobalChainValueIndex → Digest)

theorem evalDist_uniformGlobalTable_simulate_eagerTrace_reveal_programmed_continuation
    (index : GlobalChainValueIndex) (finish : Digest → HashOutput → α)
    (continuation : (GlobalChainValueIndex → Digest) →
      (α × RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) → ProbComp β) :
    𝒟[do
      let table ← $ᵗ (GlobalChainValueIndex → Digest)
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table) (do
          let value ← RevealProbeOracleSimulation.revealQuery index
          let output ← RevealProbeOracleSimulation.liftProbComp
            (Rom.sampleHashOutputWithDigest value)
          pure (finish value output))).run
      continuation table result] =
    𝒟[do
      let output ← $ᵗ HashOutput
      let base ← $ᵗ (GlobalChainValueIndex → Digest)
      let table := Function.update base index (truncateHash output)
      continuation table (finish (truncateHash output) output,
        [RevealProbeOracleSimulation.ObservedAction.reveal
          index (truncateHash output)])] := by
  calc
    𝒟[do
      let table ← $ᵗ (GlobalChainValueIndex → Digest)
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table) (do
          let value ← RevealProbeOracleSimulation.revealQuery index
          let output ← RevealProbeOracleSimulation.liftProbComp
            (Rom.sampleHashOutputWithDigest value)
          pure (finish value output))).run
      continuation table result] =
        𝒟[do
          let table ← $ᵗ (GlobalChainValueIndex → Digest)
          let output ← Rom.sampleHashOutputWithDigest (table index)
          continuation table (finish (table index) output,
            [RevealProbeOracleSimulation.ObservedAction.reveal
              index (table index)])] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro table
      rw [RevealProbeOracleSimulation.simulate_eagerTrace_reveal_then_liftProbComp]
      simp [map_eq_bind_pure_comp, bind_assoc]
    _ = _ :=
      RevealProbeOracleSimulation.evalDist_uniformTable_bind_programmedCoordinate_continuation
        index (fun table value output =>
          continuation table (finish value output,
            [RevealProbeOracleSimulation.ObservedAction.reveal index value]))

theorem simulate_eagerTrace_globalCausalAttackerHashQuery_fresh_eq_globalCausalHashQuery
    (table : GlobalChainValueIndex → Digest) (secretKey : SecretKey)
    (input : HashInput) (state : GlobalCausalHashState)
    (hplan : globalCausalAttackerHashPlan secretKey input state = .fresh) :
    simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalAttackerHashQuery secretKey input).run state) =
      simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalHashQuery input).run
          (globalCausalRecordedState secretKey input state)) := by
  rw [globalCausalAttackerHashQuery_run, hplan]

theorem simulate_eagerTrace_globalCausalHashQuery
    (table : GlobalChainValueIndex → Digest) (input : HashInput)
    (state : GlobalCausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      ((globalCausalHashQuery input).run state)).run =
      (fun result : HashOutput × QueryCache HashSpec =>
        ((result.1, state.setCache result.2),
          ([] : RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))) <$>
        ((randomOracle input).run state.cache) := by
  rw [globalCausalHashQuery_run, simulateQ_map, WriterT.run_map',
    RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp]
  simp [Functor.map_map]

theorem simulate_eagerTrace_globalCausalAttackerHashQuery_reveal_eq
    (table : GlobalChainValueIndex → Digest) (secretKey : SecretKey)
    (input : HashInput) (state : GlobalCausalHashState)
    (index : GlobalChainValueIndex)
    (hplan : globalCausalAttackerHashPlan secretKey input state = .reveal index) :
    simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalAttackerHashQuery secretKey input).run state) =
      simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table) (do
        let value ← RevealProbeOracleSimulation.revealQuery index
        let output ← RevealProbeOracleSimulation.liftProbComp
          (Rom.sampleHashOutputWithDigest value)
        pure (output, globalCausalRevealResultState secretKey input state
          index value output)) := by
  rw [globalCausalAttackerHashQuery_run, hplan]
  rfl

theorem evalDist_uniformGlobalTable_simulate_eagerTrace_globalCausalAttackerHashQuery_reveal_continuation
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex)
    (hplan : globalCausalAttackerHashPlan secretKey input state = .reveal index)
    (continuation : (GlobalChainValueIndex → Digest) →
      ((HashOutput × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) → ProbComp α) :
    𝒟[do
      let table ← $ᵗ (GlobalChainValueIndex → Digest)
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalAttackerHashQuery secretKey input).run state)).run
      continuation table result] =
    𝒟[do
      let output ← $ᵗ HashOutput
      let base ← $ᵗ (GlobalChainValueIndex → Digest)
      let value := truncateHash output
      let table := Function.update base index value
      continuation table ((output, globalCausalRevealResultState secretKey input state
        index value output),
        [RevealProbeOracleSimulation.ObservedAction.reveal index value])] := by
  calc
    𝒟[do
      let table ← $ᵗ (GlobalChainValueIndex → Digest)
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalAttackerHashQuery secretKey input).run state)).run
      continuation table result] =
        𝒟[do
          let table ← $ᵗ (GlobalChainValueIndex → Digest)
          let result ← (simulateQ
            (RevealProbeOracleSimulation.eagerTraceImpl table) (do
              let value ← RevealProbeOracleSimulation.revealQuery index
              let output ← RevealProbeOracleSimulation.liftProbComp
                (Rom.sampleHashOutputWithDigest value)
              pure (output, globalCausalRevealResultState secretKey input state
                index value output))).run
          continuation table result] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro table
      rw [simulate_eagerTrace_globalCausalAttackerHashQuery_reveal_eq
        table secretKey input state index hplan]
    _ = _ :=
      evalDist_uniformGlobalTable_simulate_eagerTrace_reveal_programmed_continuation
        index
        (fun value output =>
          (output, globalCausalRevealResultState secretKey input state
            index value output))
        continuation

theorem evalDist_uniformGlobalTable_simulate_eagerTrace_globalCausalAttackerHashQuery_reveal
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex)
    (hplan : globalCausalAttackerHashPlan secretKey input state = .reveal index) :
    𝒟[do
      let table ← $ᵗ (GlobalChainValueIndex → Digest)
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalAttackerHashQuery secretKey input).run state)).run
      pure (table, result)] =
    𝒟[do
      let output ← $ᵗ HashOutput
      let base ← $ᵗ (GlobalChainValueIndex → Digest)
      let value := truncateHash output
      let table := Function.update base index value
      pure (table, ((output, globalCausalRevealResultState secretKey input state
        index value output),
        [RevealProbeOracleSimulation.ObservedAction.reveal index value]))] := by
  exact
    evalDist_uniformGlobalTable_simulate_eagerTrace_globalCausalAttackerHashQuery_reveal_continuation
      secretKey input state index hplan
      (fun table result => pure (table, result))

theorem simulate_eagerTrace_globalCausalAttackerHashQuery_redirect_eq
    (table : GlobalChainValueIndex → Digest) (secretKey : SecretKey)
    (input : HashInput) (state : GlobalCausalHashState) (output : HashOutput)
    (hplan : globalCausalAttackerHashPlan secretKey input state = .redirect output) :
    simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalAttackerHashQuery secretKey input).run state) =
      pure (output,
        { (globalCausalRecordedState secretKey input state) with
          cache := (globalCausalRecordedState secretKey input state).cache.cacheQuery
            input output }) := by
  rw [globalCausalAttackerHashQuery_run, hplan]
  rfl

end XmssSecurity.CappedChain
