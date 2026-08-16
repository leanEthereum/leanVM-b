import XmssSecurity.CappedChain.CausalInstalledDetailedGame

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

noncomputable local instance causalInstalledStrategySampleableChainTable :
    SampleableType (ChainValueIndex → Digest) :=
  SampleableType.ofFintype (ChainValueIndex → Digest)

noncomputable def lazyCausalStrategyResult
    (chain : ChainIndex)
    (keyResult : (PublicKey × SecretKey) × CausalHashState)
    (execution : ((((Forgery × Bool) × AttackerActionTrace) ×
      CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) :
    ((List Bool → ChainValueIndex × Digest) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :=
  ((actionTracedRevealProbeView chain
    (causalDetailedResult keyResult execution.1)).strategy, execution.2)

set_option maxRecDepth 100000 in
theorem evalDist_installed_causalStrategyAfterRealKeygenAndSigning_eq_lazy
    (adversary : Adversary Concrete.cappedScheme) (chain : ChainIndex)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (continuation : (ChainValueIndex → Digest) →
      ((List Bool → ChainValueIndex × Digest) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    let causalKeyResult := causalKeyResultOfReal keyResult
    let initial := causalKeyResult.2.finishKeygen
    𝒟[do
      let base ← $ᵗ (ChainValueIndex → Digest)
      let table := causalInstalledTable initial base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        (causalStrategyAfterRealKeygenAndSigning
          adversary chain keyResult)).run
      continuation table result] =
    𝒟[do
      let execution ← causalLazyDetailedGameAfterKeygen adversary
        causalKeyResult.1.1 causalKeyResult.1.2 chain initial
      let base ← $ᵗ (ChainValueIndex → Digest)
      let table := causalInstalledTable execution.1.2 base
      continuation table (lazyCausalStrategyResult
        chain causalKeyResult execution)] := by
  dsimp only
  simpa [causalStrategyAfterRealKeygenAndSigning, causalKeyResultOfReal,
    lazyCausalStrategyResult, simulateQ_bind, WriterT.run_bind',
    map_eq_bind_pure_comp, bind_assoc, Function.comp_apply] using
    (evalDist_installed_causalDetailedGameAfterKeygenAfterRealRom_eq_lazy
      adversary keyResult.1.1 keyResult.1.2 chain
        (causalKeyResultOfReal keyResult).2.finishKeygen
        (fun table execution => continuation table
          (lazyCausalStrategyResult chain
            (causalKeyResultOfReal keyResult) execution)))

def strategyProbeTrace
    (queries : Nat) (strategy : List Bool → ChainValueIndex × Digest) :
    RevealProbeOracleSimulation.ActionTrace ChainValueIndex :=
  (RevealProbeOracleSimulation.strategyProbes queries strategy).map fun probe =>
    RevealProbeOracleSimulation.ObservedAction.probe probe.1 probe.2

noncomputable def lazyCausalStrategyViewAfterKeygen
    (adversary : Adversary Concrete.cappedScheme) (chain : ChainIndex)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec) :
    ProbComp ((ChainValueIndex → Digest) ×
      ((List Bool → ChainValueIndex × Digest) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) := do
  let causalKeyResult := causalKeyResultOfReal keyResult
  let execution ← causalLazyDetailedGameAfterKeygen adversary
    causalKeyResult.1.1 causalKeyResult.1.2 chain
      causalKeyResult.2.finishKeygen
  let base ← $ᵗ (ChainValueIndex → Digest)
  let table := causalInstalledTable execution.1.2 base
  pure (table, lazyCausalStrategyResult chain causalKeyResult execution)

noncomputable def causalLazyStrategyViewExperiment
    (adversary : Adversary Concrete.cappedScheme) (chain : ChainIndex) :
    ProbComp ((ChainValueIndex → Digest) ×
      ((List Bool → ChainValueIndex × Digest) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) := do
  let keyResult ← (simulateQ xmssRomImpl Concrete.keygen).run ∅
  lazyCausalStrategyViewAfterKeygen adversary chain keyResult

noncomputable def causalEagerStrategyViewExperiment
    (adversary : Adversary Concrete.cappedScheme) (chain : ChainIndex) :
    ProbComp ((ChainValueIndex → Digest) ×
      ((List Bool → ChainValueIndex × Digest) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) := do
  let keyResult ← (simulateQ xmssRomImpl Concrete.keygen).run ∅
  let base ← $ᵗ (ChainValueIndex → Digest)
  let result ← (simulateQ
    (RevealProbeOracleSimulation.eagerTraceImpl base)
    (causalStrategyAfterRealKeygenAndSigning adversary chain keyResult)).run
  pure (base, result)

def appendStrategyProbeTrace
    (queries : Nat)
    (result : (ChainValueIndex → Digest) ×
      ((List Bool → ChainValueIndex × Digest) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) :
    (ChainValueIndex → Digest) ×
      ((List Bool → ChainValueIndex × Digest) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :=
  (result.1, (result.2.1,
    result.2.2 ++ strategyProbeTrace queries result.2.1))

theorem simulate_eagerTrace_emitProbes
    (table : ChainValueIndex → Digest)
    (probes : List (ChainValueIndex × Digest)) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (RevealProbeOracleSimulation.emitProbes probes)).run =
      pure ((), probes.map fun probe =>
        RevealProbeOracleSimulation.ObservedAction.probe probe.1 probe.2) := by
  induction probes with
  | nil => simp [RevealProbeOracleSimulation.emitProbes]
  | cons probe probes ih =>
      rw [RevealProbeOracleSimulation.emitProbes, simulateQ_bind,
        WriterT.run_bind']
      simp [RevealProbeOracleSimulation.probeQuery,
        RevealProbeOracleSimulation.eagerTraceImpl,
        RevealProbeOracleSimulation.eagerImpl,
        RevealProbeOracleSimulation.traceFragment,
        QueryImpl.withTraceAppend_apply, WriterT.run_tell]
      change (Prod.map id (fun trace =>
        RevealProbeOracleSimulation.ObservedAction.probe
          probe.1 probe.2 :: trace)) <$>
          (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
            (RevealProbeOracleSimulation.emitProbes probes)).run = _
      rw [ih]
      simp

noncomputable def lazyCompiledStrategyExperimentAfterKeygen
    (queries : Nat) (adversary : Adversary Concrete.cappedScheme)
    (chain : ChainIndex)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec) :
    ProbComp ((ChainValueIndex → Digest) ×
      ((List Bool → ChainValueIndex × Digest) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) := do
  let causalKeyResult := causalKeyResultOfReal keyResult
  let execution ← causalLazyDetailedGameAfterKeygen adversary
    causalKeyResult.1.1 causalKeyResult.1.2 chain
      causalKeyResult.2.finishKeygen
  let base ← $ᵗ (ChainValueIndex → Digest)
  let table := causalInstalledTable execution.1.2 base
  let strategyResult := lazyCausalStrategyResult chain causalKeyResult execution
  pure (table, (strategyResult.1,
    strategyResult.2 ++ strategyProbeTrace queries strategyResult.1))

set_option maxRecDepth 100000 in
theorem evalDist_installed_compileStrategyProbes_afterRealKeygenAndSigning_eq_lazy
    (queries : Nat) (adversary : Adversary Concrete.cappedScheme)
    (chain : ChainIndex)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec) :
    let initial := (causalKeyResultOfReal keyResult).2.finishKeygen
    𝒟[do
      let base ← $ᵗ (ChainValueIndex → Digest)
      let table := causalInstalledTable initial base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        (RevealProbeOracleSimulation.compileStrategyProbes queries
          (causalStrategyAfterRealKeygenAndSigning
            adversary chain keyResult))).run
      pure (table, result)] =
    𝒟[lazyCompiledStrategyExperimentAfterKeygen
      queries adversary chain keyResult] := by
  dsimp only
  unfold RevealProbeOracleSimulation.compileStrategyProbes
  simpa [lazyCompiledStrategyExperimentAfterKeygen, strategyProbeTrace,
    simulate_eagerTrace_emitProbes,
    simulateQ_bind, WriterT.run_bind', map_eq_bind_pure_comp,
    bind_assoc, Function.comp_apply] using
    (evalDist_installed_causalStrategyAfterRealKeygenAndSigning_eq_lazy
      adversary chain keyResult
      (fun table strategyResult => do
        let emitted ← (simulateQ
          (RevealProbeOracleSimulation.eagerTraceImpl table)
          (RevealProbeOracleSimulation.emitProbes
            (RevealProbeOracleSimulation.strategyProbes
              queries strategyResult.1))).run
        pure (table, (strategyResult.1, strategyResult.2 ++ emitted.2))))

noncomputable def causalLazyCompiledStrategyExperiment
    (queries : Nat) (adversary : Adversary Concrete.cappedScheme)
    (chain : ChainIndex) :
    ProbComp ((ChainValueIndex → Digest) ×
      ((List Bool → ChainValueIndex × Digest) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) := do
  let keyResult ← (simulateQ xmssRomImpl Concrete.keygen).run ∅
  lazyCompiledStrategyExperimentAfterKeygen
    queries adversary chain keyResult

theorem causalLazyCompiledStrategyExperiment_eq_map_view
    (queries : Nat) (adversary : Adversary Concrete.cappedScheme)
    (chain : ChainIndex) :
    causalLazyCompiledStrategyExperiment queries adversary chain =
      appendStrategyProbeTrace queries <$>
        causalLazyStrategyViewExperiment adversary chain := by
  unfold causalLazyCompiledStrategyExperiment
    causalLazyStrategyViewExperiment
  rw [map_eq_bind_pure_comp]
  simp only [bind_assoc]
  apply bind_congr
  intro keyResult
  unfold lazyCompiledStrategyExperimentAfterKeygen
    lazyCausalStrategyViewAfterKeygen appendStrategyProbeTrace
  simp [map_eq_bind_pure_comp, bind_assoc]

@[simp]
theorem causalInstalledTable_causalKeyResultOfReal_finishKeygen
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (base : ChainValueIndex → Digest) :
    causalInstalledTable
      (causalKeyResultOfReal keyResult).2.finishKeygen base = base := by
  funext index
  rfl

set_option maxRecDepth 100000 in
theorem evalDist_causalEagerStrategyViewExperiment_eq_lazy
    (adversary : Adversary Concrete.cappedScheme) (chain : ChainIndex) :
    𝒟[causalEagerStrategyViewExperiment adversary chain] =
      𝒟[causalLazyStrategyViewExperiment adversary chain] := by
  unfold causalEagerStrategyViewExperiment causalLazyStrategyViewExperiment
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro keyResult
  simpa [lazyCausalStrategyViewAfterKeygen,
    causalInstalledTable_causalKeyResultOfReal_finishKeygen] using
    (evalDist_installed_causalStrategyAfterRealKeygenAndSigning_eq_lazy
      adversary chain keyResult (fun table result => pure (table, result)))

set_option maxRecDepth 100000 in
theorem evalDist_eagerExperiment_compile_causalStrategyProgram_eq_lazy
    (queries : Nat) (adversary : Adversary Concrete.cappedScheme)
    (chain : ChainIndex) :
    𝒟[RevealProbeOracleSimulation.eagerExperiment
      (RevealProbeOracleSimulation.compileStrategyProbes queries
        (causalStrategyProgram adversary chain))] =
    𝒟[causalLazyCompiledStrategyExperiment
      queries adversary chain] := by
  unfold RevealProbeOracleSimulation.eagerExperiment
    causalLazyCompiledStrategyExperiment
  calc
    _ = 𝒟[do
        let table ← $ᵗ (ChainValueIndex → Digest)
        let keyResult ← (simulateQ xmssRomImpl Concrete.keygen).run ∅
        let result ← (simulateQ
          (RevealProbeOracleSimulation.eagerTraceImpl table)
          (RevealProbeOracleSimulation.compileStrategyProbes queries
            (causalStrategyAfterRealKeygenAndSigning
              adversary chain keyResult))).run
        pure (table, result)] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro table
      rw [simulate_eagerTrace_compileStrategyProbes_causalStrategyProgram_eq_afterRealKeygenAndSigning]
      simp [bind_assoc]
    _ = 𝒟[do
        let keyResult ← (simulateQ xmssRomImpl Concrete.keygen).run ∅
        let table ← $ᵗ (ChainValueIndex → Digest)
        let result ← (simulateQ
          (RevealProbeOracleSimulation.eagerTraceImpl table)
          (RevealProbeOracleSimulation.compileStrategyProbes queries
            (causalStrategyAfterRealKeygenAndSigning
              adversary chain keyResult))).run
        pure (table, result)] := by
      rw [OracleComp.DeferredSampling.evalDist_bind_comm]
    _ = _ := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro keyResult
      simpa using
        (evalDist_installed_compileStrategyProbes_afterRealKeygenAndSigning_eq_lazy
          queries adversary chain keyResult)

end XmssSecurity.CappedChain
