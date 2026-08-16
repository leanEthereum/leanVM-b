import XmssSecurity.CappedGlobalCausalInstalledDetailedGame

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

noncomputable local instance globalCausalInstalledStrategySampleableChainTable :
    SampleableType (GlobalChainValueIndex → Digest) :=
  SampleableType.ofFintype (GlobalChainValueIndex → Digest)

noncomputable def lazyGlobalCausalStrategyResult
    (keyResult : (PublicKey × SecretKey) × GlobalCausalHashState)
    (execution : ((((Forgery × Bool) × AttackerActionTrace) ×
      GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) :
    ((List Bool → GlobalChainValueIndex × Digest) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :=
  ((globalActionTracedRevealProbeView
    (globalCausalDetailedResult keyResult execution.1)).strategy, execution.2)

set_option maxRecDepth 100000 in
theorem evalDist_installed_globalCausalStrategyAfterRealKeygenAndSigning_eq_lazy
    (adversary : Adversary Concrete.cappedScheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (continuation : (GlobalChainValueIndex → Digest) →
      ((List Bool → GlobalChainValueIndex × Digest) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) → ProbComp α) :
    let causalKeyResult := globalCausalKeyResultOfReal keyResult
    let initial := causalKeyResult.2.finishKeygen
    𝒟[do
      let base ← $ᵗ (GlobalChainValueIndex → Digest)
      let table := globalCausalInstalledTable initial base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalCausalStrategyAfterRealKeygenAndSigning
          adversary keyResult)).run
      continuation table result] =
    𝒟[do
      let execution ← globalCausalLazyDetailedGameAfterKeygen adversary
        causalKeyResult.1.1 causalKeyResult.1.2 initial
      let base ← $ᵗ (GlobalChainValueIndex → Digest)
      let table := globalCausalInstalledTable execution.1.2 base
      continuation table (lazyGlobalCausalStrategyResult
        causalKeyResult execution)] := by
  dsimp only
  simpa [globalCausalStrategyAfterRealKeygenAndSigning,
    globalCausalKeyResultOfReal, lazyGlobalCausalStrategyResult,
    simulateQ_bind, WriterT.run_bind', map_eq_bind_pure_comp,
    bind_assoc, Function.comp_apply] using
    (evalDist_installed_globalCausalDetailedGameAfterKeygenAfterRealRom_eq_lazy
      adversary keyResult.1.1 keyResult.1.2
        (globalCausalKeyResultOfReal keyResult).2.finishKeygen
        (fun table execution => continuation table
          (lazyGlobalCausalStrategyResult
            (globalCausalKeyResultOfReal keyResult) execution)))

def globalStrategyProbeTrace
    (queries : Nat)
    (strategy : List Bool → GlobalChainValueIndex × Digest) :
    RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex :=
  (RevealProbeOracleSimulation.strategyProbes queries strategy).map fun probe =>
    RevealProbeOracleSimulation.ObservedAction.probe probe.1 probe.2

noncomputable def lazyGlobalCausalStrategyViewAfterKeygen
    (adversary : Adversary Concrete.cappedScheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec) :
    ProbComp ((GlobalChainValueIndex → Digest) ×
      ((List Bool → GlobalChainValueIndex × Digest) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) := do
  let causalKeyResult := globalCausalKeyResultOfReal keyResult
  let execution ← globalCausalLazyDetailedGameAfterKeygen adversary
    causalKeyResult.1.1 causalKeyResult.1.2
      causalKeyResult.2.finishKeygen
  let base ← $ᵗ (GlobalChainValueIndex → Digest)
  let table := globalCausalInstalledTable execution.1.2 base
  pure (table, lazyGlobalCausalStrategyResult causalKeyResult execution)

noncomputable def globalCausalLazyStrategyViewExperiment
    (adversary : Adversary Concrete.cappedScheme) :
    ProbComp ((GlobalChainValueIndex → Digest) ×
      ((List Bool → GlobalChainValueIndex × Digest) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) := do
  let keyResult ← (simulateQ xmssRomImpl Concrete.keygen).run ∅
  lazyGlobalCausalStrategyViewAfterKeygen adversary keyResult

noncomputable def globalCausalEagerStrategyViewExperiment
    (adversary : Adversary Concrete.cappedScheme) :
    ProbComp ((GlobalChainValueIndex → Digest) ×
      ((List Bool → GlobalChainValueIndex × Digest) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) := do
  let keyResult ← (simulateQ xmssRomImpl Concrete.keygen).run ∅
  let base ← $ᵗ (GlobalChainValueIndex → Digest)
  let result ← (simulateQ
    (RevealProbeOracleSimulation.eagerTraceImpl base)
    (globalCausalStrategyAfterRealKeygenAndSigning adversary keyResult)).run
  pure (base, result)

def appendGlobalStrategyProbeTrace
    (queries : Nat)
    (result : (GlobalChainValueIndex → Digest) ×
      ((List Bool → GlobalChainValueIndex × Digest) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) :
    (GlobalChainValueIndex → Digest) ×
      ((List Bool → GlobalChainValueIndex × Digest) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :=
  (result.1, (result.2.1,
    result.2.2 ++ globalStrategyProbeTrace queries result.2.1))

theorem simulate_eagerTrace_emitGlobalProbes
    (table : GlobalChainValueIndex → Digest)
    (probes : List (GlobalChainValueIndex × Digest)) :
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

noncomputable def lazyGlobalCompiledStrategyExperimentAfterKeygen
    (queries : Nat) (adversary : Adversary Concrete.cappedScheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec) :
    ProbComp ((GlobalChainValueIndex → Digest) ×
      ((List Bool → GlobalChainValueIndex × Digest) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) := do
  let causalKeyResult := globalCausalKeyResultOfReal keyResult
  let execution ← globalCausalLazyDetailedGameAfterKeygen adversary
    causalKeyResult.1.1 causalKeyResult.1.2
      causalKeyResult.2.finishKeygen
  let base ← $ᵗ (GlobalChainValueIndex → Digest)
  let table := globalCausalInstalledTable execution.1.2 base
  let strategyResult := lazyGlobalCausalStrategyResult causalKeyResult execution
  pure (table, (strategyResult.1,
    strategyResult.2 ++ globalStrategyProbeTrace queries strategyResult.1))

set_option maxRecDepth 100000 in
theorem evalDist_installed_compileGlobalStrategyProbes_afterRealKeygenAndSigning_eq_lazy
    (queries : Nat) (adversary : Adversary Concrete.cappedScheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec) :
    let initial := (globalCausalKeyResultOfReal keyResult).2.finishKeygen
    𝒟[do
      let base ← $ᵗ (GlobalChainValueIndex → Digest)
      let table := globalCausalInstalledTable initial base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        (RevealProbeOracleSimulation.compileStrategyProbes queries
          (globalCausalStrategyAfterRealKeygenAndSigning
            adversary keyResult))).run
      pure (table, result)] =
    𝒟[lazyGlobalCompiledStrategyExperimentAfterKeygen
      queries adversary keyResult] := by
  dsimp only
  unfold RevealProbeOracleSimulation.compileStrategyProbes
  simpa [lazyGlobalCompiledStrategyExperimentAfterKeygen,
    globalStrategyProbeTrace, simulate_eagerTrace_emitGlobalProbes,
    simulateQ_bind, WriterT.run_bind', map_eq_bind_pure_comp,
    bind_assoc, Function.comp_apply] using
    (evalDist_installed_globalCausalStrategyAfterRealKeygenAndSigning_eq_lazy
      adversary keyResult
      (fun table strategyResult => do
        let emitted ← (simulateQ
          (RevealProbeOracleSimulation.eagerTraceImpl table)
          (RevealProbeOracleSimulation.emitProbes
            (RevealProbeOracleSimulation.strategyProbes
              queries strategyResult.1))).run
        pure (table, (strategyResult.1, strategyResult.2 ++ emitted.2))))

noncomputable def globalCausalLazyCompiledStrategyExperiment
    (queries : Nat) (adversary : Adversary Concrete.cappedScheme) :
    ProbComp ((GlobalChainValueIndex → Digest) ×
      ((List Bool → GlobalChainValueIndex × Digest) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) := do
  let keyResult ← (simulateQ xmssRomImpl Concrete.keygen).run ∅
  lazyGlobalCompiledStrategyExperimentAfterKeygen
    queries adversary keyResult

theorem globalCausalLazyCompiledStrategyExperiment_eq_map_view
    (queries : Nat) (adversary : Adversary Concrete.cappedScheme) :
    globalCausalLazyCompiledStrategyExperiment queries adversary =
      appendGlobalStrategyProbeTrace queries <$>
        globalCausalLazyStrategyViewExperiment adversary := by
  unfold globalCausalLazyCompiledStrategyExperiment
    globalCausalLazyStrategyViewExperiment
  rw [map_eq_bind_pure_comp]
  simp only [bind_assoc]
  apply bind_congr
  intro keyResult
  unfold lazyGlobalCompiledStrategyExperimentAfterKeygen
    lazyGlobalCausalStrategyViewAfterKeygen appendGlobalStrategyProbeTrace
  simp [map_eq_bind_pure_comp, bind_assoc]

@[simp]
theorem globalCausalInstalledTable_globalCausalKeyResultOfReal_finishKeygen
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (base : GlobalChainValueIndex → Digest) :
    globalCausalInstalledTable
      (globalCausalKeyResultOfReal keyResult).2.finishKeygen base = base := by
  funext index
  rfl

set_option maxRecDepth 100000 in
theorem evalDist_globalCausalEagerStrategyViewExperiment_eq_lazy
    (adversary : Adversary Concrete.cappedScheme) :
    𝒟[globalCausalEagerStrategyViewExperiment adversary] =
      𝒟[globalCausalLazyStrategyViewExperiment adversary] := by
  unfold globalCausalEagerStrategyViewExperiment
    globalCausalLazyStrategyViewExperiment
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro keyResult
  simpa [lazyGlobalCausalStrategyViewAfterKeygen,
    globalCausalInstalledTable_globalCausalKeyResultOfReal_finishKeygen] using
    (evalDist_installed_globalCausalStrategyAfterRealKeygenAndSigning_eq_lazy
      adversary keyResult (fun table result => pure (table, result)))

set_option maxRecDepth 100000 in
theorem evalDist_eagerExperiment_compile_globalCausalStrategyProgram_eq_lazy
    (queries : Nat) (adversary : Adversary Concrete.cappedScheme) :
    𝒟[RevealProbeOracleSimulation.eagerExperiment
      (RevealProbeOracleSimulation.compileStrategyProbes queries
        (globalCausalStrategyProgram adversary))] =
    𝒟[globalCausalLazyCompiledStrategyExperiment queries adversary] := by
  unfold RevealProbeOracleSimulation.eagerExperiment
    globalCausalLazyCompiledStrategyExperiment
  calc
    _ = 𝒟[do
        let table ← $ᵗ (GlobalChainValueIndex → Digest)
        let keyResult ← (simulateQ xmssRomImpl Concrete.keygen).run ∅
        let result ← (simulateQ
          (RevealProbeOracleSimulation.eagerTraceImpl table)
          (RevealProbeOracleSimulation.compileStrategyProbes queries
            (globalCausalStrategyAfterRealKeygenAndSigning
              adversary keyResult))).run
        pure (table, result)] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro table
      rw [simulate_eagerTrace_compileStrategyProbes_globalCausalStrategyProgram_eq_afterRealKeygen]
      simp only [bind_assoc]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro keyResult
      rw [simulate_eagerTrace_compileStrategyProbes_globalAfterRealKeygen_eq_afterRealSigning]
    _ = 𝒟[do
        let keyResult ← (simulateQ xmssRomImpl Concrete.keygen).run ∅
        let table ← $ᵗ (GlobalChainValueIndex → Digest)
        let result ← (simulateQ
          (RevealProbeOracleSimulation.eagerTraceImpl table)
          (RevealProbeOracleSimulation.compileStrategyProbes queries
            (globalCausalStrategyAfterRealKeygenAndSigning
              adversary keyResult))).run
        pure (table, result)] := by
      rw [OracleComp.DeferredSampling.evalDist_bind_comm]
    _ = _ := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro keyResult
      simpa using
        (evalDist_installed_compileGlobalStrategyProbes_afterRealKeygenAndSigning_eq_lazy
          queries adversary keyResult)

end XmssSecurity.CappedChain
