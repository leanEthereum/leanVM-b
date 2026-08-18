import XmssSecurity.CappedGlobalCausalInstalledDetailedGame

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

noncomputable local instance globalCausalInstalledStrategySampleableTable :
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
    (globalCausalDetailedResult keyResult execution.1)).strategy,
      execution.2)

set_option maxRecDepth 200000 in
theorem evalDist_installed_globalCausalStrategyAfterRealKeygenAndSigning_eq_lazy
    (adversary : Adversary Concrete.scheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (continuation : (GlobalChainValueIndex → Digest) →
      ((List Bool → GlobalChainValueIndex × Digest) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) →
          ProbComp α) :
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
      continuation table
        (lazyGlobalCausalStrategyResult causalKeyResult execution)] := by
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

noncomputable def lazyGlobalCausalStrategyViewAfterKeygen
    (adversary : Adversary Concrete.scheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec) :
    ProbComp ((GlobalChainValueIndex → Digest) ×
      ((List Bool → GlobalChainValueIndex × Digest) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) := do
  let causalKeyResult := globalCausalKeyResultOfReal keyResult
  let execution ← globalCausalLazyDetailedGameAfterKeygen adversary
    causalKeyResult.1.1 causalKeyResult.1.2 causalKeyResult.2.finishKeygen
  let base ← $ᵗ (GlobalChainValueIndex → Digest)
  let table := globalCausalInstalledTable execution.1.2 base
  pure (table, lazyGlobalCausalStrategyResult causalKeyResult execution)

noncomputable def globalCausalLazyStrategyViewExperiment
    (adversary : Adversary Concrete.scheme) :
    ProbComp ((GlobalChainValueIndex → Digest) ×
      ((List Bool → GlobalChainValueIndex × Digest) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) := do
  let keyResult ← (simulateQ xmssRomImpl Concrete.keygen).run ∅
  lazyGlobalCausalStrategyViewAfterKeygen adversary keyResult

noncomputable def globalCausalEagerStrategyViewExperiment
    (adversary : Adversary Concrete.scheme) :
    ProbComp ((GlobalChainValueIndex → Digest) ×
      ((List Bool → GlobalChainValueIndex × Digest) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) := do
  let keyResult ← (simulateQ xmssRomImpl Concrete.keygen).run ∅
  let base ← $ᵗ (GlobalChainValueIndex → Digest)
  let result ← (simulateQ
    (RevealProbeOracleSimulation.eagerTraceImpl base)
    (globalCausalStrategyAfterRealKeygenAndSigning adversary keyResult)).run
  pure (base, result)

@[simp]
theorem globalCausalInstalledTable_globalCausalKeyResultOfReal_finishKeygen
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (base : GlobalChainValueIndex → Digest) :
    globalCausalInstalledTable
      (globalCausalKeyResultOfReal keyResult).2.finishKeygen base = base := by
  funext index
  rfl

set_option maxRecDepth 200000 in
theorem evalDist_globalCausalEagerStrategyViewExperiment_eq_lazy
    (adversary : Adversary Concrete.scheme) :
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

end XmssSecurity.CappedChain
