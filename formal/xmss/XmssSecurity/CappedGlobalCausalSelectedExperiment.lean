import XmssSecurity.CappedGlobalCausalSelectedProbes

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

noncomputable local instance globalCausalSelectedSampleableTable :
    SampleableType (GlobalChainValueIndex → Digest) :=
  SampleableType.ofFintype (GlobalChainValueIndex → Digest)

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

noncomputable def globalCausalSelectedAfterRealKeygenProgram
    (adversary : Adversary Concrete.scheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      DetailedActionTracedResult := do
  let causalKeyResult := globalCausalKeyResultOfReal keyResult
  let execution ← (globalCausalDetailedGameAfterKeygenAfterRealRom adversary
    causalKeyResult.1.1 causalKeyResult.1.2).run
      causalKeyResult.2.finishKeygen
  let detailed := globalCausalDetailedResult causalKeyResult execution
  let _ ← RevealProbeOracleSimulation.emitProbes
    (globalSelectedUnrevealedProbes detailed)
  pure detailed

noncomputable def globalCausalSelectedContinuation
    (keyResult : (PublicKey × SecretKey) × GlobalCausalHashState)
    (table : GlobalChainValueIndex → Digest)
    (execution : ((((Forgery × Bool) × AttackerActionTrace) ×
      GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) :
    ProbComp (DetailedActionTracedResult ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) := do
  let detailed := globalCausalDetailedResult keyResult execution.1
  let emitted ← (simulateQ
    (RevealProbeOracleSimulation.eagerTraceImpl table)
    (RevealProbeOracleSimulation.emitProbes
      (globalSelectedUnrevealedProbes detailed))).run
  pure (detailed, execution.2 ++ emitted.2)

set_option maxRecDepth 200000 in
theorem simulate_eagerTrace_globalCausalSelectedAfterRealKeygenProgram
    (adversary : Adversary Concrete.scheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (table : GlobalChainValueIndex → Digest) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (globalCausalSelectedAfterRealKeygenProgram adversary keyResult)).run = (do
      let causalKeyResult := globalCausalKeyResultOfReal keyResult
      let execution ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalDetailedGameAfterKeygenAfterRealRom adversary
          causalKeyResult.1.1 causalKeyResult.1.2).run
            causalKeyResult.2.finishKeygen)).run
      globalCausalSelectedContinuation causalKeyResult table execution) := by
  simp [globalCausalSelectedAfterRealKeygenProgram, simulateQ_bind,
    globalCausalSelectedContinuation, map_eq_bind_pure_comp, bind_assoc,
    Function.comp_apply]

noncomputable def globalCausalSelectedEagerAfterKeygenExperiment
    (adversary : Adversary Concrete.scheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec) :
    ProbComp ((GlobalChainValueIndex → Digest) ×
      (DetailedActionTracedResult ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) :=
  RevealProbeOracleSimulation.eagerExperiment
    (globalCausalSelectedAfterRealKeygenProgram adversary keyResult)

noncomputable def globalCausalSelectedLazyAfterKeygenExperiment
    (adversary : Adversary Concrete.scheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec) :
    ProbComp ((GlobalChainValueIndex → Digest) ×
      (DetailedActionTracedResult ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) := do
  let causalKeyResult := globalCausalKeyResultOfReal keyResult
  let initial := causalKeyResult.2.finishKeygen
  let execution ← globalCausalLazyDetailedGameAfterKeygen adversary
    causalKeyResult.1.1 causalKeyResult.1.2 initial
  let base ← $ᵗ (GlobalChainValueIndex → Digest)
  let table := globalCausalInstalledTable execution.1.2 base
  let selected ← globalCausalSelectedContinuation
    causalKeyResult table execution
  pure (table, selected)

@[simp]
theorem globalCausalInstalledTable_realKeyResult_finishKeygen
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (base : GlobalChainValueIndex → Digest) :
    globalCausalInstalledTable
      (globalCausalKeyResultOfReal keyResult).2.finishKeygen base = base := by
  funext index
  rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem evalDist_globalCausalSelectedEagerAfterKeygen_eq_lazy
    (adversary : Adversary Concrete.scheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec) :
    𝒟[globalCausalSelectedEagerAfterKeygenExperiment adversary keyResult] =
      𝒟[globalCausalSelectedLazyAfterKeygenExperiment adversary keyResult] := by
  let causalKeyResult := globalCausalKeyResultOfReal keyResult
  let initial := causalKeyResult.2.finishKeygen
  have hinstalled :=
    evalDist_installed_globalCausalDetailedGameAfterKeygenAfterRealRom_eq_lazy
      adversary causalKeyResult.1.1 causalKeyResult.1.2 initial
        (fun table execution => do
          let selected ← globalCausalSelectedContinuation
            causalKeyResult table execution
          pure (table, selected))
  calc
    _ = 𝒟[do
        let base ← $ᵗ (GlobalChainValueIndex → Digest)
        let table := globalCausalInstalledTable initial base
        let execution ← (simulateQ
          (RevealProbeOracleSimulation.eagerTraceImpl table)
          ((globalCausalDetailedGameAfterKeygenAfterRealRom adversary
            causalKeyResult.1.1 causalKeyResult.1.2).run initial)).run
        let selected ← globalCausalSelectedContinuation
          causalKeyResult table execution
        pure (table, selected)] := by
      simp [globalCausalSelectedEagerAfterKeygenExperiment,
        RevealProbeOracleSimulation.eagerExperiment,
        RevealProbeOracleSimulation.eagerTableSample,
        simulate_eagerTrace_globalCausalSelectedAfterRealKeygenProgram,
        causalKeyResult, initial,
        globalCausalInstalledTable_realKeyResult_finishKeygen]
    _ = _ := by
      simpa [globalCausalSelectedLazyAfterKeygenExperiment,
        causalKeyResult, initial, bind_assoc] using hinstalled

noncomputable def globalCausalSelectedEagerExperiment
    (adversary : Adversary Concrete.scheme) :
    ProbComp ((GlobalChainValueIndex → Digest) ×
      (DetailedActionTracedResult ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) := do
  let keyResult ← (simulateQ xmssRomImpl Concrete.keygen).run ∅
  globalCausalSelectedEagerAfterKeygenExperiment adversary keyResult

noncomputable def globalCausalSelectedLazyExperiment
    (adversary : Adversary Concrete.scheme) :
    ProbComp ((GlobalChainValueIndex → Digest) ×
      (DetailedActionTracedResult ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) := do
  let keyResult ← (simulateQ xmssRomImpl Concrete.keygen).run ∅
  globalCausalSelectedLazyAfterKeygenExperiment adversary keyResult

theorem evalDist_globalCausalSelectedEagerExperiment_eq_lazy
    (adversary : Adversary Concrete.scheme) :
    𝒟[globalCausalSelectedEagerExperiment adversary] =
      𝒟[globalCausalSelectedLazyExperiment adversary] := by
  unfold globalCausalSelectedEagerExperiment
    globalCausalSelectedLazyExperiment
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro keyResult
  exact evalDist_globalCausalSelectedEagerAfterKeygen_eq_lazy adversary keyResult

end XmssSecurity.CappedChain
