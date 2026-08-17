import XmssSecurity.CappedGlobalCausalKeygenProjection

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

def globalCausalKeyResultOfReal
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec) :
    (PublicKey × SecretKey) × GlobalCausalHashState :=
  (keyResult.1,
    { GlobalCausalHashState.empty with cache := keyResult.2 })

def globalCausalRealKeyResultOfView
    (keyView : ProgrammedGlobalChainKeygenView) :
    (PublicKey × SecretKey) × QueryCache HashSpec :=
  ((keyView.publicKey, keyView.secretKey), keyView.cache)

theorem evalDist_realGlobalKeygen_eq_trajectoryProgrammedKeyResults :
    evalDist ((simulateQ xmssRomImpl Concrete.keygen).run ∅) =
      evalDist (globalCausalRealKeyResultOfView <$>
        trajectoryProgrammedGlobalChainKeygen) := by
  calc
    _ = evalDist (globalCausalRealKeyResultOfView <$>
          actualGlobalChainKeygen) := by
      unfold actualGlobalChainKeygen globalCausalRealKeyResultOfView
      simp [map_eq_bind_pure_comp, bind_assoc]
    _ = evalDist (globalCausalRealKeyResultOfView <$>
          trajectoryProgrammedGlobalChainKeygen) :=
      evalDist_map_eq_of_evalDist_eq
        evalDist_actualGlobalChainKeygen_eq_trajectoryProgrammed
        globalCausalRealKeyResultOfView

noncomputable def globalCausalStrategyAfterRealKeygen
    (adversary : Adversary Concrete.scheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (List Bool → GlobalChainValueIndex × Digest) := do
  let causalKeyResult := globalCausalKeyResultOfReal keyResult
  let execution ← (globalCausalDetailedGameAfterKeygen adversary
    causalKeyResult.1.1 causalKeyResult.1.2).run
      causalKeyResult.2.finishKeygen
  pure (globalActionTracedRevealProbeView
    (globalCausalDetailedResult causalKeyResult execution)).strategy

theorem simulate_eagerTrace_globalCausalStrategyProgram_eq_afterRealKeygen
    (table : GlobalChainValueIndex → Digest)
    (adversary : Adversary Concrete.scheme) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalCausalStrategyProgram adversary)).run =
      ((simulateQ xmssRomImpl Concrete.keygen).run ∅ >>= fun keyResult =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          (globalCausalStrategyAfterRealKeygen adversary keyResult)).run) := by
  unfold globalCausalStrategyProgram
  rw [simulateQ_bind, WriterT.run_bind',
    simulate_eagerTrace_globalCausalKeygen_reconstruct]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply, List.nil_append]
  apply bind_congr
  intro keyResult
  simp [globalCausalStrategyAfterRealKeygen, globalCausalKeyResultOfReal]

theorem simulate_eagerTrace_compileStrategyProbes_globalCausalStrategyProgram_eq_afterRealKeygen
    (table : GlobalChainValueIndex → Digest) (queries : Nat)
    (adversary : Adversary Concrete.scheme) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (RevealProbeOracleSimulation.compileStrategyProbes queries
          (globalCausalStrategyProgram adversary))).run =
      ((simulateQ xmssRomImpl Concrete.keygen).run ∅ >>= fun keyResult =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          (RevealProbeOracleSimulation.compileStrategyProbes queries
            (globalCausalStrategyAfterRealKeygen adversary keyResult))).run) := by
  unfold RevealProbeOracleSimulation.compileStrategyProbes
  rw [simulateQ_bind, WriterT.run_bind',
    simulate_eagerTrace_globalCausalStrategyProgram_eq_afterRealKeygen]
  simp only [bind_assoc]
  apply bind_congr
  intro keyResult
  rw [simulateQ_bind, WriterT.run_bind']

noncomputable def globalCausalCompiledAfterRealKeygenExperiment
    (queries : Nat) (adversary : Adversary Concrete.scheme) :
    ProbComp ((GlobalChainValueIndex → Digest) ×
      ((List Bool → GlobalChainValueIndex × Digest) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) := do
  let table ← RevealProbeOracleSimulation.eagerTableSample
  let keyResult ← (simulateQ xmssRomImpl Concrete.keygen).run ∅
  let result ← (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
    (RevealProbeOracleSimulation.compileStrategyProbes queries
      (globalCausalStrategyAfterRealKeygen adversary keyResult))).run
  pure (table, result)

theorem evalDist_eagerExperiment_globalCausalStrategyProgram_eq_afterRealKeygen
    (queries : Nat) (adversary : Adversary Concrete.scheme) :
    evalDist (RevealProbeOracleSimulation.eagerExperiment
      (RevealProbeOracleSimulation.compileStrategyProbes queries
        (globalCausalStrategyProgram adversary))) =
    evalDist (globalCausalCompiledAfterRealKeygenExperiment queries
      adversary) := by
  unfold RevealProbeOracleSimulation.eagerExperiment
    globalCausalCompiledAfterRealKeygenExperiment
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro table
  rw [simulate_eagerTrace_compileStrategyProbes_globalCausalStrategyProgram_eq_afterRealKeygen]
  simp only [bind_assoc]

noncomputable def globalCausalCompiledAfterProgrammedKeygenExperiment
    (queries : Nat) (adversary : Adversary Concrete.scheme) :
    ProbComp ((GlobalChainValueIndex → Digest) ×
      ((List Bool → GlobalChainValueIndex × Digest) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) := do
  let table ← RevealProbeOracleSimulation.eagerTableSample
  let keyView ← trajectoryProgrammedGlobalChainKeygen
  let keyResult := globalCausalRealKeyResultOfView keyView
  let result ← (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
    (RevealProbeOracleSimulation.compileStrategyProbes queries
      (globalCausalStrategyAfterRealKeygen adversary keyResult))).run
  pure (table, result)

theorem evalDist_globalCausalCompiledAfterRealKeygen_eq_programmed
    (queries : Nat) (adversary : Adversary Concrete.scheme) :
    evalDist (globalCausalCompiledAfterRealKeygenExperiment queries
      adversary) =
    evalDist (globalCausalCompiledAfterProgrammedKeygenExperiment queries
      adversary) := by
  unfold globalCausalCompiledAfterRealKeygenExperiment
    globalCausalCompiledAfterProgrammedKeygenExperiment
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro table
  conv_lhs => rw [evalDist_bind]
  conv_rhs => rw [evalDist_bind]
  rw [evalDist_realGlobalKeygen_eq_trajectoryProgrammedKeyResults]
  simp [map_eq_bind_pure_comp, bind_assoc]

end XmssSecurity.CappedChain
