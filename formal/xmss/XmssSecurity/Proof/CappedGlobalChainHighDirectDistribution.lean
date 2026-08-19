import XmssSecurity.Proof.CappedGlobalChainHighDirectReduction

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.tacticAnalysis false
set_option linter.unusedSimpArgs false

abbrev GlobalHighEagerResult :=
  (GlobalChainValueIndex → Digest) ×
    (GlobalHighDirectResult ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)

theorem globalHighMonitoredProgram_projection_eq_parameterFirst
    (adversary : Adversary Concrete.scheme) :
    globalHighMonitoredDirectProjection <$>
      globalHighMonitoredProgram adversary =
    (do
      let parameter ← Concrete.samplePublicParameter
      let base ← independentGlobalChainValueTable
      globalHighDirectContinuation adversary parameter base :
        ProbComp GlobalHighEagerResult) := by
  rw [globalHighMonitoredProgram_eq_directKeygen]
  simp only [map_eq_bind_pure_comp, bind_assoc]
  apply bind_congr
  intro parameter
  apply bind_congr
  intro base
  unfold globalHighDirectContinuation
  exact globalHighMonitored_afterKey_projection adversary parameter base

theorem evalDist_globalHighParameterFirst_eq_baseFirst
    (adversary : Adversary Concrete.scheme) :
    evalDist (do
      let parameter ← Concrete.samplePublicParameter
      let base ← independentGlobalChainValueTable
      globalHighDirectContinuation adversary parameter base :
        ProbComp GlobalHighEagerResult) =
    evalDist (do
      let base ← independentGlobalChainValueTable
      let parameter ← Concrete.samplePublicParameter
      globalHighDirectContinuation adversary parameter base :
        ProbComp GlobalHighEagerResult) := by
  exact OracleComp.DeferredSampling.evalDist_bind_comm
    Concrete.samplePublicParameter independentGlobalChainValueTable _

theorem eagerTrace_liftProbComp_then_bind
    (base : GlobalChainValueIndex → Digest)
    (keygen : ProbComp κ)
    (body : κ → OracleComp
      (RevealProbeOracleSimulation.World GlobalChainValueIndex) α) :
    (do
      let keyResult ← keygen
      let execution ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl base)
        (body keyResult)).run
      pure (base, ((keyResult, execution.1), execution.2))) = (do
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl base) (do
          let keyResult ← RevealProbeOracleSimulation.liftProbComp keygen
          let execution ← body keyResult
          pure (keyResult, execution))).run
      pure (base, result)) := by
  simp only [simulateQ_bind, WriterT.run_bind', bind_assoc]
  rw [RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp]
  simp [simulateQ_pure, WriterT.run_pure, Function.comp_def]

theorem globalHighDirectContinuation_eq_eagerAfterBase
    (adversary : Adversary Concrete.scheme)
    (base : GlobalChainValueIndex → Digest) :
    (do
      let parameter ← Concrete.samplePublicParameter
      globalHighDirectContinuation adversary parameter base :
        ProbComp GlobalHighEagerResult) = (do
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl base)
        (globalHighDirectProgram adversary)).run
      pure (base, result)) := by
  unfold globalHighDirectContinuation globalHighDirectProgram
    globalHighDirectKeygen
  simpa only [bind_assoc] using
    (eagerTrace_liftProbComp_then_bind base
      (do
        let parameter ← Concrete.samplePublicParameter
        globalHighDirectKeygenAfterParameter parameter)
      (fun keyResult =>
        (globalHighDirectDetailedExecution adversary keyResult.1 keyResult.2).run
          (globalFilteredCausalKeygenState keyResult.1)))

noncomputable def globalHighLeftContinuation
    (adversary : Adversary Concrete.scheme)
    (base : GlobalChainValueIndex → Digest) :
    ProbComp GlobalHighEagerResult := do
  let parameter ← Concrete.samplePublicParameter
  globalHighDirectContinuation adversary parameter base

noncomputable def globalHighRightContinuation
    (adversary : Adversary Concrete.scheme)
    (base : GlobalChainValueIndex → Digest) :
    ProbComp GlobalHighEagerResult := do
  let result ← (simulateQ
    (RevealProbeOracleSimulation.eagerTraceImpl base)
    (globalHighDirectProgram adversary)).run
  pure (base, result)

theorem globalHighContinuations_eq
    (adversary : Adversary Concrete.scheme) :
    globalHighLeftContinuation adversary =
      globalHighRightContinuation adversary := by
  funext base
  unfold globalHighLeftContinuation globalHighRightContinuation
  exact globalHighDirectContinuation_eq_eagerAfterBase adversary base

noncomputable def globalHighBaseFirstProgram
    (adversary : Adversary Concrete.scheme) :
    ProbComp GlobalHighEagerResult :=
  independentGlobalChainValueTable >>= globalHighLeftContinuation adversary

noncomputable def globalHighDirectEagerExperiment
    (adversary : Adversary Concrete.scheme) :
    ProbComp GlobalHighEagerResult :=
  RevealProbeOracleSimulation.eagerExperiment
    (globalHighDirectProgram adversary)

theorem globalHighBaseFirstExperiment_eq_eagerExperiment
    (adversary : Adversary Concrete.scheme) :
    evalDist (globalHighBaseFirstProgram adversary) =
      evalDist (globalHighDirectEagerExperiment adversary) := by
  unfold globalHighBaseFirstProgram globalHighDirectEagerExperiment
    RevealProbeOracleSimulation.eagerExperiment
  rw [globalHighContinuations_eq adversary]
  rw [evalDist_bind, evalDist_bind]
  unfold independentGlobalChainValueTable
    RevealProbeOracleSimulation.eagerTableSample
  rw [evalDist_uniformSample, evalDist_uniformSample]
  unfold globalHighRightContinuation
  rfl

theorem evalDist_globalHighMonitoredDirectProjection_eq_eagerExperiment
    (adversary : Adversary Concrete.scheme) :
    evalDist (globalHighMonitoredDirectProjection <$>
      globalHighMonitoredProgram adversary) =
    evalDist (globalHighDirectEagerExperiment adversary) := by
  calc
    _ = evalDist (do
        let parameter ← Concrete.samplePublicParameter
        let base ← independentGlobalChainValueTable
        globalHighDirectContinuation adversary parameter base :
          ProbComp GlobalHighEagerResult) := by
      rw [globalHighMonitoredProgram_projection_eq_parameterFirst]
    _ = evalDist (globalHighBaseFirstProgram adversary) := by
      unfold globalHighBaseFirstProgram
      exact evalDist_globalHighParameterFirst_eq_baseFirst adversary
    _ = _ := globalHighBaseFirstExperiment_eq_eagerExperiment adversary

end XmssSecurity.CappedChain
