import XmssSecurity.CappedGlobalChainHighDirectReduction

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

abbrev GlobalHighEagerResult :=
  (GlobalChainValueIndex → Digest) ×
    (GlobalHighDirectResult ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)

theorem globalHighMonitoredProgram_projection_eq_parameterFirst
    (adversary : Adversary Concrete.cappedScheme) :
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
    (adversary : Adversary Concrete.cappedScheme) :
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

theorem globalHighDirectContinuation_eq_eagerAfterBase
    (adversary : Adversary Concrete.cappedScheme)
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
  simp only [simulateQ_bind, WriterT.run_bind', bind_assoc]
  rw [RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, List.nil_append]

theorem globalHighBaseFirstExperiment_eq_eagerExperiment
    (adversary : Adversary Concrete.cappedScheme) :
    evalDist (do
      let base ← independentGlobalChainValueTable
      let parameter ← Concrete.samplePublicParameter
      globalHighDirectContinuation adversary parameter base :
        ProbComp GlobalHighEagerResult) =
    evalDist (RevealProbeOracleSimulation.eagerExperiment
      (globalHighDirectProgram adversary)) := by
  let left := fun base : GlobalChainValueIndex → Digest => do
    let parameter ← Concrete.samplePublicParameter
    globalHighDirectContinuation adversary parameter base
  let right := fun base : GlobalChainValueIndex → Digest => do
    let result ← (simulateQ
      (RevealProbeOracleSimulation.eagerTraceImpl base)
      (globalHighDirectProgram adversary)).run
    pure (base, result)
  change evalDist (independentGlobalChainValueTable >>= left) =
    evalDist (RevealProbeOracleSimulation.eagerTableSample >>= right)
  unfold RevealProbeOracleSimulation.eagerTableSample
    independentGlobalChainValueTable
  apply congrArg evalDist
  apply congrArg
    (fun continuation : (GlobalChainValueIndex → Digest) →
        ProbComp GlobalHighEagerResult =>
      ($ᵗ (GlobalChainValueIndex → Digest)) >>= continuation)
  funext base
  unfold left right
  exact globalHighDirectContinuation_eq_eagerAfterBase adversary base

theorem evalDist_globalHighMonitoredDirectProjection_eq_eagerExperiment
    (adversary : Adversary Concrete.cappedScheme) :
    evalDist (globalHighMonitoredDirectProjection <$>
      globalHighMonitoredProgram adversary) =
    evalDist (RevealProbeOracleSimulation.eagerExperiment
      (globalHighDirectProgram adversary)) := by
  calc
    _ = evalDist (do
        let parameter ← Concrete.samplePublicParameter
        let base ← independentGlobalChainValueTable
        globalHighDirectContinuation adversary parameter base :
          ProbComp GlobalHighEagerResult) := by
      rw [globalHighMonitoredProgram_projection_eq_parameterFirst]
    _ = evalDist (do
        let base ← independentGlobalChainValueTable
        let parameter ← Concrete.samplePublicParameter
        globalHighDirectContinuation adversary parameter base :
          ProbComp GlobalHighEagerResult) :=
      evalDist_globalHighParameterFirst_eq_baseFirst adversary
    _ = _ := globalHighBaseFirstExperiment_eq_eagerExperiment adversary

end XmssSecurity.CappedChain
