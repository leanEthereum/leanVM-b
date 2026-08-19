import XmssSecurity.CappedExactFirstLaneBoundedCoupling

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000

abbrev GlobalFirstLaneExactCoupledProgramResult :=
  (((ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) ×
    (((Forgery × Bool) × GlobalFirstLaneExactTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex))

noncomputable def globalFirstLaneExactCoupledProgram
    (adversary : Adversary Concrete.scheme) :
    ProbComp GlobalFirstLaneExactCoupledProgramResult := do
  let right ← coupledGlobalChainKeygenWithBaseHighFull
  let execution ← (simulateQ
    (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
    ((globalFirstLaneExactTracedDetailedExecution adversary right.1.1
      right.2).run (GlobalExactTracedState.mk
        (globalFilteredCausalKeygenState right.1.1) [] []))).run
  pure (right, execution)

def SourceFirstLaneExactBoundedProgramRelation
    (countLimit hitLimit : Nat)
    (left : SourceGlobalExactTracedProgramResult)
    (right : GlobalFirstLaneExactCoupledProgramResult) : Prop :=
  ProgrammedGlobalChainKeygenBaseHighStableRelation left.1 right.1 ∧
    ((left.2.1 = right.2.1.1 ∧
      SourceFirstLaneExactGoodStateRelation left.1 right.1.1 left.2.2
        right.2.1.2 right.2.2 ∧
      FirstLaneOracleSimulation.hazardCount right.2.2 ≤ countLimit) ∨
    FirstLaneOracleSimulation.CombinedHit right.1.1.2
      (FirstLaneOracleSimulation.enforceHazardTrace hitLimit right.2.2))

theorem relTriple_sourceGlobalExact_firstLane_program_boundedHit_sub_keygen
    (q hitLimit : Nat)
    (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (hlimits : q - treeHashQueryCount treeHeight ≤ hitLimit) :
    RelTriple (sourceGlobalExactTracedProgram adversary)
      (globalFirstLaneExactCoupledProgram adversary)
      (SourceFirstLaneExactBoundedProgramRelation
        (q - treeHashQueryCount treeHeight) hitLimit) := by
  unfold sourceGlobalExactTracedProgram globalFirstLaneExactCoupledProgram
  apply relTriple_bind
    (relTriple_with_support
      relTriple_trajectoryProgrammedGlobalChainKeygen_withBaseHigh_stable)
  intro left right hkeygen
  obtain ⟨hrel, hleftSupport, hrightSupport⟩ := hkeygen
  have hrightViewSupport :=
    coupledGlobalChainKeygenWithBaseHighFull_support_keyView right
      hrightSupport
  have hleftKeyResult :=
    trajectoryProgrammedGlobalChainKeygen_support_keyResult left hleftSupport
  have hmaterializedKeyResult :
      Concrete.materializeCachedKeyResult left.keyResult ∈ support
        ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅) := by
    exact Concrete.oldKeygen_support_materializedPrecomputedKeygen
      left.keyResult hleftKeyResult
  have hsourceBound :=
    sourceUnloggedDetailedGameAfterKeygen_hashQueryBound_sub_keygen
      q adversary hbound (Concrete.materializeCachedKeyResult left.keyResult)
        hmaterializedKeyResult
  apply relTriple_bind
    (relTriple_sourceExact_firstLane_detailedExecution_boundedHit
      (q - treeHashQueryCount treeHeight) hitLimit adversary left right hrel
        hleftSupport hrightViewSupport hsourceBound hlimits)
  intro leftExecution rightExecution hexecution
  apply relTriple_pure_pure
  exact ⟨hrel, hexecution⟩

def globalFirstLaneExactCoupledProjection
    (result : GlobalFirstLaneExactCoupledProgramResult) :
    GlobalFirstLaneExactPublicEagerResult :=
  (result.1.1.2,
    (((result.1.1.1, result.1.2), result.2.1), result.2.2))

noncomputable def globalFirstLaneExactCoupledContinuation
    (adversary : Adversary Concrete.scheme)
    (parameter : PublicParameter)
    (base : GlobalChainValueIndex → Digest) :
    ProbComp GlobalFirstLaneExactPublicEagerResult := do
  let keyResult ← globalHighDirectKeygenAfterParameter parameter
  let execution ← (simulateQ
    (FirstLaneOracleSimulation.eagerTraceImpl base)
    ((globalFirstLaneExactTracedDetailedExecution adversary keyResult.1
      keyResult.2).run (GlobalExactTracedState.mk
        (globalFilteredCausalKeygenState keyResult.1) [] []))).run
  pure (base, ((keyResult, execution.1), execution.2))

theorem globalFirstLaneExactCoupledProgram_projection_eq_parameterFirst
    (adversary : Adversary Concrete.scheme) :
    globalFirstLaneExactCoupledProjection <$>
      globalFirstLaneExactCoupledProgram adversary = (do
        let parameter ← Concrete.samplePublicParameter
        let base ← independentGlobalChainValueTable
        globalFirstLaneExactCoupledContinuation adversary parameter base) := by
  unfold globalFirstLaneExactCoupledProgram
  rw [coupledGlobalChainKeygenWithBaseHighFull_eq_direct]
  simp [globalFirstLaneExactCoupledProjection,
    globalFirstLaneExactCoupledContinuation, bind_assoc]

theorem firstLane_eagerTrace_liftProbComp_then_bind
    (base : GlobalChainValueIndex → Digest)
    (keygen : ProbComp κ)
    (body : κ → OracleComp GlobalFirstLaneWorld α) :
    (do
      let keyResult ← keygen
      let execution ← (simulateQ
        (FirstLaneOracleSimulation.eagerTraceImpl base)
        (body keyResult)).run
      pure (base, ((keyResult, execution.1), execution.2))) = (do
      let result ← (simulateQ
        (FirstLaneOracleSimulation.eagerTraceImpl base) (do
          let keyResult ← FirstLaneOracleSimulation.liftProbComp keygen
          let execution ← body keyResult
          pure (keyResult, execution))).run
      pure (base, result)) := by
  simp only [simulateQ_bind, WriterT.run_bind', bind_assoc]
  rw [FirstLaneOracleSimulation.simulate_eagerTrace_liftProbComp]
  simp [simulateQ_pure, WriterT.run_pure]

theorem globalFirstLaneExactCoupledContinuation_eq_eagerAfterBase
    (adversary : Adversary Concrete.scheme)
    (base : GlobalChainValueIndex → Digest) :
    (do
      let parameter ← Concrete.samplePublicParameter
      globalFirstLaneExactCoupledContinuation adversary parameter base) = (do
      let result ← (simulateQ
        (FirstLaneOracleSimulation.eagerTraceImpl base)
        (globalFirstLaneExactTracedProgram adversary)).run
      pure (base, result)) := by
  unfold globalFirstLaneExactCoupledContinuation
    globalFirstLaneExactTracedProgram globalHighDirectKeygen
  simpa only [bind_assoc] using
    (firstLane_eagerTrace_liftProbComp_then_bind base
      (do
        let parameter ← Concrete.samplePublicParameter
        globalHighDirectKeygenAfterParameter parameter)
      (fun keyResult =>
        (globalFirstLaneExactTracedDetailedExecution adversary keyResult.1
          keyResult.2).run (GlobalExactTracedState.mk
            (globalFilteredCausalKeygenState keyResult.1) [] [])))

theorem evalDist_globalFirstLaneExactCoupledProjection_eq_eagerExperiment
    (adversary : Adversary Concrete.scheme) :
    evalDist (globalFirstLaneExactCoupledProjection <$>
      globalFirstLaneExactCoupledProgram adversary) =
    evalDist (FirstLaneOracleSimulation.eagerExperiment
      (globalFirstLaneExactTracedProgram adversary)) := by
  rw [globalFirstLaneExactCoupledProgram_projection_eq_parameterFirst]
  calc
    evalDist (do
        let parameter ← Concrete.samplePublicParameter
        let base ← independentGlobalChainValueTable
        globalFirstLaneExactCoupledContinuation adversary parameter base) =
      evalDist (do
        let base ← independentGlobalChainValueTable
        let parameter ← Concrete.samplePublicParameter
        globalFirstLaneExactCoupledContinuation adversary parameter base) := by
          exact OracleComp.DeferredSampling.evalDist_bind_comm
            Concrete.samplePublicParameter independentGlobalChainValueTable _
    _ = evalDist (do
        let base ← independentGlobalChainValueTable
        let result ← (simulateQ
          (FirstLaneOracleSimulation.eagerTraceImpl base)
          (globalFirstLaneExactTracedProgram adversary)).run
        pure (base, result)) := by
          rw [evalDist_bind, evalDist_bind]
          apply bind_congr
          intro base
          exact congrArg evalDist
            (globalFirstLaneExactCoupledContinuation_eq_eagerAfterBase
              adversary base)
    _ = _ := by
      unfold FirstLaneOracleSimulation.eagerExperiment
      rw [evalDist_bind, evalDist_bind]
      unfold independentGlobalChainValueTable
        RevealProbeOracleSimulation.eagerTableSample
      rw [evalDist_uniformSample, evalDist_uniformSample]

end XmssSecurity.CappedChain
