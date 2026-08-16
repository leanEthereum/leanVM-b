import XmssSecurity.CappedGlobalCausalStrategyProgram

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

noncomputable def globalCausalCompiledStrategyExperiment
    (queries : Nat) (adversary : Adversary Concrete.cappedScheme) :=
  RevealProbeOracleSimulation.eagerExperiment
    (RevealProbeOracleSimulation.compileStrategyProbes queries
      (globalCausalStrategyProgram adversary))

theorem hasGlobalChainEagerReduction_of_programmedViewProbability
    (queries : Nat) (adversary : Adversary Concrete.cappedScheme)
    (hbound : HasHashQueryBound Concrete.cappedScheme adversary queries)
    (hprogrammed :
      Pr[IndexedHiddenValue.RevealProbeView.HitsAvoidingReveals queries |
          trajectoryProgrammedGlobalRevealProbeViewExperiment adversary] ≤
        Pr[RevealProbeOracleSimulation.ObservedHit |
          globalCausalCompiledStrategyExperiment queries adversary]) :
    HasGlobalChainEagerReduction queries adversary := by
  refine ⟨List Bool → GlobalChainValueIndex × Digest,
    RevealProbeOracleSimulation.compileStrategyProbes queries
      (globalCausalStrategyProgram adversary),
    RevealProbeOracleSimulation.compileStrategyProbes_isProbeQueryBoundP
      queries (globalCausalStrategyProgram adversary)
        (globalCausalStrategyProgram_isProbeQueryBoundP adversary), ?_⟩
  calc
    Pr[fun result =>
        GlobalWinningOutcomeChainValueHasKeygenOrigin result.1.2 result.2.2
          result.1.1.2 result.2.1 |
        detailedGameWithKeygenCache adversary] ≤
      Pr[IndexedHiddenValue.RevealProbeView.HitsAvoidingReveals queries |
        globalActionTracedRevealProbeView <$>
          detailedGameWithKeygenCacheAndActionTrace adversary] :=
      globalWinningChainOrigin_probability_le_revealProbeView
        queries adversary hbound
    _ = Pr[IndexedHiddenValue.RevealProbeView.HitsAvoidingReveals queries |
        trajectoryProgrammedGlobalRevealProbeViewExperiment adversary] :=
      probEvent_congr' (fun _ _ => Iff.rfl)
        (evalDist_globalActionTracedRevealProbeView_eq_programmed adversary)
    _ ≤ Pr[RevealProbeOracleSimulation.ObservedHit |
        globalCausalCompiledStrategyExperiment queries adversary] := hprogrammed

end XmssSecurity.CappedChain
