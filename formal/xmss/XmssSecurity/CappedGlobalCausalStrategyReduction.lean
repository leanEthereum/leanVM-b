import XmssSecurity.CappedGlobalCausalHitTransfer

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

theorem globalCausalCompiledStrategy_observedHit_probability_eq_lazy
    (queries : Nat) (adversary : Adversary Concrete.cappedScheme) :
    Pr[RevealProbeOracleSimulation.ObservedHit |
        globalCausalCompiledStrategyExperiment queries adversary] =
      Pr[RevealProbeOracleSimulation.ObservedHit |
        globalCausalLazyCompiledStrategyExperiment queries adversary] := by
  exact probEvent_congr' (fun _ _ => Iff.rfl)
    (evalDist_eagerExperiment_compile_globalCausalStrategyProgram_eq_lazy
      queries adversary)

theorem hasGlobalChainEagerReduction_of_causalTraceProbability
    (queries : Nat) (adversary : Adversary Concrete.cappedScheme)
    (hbound : HasHashQueryBound Concrete.cappedScheme adversary queries)
    (hcausal :
      Pr[IndexedHiddenValue.RevealProbeView.HitsAvoidingReveals queries |
          trajectoryProgrammedGlobalRevealProbeViewExperiment adversary] ≤
        Pr[GlobalCausalTraceHitsAvoidingReveals queries |
          globalCausalLazyStrategyViewExperiment adversary]) :
    HasGlobalChainEagerReduction queries adversary := by
  apply hasGlobalChainEagerReduction_of_programmedViewProbability
    queries adversary hbound
  calc
    _ ≤ Pr[GlobalCausalTraceHitsAvoidingReveals queries |
          globalCausalLazyStrategyViewExperiment adversary] := hcausal
    _ ≤ Pr[RevealProbeOracleSimulation.ObservedHit |
          globalCausalLazyCompiledStrategyExperiment queries adversary] :=
      globalCausalTraceHit_probability_le_lazyObservedHit queries adversary
    _ = Pr[RevealProbeOracleSimulation.ObservedHit |
          globalCausalCompiledStrategyExperiment queries adversary] :=
      (globalCausalCompiledStrategy_observedHit_probability_eq_lazy
        queries adversary).symm

end XmssSecurity.CappedChain
