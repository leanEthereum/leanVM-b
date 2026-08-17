import XmssSecurity.CappedGlobalChainHighBoundedPublic
import XmssSecurity.ExpectedRevealProbeSimulation

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

theorem globalWinningChainOrigin_probability_le_expectedProbes
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hreduction : HasGlobalHighBoundedPublicReduction q adversary) :
    Pr[fun result =>
      GlobalWinningOutcomeChainValueHasKeygenOrigin result.1.2 result.2.2
        result.1.1.2 result.2.1 |
      detailedGameWithKeygenCache adversary] ≤
      expectedSimulatedQueryCount
          RevealProbeOracleSimulation.lazyMonitorImpl
          RevealProbeOracleSimulation.IsProbeQuery
          (globalHighBoundedPublicProgram q adversary)
          AdaptiveRevealMonitor.State.empty /
        ((2 ^ digestBits : Nat) : ENNReal) := by
  exact hreduction.trans
    (RevealProbeOracleSimulation.eagerExperiment_observedHit_probability_le_expectedProbeCount
      (q + numChains) (globalHighBoundedPublicProgram q adversary)
      (globalHighBoundedPublicProgram_isProbeQueryBoundP q adversary))

theorem globalWinningChainOrigin_probability_le_unboundedExpectedProbes
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hreduction : HasGlobalHighBoundedPublicReduction q adversary) :
    Pr[fun result =>
      GlobalWinningOutcomeChainValueHasKeygenOrigin result.1.2 result.2.2
        result.1.1.2 result.2.1 |
      detailedGameWithKeygenCache adversary] ≤
      expectedSimulatedQueryCount
          RevealProbeOracleSimulation.lazyMonitorImpl
          RevealProbeOracleSimulation.IsProbeQuery
          (globalHighDirectPublicProgram adversary)
          AdaptiveRevealMonitor.State.empty /
        ((2 ^ digestBits : Nat) : ENNReal) := by
  calc
    _ ≤ expectedSimulatedQueryCount
          RevealProbeOracleSimulation.lazyMonitorImpl
          RevealProbeOracleSimulation.IsProbeQuery
          (globalHighBoundedPublicProgram q adversary)
          AdaptiveRevealMonitor.State.empty /
        ((2 ^ digestBits : Nat) : ENNReal) :=
      globalWinningChainOrigin_probability_le_expectedProbes q adversary
        hreduction
    _ = RevealProbeOracleSimulation.expectedEagerObservedProbeCount
          AdaptiveRevealMonitor.State.empty
          (globalHighBoundedPublicProgram q adversary) /
        ((2 ^ digestBits : Nat) : ENNReal) := by
      rw [RevealProbeOracleSimulation.expectedEagerObservedProbeCount_eq_expectedSimulatedQueryCount]
    _ ≤ RevealProbeOracleSimulation.expectedEagerObservedProbeCount
          AdaptiveRevealMonitor.State.empty
          (globalHighDirectPublicProgram adversary) /
        ((2 ^ digestBits : Nat) : ENNReal) := by
      gcongr
      unfold globalHighBoundedPublicProgram
      exact
        RevealProbeOracleSimulation.expectedEagerObservedProbeCount_enforceProbeBound_le
          AdaptiveRevealMonitor.State.empty (q + numChains)
            (globalHighDirectPublicProgram adversary)
    _ = _ := by
      rw [RevealProbeOracleSimulation.expectedEagerObservedProbeCount_eq_expectedSimulatedQueryCount]

end XmssSecurity.CappedChain
