import XmssSecurity.CappedGlobalChainHighPublicExperiment
import XmssSecurity.CappedVerifierQueryFloor

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

noncomputable def globalHighBoundedPublicProgram
    (q : Nat) (adversary : Adversary Concrete.cappedScheme) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex) Unit :=
  RevealProbeOracleSimulation.enforceProbeBound (q + numChains)
    (globalHighDirectPublicProgram adversary)

theorem globalHighBoundedPublicProgram_isProbeQueryBoundP
    (q : Nat) (adversary : Adversary Concrete.cappedScheme) :
    (globalHighBoundedPublicProgram q adversary).IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery (q + numChains) := by
  exact RevealProbeOracleSimulation.enforceProbeBound_isProbeQueryBoundP
    (q + numChains) (globalHighDirectPublicProgram adversary)

def HasGlobalHighBoundedPublicReduction
    (q : Nat) (adversary : Adversary Concrete.cappedScheme) : Prop :=
  Pr[fun result =>
      GlobalWinningOutcomeChainValueHasKeygenOrigin result.1.2 result.2.2
        result.1.1.2 result.2.1 |
    detailedGameWithKeygenCache adversary] ≤
  Pr[RevealProbeOracleSimulation.ObservedHit |
    RevealProbeOracleSimulation.eagerExperiment
      (globalHighBoundedPublicProgram q adversary)]

theorem globalWinningChainOrigin_probability_le_unboundedPublicExperiment
    (adversary : Adversary Concrete.cappedScheme) :
    Pr[fun result =>
      GlobalWinningOutcomeChainValueHasKeygenOrigin result.1.2 result.2.2
        result.1.1.2 result.2.1 |
      detailedGameWithKeygenCache adversary] ≤
    Pr[RevealProbeOracleSimulation.ObservedHit |
      RevealProbeOracleSimulation.eagerExperiment
        (globalHighDirectPublicProgram adversary)] := by
  apply (globalWinningChainOrigin_probability_le_publicObservedHit
    adversary).trans
  rw [show Pr[fun right : GlobalHighMonitoredProgramResult =>
      RevealProbeOracleSimulation.ObservedHit
        (globalHighMonitoredPublicProjection right) |
      globalHighMonitoredProgram adversary] =
    Pr[RevealProbeOracleSimulation.ObservedHit |
      globalHighMonitoredPublicProjection <$>
        globalHighMonitoredProgram adversary] by
      rw [probEvent_map]
      rfl]
  exact le_of_eq (probEvent_congr' (fun _ _ => Iff.rfl)
    (evalDist_globalHighMonitoredPublicProjection_eq_publicExperiment
      adversary))

def HasGlobalHighPublicEnforcement
    (q : Nat) (adversary : Adversary Concrete.cappedScheme) : Prop :=
  Pr[RevealProbeOracleSimulation.ObservedHit |
      RevealProbeOracleSimulation.eagerExperiment
        (globalHighDirectPublicProgram adversary)] ≤
    Pr[RevealProbeOracleSimulation.ObservedHit |
      RevealProbeOracleSimulation.eagerExperiment
        (globalHighBoundedPublicProgram q adversary)]

theorem hasGlobalHighBoundedPublicReduction_of_enforcement
    (q : Nat) (adversary : Adversary Concrete.cappedScheme)
    (henforcement : HasGlobalHighPublicEnforcement q adversary) :
    HasGlobalHighBoundedPublicReduction q adversary :=
  (globalWinningChainOrigin_probability_le_unboundedPublicExperiment
    adversary).trans henforcement

theorem globalWinningChainOrigin_probability_le_q_add_numChains
    (q : Nat) (adversary : Adversary Concrete.cappedScheme)
    (hreduction : HasGlobalHighBoundedPublicReduction q adversary) :
    Pr[fun result =>
      GlobalWinningOutcomeChainValueHasKeygenOrigin result.1.2 result.2.2
        result.1.1.2 result.2.1 |
      detailedGameWithKeygenCache adversary] ≤
      ((q + numChains : Nat) : ENNReal) /
        ((2 ^ digestBits : Nat) : ENNReal) := by
  exact hreduction.trans
    (RevealProbeOracleSimulation.eagerExperiment_observedHit_probability_le
      (q + numChains) (globalHighBoundedPublicProgram q adversary)
        (globalHighBoundedPublicProgram_isProbeQueryBoundP q adversary))

theorem globalWinningChainOrigin_probability_le_two_queries
    (q : Nat) (adversary : Adversary Concrete.cappedScheme)
    (hbound : HasHashQueryBound Concrete.cappedScheme adversary q)
    (hreduction : HasGlobalHighBoundedPublicReduction q adversary) :
    Pr[fun result =>
      GlobalWinningOutcomeChainValueHasKeygenOrigin result.1.2 result.2.2
        result.1.1.2 result.2.1 |
      detailedGameWithKeygenCache adversary] ≤
      2 * ((q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal)) := by
  apply (globalWinningChainOrigin_probability_le_q_add_numChains q adversary
    hreduction).trans
  have hfloor := hashQueryBound_at_least_numChains adversary q hbound
  have hcast : ((q + numChains : Nat) : ENNReal) ≤ 2 * (q : ENNReal) := by
    exact_mod_cast (show q + numChains ≤ 2 * q by omega)
  rw [div_eq_mul_inv]
  calc
    ((q + numChains : Nat) : ENNReal) *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ ≤
      (2 * (q : ENNReal)) *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by gcongr
    _ = 2 * ((q : ENNReal) *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by ring

end XmssSecurity.CappedChain
