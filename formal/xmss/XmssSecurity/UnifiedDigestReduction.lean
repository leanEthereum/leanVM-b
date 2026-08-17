import XmssSecurity.ExactLoss
import XmssSecurity.RevealProbeReindex
import XmssSecurity.CappedGlobalChainHighBoundedPublic

open OracleComp OracleSpec

namespace XmssSecurity

def chainDigestIndex : CappedChain.GlobalChainValueIndex → UnifiedDigestIndex :=
  UnifiedDigestIndex.chainValue

theorem chainDigestIndex_injective : Function.Injective chainDigestIndex := by
  intro left right heq
  cases heq
  rfl

noncomputable def unifiedChainProgram
    (q : Nat) (adversary : XmssAdversary) :
    OracleComp (RevealProbeOracleSimulation.World UnifiedDigestIndex) Unit :=
  RevealProbeOracleSimulation.reindex chainDigestIndex
    (CappedChain.globalHighBoundedPublicProgram q adversary)

theorem unifiedChainProgram_isProbeQueryBoundP
    (q : Nat) (adversary : XmssAdversary) :
    (unifiedChainProgram q adversary).IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery (q + numChains) := by
  exact RevealProbeOracleSimulation.reindex_isProbeQueryBoundP
    chainDigestIndex (CappedChain.globalHighBoundedPublicProgram q adversary)
      (q + numChains)
        (CappedChain.globalHighBoundedPublicProgram_isProbeQueryBoundP
          q adversary)

theorem unifiedChainProgram_observedHit_probability_eq
    (q : Nat) (adversary : XmssAdversary) :
    Pr[RevealProbeOracleSimulation.ObservedHit |
        RevealProbeOracleSimulation.eagerExperiment
          (unifiedChainProgram q adversary)] =
      Pr[RevealProbeOracleSimulation.ObservedHit |
        RevealProbeOracleSimulation.eagerExperiment
          (CappedChain.globalHighBoundedPublicProgram q adversary)] := by
  exact
    RevealProbeOracleSimulation.eagerExperiment_reindex_observedHit_probability_eq
      chainDigestIndex chainDigestIndex_injective
        (CappedChain.globalHighBoundedPublicProgram q adversary)

theorem globalWinningChainOrigin_probability_le_unifiedChainProgram
    (q : Nat) (adversary : XmssAdversary)
    (hbound : XmssHasHashQueryBound adversary q) :
    Pr[fun result =>
        CappedChain.GlobalWinningOutcomeChainValueHasKeygenOrigin
          result.1.2 result.2.2 result.1.1.2 result.2.1 |
      CappedChain.detailedGameWithKeygenCache adversary] ≤
    Pr[RevealProbeOracleSimulation.ObservedHit |
      RevealProbeOracleSimulation.eagerExperiment
        (unifiedChainProgram q adversary)] := by
  rw [unifiedChainProgram_observedHit_probability_eq]
  exact CappedChain.hasGlobalHighBoundedPublicReduction_of_hashQueryBound
    q adversary hbound

end XmssSecurity
