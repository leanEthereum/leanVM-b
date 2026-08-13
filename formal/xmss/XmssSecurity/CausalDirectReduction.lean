import XmssSecurity.CausalProbeEnforcement

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity

abbrev FilteredDirectExecution :=
  (((Forgery × Bool) × AttackerActionTrace) × CausalHashState)

abbrev FilteredDirectResult :=
  ProgrammedFixedChainKeygenView × FilteredDirectExecution

noncomputable def filteredDirectProgram
    (adversary : Adversary Concrete.scheme) (selected : ChainIndex) :
    OracleComp (RevealProbeOracleSimulation.World ChainValueIndex)
      FilteredDirectResult := do
  let keyView ← RevealProbeOracleSimulation.liftProbComp
    (actualFixedChainKeygen selected)
  let execution ← (filteredDirectDetailedGameAfterKeygen adversary
    keyView selected).run (filteredCausalKeygenState selected keyView)
  pure (keyView, execution)

noncomputable def boundedFilteredDirectProgram
    (queries : Nat) (adversary : Adversary Concrete.scheme)
    (selected : ChainIndex) :
    OracleComp (RevealProbeOracleSimulation.World ChainValueIndex)
      FilteredDirectResult :=
  RevealProbeOracleSimulation.enforceProbeBound queries
    (filteredDirectProgram adversary selected)

theorem boundedFilteredDirectProgram_isProbeQueryBoundP
    (queries : Nat) (adversary : Adversary Concrete.scheme)
    (selected : ChainIndex) :
    (boundedFilteredDirectProgram queries adversary selected).IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery queries := by
  exact RevealProbeOracleSimulation.enforceProbeBound_isProbeQueryBoundP
    queries (filteredDirectProgram adversary selected)

theorem hasActionTracedEagerViewReduction_of_boundedFilteredDirectProgram
    (queries : Nat) (adversary : Adversary Concrete.scheme)
    (selected : ChainIndex)
    (hprobability :
      Pr[ActionTracedChainProbeHit queries selected |
          detailedGameWithKeygenCacheAndActionTrace adversary] ≤
        Pr[RevealProbeOracleSimulation.ObservedHit |
          RevealProbeOracleSimulation.eagerExperiment
            (boundedFilteredDirectProgram queries adversary selected)]) :
    HasActionTracedEagerViewReduction queries adversary selected := by
  exact ⟨FilteredDirectResult,
    boundedFilteredDirectProgram queries adversary selected,
    boundedFilteredDirectProgram_isProbeQueryBoundP queries adversary selected,
    hprobability⟩

def FilteredDirectHitRelation
    (queries : Nat) (selected : ChainIndex)
    (real : DetailedActionTracedResult)
    (ideal : (ChainValueIndex → Digest) ×
      (FilteredDirectResult ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) : Prop :=
  ActionTracedChainProbeHit queries selected real →
    RevealProbeOracleSimulation.ObservedHit ideal

theorem hasActionTracedEagerViewReduction_of_boundedFilteredDirectRelTriple
    (queries : Nat) (adversary : Adversary Concrete.scheme)
    (selected : ChainIndex)
    (hcoupling : RelTriple
      (detailedGameWithKeygenCacheAndActionTrace adversary)
      (RevealProbeOracleSimulation.eagerExperiment
        (boundedFilteredDirectProgram queries adversary selected))
      (FilteredDirectHitRelation queries selected)) :
    HasActionTracedEagerViewReduction queries adversary selected := by
  apply hasActionTracedEagerViewReduction_of_boundedFilteredDirectProgram
  apply probEvent_le_of_relTriple hcoupling
  intro real ideal hrel hhit
  exact hrel hhit

end XmssSecurity
