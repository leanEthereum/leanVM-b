import XmssSecurity.CappedGlobalChainHighAttackerHashCoupling

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

theorem relTriple_programmed_globalFilteredHashQuery_revealEdge
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftCache : QueryCache HashSpec) (rightState : GlobalCausalHashState)
    (hstate : GlobalFilteredCausalStateRelation left right.1 leftCache
      rightState)
    (edge : GlobalChainEdgeIndex)
    (hrightCache : rightState.cache
      (globalChainTableEdgeInput left.secretKey.parameter left.table edge) =
        none)
    (hrevealed : rightState.revealed
      (edge.1, edge.2.1, chainStepDigit edge.2.2) =
        some (right.1.2
          (edge.1, edge.2.1, chainStepDigit edge.2.2))) :
    RelTriple
      ((randomOracle
        (globalChainTableEdgeInput left.secretKey.parameter left.table edge)).run
          leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
        ((globalCausalAttackerHashQueryFromHigh
          (globalChainValueHighTableOfEdges right.2) right.1.1.secretKey
            (globalChainTableEdgeInput left.secretKey.parameter left.table
              edge)).run rightState)).run)
      (GlobalFilteredHashResultRelation left right.1) := by
  have hleftKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    left hleftSupport
  have hrightKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    right.1.1 hrightSupport
  have hparameter : left.secretKey.parameter =
      right.1.1.secretKey.parameter := by
    calc
      left.secretKey.parameter = left.publicKey.parameter :=
        (keygen_parameter_eq left.keyResult hleftKey).symm
      _ = right.1.1.publicKey.parameter :=
        congrArg PublicKey.parameter hrel.1.toStable.1.2.1
      _ = right.1.1.secretKey.parameter :=
        keygen_parameter_eq right.1.1.keyResult hrightKey
  have htable : left.table = right.1.2 := hrel.1.toStable.1.1
  have hedgeInput :
      globalChainTableEdgeInput left.secretKey.parameter left.table edge =
        globalChainTableEdgeInput right.1.1.secretKey.parameter right.1.2
          edge := by
    rw [hparameter, htable]
  have hrightCanonical : rightState.cache
      (globalChainTableEdgeInput right.1.1.secretKey.parameter right.1.2
        edge) = none := by
    rw [← hedgeInput]
    exact hrightCache
  have hplanCanonical := globalFilteredCausalAttackerHashPlan_eq_reveal_globalEdge
    right.1.1.secretKey right.1.2 edge rightState hrightCanonical hrevealed
  have hplan : globalFilteredCausalAttackerHashPlan right.1.1.secretKey
      (globalChainTableEdgeInput left.secretKey.parameter left.table edge)
        rightState =
      .reveal (edge.1, edge.2.1, chainStepNextDigit edge.2.2) := by
    rw [hedgeInput]
    exact hplanCanonical
  obtain ⟨output, hbase, htruncate⟩ := hrel.2.2 edge
  have hleft : leftCache
      (globalChainTableEdgeInput left.secretKey.parameter left.table edge) =
        some output := hstate.2.2.1 hbase
  rw [randomOracle, QueryImpl.withCaching_run_some _ hleft,
    globalCausalAttackerHashQueryFromHigh_run, hplan,
    simulate_eagerTrace_globalCausalRevealHashQueryFromHigh]
  apply relTriple_pure_pure
  have hconstructed :
      Rom.hashOutputEquivDigestPair.symm
          (globalChainValueHighTableOfEdges right.2
            (edge.1, edge.2.1, chainStepNextDigit edge.2.2),
            right.1.2
              (edge.1, edge.2.1, chainStepNextDigit edge.2.2)) =
        output := by
    calc
      _ = globalChainEdgeOutputFromHigh right.2 right.1.2 edge :=
        globalChainEdgeOutputFromHigh_eq_revealOutput right.2 right.1.2 edge
      _ = globalChainEdgeOutputFromHigh
          (globalChainEdgeHighTableOfCache left.cache
            left.secretKey.parameter left.table) left.table edge := by
        rw [hrel.2.1, htable]
      _ = output := globalChainEdgeOutputFromHigh_eq_cached left.cache
        left.secretKey.parameter left.table edge output hbase htruncate
  refine ⟨hconstructed.symm, ?_⟩
  rw [hconstructed]
  apply hstate.revealResultState right.1.1.secretKey
    (globalChainTableEdgeInput left.secretKey.parameter left.table edge)
    (edge.1, edge.2.1, chainStepNextDigit edge.2.2)
    (right.1.2 (edge.1, edge.2.1, chainStepNextDigit edge.2.2)) output
  · exact globalChainTableEdgeInput_not_signingComparable
      left.secretKey.parameter left.table edge
  · exact hleft
  · rfl

end XmssSecurity.CappedChain
