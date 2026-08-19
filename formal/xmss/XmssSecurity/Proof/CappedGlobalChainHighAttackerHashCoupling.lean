import XmssSecurity.Proof.CappedGlobalChainHighAttackerHashPlan

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

theorem relTriple_programmed_globalFilteredHashQuery_cached
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (leftCache : QueryCache HashSpec) (rightState : GlobalCausalHashState)
    (hstate : GlobalFilteredCausalStateRelation left right.1 leftCache
      rightState)
    (input : HashInput) (output : HashOutput)
    (hright : rightState.cache input = some output) :
    RelTriple
      ((randomOracle input).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
        ((globalCausalAttackerHashQueryFromHigh
          (globalChainValueHighTableOfEdges right.2) right.1.1.secretKey
            input).run rightState)).run)
      (GlobalFilteredHashResultRelation left right.1) := by
  have hleft : leftCache input = some output :=
    hstate.2.1.right_le_left hright
  have hplan : globalFilteredCausalAttackerHashPlan right.1.1.secretKey input
      rightState = .cached output := by
    simp [globalFilteredCausalAttackerHashPlan, hright]
  rw [randomOracle, QueryImpl.withCaching_run_some _ hleft,
    globalCausalAttackerHashQueryFromHigh_run, hplan, simulateQ_pure,
    WriterT.run_pure]
  apply relTriple_pure_pure
  exact ⟨rfl, hstate.recordedState right.1.1.secretKey input⟩

theorem relTriple_programmed_globalFilteredHashQuery_fresh
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (leftCache : QueryCache HashSpec) (rightState : GlobalCausalHashState)
    (hstate : GlobalFilteredCausalStateRelation left right.1 leftCache
      rightState)
    (input : HashInput)
    (hbaseNone : left.cache input = none)
    (hplan : globalFilteredCausalAttackerHashPlan right.1.1.secretKey input
      rightState = .fresh) :
    RelTriple
      ((randomOracle input).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
        ((globalCausalAttackerHashQueryFromHigh
          (globalChainValueHighTableOfEdges right.2) right.1.1.secretKey
            input).run rightState)).run)
      (GlobalFilteredHashResultRelation left right.1) := by
  have hcurrent : leftCache input = rightState.cache input := by
    rcases hstate.2.1 input with hagree | ⟨hleft, hright⟩
    · exact hagree
    · rw [hleft, hbaseNone, hright]
  have hcouple := relTriple_randomOracle_run_of_current_eq_filtered
    (GlobalSigningComparableHashInput left.secretKey.parameter) left.cache
      leftCache rightState.cache input hcurrent hstate.1 hstate.2.1
  let recorded :=
    globalCausalRecordedState right.1.1.secretKey input rightState
  let wrap := fun result : HashOutput × QueryCache HashSpec =>
    ((result.1, recorded.setCache result.2),
      ([] : RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
  have hprepared : RelTriple ((randomOracle input).run leftCache)
      ((randomOracle input).run rightState.cache)
      (fun leftResult rightResult =>
        GlobalFilteredHashResultRelation left right.1 leftResult
          (wrap rightResult)) := by
    apply relTriple_post_mono hcouple
    intro leftResult rightResult hresult
    refine ⟨hresult.1, ?_⟩
    exact hstate.recordedStateSetCache right.1.1.secretKey input
      leftResult.2 rightResult.2 hresult.2.1 hresult.2.2.2.2
        hresult.2.2.1
  have hmapped := relTriple_map
    (R := GlobalFilteredHashResultRelation left right.1)
    (f := id) (g := wrap) hprepared
  rw [globalCausalAttackerHashQueryFromHigh_run, hplan,
    simulate_eagerTrace_globalCausalHashQuery]
  simpa [wrap, recorded, GlobalCausalHashState.setCache] using hmapped

theorem relTriple_programmed_globalFilteredHashQuery_redirect
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (leftCache : QueryCache HashSpec) (rightState : GlobalCausalHashState)
    (hstate : GlobalFilteredCausalStateRelation left right.1 leftCache
      rightState)
    (input : HashInput) (output : HashOutput)
    (hbase : left.cache input = some output)
    (hinput : ¬ GlobalSigningComparableHashInput left.secretKey.parameter input)
    (hplan : globalFilteredCausalAttackerHashPlan right.1.1.secretKey input
      rightState = .redirect output) :
    RelTriple
      ((randomOracle input).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
        ((globalCausalAttackerHashQueryFromHigh
          (globalChainValueHighTableOfEdges right.2) right.1.1.secretKey
            input).run rightState)).run)
      (GlobalFilteredHashResultRelation left right.1) := by
  have hleft : leftCache input = some output := hstate.2.2.1 hbase
  have hagrees : HashCachesAgreeOn
      (GlobalSigningComparableHashInput left.secretKey.parameter) leftCache
      ((globalCausalRecordedState right.1.1.secretKey input rightState).cache
        |>.cacheQuery input output) := by
    intro candidate hcandidate
    have hne : candidate ≠ input := by
      intro heq
      subst candidate
      exact hinput hcandidate
    rw [QueryCache.cacheQuery_of_ne _ _ hne,
      globalCausalRecordedState_cache]
    exact hstate.1 candidate hcandidate
  have hfiltered : FilteredCacheExtensionRelation left.cache leftCache
      ((globalCausalRecordedState right.1.1.secretKey input rightState).cache
        |>.cacheQuery input output) := by
    intro candidate
    by_cases heq : candidate = input
    · subst candidate
      left
      simp [hleft]
    · rw [QueryCache.cacheQuery_of_ne _ _ heq,
        globalCausalRecordedState_cache]
      exact hstate.2.1 candidate
  have hnext := hstate.recordedStateSetCache right.1.1.secretKey input
    leftCache
    ((globalCausalRecordedState right.1.1.secretKey input rightState).cache
      |>.cacheQuery input output)
    hagrees hfiltered le_rfl
  rw [randomOracle, QueryImpl.withCaching_run_some _ hleft,
    globalCausalAttackerHashQueryFromHigh_run, hplan, simulateQ_pure,
    WriterT.run_pure]
  exact relTriple_pure_pure ⟨rfl, hnext⟩

end XmssSecurity.CappedChain
