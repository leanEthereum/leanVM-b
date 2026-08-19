import XmssSecurity.Proof.CappedGlobalChainHighLeafPlanFacts

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

theorem globalLeaf_not_match_endpoint_miss
    (table : GlobalChainValueIndex → Digest)
    (state : GlobalCausalHashState) (epoch : Epoch)
    (endpoints : ChainIndex → Digest)
    (hreveals : GlobalSigningRevealsAgree table state)
    (hhidden : globalHiddenLeafProbe? state epoch endpoints = none)
    (hmatch : ¬ GlobalLeafRevealsMatch state epoch endpoints) :
    ∃ chain : ChainIndex,
      table (chain, epoch, chainEndpointDigit) ≠ endpoints chain := by
  classical
  have hall :=
    (globalHiddenLeafProbe?_eq_none_iff state epoch endpoints).mp hhidden
  unfold GlobalLeafRevealsMatch at hmatch
  push Not at hmatch
  obtain ⟨chain, hmismatch⟩ := hmatch
  cases hvalue : state.revealed (chain, epoch, chainEndpointDigit) with
  | none => exact (hall chain hvalue).elim
  | some value =>
      refine ⟨chain, ?_⟩
      have htable : table (chain, epoch, chainEndpointDigit) = value :=
        hreveals (chain, epoch, chainEndpointDigit) value hvalue
      intro heq
      apply hmismatch
      rw [hvalue, ← htable, heq]

theorem programmedGlobal_left_leaf_cache_none_of_hidden_probe_miss
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (state : GlobalCausalHashState) (input : HashInput)
    (epoch : Epoch) (endpoints : ChainIndex → Digest)
    (index : GlobalChainValueIndex) (target : Digest)
    (hinput : input = Concrete.CacheView.leafInput
      right.1.1.secretKey.parameter epoch endpoints)
    (hprobe : globalHiddenLeafProbe? state epoch endpoints =
      some (index, target))
    (hmiss : right.1.2 index ≠ target) :
    left.cache input = none := by
  obtain ⟨chain, hindex, htarget, _hhidden⟩ :=
    globalHiddenLeafProbe?_eq_some state epoch endpoints index target hprobe
  have hparameter := programmedGlobal_secretKey_parameter_eq left right hrel
    hleftSupport hrightSupport
  rw [hinput, hparameter]
  apply programmedGlobal_left_leaf_cache_none_of_endpoint_miss left right hrel
    hleftSupport epoch endpoints chain
  simpa [hindex, htarget] using hmiss

theorem relTriple_programmed_globalFilteredLeafHashQuery_until_hit
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
    (monitor : AdaptiveRevealMonitor.State GlobalChainValueIndex)
    (hmonitor : monitor.revealed = rightState.revealed)
    (input : HashInput) (epoch : Epoch)
    (endpoints : ChainIndex → Digest)
    (hinput : input = Concrete.CacheView.leafInput
      right.1.1.secretKey.parameter epoch endpoints) :
    RelTriple
      ((randomOracle input).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
        ((globalCausalAttackerHashQueryFromHigh
          (globalChainValueHighTableOfEdges right.2) right.1.1.secretKey
            input).run rightState)).run)
      (GlobalFilteredHashUntilHitRelation left right.1 monitor) := by
  cases hcache : rightState.cache input with
  | some output =>
      apply relTriple_post_mono
        (relTriple_programmed_globalFilteredHashQuery_cached left right
          leftCache rightState hstate input output hcache)
      intro _leftResult _rightResult hresult
      exact Or.inl hresult
  | none =>
      cases hprobe : globalHiddenLeafProbe? rightState epoch endpoints with
      | some probe =>
          obtain ⟨index, target⟩ := probe
          have hplan :=
            globalFilteredCausalAttackerHashPlan_eq_leafProbeThenFresh
              right.1.1.secretKey rightState input epoch endpoints index target
                hinput hcache hprobe
          obtain ⟨_chain, _hindex, _htarget, hhidden⟩ :=
            globalHiddenLeafProbe?_eq_some rightState epoch endpoints index
              target hprobe
          exact
            relTriple_programmed_globalFilteredHashQuery_probeThenFresh_until_hit
              left right leftCache rightState hstate monitor hmonitor input index
                target hhidden hplan
                  (programmedGlobal_left_leaf_cache_none_of_hidden_probe_miss
                    left right hrel hleftSupport hrightSupport rightState input
                      epoch endpoints index target hinput hprobe)
      | none =>
          by_cases hmatch : GlobalLeafRevealsMatch rightState epoch endpoints
          · obtain ⟨output, hleftBase, hrightBase⟩ :=
              programmedGlobal_leaf_cache_pair_of_reveals_match left right hrel
                hleftSupport hrightSupport rightState hstate.2.2.2.1
                  hstate.2.2.2.2 input epoch endpoints hinput hmatch
            have hplan :=
              globalFilteredCausalAttackerHashPlan_eq_leafRedirect
                right.1.1.secretKey rightState input epoch endpoints output
                  hinput hcache hprobe hmatch hrightBase
            have hparameter := programmedGlobal_secretKey_parameter_eq left
              right hrel hleftSupport hrightSupport
            have hnotSigning : ¬ GlobalSigningComparableHashInput
                left.secretKey.parameter input := by
              rw [hinput, hparameter]
              exact globalLeafInput_not_signingComparable left.secretKey.parameter
                epoch endpoints
            apply relTriple_post_mono
              (relTriple_programmed_globalFilteredHashQuery_redirect left right
                leftCache rightState hstate input output hleftBase hnotSigning
                  hplan)
            intro _leftResult _rightResult hresult
            exact Or.inl hresult
          · obtain ⟨chain, hmiss⟩ := globalLeaf_not_match_endpoint_miss
              right.1.2 rightState epoch endpoints hstate.2.2.2.2 hprobe hmatch
            have hparameter := programmedGlobal_secretKey_parameter_eq left
              right hrel hleftSupport hrightSupport
            have hbaseNone : left.cache input = none := by
              rw [hinput, hparameter]
              exact programmedGlobal_left_leaf_cache_none_of_endpoint_miss left
                right hrel hleftSupport epoch endpoints chain hmiss
            have hplan :=
              globalFilteredCausalAttackerHashPlan_eq_leafFresh_of_mismatch
                right.1.1.secretKey rightState input epoch endpoints hinput
                  hcache hprobe hmatch
            apply relTriple_post_mono
              (relTriple_programmed_globalFilteredHashQuery_fresh left right
                leftCache rightState hstate input hbaseNone hplan)
            intro _leftResult _rightResult hresult
            exact Or.inl hresult

end XmssSecurity.CappedChain
