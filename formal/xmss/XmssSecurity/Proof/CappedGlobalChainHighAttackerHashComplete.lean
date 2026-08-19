import XmssSecurity.Proof.CappedGlobalChainHighOrdinaryUntilHit

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

def GlobalMerkleKeygenCacheRetained
    (secretKey : SecretKey) (state : GlobalCausalHashState) : Prop :=
  ∀ input, MerkleHashInput secretKey.parameter input →
    ∀ output, state.keygenCache input = some output →
      state.cache input = some output

theorem globalFilteredCausalKeygenState_merkleRetained
    (view : ProgrammedGlobalChainKeygenView) :
    GlobalMerkleKeygenCacheRetained view.secretKey
      (globalFilteredCausalKeygenState view) := by
  intro input hmerkle output hkeygen
  simpa [globalFilteredCausalKeygenState, hmerkle] using hkeygen

theorem programmedGlobal_left_cache_none_of_retained_merkle_miss
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (state : GlobalCausalHashState)
    (hkeygen : state.keygenCache = right.1.1.cache)
    (hretained : GlobalMerkleKeygenCacheRetained right.1.1.secretKey state)
    (input : HashInput)
    (hmerkle : MerkleHashInput right.1.1.secretKey.parameter input)
    (hcache : state.cache input = none) :
    left.cache input = none := by
  have hrightBase : right.1.1.cache input = none := by
    cases hbase : right.1.1.cache input with
    | none => rfl
    | some output =>
        have hcurrent := hretained input hmerkle output (by
          rw [hkeygen]
          exact hbase)
        rw [hcache] at hcurrent
        contradiction
  have hparameter := programmedGlobal_secretKey_parameter_eq left right hrel
    hleftSupport hrightSupport
  have hmerkleLeft : MerkleHashInput left.secretKey.parameter input := by
    rw [← hparameter]
    exact hmerkle
  obtain ⟨leftEndpoints, rightEndpoints, htree, _hleftReplay,
    _hrightReplay⟩ := hrel.1.2.2.2
  rw [htree.merkle input hmerkleLeft, hrightBase]

theorem relTriple_programmed_globalFilteredAttackerHashQuery_until_hit
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
    (hretained : GlobalMerkleKeygenCacheRetained right.1.1.secretKey
      rightState)
    (monitor : AdaptiveRevealMonitor.State GlobalChainValueIndex)
    (hmonitor : monitor.revealed = rightState.revealed)
    (input : HashInput) :
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
      have hparameter := programmedGlobal_secretKey_parameter_eq left right
        hrel hleftSupport hrightSupport
      cases hchain : globalChainInputProbe? right.1.1.secretKey.parameter input with
      | some probe =>
          obtain ⟨index, target⟩ := probe
          have hchainLeft : globalChainInputProbe? left.secretKey.parameter
              input = some (index, target) := by
            rw [← hparameter]
            exact hchain
          exact relTriple_programmed_globalFilteredChainHashQuery_until_hit
            left right hrel hleftSupport hrightSupport leftCache rightState
              hstate monitor hmonitor input index target hchainLeft
      | none =>
          cases hleaf : globalLeafInputData?
              right.1.1.secretKey.parameter input with
          | some data =>
              have hinput :=
                (globalLeafInputData?_eq_some_iff
                  right.1.1.secretKey.parameter input data).mp hleaf
              exact relTriple_programmed_globalFilteredLeafHashQuery_until_hit
                left right hrel hleftSupport hrightSupport leftCache rightState
                  hstate monitor hmonitor input data.epoch data.endpoints hinput
          | none =>
              have hbaseNone : left.cache input = none := by
                by_cases hmerkle : MerkleHashInput
                    right.1.1.secretKey.parameter input
                · exact programmedGlobal_left_cache_none_of_retained_merkle_miss
                    left right hrel hleftSupport hrightSupport rightState
                      hstate.2.2.2.1 hretained input hmerkle hcache
                · apply Concrete.keygen_cache_none_of_global_probes_none_not_merkle
                    left.keyResult
                    (trajectoryProgrammedGlobalChainKeygen_support_keyResult
                      left hleftSupport) input
                  · change globalChainInputProbe? left.secretKey.parameter
                      input = none
                    rw [← hparameter]
                    exact hchain
                  · change globalLeafInputData? left.secretKey.parameter
                      input = none
                    rw [← hparameter]
                    exact hleaf
                  · change ¬ MerkleHashInput left.secretKey.parameter input
                    rw [← hparameter]
                    exact hmerkle
              apply relTriple_post_mono
                (relTriple_programmed_globalFilteredOrdinaryHashQuery left right
                  leftCache rightState hstate input hcache hchain hleaf
                    hbaseNone)
              intro _leftResult _rightResult hresult
              exact Or.inl hresult

end XmssSecurity.CappedChain
