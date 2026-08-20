import XmssSecurity.Proof.CappedGlobalChainHighLeafUntilHit
import XmssSecurity.Proof.CappedChain.KeygenUnaddressedCache

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

set_option maxRecDepth 10000000
set_option maxHeartbeats 2000000

theorem Concrete.keygen_cache_none_at_global_chainAddress_of_probe_none
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (input : HashInput) (epoch : Epoch) (chain : ChainIndex)
    (step : ChainStep)
    (haddress : AtHashAddress keyResult.1.2.parameter
      (.chain epoch chain step) input)
    (hprobe : globalChainInputProbe? keyResult.1.2.parameter input = none) :
    keyResult.2 input = none := by
  obtain ⟨honestOutput, hhonest⟩ :=
    Concrete.keygen_cache_has_chainInput keyResult hmem epoch chain step
  cases hcached : keyResult.2 input with
  | none => rfl
  | some output =>
      have heq : input = Concrete.CacheView.chainInput
          keyResult.1.2.parameter epoch chain step
            (Wots.walk
              (Concrete.CacheView.chainStep keyResult.2
                keyResult.1.2.parameter epoch chain)
              0 step.val (keyResult.1.2.chainStart epoch chain)) :=
        Concrete.keygen_cache_unique_chainAddress keyResult hmem epoch chain
          step input _ output honestOutput haddress (by
            simp [Concrete.CacheView.chainInput]) hcached hhonest
      rw [heq, globalChainInputProbe?_chainInput] at hprobe
      contradiction

theorem Concrete.keygen_cache_none_at_global_leafAddress_of_probe_none
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (input : HashInput) (epoch : Epoch)
    (haddress : AtHashAddress keyResult.1.2.parameter (.leaf epoch) input)
    (hprobe : globalLeafInputData? keyResult.1.2.parameter input = none) :
    keyResult.2 input = none := by
  obtain ⟨honestOutput, hhonest⟩ :=
    Concrete.keygen_cache_has_leafInput keyResult hmem epoch
  cases hcached : keyResult.2 input with
  | none => rfl
  | some output =>
      have heq : input = Concrete.CacheView.leafInput
          keyResult.1.2.parameter epoch
            (Concrete.CacheReplay.oneTimePublicKey keyResult.2
              keyResult.1.2.parameter keyResult.1.2.chainStart epoch) :=
        Concrete.keygen_cache_unique_leafAddress keyResult hmem epoch input _
          output honestOutput haddress (by
            simp [Concrete.CacheView.leafInput]) hcached hhonest
      rw [heq, globalLeafInputData?_leafInput] at hprobe
      contradiction

theorem Concrete.keygen_cache_none_of_global_probes_none_not_merkle
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (input : HashInput)
    (hchain : globalChainInputProbe? keyResult.1.2.parameter input = none)
    (hleaf : globalLeafInputData? keyResult.1.2.parameter input = none)
    (hmerkle : ¬ MerkleHashInput keyResult.1.2.parameter input) :
    keyResult.2 input = none := by
  by_cases haddressed : KeygenAddressedHashInput
      keyResult.1.2.parameter input
  · obtain ⟨domain, hdomain⟩ := haddressed
    cases domain with
    | chain epoch chain step =>
        exact Concrete.keygen_cache_none_at_global_chainAddress_of_probe_none
          keyResult hmem input epoch chain step hdomain hchain
    | leaf epoch =>
        exact Concrete.keygen_cache_none_at_global_leafAddress_of_probe_none
          keyResult hmem input epoch hdomain hleaf
    | merkle level node => exact (hmerkle ⟨level, node, hdomain⟩).elim
    | encoding epoch =>
        exact Concrete.keygen_cache_none_at_encodingAddress keyResult hmem
          epoch input hdomain
  · exact Concrete.keygen_cache_none_unaddressed keyResult hmem input
      haddressed

theorem globalFilteredCausalAttackerHashPlan_eq_ordinaryFresh
    (secretKey : SecretKey) (state : GlobalCausalHashState)
    (input : HashInput)
    (hcache : state.cache input = none)
    (hchain : globalChainInputProbe? secretKey.parameter input = none)
    (hleaf : globalLeafInputData? secretKey.parameter input = none) :
    globalFilteredCausalAttackerHashPlan secretKey input state = .fresh := by
  rw [globalFilteredCausalAttackerHashPlan, hcache, hchain]
  simp only [globalFilteredCausalUncachedAttackerHashPlan]
  rw [globalFilteredCausalLeafHashPlan, hleaf]

theorem relTriple_programmed_globalFilteredOrdinaryHashQuery
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (leftCache : QueryCache HashSpec) (rightState : GlobalCausalHashState)
    (hstate : GlobalFilteredCausalStateRelation left right.1 leftCache
      rightState)
    (input : HashInput)
    (hcache : rightState.cache input = none)
    (hchain : globalChainInputProbe? right.1.1.secretKey.parameter input = none)
    (hleaf : globalLeafInputData? right.1.1.secretKey.parameter input = none)
    (hbaseNone : left.cache input = none) :
    RelTriple
      ((randomOracle input).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
        ((globalCausalAttackerHashQueryFromHigh
          (globalChainValueHighTableOfEdges right.2) right.1.1.secretKey
            input).run rightState)).run)
      (GlobalFilteredHashResultRelation left right.1) := by
  apply relTriple_programmed_globalFilteredHashQuery_fresh left right leftCache
    rightState hstate input hbaseNone
  exact globalFilteredCausalAttackerHashPlan_eq_ordinaryFresh
    right.1.1.secretKey rightState input hcache hchain hleaf

end XmssSecurity.CappedChain
