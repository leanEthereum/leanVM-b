import XmssSecurity.Proof.CappedGlobalChainHighAttackerHashUntilHit

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

set_option maxRecDepth 10000000
set_option maxHeartbeats 2000000

theorem globalLeafInput_not_signingComparable
    (parameter : PublicParameter) (epoch : Epoch)
    (endpoints : ChainIndex → Digest) :
    ¬ GlobalSigningComparableHashInput parameter
      (Concrete.CacheView.leafInput parameter epoch endpoints) := by
  rintro ⟨encodingEpoch, message, randomness, hencoding⟩
  exact Concrete.CacheView.encodingInput_ne_leafInput parameter encodingEpoch
    epoch message randomness endpoints hencoding.symm

theorem programmedGlobal_left_endpoint_eq_table
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (epoch : Epoch) (chain : ChainIndex) :
    Concrete.CacheReplay.oneTimePublicKey left.cache
        left.secretKey.parameter left.secretKey.chainStart epoch chain =
      right.1.2 (chain, epoch, chainEndpointDigit) := by
  exact programmedGlobal_left_chainValue_eq_table left right hrel hleftSupport
    (chain, epoch, chainEndpointDigit)

theorem programmedGlobal_left_leaf_cache_none_of_endpoint_miss
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (epoch : Epoch) (endpoints : ChainIndex → Digest)
    (chain : ChainIndex)
    (hmiss : right.1.2 (chain, epoch, chainEndpointDigit) ≠ endpoints chain) :
    left.cache (Concrete.CacheView.leafInput left.secretKey.parameter epoch
      endpoints) = none := by
  apply Concrete.keygen_cache_leafInput_eq_none_of_ne left.keyResult
    (trajectoryProgrammedGlobalChainKeygen_support_keyResult left hleftSupport)
      epoch endpoints
  intro heq
  apply hmiss
  rw [← programmedGlobal_left_endpoint_eq_table left right hrel hleftSupport
    epoch chain]
  exact congrFun heq.symm chain

theorem globalLeafRevealsMatch_endpoints_eq_leftReplay
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (state : GlobalCausalHashState) (epoch : Epoch)
    (endpoints : ChainIndex → Digest)
    (hreveals : GlobalSigningRevealsAgree right.1.2 state)
    (hmatch : GlobalLeafRevealsMatch state epoch endpoints) :
    endpoints = Concrete.CacheReplay.oneTimePublicKey left.cache
      left.secretKey.parameter left.secretKey.chainStart epoch := by
  funext chain
  have htable : right.1.2 (chain, epoch, chainEndpointDigit) =
      endpoints chain :=
    hreveals (chain, epoch, chainEndpointDigit) (endpoints chain)
      (hmatch chain)
  rw [← htable]
  exact (programmedGlobal_left_endpoint_eq_table left right hrel hleftSupport
    epoch chain).symm

theorem programmedGlobal_secretKey_parameter_eq
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen) :
    right.1.1.secretKey.parameter = left.secretKey.parameter := by
  have hleftKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    left hleftSupport
  have hrightKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    right.1.1 hrightSupport
  calc
    right.1.1.secretKey.parameter = right.1.1.publicKey.parameter :=
      (keygen_parameter_eq right.1.1.keyResult hrightKey).symm
    _ = left.publicKey.parameter :=
      congrArg PublicKey.parameter hrel.1.toStable.1.2.1.symm
    _ = left.secretKey.parameter := keygen_parameter_eq left.keyResult hleftKey

theorem leafBaseCachePair_of_treeCorrespondence
    (parameter : PublicParameter)
    (leftSecret : Epoch → ChainIndex → Digest)
    (rightSecret : SecretKey)
    (leftCache rightCache : QueryCache HashSpec)
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
    (htree : GlobalTreeCacheCorrespondence parameter leftEndpoints
      rightEndpoints leftCache rightCache)
    (hleftReplay : ReplayEndpointsMatch parameter leftSecret leftEndpoints
      leftCache)
    (hrightReplay : ReplayEndpointsMatch parameter rightSecret.chainStart
      rightEndpoints rightCache)
    (hparameter : rightSecret.parameter = parameter)
    (input : HashInput) (epoch : Epoch)
    (endpoints : ChainIndex → Digest)
    (hinput : input = Concrete.CacheView.leafInput rightSecret.parameter epoch
      endpoints)
    (hendpoints : endpoints = Concrete.CacheReplay.oneTimePublicKey leftCache
      parameter leftSecret epoch)
    (hcached : ∃ output : HashOutput, leftCache
      (Concrete.CacheView.leafInput parameter epoch
        (Concrete.CacheReplay.oneTimePublicKey leftCache parameter leftSecret
          epoch)) = some output) :
    ∃ output : HashOutput,
      leftCache input = some output ∧
      rightCache (keygenLeafTargetInput rightSecret rightCache input) =
        some output := by
  obtain ⟨output, hleftHonest⟩ := hcached
  refine ⟨output, ?_, ?_⟩
  · rw [hinput, hparameter, hendpoints]
    exact hleftHonest
  · rw [hinput, keygenLeafTargetInput_leafInput, hparameter]
    calc
      rightCache (Concrete.CacheView.leafInput parameter epoch
          (Concrete.CacheReplay.oneTimePublicKey rightCache parameter
            rightSecret.chainStart epoch)) =
          rightCache (Concrete.CacheView.leafInput parameter epoch
            (rightEndpoints epoch)) := by rw [hrightReplay epoch]
      _ = leftCache (Concrete.CacheView.leafInput parameter epoch
          (leftEndpoints epoch)) := (htree.leaves epoch).symm
      _ = leftCache (Concrete.CacheView.leafInput parameter epoch
          (Concrete.CacheReplay.oneTimePublicKey leftCache parameter
            leftSecret epoch)) := by rw [hleftReplay epoch]
      _ = some output := hleftHonest

theorem programmedGlobal_leaf_base_cache_pair
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (input : HashInput) (epoch : Epoch)
    (endpoints : ChainIndex → Digest)
    (hinput : input = Concrete.CacheView.leafInput
      right.1.1.secretKey.parameter epoch endpoints)
    (hendpoints : endpoints = Concrete.CacheReplay.oneTimePublicKey left.cache
      left.secretKey.parameter left.secretKey.chainStart epoch) :
    ∃ output : HashOutput,
      left.cache input = some output ∧
      right.1.1.cache
        (keygenLeafTargetInput right.1.1.secretKey right.1.1.cache input) =
          some output := by
  have hleftKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    left hleftSupport
  have hparameter : right.1.1.secretKey.parameter =
      left.secretKey.parameter :=
    programmedGlobal_secretKey_parameter_eq left right hrel hleftSupport
      hrightSupport
  obtain ⟨leftEndpoints, rightEndpoints, htree, hleftReplay, hrightReplay⟩ :=
    hrel.1.2.2.2
  apply leafBaseCachePair_of_treeCorrespondence left.secretKey.parameter
    left.secretKey.chainStart right.1.1.secretKey left.cache right.1.1.cache
      leftEndpoints rightEndpoints htree hleftReplay hrightReplay hparameter
        input epoch endpoints hinput hendpoints
  exact Concrete.keygen_cache_has_leafInput left.keyResult hleftKey epoch

theorem programmedGlobal_leaf_cache_pair_of_reveals_match
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (state : GlobalCausalHashState)
    (hkeygenCache : state.keygenCache = right.1.1.cache)
    (hreveals : GlobalSigningRevealsAgree right.1.2 state)
    (input : HashInput) (epoch : Epoch)
    (endpoints : ChainIndex → Digest)
    (hinput : input = Concrete.CacheView.leafInput
      right.1.1.secretKey.parameter epoch endpoints)
    (hmatch : GlobalLeafRevealsMatch state epoch endpoints) :
    ∃ output : HashOutput,
      left.cache input = some output ∧
      state.keygenCache
        (keygenLeafTargetInput right.1.1.secretKey state.keygenCache input) =
          some output := by
  have hendpoints := globalLeafRevealsMatch_endpoints_eq_leftReplay left right
    hrel hleftSupport state epoch endpoints hreveals hmatch
  obtain ⟨output, hleft, hright⟩ := programmedGlobal_leaf_base_cache_pair
    left right hrel hleftSupport hrightSupport input epoch endpoints hinput
      hendpoints
  refine ⟨output, hleft, ?_⟩
  rw [hkeygenCache]
  exact hright

end XmssSecurity.CappedChain
