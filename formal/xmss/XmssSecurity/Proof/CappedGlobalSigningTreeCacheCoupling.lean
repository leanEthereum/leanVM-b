import XmssSecurity.Proof.CappedGlobalTreeKeygenCacheCoupling
import XmssSecurity.Proof.CappedGlobalSigningKeygenCoupling
import XmssSecurity.Proof.StatementLemmas

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

theorem Concrete.CacheView.encodingInput_ne_chainInput
    (parameter : PublicParameter) (encodingEpoch epoch : Epoch)
    (message : Message) (randomness : Randomness) (chain : ChainIndex)
    (position : ChainStep) (value : Digest) :
    Concrete.CacheView.encodingInput parameter encodingEpoch
        (message, randomness) ≠
      Concrete.CacheView.chainInput parameter epoch chain position value := by
  intro heq
  have hdomain := domain_eq_of_tweakableHashInput_eq parameter heq
  simp at hdomain

theorem Concrete.CacheView.encodingInput_ne_leafInput
    (parameter : PublicParameter) (encodingEpoch epoch : Epoch)
    (message : Message) (randomness : Randomness)
    (endpoints : ChainIndex → Digest) :
    Concrete.CacheView.encodingInput parameter encodingEpoch
        (message, randomness) ≠
      Concrete.CacheView.leafInput parameter epoch endpoints := by
  intro heq
  have hdomain := domain_eq_of_tweakableHashInput_eq parameter heq
  simp at hdomain

theorem Concrete.CacheView.encodingInput_ne_merkleInput
    (parameter : PublicParameter) (epoch : Epoch)
    (message : Message) (randomness : Randomness) (level : MerkleLevel)
    (node : MerkleNode) (left right : Digest) :
    Concrete.CacheView.encodingInput parameter epoch (message, randomness) ≠
      Concrete.CacheView.merkleInput parameter level node left right := by
  intro heq
  have hdomain := domain_eq_of_tweakableHashInput_eq parameter heq
  simp at hdomain

theorem Concrete.CacheView.chainStep_cacheQuery_encodingInput
    (cache : QueryCache HashSpec) (output : HashOutput)
    (parameter : PublicParameter) (encodingEpoch epoch : Epoch)
    (message : Message) (randomness : Randomness) (chain : ChainIndex) :
    Concrete.CacheView.chainStep
        (cache.cacheQuery
          (Concrete.CacheView.encodingInput parameter encodingEpoch
            (message, randomness)) output)
        parameter epoch chain =
      Concrete.CacheView.chainStep cache parameter epoch chain := by
  funext position value
  unfold Concrete.CacheView.chainStep
  split
  · unfold Concrete.CacheView.digestAt
    rw [QueryCache.cacheQuery_of_ne]
    exact (Concrete.CacheView.encodingInput_ne_chainInput parameter
      encodingEpoch epoch message randomness chain _ value).symm
  · rfl

theorem Concrete.CacheReplay.oneTimePublicKey_cacheQuery_encodingInput
    (cache : QueryCache HashSpec) (output : HashOutput)
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (encodingEpoch epoch : Epoch) (message : Message)
    (randomness : Randomness) :
    Concrete.CacheReplay.oneTimePublicKey
        (cache.cacheQuery
          (Concrete.CacheView.encodingInput parameter encodingEpoch
            (message, randomness)) output)
        parameter secret epoch =
      Concrete.CacheReplay.oneTimePublicKey cache parameter secret epoch := by
  unfold Concrete.CacheReplay.oneTimePublicKey
  funext chain
  rw [Concrete.CacheView.chainStep_cacheQuery_encodingInput]

theorem ReplayEndpointsMatch.cacheQuery_encodingInput
    (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest)
    (endpoints : Epoch → ChainIndex → Digest)
    (cache : QueryCache HashSpec)
    (hrel : ReplayEndpointsMatch parameter secret endpoints cache)
    (encodingEpoch : Epoch) (message : Message) (randomness : Randomness)
    (output : HashOutput) :
    ReplayEndpointsMatch parameter secret endpoints
      (cache.cacheQuery
        (Concrete.CacheView.encodingInput parameter encodingEpoch
          (message, randomness)) output) := by
  intro epoch
  rw [Concrete.CacheReplay.oneTimePublicKey_cacheQuery_encodingInput]
  exact hrel epoch

theorem GlobalTreeCacheCorrespondence.cacheQuery_encodingInput
    (parameter : PublicParameter)
    (leftEndpoints rightEndpoints : Epoch → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec)
    (hrel : GlobalTreeCacheCorrespondence parameter leftEndpoints
      rightEndpoints leftCache rightCache)
    (epoch : Epoch) (message : Message) (randomness : Randomness)
    (output : HashOutput) :
    GlobalTreeCacheCorrespondence parameter leftEndpoints rightEndpoints
      (leftCache.cacheQuery
        (Concrete.CacheView.encodingInput parameter epoch
          (message, randomness)) output)
      (rightCache.cacheQuery
        (Concrete.CacheView.encodingInput parameter epoch
          (message, randomness)) output) := by
  constructor
  · apply hrel.merkle.cacheQuery_distinct
    · intro input hinput
      obtain ⟨level, node, haddress⟩ := hinput
      intro heq
      have hencoding : AtHashAddress parameter (.encoding epoch) input := by
        rw [heq]
        simp [Concrete.CacheView.encodingInput]
      have hdomain := atHashAddress_unique parameter (.merkle level node)
        (.encoding epoch) input haddress hencoding
      simp at hdomain
    · intro input hinput
      obtain ⟨level, node, haddress⟩ := hinput
      intro heq
      have hencoding : AtHashAddress parameter (.encoding epoch) input := by
        rw [heq]
        simp [Concrete.CacheView.encodingInput]
      have hdomain := atHashAddress_unique parameter (.merkle level node)
        (.encoding epoch) input haddress hencoding
      simp at hdomain
  · apply hrel.leaves.cacheQuery_distinct
    · intro candidate
      exact Concrete.CacheView.encodingInput_ne_leafInput parameter epoch
        candidate message randomness (leftEndpoints candidate)
    · intro candidate
      exact Concrete.CacheView.encodingInput_ne_leafInput parameter epoch
        candidate message randomness (rightEndpoints candidate)

def GlobalTreeSigningCacheRelation
    (parameter : PublicParameter)
    (leftSecret rightSecret : Epoch → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec) : Prop :=
  ∃ leftEndpoints rightEndpoints,
    GlobalTreeCacheCorrespondence parameter leftEndpoints rightEndpoints
      leftCache rightCache ∧
    ReplayEndpointsMatch parameter leftSecret leftEndpoints leftCache ∧
    ReplayEndpointsMatch parameter rightSecret rightEndpoints rightCache

def ProgrammedGlobalChainKeygenFullCacheStableRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) : Prop :=
  ProgrammedGlobalChainKeygenFullCacheRelation left right ∧
    TreeCacheStable left.secretKey.parameter left.secretKey.chainStart
      left.cache ∧
    TreeCacheStable right.1.secretKey.parameter right.1.secretKey.chainStart
      right.1.cache ∧
    GlobalTreeSigningCacheRelation left.secretKey.parameter
      left.secretKey.chainStart right.1.secretKey.chainStart left.cache
        right.1.cache

theorem ProgrammedGlobalChainKeygenFullCacheStableRelation.toStable
    {left : ProgrammedGlobalChainKeygenView}
    {right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)}
    (hrel : ProgrammedGlobalChainKeygenFullCacheStableRelation left right) :
    ProgrammedGlobalChainKeygenStableRelation left right :=
  ⟨hrel.1.1.1, hrel.2.1, hrel.2.2.1⟩


end XmssSecurity.CappedChain
