import XmssSecurity.Proof.CappedGlobalTreeKeygenCacheCoupling
import XmssSecurity.Proof.CappedGlobalSigningKeygenCoupling
import XmssSecurity.Proof.StatementLemmas

open OracleSpec

namespace XmssSecurity.CappedChain

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
