import XmssSecurity.Proof.CappedGlobalTreeCacheCorrespondence
import XmssSecurity.Proof.CappedGlobalChainKeygenGameCoupling

namespace XmssSecurity.CappedChain

def CoupledGlobalChainKeygenFullCacheRelation
    (parameter : PublicParameter)
    (left : CoupledGlobalChainKeygenView)
    (right : CoupledGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) : Prop :=
  CoupledGlobalChainKeygenRelation parameter left right ∧
    ∃ leftEndpoints rightEndpoints,
      GlobalTreeCacheCorrespondence parameter leftEndpoints rightEndpoints
        left.cache right.1.cache ∧
      ReplayEndpointsMatch parameter left.secret leftEndpoints left.cache ∧
      ReplayEndpointsMatch parameter right.1.secret rightEndpoints
        right.1.cache

def ProgrammedGlobalChainKeygenFullCacheRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) : Prop :=
  ProgrammedGlobalChainKeygenFullRelation left right ∧
    ∃ leftEndpoints rightEndpoints,
      GlobalTreeCacheCorrespondence left.secretKey.parameter leftEndpoints
        rightEndpoints left.cache right.1.cache ∧
      ReplayEndpointsMatch left.secretKey.parameter left.secretKey.chainStart
        leftEndpoints left.cache ∧
      ReplayEndpointsMatch right.1.secretKey.parameter
        right.1.secretKey.chainStart rightEndpoints right.1.cache

end XmssSecurity.CappedChain
