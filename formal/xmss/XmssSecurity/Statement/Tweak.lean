import XmssSecurity.Statement.Parameters

namespace XmssSecurity

abbrev Tweak := BitVec 128

structure TweakFields where
  tag : BitVec 8
  position : BitVec 32
  epoch : BitVec 32
deriving DecidableEq

/-- The specification's 16-byte tweak `tag || position || epoch || 0^56`. -/
def encodeTweak (fields : TweakFields) : Tweak :=
  (((0#56) ++ fields.epoch) ++ fields.position) ++ fields.tag

abbrev ChainStep := Fin (chainLength - 1)
abbrev MerkleLevel := Fin treeHeight

/-- Every domain-separated hash call made by the concrete XMSS instance. -/
inductive HashDomain where
  | chain (epoch : Epoch) (chain : ChainIndex) (step : ChainStep)
  | leaf (epoch : Epoch)
  | merkle (level : MerkleLevel) (node : MerkleNode)
  | encoding (epoch : Epoch)
deriving DecidableEq

def hashDomainTag : HashDomain → Nat
  | .chain .. => 0
  | .leaf .. => 1
  | .merkle .. => 2
  | .encoding .. => 3

/-- Serialize a typed hash domain into the three nonzero fields of an XMSS tweak. -/
def hashDomainFields : HashDomain → TweakFields
  | .chain epoch chain step =>
      ⟨0#8, BitVec.ofNat 32 (chainLength * chain.val + step.val), BitVec.ofNat 32 epoch.val⟩
  | .leaf epoch => ⟨1#8, 0#32, BitVec.ofNat 32 epoch.val⟩
  | .merkle level node =>
      ⟨2#8, BitVec.ofNat 32 (level.val + 1), BitVec.ofNat 32 node.val⟩
  | .encoding epoch => ⟨3#8, 0#32, BitVec.ofNat 32 epoch.val⟩

def hashDomainTweak (domain : HashDomain) : Tweak :=
  encodeTweak (hashDomainFields domain)

end XmssSecurity
