import XmssSecurity.Statement.ConcreteHash
import XmssSecurity.Statement.Encoding
import VCVio.OracleComp.QueryTracking.CachingOracle

open OracleComp OracleSpec

namespace XmssSecurity.Concrete.CacheView

def digestAt (cache : QueryCache HashSpec) (input : HashInput) : Digest :=
  match cache input with
  | some output => truncateHash output
  | none => 0

def tweakableHash (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (domain : HashDomain) (payload : HashInput) : Digest :=
  digestAt cache (XmssSecurity.tweakableHashInput parameter domain payload)

def encodingInput (parameter : PublicParameter) (epoch : Epoch)
    (input : Message × Randomness) : HashInput :=
  XmssSecurity.tweakableHashInput parameter (.encoding epoch)
    (Concrete.encodingPayload input.1 input.2)

def chainInput (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position : ChainStep) (value : Digest) : HashInput :=
  XmssSecurity.tweakableHashInput parameter (.chain epoch chain position)
    (Concrete.digestBytes value)

def leafInput (parameter : PublicParameter) (epoch : Epoch)
    (endpoints : ChainIndex → Digest) : HashInput :=
  XmssSecurity.tweakableHashInput parameter (.leaf epoch)
    (Concrete.leafPayload endpoints)

def merkleInput (parameter : PublicParameter) (level : MerkleLevel)
    (node : MerkleNode) (left right : Digest) : HashInput :=
  XmssSecurity.tweakableHashInput parameter (.merkle level node)
    (Concrete.nodePayload left right)

def encodingHash (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (epoch : Epoch) (input : Message × Randomness) : Digest :=
  digestAt cache (encodingInput parameter epoch input)

def chainStep (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (epoch : Epoch) (chain : ChainIndex) (position : Nat) (value : Digest) : Digest :=
  if hposition : position < chainLength - 1 then
    digestAt cache (chainInput parameter epoch chain ⟨position, hposition⟩ value)
  else
    0

def leafHash (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (epoch : Epoch) (endpoints : ChainIndex → Digest) : Digest :=
  digestAt cache (leafInput parameter epoch endpoints)

def merkleHash (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (level : MerkleLevel) (node : MerkleNode) (left right : Digest) : Digest :=
  digestAt cache (merkleInput parameter level node left right)

def nodeIndex (epoch : Epoch) (level : Nat) : MerkleNode :=
  ⟨epoch.val / 2 ^ (level + 1), by
    have hle := Nat.div_le_self epoch.val (2 ^ (level + 1))
    exact hle.trans_lt epoch.isLt⟩

def authenticationNodePayload (epoch : Epoch) (level : Nat)
    (current sibling : Digest) : HashInput :=
  if epoch.val.testBit level then
    Concrete.nodePayload sibling current
  else
    Concrete.nodePayload current sibling

def nodeInput (parameter : PublicParameter) (epoch : Epoch) (level : MerkleLevel)
    (current sibling : Digest) : HashInput :=
  XmssSecurity.tweakableHashInput parameter (.merkle level (nodeIndex epoch level.val))
    (authenticationNodePayload epoch level.val current sibling)

def nodeHash (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (epoch : Epoch) (level : Nat) (left right : Digest) : Digest :=
  if hlevel : level < treeHeight then
    digestAt cache (nodeInput parameter epoch ⟨level, hlevel⟩ left right)
  else
    0

end XmssSecurity.Concrete.CacheView
