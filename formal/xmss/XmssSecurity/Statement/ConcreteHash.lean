import XmssSecurity.Statement.Scheme
import XmssSecurity.Statement.Serialization

open OracleComp OracleSpec

namespace XmssSecurity.Concrete

def digestBytes (value : Digest) : HashInput :=
  bytesLE 16 value

def messageBytes (message : Message) : HashInput :=
  bytesLE 32 message

def randomnessBytes (randomness : Randomness) : HashInput :=
  bytesLE 24 randomness

def encodingPayload (message : Message) (randomness : Randomness) : HashInput :=
  messageBytes message ++ randomnessBytes randomness ++ List.replicate 8 0

def leafPayload (endpoints : ChainIndex → Digest) : HashInput :=
  (List.ofFn endpoints).flatMap digestBytes

def nodePayload (left right : Digest) : HashInput :=
  digestBytes left ++ digestBytes right

def oracleHash {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (input : HashInput) : m HashOutput :=
  HasQuery.query (spec := HashSpec) (m := m) input

def tweakableHash {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) : m Digest := do
  let output ← oracleHash (tweakableHashInput parameter domain payload)
  return truncateHash output

def encodingHash {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (epoch : Epoch)
    (message : Message) (randomness : Randomness) : m Digest :=
  tweakableHash parameter (.encoding epoch) (encodingPayload message randomness)

def chainHash {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) : m Digest :=
  tweakableHash parameter (.chain epoch chain step) (digestBytes value)

def leafHash {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (epoch : Epoch)
    (endpoints : ChainIndex → Digest) : m Digest :=
  tweakableHash parameter (.leaf epoch) (leafPayload endpoints)

def nodeHash {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (level : MerkleLevel) (node : MerkleNode)
    (left right : Digest) : m Digest :=
  tweakableHash parameter (.merkle level node) (nodePayload left right)

end XmssSecurity.Concrete
