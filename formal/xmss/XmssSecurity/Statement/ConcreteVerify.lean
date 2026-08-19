import XmssSecurity.Statement.CacheView

open OracleComp

namespace XmssSecurity.Concrete

def signaturePath (signature : Signature) (level : Nat) : Digest :=
  if hlevel : level < treeHeight then
    signature.authPath ⟨level, hlevel⟩
  else
    0

def sequenceFin {m : Type → Type} [Monad m] {n : Nat}
    (computation : Fin n → m α) : m (Fin n → α) :=
  match n with
  | 0 => pure Fin.elim0
  | n + 1 => do
      let head ← computation 0
      let tail ← sequenceFin fun index : Fin n => computation index.succ
      return Fin.cases head tail

def chainWalk {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex) :
    Nat → Nat → Digest → m Digest
  | _, 0, value => pure value
  | position, steps + 1, value => do
      let previous ← chainWalk parameter epoch chain position steps value
      if hposition : position + steps < chainLength - 1 then
        chainHash parameter epoch chain ⟨position + steps, hposition⟩ previous
      else
        pure 0

def recoverChain {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (digit : Digit) (value : Digest) : m Digest :=
  chainWalk parameter epoch chain digit.val (chainLength - 1 - digit.val) value

def recoverEndpoints {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (epoch : Epoch)
    (encoding : Encoding) (signature : Signature) :
    m (ChainIndex → Digest) :=
  sequenceFin fun chain =>
    recoverChain parameter epoch chain (encoding chain) (signature.chainValue chain)

def authenticationNodeHash {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (epoch : Epoch)
    (level : Nat) (current sibling : Digest) : m Digest :=
  if hlevel : level < treeHeight then
    if epoch.val.testBit level then
      nodeHash parameter ⟨level, hlevel⟩ (CacheView.nodeIndex epoch level) sibling current
    else
      nodeHash parameter ⟨level, hlevel⟩ (CacheView.nodeIndex epoch level) current sibling
  else
    pure 0

def authenticationRoot {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (epoch : Epoch)
    (signature : Signature) : Nat → Digest → m Digest
  | 0, leaf => pure leaf
  | levels + 1, leaf => do
      let current ← authenticationRoot parameter epoch signature levels leaf
      authenticationNodeHash parameter epoch levels current (signaturePath signature levels)

def verifyAfterLeaf {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (publicKey : PublicKey) (epoch : Epoch) (signature : Signature) (leaf : Digest) : m Bool := do
  let root ← authenticationRoot publicKey.parameter epoch signature treeHeight leaf
  return decide (root = publicKey.root)

attribute [irreducible] verifyAfterLeaf

noncomputable def verify {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (publicKey : PublicKey) (epoch : Epoch)
    (message : Message) (signature : Signature) : m Bool := do
  let digest ← encodingHash publicKey.parameter epoch message signature.randomness
  match TargetSum.decodeDigest digest with
  | none => pure false
  | some encoding => do
      let endpoints ← recoverEndpoints publicKey.parameter epoch encoding signature
      let leaf ← leafHash publicKey.parameter epoch endpoints
      verifyAfterLeaf publicKey epoch signature leaf

end XmssSecurity.Concrete
