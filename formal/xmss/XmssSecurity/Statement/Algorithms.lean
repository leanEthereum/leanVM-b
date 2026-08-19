import XmssSecurity.Statement.Spec
import VCVio.OracleComp.Constructions.BitVec
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.ProbCompLift
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import VCVio.OracleComp.QueryTracking.CachingOracle
import VCVio.OracleComp.QueryTracking.LoggingOracle

/-!
# The XMSS instance, algorithms

The three algorithms of the scheme, exactly as run in the security experiment: key generation, signing, and verification, together with the oracle hash calls they make.

The secret key is the ideal precomputed key from the specification: it contains every Winternitz chain value and every Merkle node. `Concrete.precomputedKeygen` obtains those values through the random oracle by computing the Merkle root, then stores them as the pure replay of its own query log (`CacheView`, `CacheReplay`). Reading them while signing is local computation and therefore does not count as a random-oracle query. `Concrete.precomputedCappedSign` performs at most `2^23` encoding attempts, each sampling 192 fresh bits and querying the random oracle once; `Concrete.verify` is the ordinary XMSS verifier.
-/

open OracleComp OracleSpec

namespace XmssSecurity

/-- A hash query takes an arbitrary byte string and returns 32 bytes. -/
abbrev HashSpec := HashInput →ₒ HashOutput

/-- The algorithms may sample uniform values or query the shared random oracle. Uniform sampling is kept separate because it is not charged as a hash query. -/
abbrev OracleWorld := unifSpec + HashSpec

namespace Concrete

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

/-! Pure recomputation of the same hash calls from a query cache. Key generation uses this below to define the stored tables as the replay of its own oracle queries. -/

namespace CacheView

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

end CacheView

/-! Verification. -/

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

/-! Key generation. -/

noncomputable local instance : SampleableType PublicParameter :=
  SampleableType.ofFintype PublicParameter

noncomputable local instance : SampleableType (Epoch → ChainIndex → Digest) :=
  SampleableType.ofFintype (Epoch → ChainIndex → Digest)

def oneTimePublicKey {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) : m (ChainIndex → Digest) :=
  sequenceFin fun chain =>
    chainWalk parameter epoch chain 0 (chainLength - 1) (secret epoch chain)

def leafAt {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) : m Digest := do
  let endpoints ← oneTimePublicKey parameter secret epoch
  leafHash parameter epoch endpoints

def merkleNodeOfNat (value : Nat) : MerkleNode :=
  ⟨value % lifetime,
    Nat.mod_lt _ (by simp [lifetime])⟩

def childNode (node : MerkleNode) (right : Bool) : MerkleNode :=
  merkleNodeOfNat (2 * node.val + if right then 1 else 0)

def treeNode {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest) :
    Nat → MerkleNode → m Digest
  | 0, node => leafAt parameter secret node
  | levels + 1, node => do
      let left ← treeNode parameter secret levels (childNode node false)
      let right ← treeNode parameter secret levels (childNode node true)
      if hlevel : levels < treeHeight then
        nodeHash parameter ⟨levels, hlevel⟩ node left right
      else
        pure 0

attribute [irreducible] treeNode

def rootNode : MerkleNode :=
  ⟨0, by simp [lifetime]⟩

noncomputable def samplePublicParameter : ProbComp PublicParameter :=
  $ᵗ PublicParameter

noncomputable def sampleSecret : ProbComp (Epoch → ChainIndex → Digest) :=
  $ᵗ (Epoch → ChainIndex → Digest)

attribute [irreducible] samplePublicParameter sampleSecret

namespace CacheReplay

def oneTimePublicKey (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) (epoch : Epoch) : ChainIndex → Digest :=
  fun chain => Wots.walk (CacheView.chainStep cache parameter epoch chain) 0
    (chainLength - 1) (secret epoch chain)

def leafAt (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) (epoch : Epoch) : Digest :=
  CacheView.leafHash cache parameter epoch
    (oneTimePublicKey cache parameter secret epoch)

def treeNode (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) : Nat → MerkleNode → Digest
  | 0, node => leafAt cache parameter secret node
  | levels + 1, node =>
      if hlevel : levels < treeHeight then
        CacheView.merkleHash cache parameter ⟨levels, hlevel⟩ node
          (treeNode cache parameter secret levels (Concrete.childNode node false))
          (treeNode cache parameter secret levels (Concrete.childNode node true))
      else
        0

attribute [irreducible] treeNode

end CacheReplay

end Concrete

def extendHashCacheWithLog (initialCache : QueryCache HashSpec) :
    QueryLog HashSpec → QueryCache HashSpec
  | [] => initialCache
  | ⟨input, output⟩ :: tail =>
      extendHashCacheWithLog (initialCache.cacheQuery input output) tail

def hashCacheOfLog (log : QueryLog HashSpec) : QueryCache HashSpec :=
  extendHashCacheWithLog ∅ log

namespace Concrete

def precomputedSecretKey (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) (cache : QueryCache HashSpec) :
    SecretKey where
  parameter := parameter
  chainStart := secret
  chainValue := fun epoch chain digit =>
    Wots.walk (CacheView.chainStep cache parameter epoch chain) 0 digit.val
      (secret epoch chain)
  treeValue := fun height node =>
    CacheReplay.treeNode cache parameter secret height.val node

noncomputable def precomputedKeygen :
    OracleComp OracleWorld (PublicKey × SecretKey) := do
  let parameter ← liftM samplePublicParameter
  let secret ← liftM sampleSecret
  let result ← liftM
    (treeNode parameter secret treeHeight rootNode :
      OracleComp HashSpec Digest).withQueryLog
  let cache := hashCacheOfLog result.2
  return (⟨result.1, parameter⟩, precomputedSecretKey parameter secret cache)

attribute [irreducible] precomputedKeygen

/-! Signing. -/

noncomputable local instance : SampleableType Randomness :=
  SampleableType.ofFintype Randomness

noncomputable def signingRandomness : ProbComp Randomness :=
  $ᵗ Randomness

attribute [irreducible] signingRandomness

def authenticationPathNode (epoch : Epoch) (level : MerkleLevel) : MerkleNode :=
  merkleNodeOfNat (Nat.xor (epoch.val / 2 ^ level.val) 1)

def precomputedSignedChainValues (secretKey : SecretKey) (epoch : Epoch)
    (encoding : Encoding) : ChainIndex → Digest :=
  fun chain => secretKey.chainValue epoch chain (encoding chain)

def precomputedAuthenticationPath (secretKey : SecretKey) (epoch : Epoch) :
    Fin treeHeight → Digest :=
  fun level => secretKey.treeValue ⟨level.val, by omega⟩
    (authenticationPathNode epoch level)

def precomputedSignWithEncoding (secretKey : SecretKey) (epoch : Epoch)
    (randomness : Randomness) (encoding : Encoding) : Signature :=
  ⟨randomness, precomputedSignedChainValues secretKey epoch encoding,
    precomputedAuthenticationPath secretKey epoch⟩

noncomputable def precomputedSignAttempt {m : Type → Type} [Monad m]
    [HasQuery HashSpec m] (secretKey : SecretKey) (epoch : Epoch)
    (message : Message) (randomness : Randomness) : m (Option Signature) := do
  let digest ← encodingHash secretKey.parameter epoch message randomness
  match TargetSum.decodeDigest digest with
  | none => pure none
  | some encoding =>
      pure (some (precomputedSignWithEncoding secretKey epoch randomness encoding))

noncomputable def precomputedSignBoundedAttempts :
    Nat → SecretKey → Epoch → Message →
      OracleComp OracleWorld (Option Signature)
  | 0, _secretKey, _epoch, _message => pure none
  | attempts + 1, secretKey, epoch, message => do
      let randomness ← liftM signingRandomness
      let result ← liftM
        (precomputedSignAttempt secretKey epoch message randomness :
          OracleComp HashSpec (Option Signature))
      match result with
      | some signature => pure (some signature)
      | none => precomputedSignBoundedAttempts attempts secretKey epoch message

noncomputable def precomputedCappedSign (_publicKey : PublicKey)
    (secretKey : SecretKey) (epoch : Epoch) (message : Message) :
    OracleComp OracleWorld (Option Signature) :=
  precomputedSignBoundedAttempts signingAttemptLimit secretKey epoch message

attribute [irreducible] precomputedCappedSign

end Concrete

end XmssSecurity
