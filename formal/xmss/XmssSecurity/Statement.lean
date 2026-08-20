import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Classical random-oracle security of the concrete XMSS instance

This single module is the reviewer-facing statement of the formalization. It contains everything the statement depends on: the concrete parameters and types, the byte layout of every hash input, the three algorithms exactly as run in the security experiment, the strong-unforgeability experiment, and the security claim `XmssSecurityStatement`. Nothing here imports proof machinery, and nothing below describes a reduction or an intermediate game. The theorem itself is stated and proved in the root module `XmssSecurity`.

The concrete instance has 32-byte messages, 32-bit epochs, 128-bit digests, a 256-bit random-oracle output truncated to 128 bits, 42 Winternitz chains of length 8, and a Merkle tree of height 32.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

/-! ## The instance: parameters, types, and hash-input layout -/

def digestBits : Nat := 128
def hashOutputBits : Nat := 256
def messageBits : Nat := 256
def publicParameterBits : Nat := 128
def randomnessBits : Nat := 192
def signingAttemptLimit : Nat := 2 ^ 23
def treeHeight : Nat := 32
def lifetime : Nat := 2 ^ treeHeight
def winternitzBits : Nat := 3
def chainLength : Nat := 2 ^ winternitzBits
def numChains : Nat := 42
def targetSum : Nat := 195

abbrev Digest := BitVec digestBits
abbrev HashOutput := BitVec hashOutputBits
abbrev Message := BitVec messageBits
abbrev PublicParameter := BitVec publicParameterBits
abbrev Randomness := BitVec randomnessBits
abbrev Epoch := Fin lifetime
abbrev ChainIndex := Fin numChains
abbrev Digit := Fin chainLength
abbrev MerkleHeight := Fin (treeHeight + 1)
abbrev MerkleNode := Fin lifetime
abbrev Encoding := ChainIndex → Digit
abbrev HashInput := List UInt8

/-- Keep the first 128 output bits, represented as the low bits of the little-endian bit vector. -/
def truncateHash (output : HashOutput) : Digest :=
  output.extractLsb' 0 digestBits

structure PublicKey where
  root : Digest
  parameter : PublicParameter
deriving DecidableEq

structure SecretKey where
  parameter : PublicParameter
  chainStart : Epoch → ChainIndex → Digest
  chainValue : Epoch → ChainIndex → Digit → Digest
  treeValue : MerkleHeight → MerkleNode → Digest

structure Signature where
  randomness : Randomness
  chainValue : ChainIndex → Digest
  authPath : Fin treeHeight → Digest
deriving DecidableEq

/-- Serialize a bit vector into a fixed number of bytes, least significant byte first. -/
def bytesLE (byteCount : Nat) (value : BitVec (8 * byteCount)) : List UInt8 :=
  List.ofFn fun index : Fin byteCount =>
    UInt8.ofBitVec (value.extractLsb' (8 * index.val) 8)

structure TweakFields where
  tag : BitVec 8
  position : BitVec 32
  epoch : BitVec 32
deriving DecidableEq

/-- The specification's 16 tweak bytes `tag || position || epoch || 0^7`, each field serialized least significant byte first. -/
def fieldBytes (fields : TweakFields) : List UInt8 :=
  bytesLE 1 fields.tag ++ bytesLE 4 fields.position ++ bytesLE 4 fields.epoch ++
    List.replicate 7 0

abbrev ChainStep := Fin (chainLength - 1)
abbrev MerkleLevel := Fin treeHeight

/-- Every domain-separated hash call made by the concrete XMSS instance. -/
inductive HashDomain where
  | chain (epoch : Epoch) (chain : ChainIndex) (step : ChainStep)
  | leaf (epoch : Epoch)
  | merkle (level : MerkleLevel) (node : MerkleNode)
  | encoding (epoch : Epoch)
deriving DecidableEq

/-- Serialize a typed hash domain into the fields of an XMSS tweak. -/
def hashDomainFields : HashDomain → TweakFields
  | .chain epoch chain step =>
      ⟨0#8, BitVec.ofNat 32 (chainLength * chain.val + step.val), BitVec.ofNat 32 epoch.val⟩
  | .leaf epoch => ⟨1#8, 0#32, BitVec.ofNat 32 epoch.val⟩
  | .merkle level node =>
      ⟨2#8, BitVec.ofNat 32 (level.val + 1), BitVec.ofNat 32 node.val⟩
  | .encoding epoch => ⟨3#8, 0#32, BitVec.ofNat 32 epoch.val⟩

/-- The exact 16 bytes supplied by the specification as a hash tweak. -/
def tweakBytes (domain : HashDomain) : List UInt8 :=
  fieldBytes (hashDomainFields domain)

/-- The random-oracle input `tweak || parameter || message` used by every tweakable hash call. -/
def tweakableHashInput (parameter : PublicParameter) (domain : HashDomain)
    (message : HashInput) : HashInput :=
  tweakBytes domain ++ bytesLE 16 parameter ++ message

namespace TargetSum

def sum (x : Encoding) : Nat := ∑ i, (x i).val

def Valid (x : Encoding) : Prop := sum x = targetSum

instance : DecidablePred Valid :=
  fun x => inferInstanceAs (Decidable (sum x = targetSum))

def digitsPerHalf : Nat := numChains / 2

/-- Offset of a three-bit digit, skipping padding bits 63 and 127. -/
def digitOffset (i : ChainIndex) : Nat :=
  winternitzBits * i.val + if i.val < digitsPerHalf then 0 else 1

def digestEncoding (digest : Digest) : Encoding :=
  fun i => (digest.extractLsb' (digitOffset i) winternitzBits).toFin

/-- Decode the concrete little-endian layout used by `IncEnc`: 21 three-bit digits, padding bit 63, 21 digits, and padding bit 127. A digest decodes exactly when both padding bits are clear and the digits reach the target sum. -/
def decodeDigest (digest : Digest) : Option Encoding :=
  if digest.getLsbD 63 = false ∧ digest.getLsbD 127 = false ∧ Valid (digestEncoding digest)
  then some (digestEncoding digest) else none

end TargetSum

/-! ## The algorithms

The three algorithms of the scheme, exactly as run in the security experiment: key generation, signing, and verification, together with the oracle hash calls they make.

The secret key is the ideal precomputed key from the specification: it contains every Winternitz chain value and every Merkle node. `Concrete.precomputedKeygen` obtains those values through the random oracle by computing the Merkle root, then stores them as the pure replay of its own query log: each stored table entry is the same oracle computation evaluated again, with every hash query answered from the recorded cache (`replayHash`). Reading them while signing is local computation and therefore does not count as a random-oracle query. `Concrete.precomputedCappedSign` performs at most `2^23` encoding attempts, each sampling 192 fresh bits and querying the random oracle once; `Concrete.verify` is the ordinary XMSS verifier.

The `irreducible` attributes in this section only seal definitions against accidental unfolding in proofs; they change no definition. Lean restricts global reducibility attributes to the defining module, so they must appear here. -/

/-- A hash query takes an arbitrary byte string and returns 32 bytes. -/
abbrev HashSpec := HashInput →ₒ HashOutput

/-- `unifSpec` for uniform sampling, `HashSpec` for the random oracle (hash). A query is `.inl` to sample or `.inr` to hash, so `HasHashQueryBound` counts only the hash side. -/
abbrev OracleWorld := unifSpec + HashSpec

def extendHashCacheWithLog (initialCache : QueryCache HashSpec) :
    QueryLog HashSpec → QueryCache HashSpec
  | [] => initialCache
  | ⟨input, output⟩ :: tail =>
      extendHashCacheWithLog (initialCache.cacheQuery input output) tail

def hashCacheOfLog (log : QueryLog HashSpec) : QueryCache HashSpec :=
  extendHashCacheWithLog ∅ log

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

/-- The index of the Merkle node on the path of `epoch` one level above `level`. -/
def nodeIndex (epoch : Epoch) (level : Nat) : MerkleNode :=
  ⟨epoch.val / 2 ^ (level + 1), by
    have hle := Nat.div_le_self epoch.val (2 ^ (level + 1))
    exact hle.trans_lt epoch.isLt⟩

def authenticationNodeHash {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (epoch : Epoch)
    (level : Nat) (current sibling : Digest) : m Digest :=
  if hlevel : level < treeHeight then
    if epoch.val.testBit level then
      nodeHash parameter ⟨level, hlevel⟩ (nodeIndex epoch level) sibling current
    else
      nodeHash parameter ⟨level, hlevel⟩ (nodeIndex epoch level) current sibling
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

def verify {m : Type → Type} [Monad m] [HasQuery HashSpec m]
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

/-- Answer a hash query from a recorded query cache, and by 0 for an unrecorded input. -/
def replayHash (cache : QueryCache HashSpec) : QueryImpl HashSpec Id :=
  fun input => (cache input).getD 0

/-- The ideal precomputed secret key. Every stored table entry is the corresponding oracle computation from this module, replayed against the recorded key-generation cache. -/
def precomputedSecretKey (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) (cache : QueryCache HashSpec) :
    SecretKey where
  parameter := parameter
  chainStart := secret
  chainValue := fun epoch chain digit =>
    evalWithAnswerFn (replayHash cache)
      (chainWalk parameter epoch chain 0 digit.val (secret epoch chain) :
        OracleComp HashSpec Digest)
  treeValue := fun height node =>
    evalWithAnswerFn (replayHash cache)
      (treeNode parameter secret height.val node : OracleComp HashSpec Digest)

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
  fun level => secretKey.treeValue level.castSucc (authenticationPathNode epoch level)

def precomputedSignWithEncoding (secretKey : SecretKey) (epoch : Epoch)
    (randomness : Randomness) (encoding : Encoding) : Signature :=
  ⟨randomness, precomputedSignedChainValues secretKey epoch encoding,
    precomputedAuthenticationPath secretKey epoch⟩

def precomputedSignAttempt {m : Type → Type} [Monad m]
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

noncomputable def precomputedCappedSign (secretKey : SecretKey)
    (epoch : Epoch) (message : Message) :
    OracleComp OracleWorld (Option Signature) :=
  precomputedSignBoundedAttempts signingAttemptLimit secretKey epoch message

attribute [irreducible] precomputedCappedSign

end Concrete

/-! ## The security experiment -/

/-- The random-oracle semantics: hash queries are answered lazily and consistently by uniform sampling and cached; uniform-sampling queries are forwarded unchanged. -/
noncomputable def romImpl : QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp) :=
  unifFwdImpl HashSpec +
    (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))

/-- A signing request contains a 32-bit epoch and a 32-byte message. -/
structure SignRequest where
  epoch : Epoch
  message : Message
deriving DecidableEq

/-- A claimed forgery: an epoch, a message, and a signature. -/
structure Forgery where
  epoch : Epoch
  message : Message
  signature : Signature
deriving DecidableEq

def Forgery.request (forgery : Forgery) : SignRequest :=
  ⟨forgery.epoch, forgery.message⟩

/-- The interface of a synchronized signature scheme in the random-oracle experiment. -/
structure Scheme where
  keygen : OracleComp OracleWorld (PublicKey × SecretKey)
  sign : SecretKey → Epoch → Message → OracleComp OracleWorld (Option Signature)
  verify : PublicKey → Epoch → Message → Signature → OracleComp OracleWorld Bool

/-- The signing oracle answers a request with either a signature or `none` if the signer fails. -/
abbrev SigningSpec := SignRequest →ₒ Option Signature

/-- A classical adaptive adversary. After receiving the public key, it may query the shared random oracle, request signatures, and finally return a claimed forgery. -/
structure Adversary where
  main : PublicKey → OracleComp (OracleWorld + SigningSpec) Forgery

namespace SigningTranscript

/-- A signing transcript is valid exactly when no epoch occurs twice. Thus the adversary may make adaptive signing requests, but may not request two signatures at the same epoch. -/
def Valid (log : QueryLog SigningSpec) : Prop :=
  (log.map fun entry => entry.1.epoch).Nodup

instance (log : QueryLog SigningSpec) : Decidable (Valid log) :=
  inferInstanceAs (Decidable ((log.map fun entry => entry.1.epoch).Nodup))

/-- The signer returned the claimed forgery exactly when the transcript contains the same epoch, message, and signature. A different signature for a signed message is therefore a valid strong forgery. -/
def Contains (log : QueryLog SigningSpec) (forgery : Forgery) : Prop :=
  ∃ entry ∈ log, entry.1 = forgery.request ∧ entry.2 = some forgery.signature

instance (log : QueryLog SigningSpec) (forgery : Forgery) : Decidable (Contains log forgery) :=
  inferInstanceAs
    (Decidable (∃ entry ∈ log, entry.1 = forgery.request ∧ entry.2 = some forgery.signature))

end SigningTranscript

/-- The signing oracle used in the game. It records every request and response while forwarding the request to the scheme's signer. -/
def signingOracle (scheme : Scheme) (sk : SecretKey) :
    QueryImpl SigningSpec (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  QueryImpl.withLogging fun request => scheme.sign sk request.epoch request.message

/-- Forward the shared random oracle and uniform sampling to the adversary unchanged, alongside the logged signing oracle. -/
def forwardOracles :
    QueryImpl OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  fun input => liftM (OracleWorld.query input)

/-- The complete strong-unforgeability experiment.

The random oracle is sampled lazily by the semantics of `OracleWorld`. Key generation, the adversary, the signing oracle, and final verification all share the same oracle. The game returns `true` precisely when the signing transcript uses every epoch at most once, the claimed forgery is not an exact replay, and the signature verifies. -/
noncomputable def gameCore (scheme : Scheme) (adversary : Adversary) :
    OracleComp OracleWorld Bool := do
  let (pk, sk) ← scheme.keygen
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (forwardOracles + signingOracle scheme sk) (adversary.main pk)).run
  let verified ← scheme.verify pk forgery.epoch forgery.message forgery.signature
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

/-- The probability that the adversary wins, over key generation, signer randomness, and the random oracle, which starts from the empty cache. The final cache is discarded. -/
noncomputable def forgeAdvantage (scheme : Scheme) (adversary : Adversary) : ℝ≥0∞ :=
  Pr[= true | (simulateQ romImpl (gameCore scheme adversary)).run' ∅]

/-- The whole experiment makes at most `q` random-oracle queries on every execution path. The count includes queries during key generation, adversarial hashing, signing, and final verification. Uniform sampling operations are not hash queries. -/
def HasHashQueryBound (scheme : Scheme) (adversary : Adversary) (q : Nat) : Prop :=
  (gameCore scheme adversary).IsQueryBoundP (· matches .inr _) q

/-- Having `bits` bits of classical security means that every classical adaptive adversary whose complete experiment stays within a nonzero hash-query budget `q` forges with probability at most `q / 2^bits`. -/
def HasClassicalSecurityBits (scheme : Scheme) (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary, HasHashQueryBound scheme adversary q →
    forgeAdvantage scheme adversary ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)

/-- The concrete XMSS scheme: the precomputed key generation, the capped retry signer, and the ordinary verifier defined above. -/
noncomputable def Concrete.scheme : Scheme where
  keygen := Concrete.precomputedKeygen
  sign := Concrete.precomputedCappedSign
  verify := fun publicKey epoch message signature =>
    liftM (Concrete.verify publicKey epoch message signature : OracleComp HashSpec Bool)

/-- The complete public security claim. -/
abbrev XmssSecurityStatement : Prop :=
  HasClassicalSecurityBits Concrete.scheme 127

end XmssSecurity
