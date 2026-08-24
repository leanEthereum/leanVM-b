import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Classical random-oracle security of the concrete SPHINCS instance

This single module is the reviewer-facing statement of what has to be proven. It contains everything the statement depends on: the concrete parameters and types, the byte layout of every hash input, the three algorithms exactly as run in the security experiment, the strong-unforgeability experiment, and the security claim `SphincsSecurityStatement`. Nothing here describes a reduction or an intermediate game, and nothing instantiates the hash: it is a random oracle throughout. What the concrete parameters fix about the layout is proven rather than asserted, each lemma sitting next to the definitions it concerns: the index decomposition of Section `The index`, and the authentication path next to `flattenPaths`.

The instance is the one specified in `doc/sphincs/main.tex`: 32-byte messages, 128-bit digests truncated from a 256-bit random-oracle output, 42 Winternitz chains of length 8 at target sum 191, a hypertree of height 26 over 3 layers of heights 12, 7 and 7, and a few-time forest of 14 trees of `2^10` leaves selected by a 176-bit message digest. A key answers for all `2^26` indices and signs at most `2^24` messages.

Three things differ from `formal/xmss`. The signer takes no epoch, this scheme being stateless, so a signing request is a message alone and what the game caps is the number of signing queries, at `signatureLimit`. Signing is randomized, a fresh `randomnessBits` string per digest attempt, so a message has many valid signatures and a second one on a signed message is a strong forgery. And the secret key holds the sampled secrets rather than precomputed tables, so signing recomputes through the random oracle whatever tree it reads, exactly as `Sig` is specified.

The claim is `120` bits and not `128`. Every strategy the specification accounts for costs `2^-128` per query, and the bound is a slope `q / 2^120`, so `2^8` of slack absorbs the union bounds and the constants a proof accumulates, uniformly in `q`. The few-time leak is a per-query slope too, `2^-133.3` at `q_s = 2^24`, so it does not bind, but it is what fixes `signatureLimit`: it reaches `2^-128` at `2^25.1` signatures and `2^-120` at `2^26.4`, leaving about two doublings of headroom. `HasHashQueryBound` bounds every execution path, so `digestAttemptLimit` and `encodingAttemptLimit` put the admissible floor near `q = 2^58` even though a signature costs `2^20.5` on average, and the claim is read there.
-/

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity

/-! ## The instance: parameters, types, and hash-input layout -/

def digestBits : Nat := 128
def hashOutputBits : Nat := 256
def messageBits : Nat := 256
def publicParameterBits : Nat := 128
def randomnessBits : Nat := 128
def counterBits : Nat := 32
def winternitzBits : Nat := 3
def chainLength : Nat := 2 ^ winternitzBits
def numChains : Nat := 42
def targetSum : Nat := 191
def numLayers : Nat := 3
def totalHeight : Nat := 26
/-- The tallest layer, `h_0`, which bounds every layer's leaf index. -/
def maxLayerHeight : Nat := 12
def ftsTreeHeight : Nat := 10
/-- The `k` index groups a digest carries. The forest holds `k - 1` trees, the last group being pinned to zero. -/
def ftsTrees : Nat := 15
/-- Signatures allowed per key pair, `q_s`. -/
def signatureLimit : Nat := 2 ^ 24
/-- Digest attempts per signature, `A_max`. -/
def digestAttemptLimit : Nat := 2 ^ 32
/-- Encoding counters tried per layer, `C_max`. -/
def encodingAttemptLimit : Nat := 2 ^ 32
/-- The claimed security level. -/
def securityBits : Nat := 120

abbrev Digest := BitVec digestBits
abbrev HashOutput := BitVec hashOutputBits
abbrev Message := BitVec messageBits
abbrev PublicParameter := BitVec publicParameterBits
abbrev Randomness := BitVec randomnessBits
abbrev Counter := BitVec counterBits
abbrev Layer := Fin numLayers
abbrev Index := Fin (2 ^ totalHeight)
abbrev TreeIndex := Fin (2 ^ totalHeight)
abbrev LeafIndex := Fin (2 ^ maxLayerHeight)
abbrev ChainIndex := Fin numChains
abbrev Digit := Fin chainLength
abbrev ChainStep := Fin (chainLength - 1)
/-- A tree of the few-time forest, `kappa < k - 1`. -/
abbrev FtsTree := Fin (ftsTrees - 1)
/-- An index group of the message digest, `kappa < k`. -/
abbrev DigestTree := Fin ftsTrees
abbrev FtsLeaf := Fin (2 ^ ftsTreeHeight)
/-- A position in the signature's authentication path, the `h` nodes of the `d` layers concatenated top layer first. -/
abbrev PathIndex := Fin totalHeight
abbrev Encoding := ChainIndex → Digit
abbrev HashInput := List UInt8

/-- The `d` Merkle heights, `(h_0, h_1, h_2) = (12, 7, 7)`. Layer `0` carries the public key. -/
def layerHeight (lay : Layer) : Nat := if lay.val = 0 then maxLayerHeight else 7

def topLayer : Layer := ⟨0, by decide⟩
def middleLayer : Layer := ⟨1, by decide⟩
def bottomLayer : Layer := ⟨numLayers - 1, by decide⟩

/-- `sum_{j < lay} h_j`, the index bits above layer `lay`. -/
def heightAbove (lay : Layer) : Nat := ∑ j : Layer, if j.val < lay.val then layerHeight j else 0

/-- `sum_{j > lay} h_j`, the index bits below layer `lay`. -/
def heightBelow (lay : Layer) : Nat := totalHeight - heightAbove lay - layerHeight lay

example : ∑ lay : Layer, layerHeight lay = totalHeight := by decide

example : (layerHeight topLayer, layerHeight middleLayer, layerHeight bottomLayer) = (12, 7, 7) := by
  decide

example : (heightAbove topLayer, heightAbove middleLayer, heightAbove bottomLayer) = (0, 12, 19) := by
  decide

example : (heightBelow topLayer, heightBelow middleLayer, heightBelow bottomLayer) = (14, 7, 0) := by
  decide

theorem layerHeight_le (lay : Layer) : layerHeight lay ≤ maxLayerHeight := by
  unfold layerHeight maxLayerHeight
  split <;> omega

/-- Keep the first 128 output bits, the low bits of the little-endian bit vector. -/
def truncateHash (output : HashOutput) : Digest :=
  output.extractLsb' 0 digestBits

/-- The message digest is `h + k * a = 176` bits, an index and `k` leaf indices. -/
def messageDigestBits : Nat := totalHeight + ftsTrees * ftsTreeHeight

abbrev MessageDigest := BitVec messageDigestBits

/-- The digest is `h + k * a = 176` bits and has to fit in one oracle output. -/
example : messageDigestBits = 176 ∧ messageDigestBits ≤ hashOutputBits := by decide

def truncateMessageDigest (output : HashOutput) : MessageDigest :=
  output.extractLsb' 0 messageDigestBits

structure PublicKey where
  root : Digest
  parameter : PublicParameter
deriving DecidableEq

/-- The key of the specification: the public parameter, the layer-`0` root that every digest binds, and every sampled secret. `Gen` samples them independently and uniformly; the seed derivation of the specification is an implementation of this key, not this key. -/
structure SecretKey where
  parameter : PublicParameter
  root : Digest
  otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest
  ftsSecret : Index → FtsTree → FtsLeaf → Digest

/-- A signature, with every component the verifier reads and no other: the randomizer, one few-time secret and its `a` path nodes per held tree, and per layer a counter, `v` chain values, and its share of the `h` path nodes. That is `16 + 14 * 16 + 140 * 16 + 3 * 4 + 126 * 16 + 26 * 16 = 4924` bytes. -/
structure Signature where
  randomness : Randomness
  ftsSecret : FtsTree → Digest
  ftsPath : FtsTree → Fin ftsTreeHeight → Digest
  counter : Layer → Counter
  chainValue : Layer → ChainIndex → Digest
  authPath : PathIndex → Digest
deriving DecidableEq

/-- Serialize a bit vector into a fixed number of bytes, least significant byte first. -/
def bytesLE (byteCount : Nat) (value : BitVec (8 * byteCount)) : List UInt8 :=
  List.ofFn fun index : Fin byteCount =>
    UInt8.ofBitVec (value.extractLsb' (8 * index.val) 8)

structure TweakFields where
  tag : BitVec 8
  layer : BitVec 8
  tree : BitVec 32
  position : BitVec 32
  index : BitVec 32
deriving DecidableEq

/-- The specification's 16 tweak bytes `tag || layer || tree || position || index || 0^2`, each field serialized least significant byte first. -/
def fieldBytes (fields : TweakFields) : HashInput :=
  bytesLE 1 fields.tag ++ bytesLE 1 fields.layer ++ bytesLE 4 fields.tree ++
    bytesLE 4 fields.position ++ bytesLE 4 fields.index ++ List.replicate 2 0

/-- Every domain-separated hash call the instance makes. Tweak types `0` and `5` of the specification are absent: they belong to the seed derivation, and this key samples its secrets. -/
inductive HashDomain where
  | chain (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex) (step : ChainStep)
  | leaf (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
  | node (lay : Layer) (tree : TreeIndex) (level : Nat) (nodeIdx : Nat)
  | encoding (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
  | ftsLeaf (index : Index) (tree : FtsTree) (leaf : FtsLeaf)
  | ftsNode (index : Index) (tree : FtsTree) (level : Nat) (nodeIdx : Nat)
  | ftsRoots (index : Index)
  | message
deriving DecidableEq

/-- Serialize a typed hash domain into the fields of a tweak. Inside the hypertree the layer field is the layer and the tree field the tree; inside a few-time key they are the tree of the forest and the index that selects the instance. -/
def hashDomainFields : HashDomain → TweakFields
  | .chain lay tree leaf chainIdx step =>
      ⟨1#8, BitVec.ofNat 8 lay.val, BitVec.ofNat 32 tree.val,
        BitVec.ofNat 32 (chainLength * chainIdx.val + step.val), BitVec.ofNat 32 leaf.val⟩
  | .leaf lay tree leaf =>
      ⟨2#8, BitVec.ofNat 8 lay.val, BitVec.ofNat 32 tree.val, 0#32, BitVec.ofNat 32 leaf.val⟩
  | .node lay tree level nodeIdx =>
      ⟨3#8, BitVec.ofNat 8 lay.val, BitVec.ofNat 32 tree.val,
        BitVec.ofNat 32 level, BitVec.ofNat 32 nodeIdx⟩
  | .encoding lay tree leaf =>
      ⟨4#8, BitVec.ofNat 8 lay.val, BitVec.ofNat 32 tree.val, 0#32, BitVec.ofNat 32 leaf.val⟩
  | .ftsLeaf index tree leaf =>
      ⟨6#8, BitVec.ofNat 8 tree.val, BitVec.ofNat 32 index.val, 0#32, BitVec.ofNat 32 leaf.val⟩
  | .ftsNode index tree level nodeIdx =>
      ⟨7#8, BitVec.ofNat 8 tree.val, BitVec.ofNat 32 index.val,
        BitVec.ofNat 32 level, BitVec.ofNat 32 nodeIdx⟩
  | .ftsRoots index => ⟨8#8, 0#8, BitVec.ofNat 32 index.val, 0#32, 0#32⟩
  | .message => ⟨9#8, 0#8, 0#32, 0#32, 0#32⟩

/-- The exact 16 bytes supplied by the specification as a hash tweak. -/
def tweakBytes (domain : HashDomain) : HashInput :=
  fieldBytes (hashDomainFields domain)

/-- The random-oracle input `tweak || parameter || message` used by every tweakable hash call and by the message digest. -/
def tweakableHashInput (parameter : PublicParameter) (domain : HashDomain)
    (message : HashInput) : HashInput :=
  tweakBytes domain ++ bytesLE 16 parameter ++ message

/-! ### The target-sum code

`v = 42` chunks of `w = 3` bits, 21 in each half of the digest, one pinned bit per half, and the code is the words of digit sum `T = 191`. Two distinct words of equal sum are incomparable, which is what removes the Winternitz checksum and forces the counter. -/

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

/-- Decode the concrete little-endian layout: 21 three-bit digits, padding bit 63, 21 digits, and padding bit 127. A digest decodes exactly when both padding bits are clear and the digits reach the target sum. -/
def decodeDigest (digest : Digest) : Option Encoding :=
  if digest.getLsbD 63 = false ∧ digest.getLsbD 127 = false ∧ Valid (digestEncoding digest)
  then some (digestEncoding digest) else none

end TargetSum

/-! ## The algorithms

Key generation, signing and verification exactly as run in the experiment, together with the oracle hash calls they make. Key generation samples the parameter and every secret and builds layer `0`'s tree; signing rebuilds whatever tree it reads rather than caching anything, as specified, so the honest experiment spends `2^44.5` hash queries of its own and its worst-case path, which is what the query bound counts, `2^58`; verification is the ordinary verifier.

The `irreducible` attributes only seal definitions against accidental unfolding in proofs. Lean restricts global reducibility attributes to the defining module, so they must appear here. -/

/-- A hash query takes an arbitrary byte string and returns 32 bytes. -/
abbrev HashSpec := HashInput →ₒ HashOutput

/-- `unifSpec` for uniform sampling, `HashSpec` for the random oracle. A query is `.inl` to sample or `.inr` to hash, so `HasHashQueryBound` counts only the hash side. -/
abbrev OracleWorld := unifSpec + HashSpec

namespace Concrete

def digestBytes (value : Digest) : HashInput := bytesLE 16 value

def messageBytes (message : Message) : HashInput := bytesLE 32 message

def randomnessBytes (randomness : Randomness) : HashInput := bytesLE 16 randomness

def counterBytes (counter : Counter) : HashInput := bytesLE 4 counter

def oracleHash {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (input : HashInput) : m HashOutput :=
  HasQuery.query (spec := HashSpec) (m := m) input

def tweakableHash {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) : m Digest := do
  let output ← oracleHash (tweakableHashInput parameter domain payload)
  return truncateHash output

def sequenceFin {m : Type → Type} [Monad m] {α : Type} {n : Nat}
    (computation : Fin n → m α) : m (Fin n → α) :=
  match n with
  | 0 => pure Fin.elim0
  | n + 1 => do
      let head ← computation 0
      let tail ← sequenceFin fun index : Fin n => computation index.succ
      return Fin.cases head tail

/-- Turn a family of optional results into an optional family: the specification's `Sig` returns nothing as soon as one layer fails. -/
def traverseOption {α : Type} {n : Nat} (family : Fin n → Option α) : Option (Fin n → α) :=
  match n with
  | 0 => some Fin.elim0
  | n + 1 =>
      match family 0, traverseOption fun index : Fin n => family index.succ with
      | some head, some tail => some (Fin.cases head tail)
      | _, _ => none

/-! ### The index -/

/-- `tau_lay = floor(idx / 2^(sum_{j >= lay} h_j))`. -/
def treeIndexAt (index : Index) (lay : Layer) : TreeIndex :=
  ⟨index.val / 2 ^ (totalHeight - heightAbove lay),
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) index.isLt⟩

/-- `e_lay = floor(idx / 2^(sum_{j > lay} h_j)) mod 2^h_lay`. -/
def leafIndexAt (index : Index) (lay : Layer) : LeafIndex :=
  ⟨index.val / 2 ^ heightBelow lay % 2 ^ layerHeight lay, by
    have hmod : index.val / 2 ^ heightBelow lay % 2 ^ layerHeight lay < 2 ^ layerHeight lay :=
      Nat.mod_lt _ (Nat.two_pow_pos _)
    have hpow : 2 ^ layerHeight lay ≤ 2 ^ maxLayerHeight :=
      Nat.pow_le_pow_right (by omega) (layerHeight_le lay)
    omega⟩

theorem treeIndexAt_val (index : Index) (lay : Layer) :
    (treeIndexAt index lay).val = index.val / 2 ^ (totalHeight - heightAbove lay) := rfl

theorem leafIndexAt_val (index : Index) (lay : Layer) :
    (leafIndexAt index lay).val = index.val / 2 ^ heightBelow lay % 2 ^ layerHeight lay := rfl

/-- Layer `0` holds a single tree, the public key's. -/
theorem treeIndexAt_topLayer (index : Index) : (treeIndexAt index topLayer).val = 0 := by
  have hlt : index.val < 2 ^ 26 := index.isLt
  have h0 : totalHeight - heightAbove topLayer = 26 := by decide
  simp only [treeIndexAt_val, h0]
  omega

/-- The layers link: the tree used on a layer is the one whose root sits at leaf `e_(lay-1)` of the
tree used on the layer above. -/
theorem layers_link_top (index : Index) :
    (treeIndexAt index middleLayer).val
      = (treeIndexAt index topLayer).val * 2 ^ layerHeight topLayer
        + (leafIndexAt index topLayer).val := by
  have hlt : index.val < 2 ^ 26 := index.isLt
  have h0 : totalHeight - heightAbove topLayer = 26 := by decide
  have h1 : totalHeight - heightAbove middleLayer = 14 := by decide
  have hb : heightBelow topLayer = 14 := by decide
  have hh : layerHeight topLayer = 12 := by decide
  simp only [treeIndexAt_val, leafIndexAt_val, h0, h1, hb, hh]
  omega

theorem layers_link_middle (index : Index) :
    (treeIndexAt index bottomLayer).val
      = (treeIndexAt index middleLayer).val * 2 ^ layerHeight middleLayer
        + (leafIndexAt index middleLayer).val := by
  have h1 : totalHeight - heightAbove middleLayer = 14 := by decide
  have h2 : totalHeight - heightAbove bottomLayer = 7 := by decide
  have hb : heightBelow middleLayer = 7 := by decide
  have hh : layerHeight middleLayer = 7 := by decide
  simp only [treeIndexAt_val, leafIndexAt_val, h1, h2, hb, hh]
  omega

/-- The bottom layer's leaves are the `2^h` indices themselves. -/
theorem leafIndexAt_bottomLayer (index : Index) :
    (leafIndexAt index bottomLayer).val = index.val % 2 ^ layerHeight bottomLayer := by
  have hb : heightBelow bottomLayer = 0 := by decide
  simp [leafIndexAt_val, hb]

/-! ### The one-time signature -/

def leafOfNat (value : Nat) : LeafIndex :=
  ⟨value % 2 ^ maxLayerHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- `Chain_{lay,tau,e,i}(P, start, steps, value)`: the step onto position `start + steps + 1` carries tweak position `2^w * i + start + steps`. -/
def chainWalk {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chainIdx : ChainIndex) : Nat → Nat → Digest → m Digest
  | _, 0, value => pure value
  | start, steps + 1, value => do
      let previous ← chainWalk parameter lay tree leaf chainIdx start steps value
      if hstep : start + steps < chainLength - 1 then
        tweakableHash parameter (.chain lay tree leaf chainIdx ⟨start + steps, hstep⟩)
          (digestBytes previous)
      else
        pure 0

/-- The verifier's half of a chain: walk the remaining `2^w - 1 - x_i` steps. -/
def recoverChain {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chainIdx : ChainIndex) (digit : Digit) (value : Digest) : m Digest :=
  chainWalk parameter lay tree leaf chainIdx digit.val (chainLength - 1 - digit.val) value

def oneTimePublicKey {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (secret : ChainIndex → Digest) : m (ChainIndex → Digest) :=
  sequenceFin fun chainIdx =>
    chainWalk parameter lay tree leaf chainIdx 0 (chainLength - 1) (secret chainIdx)

def leafPayload (endpoints : ChainIndex → Digest) : HashInput :=
  (List.ofFn endpoints).flatMap digestBytes

def leafHash {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (endpoints : ChainIndex → Digest) : m Digest :=
  tweakableHash parameter (.leaf lay tree leaf) (leafPayload endpoints)

/-- `Enc(P, lay, tau, e, M, c)`: hash the message with the counter under the leaf's encoding tweak, and decode. -/
def encode {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) : m (Option Encoding) := do
  let digest ← tweakableHash parameter (.encoding lay tree leaf)
    (digestBytes message ++ counterBytes counter)
  return TargetSum.decodeDigest digest

/-- `OtsSign`: the least admissible counter, and the chain values it dictates. The search starts at `0` and stops after `encodingAttemptLimit` counters. -/
def otsSignFrom {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (secret : ChainIndex → Digest) (message : Digest) :
    Nat → Nat → m (Option (Counter × (ChainIndex → Digest)))
  | 0, _ => pure none
  | attempts + 1, counter => do
      match ← encode parameter lay tree leaf message (BitVec.ofNat counterBits counter) with
      | some encoding => do
          let values ← sequenceFin fun chainIdx =>
            chainWalk parameter lay tree leaf chainIdx 0 (encoding chainIdx).val (secret chainIdx)
          return some (BitVec.ofNat counterBits counter, values)
      | none => otsSignFrom parameter lay tree leaf secret message attempts (counter + 1)

def otsSign {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (secret : ChainIndex → Digest) (message : Digest) :
    m (Option (Counter × (ChainIndex → Digest))) :=
  otsSignFrom parameter lay tree leaf secret message encodingAttemptLimit 0

/-- `OtsLeaf`: the verifier's leaf, or nothing if the counter does not encode the message. -/
def otsLeaf {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) (values : ChainIndex → Digest) : m (Option Digest) := do
  match ← encode parameter lay tree leaf message counter with
  | none => pure none
  | some encoding => do
      let endpoints ← sequenceFin fun chainIdx =>
        recoverChain parameter lay tree leaf chainIdx (encoding chainIdx) (values chainIdx)
      let value ← leafHash parameter lay tree leaf endpoints
      return some value

/-! ### A layer -/

def nodePayload (left right : Digest) : HashInput :=
  digestBytes left ++ digestBytes right

/-- `X^{lay,tau}_{level,nodeIdx}`, the Merkle tree over the layer's one-time leaves. -/
def treeNode {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) : Nat → Nat → m Digest
  | 0, nodeIdx => do
      let leaf := leafOfNat nodeIdx
      let endpoints ← oneTimePublicKey parameter lay tree leaf (secret leaf)
      leafHash parameter lay tree leaf endpoints
  | level + 1, nodeIdx => do
      let left ← treeNode parameter lay tree secret level (2 * nodeIdx)
      let right ← treeNode parameter lay tree secret level (2 * nodeIdx + 1)
      tweakableHash parameter (.node lay tree (level + 1) nodeIdx) (nodePayload left right)

attribute [irreducible] treeNode

def treeRoot {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) : m Digest :=
  treeNode parameter lay tree secret (layerHeight lay) 0

/-- `TreePath`: `A_level = X^{lay,tau}_{level, floor(e / 2^level) xor 1}` for the layer's own `h_lay` levels, and nothing above them. -/
def treePath {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex) : m (Fin maxLayerHeight → Digest) :=
  sequenceFin fun level =>
    if level.val < layerHeight lay then
      treeNode parameter lay tree secret level (Nat.xor (leaf.val / 2 ^ level.val) 1)
    else
      pure 0

/-- `TreeFold`: fold a leaf and a path into the layer's root. -/
def treeFold {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (path : Nat → Digest) : Nat → Digest → m Digest
  | 0, value => pure value
  | levels + 1, value => do
      let current ← treeFold parameter lay tree leaf path levels value
      let sibling := path levels
      let nodeIdx := leaf.val / 2 ^ (levels + 1)
      if leaf.val.testBit levels then
        tweakableHash parameter (.node lay tree (levels + 1) nodeIdx) (nodePayload sibling current)
      else
        tweakableHash parameter (.node lay tree (levels + 1) nodeIdx) (nodePayload current sibling)

/-! ### The few-time signature -/

def ftsLeafOfNat (value : Nat) : FtsLeaf :=
  ⟨value % 2 ^ ftsTreeHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- The index group of the digest that selects this tree's leaf. -/
def ftsIndexOf (tree : FtsTree) : DigestTree :=
  tree.castLE (Nat.sub_le ftsTrees 1)

/-- The last index group, the one the digest is resampled to zero and the verifier checks. Its tree is the dropped one. -/
def lastDigestTree : DigestTree := ⟨ftsTrees - 1, by decide⟩

def ftsLeafHash {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (index : Index) (tree : FtsTree) (leaf : FtsLeaf)
    (secret : Digest) : m Digest :=
  tweakableHash parameter (.ftsLeaf index tree leaf) (digestBytes secret)

/-- `Y^{idx,kappa}_{level,nodeIdx}`, one tree of the forest. -/
def ftsNode {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (secret : FtsLeaf → Digest) : Nat → Nat → m Digest
  | 0, nodeIdx => do
      let leaf := ftsLeafOfNat nodeIdx
      ftsLeafHash parameter index tree leaf (secret leaf)
  | level + 1, nodeIdx => do
      let left ← ftsNode parameter index tree secret level (2 * nodeIdx)
      let right ← ftsNode parameter index tree secret level (2 * nodeIdx + 1)
      tweakableHash parameter (.ftsNode index tree (level + 1) nodeIdx) (nodePayload left right)

attribute [irreducible] ftsNode

def ftsRootsPayload (roots : FtsTree → Digest) : HashInput :=
  (List.ofFn roots).flatMap digestBytes

/-- `FtsKey(P, idx)`, the hash of the forest's `k - 1` roots. -/
def ftsKey {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (index : Index)
    (secret : FtsTree → FtsLeaf → Digest) : m Digest := do
  let roots ← sequenceFin fun tree =>
    ftsNode parameter index tree (secret tree) ftsTreeHeight 0
  tweakableHash parameter (.ftsRoots index) (ftsRootsPayload roots)

/-- `FtsOpen`: the opened secrets and, per tree, the `a` siblings of the opened leaf. -/
def ftsOpen {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (index : Index) (leaves : DigestTree → FtsLeaf)
    (secret : FtsTree → FtsLeaf → Digest) : m (FtsTree → Fin ftsTreeHeight → Digest) :=
  sequenceFin fun tree =>
    sequenceFin fun level =>
      ftsNode parameter index tree (secret tree) level.val
        (Nat.xor ((leaves (ftsIndexOf tree)).val / 2 ^ level.val) 1)

/-- The verifier's half of one few-time tree. -/
def ftsFold {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (index : Index) (tree : FtsTree) (leaf : FtsLeaf)
    (path : Fin ftsTreeHeight → Digest) : Nat → Digest → m Digest
  | 0, value => pure value
  | levels + 1, value => do
      let current ← ftsFold parameter index tree leaf path levels value
      let sibling := if hlevel : levels < ftsTreeHeight then path ⟨levels, hlevel⟩ else 0
      let nodeIdx := leaf.val / 2 ^ (levels + 1)
      if leaf.val.testBit levels then
        tweakableHash parameter (.ftsNode index tree (levels + 1) nodeIdx)
          (nodePayload sibling current)
      else
        tweakableHash parameter (.ftsNode index tree (levels + 1) nodeIdx)
          (nodePayload current sibling)

/-- `FtsRec`: recover the few-time public key from the opened secrets and paths. -/
def ftsRecover {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (index : Index) (leaves : DigestTree → FtsLeaf)
    (secrets : FtsTree → Digest) (paths : FtsTree → Fin ftsTreeHeight → Digest) : m Digest := do
  let roots ← sequenceFin fun tree => do
    let leaf := leaves (ftsIndexOf tree)
    let value ← ftsLeafHash parameter index tree leaf (secrets tree)
    ftsFold parameter index tree leaf (paths tree) ftsTreeHeight value
  tweakableHash parameter (.ftsRoots index) (ftsRootsPayload roots)

/-! ### The message digest -/

def messageDigestPayload (root : Digest) (message : Message) (randomness : Randomness) : HashInput :=
  randomnessBytes randomness ++ digestBytes root ++ messageBytes message

/-- `Digest(P, root, m, rho)`, truncated to `h + k * a` bits. -/
def messageDigest {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) : m MessageDigest := do
  let output ← oracleHash
    (tweakableHashInput parameter .message (messageDigestPayload root message randomness))
  return truncateMessageDigest output

/-- `idx = N mod 2^h`. -/
def digestIndex (digest : MessageDigest) : Index :=
  (digest.extractLsb' 0 totalHeight).toFin

/-- `u_kappa = floor(N / 2^(h + kappa * a)) mod 2^a`. -/
def digestLeaves (digest : MessageDigest) : DigestTree → FtsLeaf :=
  fun tree => (digest.extractLsb' (totalHeight + ftsTreeHeight * tree.val) ftsTreeHeight).toFin

/-- A digest is admissible exactly when its last index group is zero. -/
def Admissible (digest : MessageDigest) : Prop := digestLeaves digest lastDigestTree = 0

instance (digest : MessageDigest) : Decidable (Admissible digest) :=
  inferInstanceAs (Decidable (digestLeaves digest lastDigestTree = 0))

/-! ### Verification -/

/-- Layer `lay`'s share of the signature's authentication path, its `h_lay` nodes starting at offset `sum_{j < lay} h_j`. -/
def signaturePath (signature : Signature) (lay : Layer) (level : Nat) : Digest :=
  if hlevel : heightAbove lay + level < totalHeight then
    signature.authPath ⟨heightAbove lay + level, hlevel⟩
  else
    0

/-- The hypertree walk, from the bottom layer up: `remaining + 1` enters at layer `remaining`, and layer `0`'s fold returns the value compared against the public root. -/
def verifyLayers {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (index : Index) (signature : Signature) :
    Nat → Digest → m (Option Digest)
  | 0, message => pure (some message)
  | remaining + 1, message => do
      if hlayer : remaining < numLayers then
        let lay : Layer := ⟨remaining, hlayer⟩
        let tree := treeIndexAt index lay
        let leaf := leafIndexAt index lay
        match ← otsLeaf parameter lay tree leaf message (signature.counter lay)
          (signature.chainValue lay) with
        | none => pure none
        | some value => do
            let root ← treeFold parameter lay tree leaf (signaturePath signature lay)
              (layerHeight lay) value
            verifyLayers parameter index signature remaining root
      else
        pure none

def verify {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (publicKey : PublicKey) (message : Message) (signature : Signature) : m Bool := do
  let digest ← messageDigest publicKey.parameter publicKey.root message signature.randomness
  if ¬ Admissible digest then
    return false
  else
    let index := digestIndex digest
    let ftsPublicKey ← ftsRecover publicKey.parameter index (digestLeaves digest)
      signature.ftsSecret signature.ftsPath
    match ← verifyLayers publicKey.parameter index signature numLayers ftsPublicKey with
    | none => return false
    | some root => return decide (root = publicKey.root)

attribute [irreducible] verify

/-! ### Key generation -/

noncomputable local instance : SampleableType PublicParameter :=
  SampleableType.ofFintype PublicParameter

noncomputable local instance :
    SampleableType (Layer → TreeIndex → LeafIndex → ChainIndex → Digest) :=
  SampleableType.ofFintype (Layer → TreeIndex → LeafIndex → ChainIndex → Digest)

noncomputable local instance : SampleableType (Index → FtsTree → FtsLeaf → Digest) :=
  SampleableType.ofFintype (Index → FtsTree → FtsLeaf → Digest)

noncomputable local instance : SampleableType Randomness :=
  SampleableType.ofFintype Randomness

noncomputable def sampleParameter : ProbComp PublicParameter :=
  $ᵗ PublicParameter

noncomputable def sampleOtsSecrets :
    ProbComp (Layer → TreeIndex → LeafIndex → ChainIndex → Digest) :=
  $ᵗ (Layer → TreeIndex → LeafIndex → ChainIndex → Digest)

noncomputable def sampleFtsSecrets : ProbComp (Index → FtsTree → FtsLeaf → Digest) :=
  $ᵗ (Index → FtsTree → FtsLeaf → Digest)

noncomputable def sampleRandomness : ProbComp Randomness :=
  $ᵗ Randomness

attribute [irreducible] sampleParameter sampleOtsSecrets sampleFtsSecrets sampleRandomness

def rootTree : TreeIndex := ⟨0, Nat.two_pow_pos _⟩

/-- `Gen`: sample the parameter and every secret, and build layer `0`'s tree for the root. The trees below it are built when a signature needs them, so nothing else is computed here. -/
noncomputable def keygen : OracleComp OracleWorld (PublicKey × SecretKey) := do
  let parameter ← liftM sampleParameter
  let otsSecret ← liftM sampleOtsSecrets
  let ftsSecret ← liftM sampleFtsSecrets
  let root ← liftM
    (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree) :
      OracleComp HashSpec Digest)
  return (⟨root, parameter⟩, ⟨parameter, root, otsSecret, ftsSecret⟩)

attribute [irreducible] keygen

/-! ### Signing -/

/-- One digest attempt: one hash, keeping the index and the leaf indices if the digest is admissible. -/
def signAttempt {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (secretKey : SecretKey) (message : Message) (randomness : Randomness) :
    m (Option (Index × (DigestTree → FtsLeaf))) := do
  let digest ← messageDigest secretKey.parameter secretKey.root message randomness
  if Admissible digest then
    return some (digestIndex digest, digestLeaves digest)
  else
    return none

/-- The digest loop: at most `digestAttemptLimit` attempts, each sampling a fresh randomizer, stopping at the first admissible digest. It takes `2^a` attempts on average. -/
noncomputable def signDigestLoop : Nat → SecretKey → Message →
    OracleComp OracleWorld (Option (Randomness × Index × (DigestTree → FtsLeaf)))
  | 0, _secretKey, _message => pure none
  | attempts + 1, secretKey, message => do
      let randomness ← liftM sampleRandomness
      let attempt ← liftM
        (signAttempt secretKey message randomness :
          OracleComp HashSpec (Option (Index × (DigestTree → FtsLeaf))))
      match attempt with
      | some (index, leaves) => pure (some (randomness, index, leaves))
      | none => signDigestLoop attempts secretKey message

/-- The message layer `lay` signs: the root of the tree below it, or the few-time public key at the bottom. Every layer's message is fixed by the index alone, which is what makes the layers independent. -/
def layerMessage {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (secretKey : SecretKey) (index : Index) (lay : Layer) : m Digest :=
  if hbelow : lay.val + 1 < numLayers then
    let below : Layer := ⟨lay.val + 1, hbelow⟩
    treeRoot secretKey.parameter below (treeIndexAt index below)
      (secretKey.otsSecret below (treeIndexAt index below))
  else
    ftsKey secretKey.parameter index (secretKey.ftsSecret index)

/-- One layer's contribution: its counter, its chain values, and its authentication path. -/
def signLayer {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (secretKey : SecretKey) (index : Index) (lay : Layer) :
    m (Option (Counter × (ChainIndex → Digest) × (Fin maxLayerHeight → Digest))) := do
  let tree := treeIndexAt index lay
  let leaf := leafIndexAt index lay
  let message ← layerMessage secretKey index lay
  match ← otsSign secretKey.parameter lay tree leaf (secretKey.otsSecret lay tree leaf) message with
  | none => return none
  | some (counter, values) => do
      let path ← treePath secretKey.parameter lay tree (secretKey.otsSecret lay tree) leaf
      return some (counter, values, path)

/-- Which layer's path an entry of the `h` belongs to. -/
def layerOfPath (position : Nat) : Layer :=
  if position < heightAbove middleLayer then topLayer
  else if position < heightAbove bottomLayer then middleLayer
  else bottomLayer

/-- Lay the `d` layers' paths end to end, top layer first, so that every one of the `h` entries is read by verification. -/
def flattenPaths (paths : Layer → Fin maxLayerHeight → Digest) : PathIndex → Digest :=
  fun position =>
    let lay := layerOfPath position.val
    let level := position.val - heightAbove lay
    if hlevel : level < maxLayerHeight then paths lay ⟨level, hlevel⟩ else 0

theorem heightAbove_add_layerHeight_le (lay : Layer) :
    heightAbove lay + layerHeight lay ≤ totalHeight := by decide +revert

/-- An entry at a layer's own offset belongs to that layer. -/
theorem layerOfPath_eq (lay : Layer) (level : Fin maxLayerHeight) (hlevel : level.val < layerHeight lay) :
    layerOfPath (heightAbove lay + level.val) = lay := by
  revert hlevel
  revert level
  revert lay
  decide

theorem flattenPaths_apply (paths : Layer → Fin maxLayerHeight → Digest) (lay : Layer)
    (level : Fin maxLayerHeight) (hlevel : level.val < layerHeight lay) (position : PathIndex)
    (hposition : position.val = heightAbove lay + level.val) :
    flattenPaths paths position = paths lay level := by
  simp only [flattenPaths, hposition, layerOfPath_eq lay level hlevel, Nat.add_sub_cancel_left,
    dif_pos level.isLt, Fin.eta]

/-- The verifier reads a layer's path node exactly where the signer laid it, so the `h` entries of the authentication path are the `d` layers' paths and nothing else. -/
theorem signaturePath_flattenPaths (signature : Signature)
    (paths : Layer → Fin maxLayerHeight → Digest) (hpath : signature.authPath = flattenPaths paths)
    (lay : Layer) (level : Fin maxLayerHeight) (hlevel : level.val < layerHeight lay) :
    signaturePath signature lay level.val = paths lay level := by
  have hlt : heightAbove lay + level.val < totalHeight :=
    lt_of_lt_of_le (by omega) (heightAbove_add_layerHeight_le lay)
  rw [signaturePath, dif_pos hlt, hpath]
  exact flattenPaths_apply paths lay level hlevel _ rfl

/-- Every one of the `h` entries is read by some layer: the offsets partition `0..h-1` into the `d` layers, so the path carries no entry verification skips and none twice. This is arithmetic about the offsets, not a statement about `verifyLayers`. -/
theorem authPath_exhausted (position : PathIndex) : ∃ lay : Layer, ∃ level : Fin maxLayerHeight,
    level.val < layerHeight lay ∧ heightAbove lay + level.val = position.val := by
  revert position
  decide

/-- `Sig(sk, m)`: the digest loop, the few-time opening, one one-time signature per layer, and the assembled signature. -/
noncomputable def sign (secretKey : SecretKey) (message : Message) :
    OracleComp OracleWorld (Option Signature) := do
  match ← signDigestLoop digestAttemptLimit secretKey message with
  | none => return none
  | some (randomness, index, leaves) => do
      let ftsPath ← liftM
        (ftsOpen secretKey.parameter index leaves (secretKey.ftsSecret index) :
          OracleComp HashSpec (FtsTree → Fin ftsTreeHeight → Digest))
      let layers ← liftM
        (sequenceFin (fun lay => signLayer secretKey index lay) :
          OracleComp HashSpec
            (Layer → Option (Counter × (ChainIndex → Digest) × (Fin maxLayerHeight → Digest))))
      match traverseOption layers with
      | none => return none
      | some parts =>
          return some
            { randomness := randomness
              ftsSecret := fun tree => secretKey.ftsSecret index tree (leaves (ftsIndexOf tree))
              ftsPath := ftsPath
              counter := fun lay => (parts lay).1
              chainValue := fun lay => (parts lay).2.1
              authPath := flattenPaths fun lay => (parts lay).2.2 }

attribute [irreducible] sign

end Concrete

/-! ## The security experiment -/

/-- The random-oracle semantics: hash queries are answered lazily and consistently by uniform sampling and cached; uniform-sampling queries are forwarded unchanged. -/
noncomputable def romImpl : QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp) :=
  unifFwdImpl HashSpec +
    (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))

/-- A signing request is a message alone: the scheme is stateless, and the signer chooses the index by hashing. -/
abbrev SignRequest := Message

/-- A claimed forgery: a message and a signature. -/
structure Forgery where
  message : Message
  signature : Signature
deriving DecidableEq

/-- The interface of a stateless signature scheme in the random-oracle experiment. Signing is randomized and may fail, so it returns an option. -/
structure Scheme where
  keygen : OracleComp OracleWorld (PublicKey × SecretKey)
  sign : SecretKey → Message → OracleComp OracleWorld (Option Signature)
  verify : PublicKey → Message → Signature → OracleComp OracleWorld Bool

/-- The signing oracle answers a request with either a signature or `none` if the signer fails. -/
abbrev SigningSpec := SignRequest →ₒ Option Signature

/-- A classical adaptive adversary. After receiving the public key, it may query the shared random oracle, request signatures, and finally return a claimed forgery. -/
structure Adversary where
  main : PublicKey → OracleComp (OracleWorld + SigningSpec) Forgery

namespace SigningTranscript

/-- A signing transcript is valid exactly when the key signed at most `q_s` messages. Nothing forbids repeating a message: the signer is stateless, and a fresh randomizer makes the second signature a different one. -/
def Valid (log : QueryLog SigningSpec) : Prop := log.length ≤ signatureLimit

instance (log : QueryLog SigningSpec) : Decidable (Valid log) :=
  inferInstanceAs (Decidable (log.length ≤ signatureLimit))

/-- The signer returned the claimed forgery exactly when the transcript contains the same message answered by the same signature. A different signature for a signed message is therefore a valid strong forgery. -/
def Contains (log : QueryLog SigningSpec) (forgery : Forgery) : Prop :=
  ∃ entry ∈ log, entry.1 = forgery.message ∧ entry.2 = some forgery.signature

instance (log : QueryLog SigningSpec) (forgery : Forgery) : Decidable (Contains log forgery) :=
  inferInstanceAs
    (Decidable (∃ entry ∈ log, entry.1 = forgery.message ∧ entry.2 = some forgery.signature))

end SigningTranscript

/-- The signing oracle used in the game. It records every request and response while forwarding the request to the scheme's signer. -/
def signingOracle (scheme : Scheme) (sk : SecretKey) :
    QueryImpl SigningSpec (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  QueryImpl.withLogging fun request => scheme.sign sk request

/-- Forward the shared random oracle and uniform sampling to the adversary unchanged, alongside the logged signing oracle. -/
def forwardOracles :
    QueryImpl OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  fun input => liftM (OracleWorld.query input)

/-- The complete strong-unforgeability experiment.

The random oracle is sampled lazily by the semantics of `OracleWorld`. Key generation, the adversary, the signing oracle, and final verification all share the same oracle. The game returns `true` precisely when the transcript holds at most `q_s` signatures, the claimed forgery is not one the signer returned for that message, and the signature verifies. -/
noncomputable def gameCore (scheme : Scheme) (adversary : Adversary) :
    OracleComp OracleWorld Bool := do
  let (pk, sk) ← scheme.keygen
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (forwardOracles + signingOracle scheme sk) (adversary.main pk)).run
  let verified ← scheme.verify pk forgery.message forgery.signature
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

/-- The probability that the adversary wins, over key generation, signer randomness, and the random oracle, which starts from the empty cache. The final cache is discarded. -/
noncomputable def forgeAdvantage (scheme : Scheme) (adversary : Adversary) : ℝ≥0∞ :=
  Pr[= true | (simulateQ romImpl (gameCore scheme adversary)).run' ∅]

/-- The whole experiment makes at most `q` random-oracle queries on every execution path. The count includes queries during key generation, adversarial hashing, signing, and final verification. Uniform sampling operations are not hash queries. -/
def HasHashQueryBound (scheme : Scheme) (adversary : Adversary) (q : Nat) : Prop :=
  (gameCore scheme adversary).IsQueryBoundP (· matches .inr _) q

/-- Having `bits` bits of classical security means that every classical adaptive adversary whose complete experiment stays within a nonzero hash-query budget `q` forges with probability at most `q / 2^bits`. The bound is a slope, so it bounds what a query buys and not what the first one does; a budget below what the honest experiment alone spends admits no adversary and the bound is vacuous there. -/
def HasClassicalSecurityBits (scheme : Scheme) (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary, HasHashQueryBound scheme adversary q →
    forgeAdvantage scheme adversary ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)

/-- The concrete SPHINCS scheme: key generation, the stateless randomized signer, and the verifier defined above. -/
noncomputable def Concrete.scheme : Scheme where
  keygen := Concrete.keygen
  sign := Concrete.sign
  verify := fun publicKey message signature =>
    liftM (Concrete.verify publicKey message signature : OracleComp HashSpec Bool)

/-- The complete public security claim: `120` bits of classical strong unforgeability in the random-oracle model, at `2^24` signatures per key pair. -/
abbrev SphincsSecurityStatement : Prop :=
  HasClassicalSecurityBits Concrete.scheme securityBits

end SphincsSecurity
