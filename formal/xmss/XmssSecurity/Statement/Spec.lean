import Mathlib.Data.BitVec
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# The XMSS instance, oracle-free part

Everything deterministic in the specification: the concrete parameters, the key and signature types, the tweak and byte layout of every hash input, the target-sum message encoding, and the hash-chain walk.
-/

namespace XmssSecurity

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

theorem hashOutputBits_eq : hashOutputBits = digestBits + digestBits := by
  decide

def splitHashOutput (output : HashOutput) : BitVec (digestBits + digestBits) :=
  output.cast hashOutputBits_eq

/-- Keep the first 128 output bits, represented as the low bits of the little-endian bit vector. -/
def truncateHash (output : HashOutput) : Digest :=
  (splitHashOutput output).extractLsb' 0 digestBits

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

/-- Serialize a bit vector into a fixed number of bytes, least significant byte first. -/
def bytesLE (byteCount : Nat) (value : BitVec (8 * byteCount)) : List UInt8 :=
  List.ofFn fun index : Fin byteCount =>
    UInt8.ofBitVec (value.extractLsb' (8 * index.val) 8)

/-- The exact 16 bytes supplied by the specification as a hash tweak. -/
def tweakBytes (domain : HashDomain) : List UInt8 :=
  bytesLE 16 (hashDomainTweak domain)

/-- The random-oracle input `tweak || parameter || message` used by every tweakable hash call. -/
def tweakableHashInput (parameter : PublicParameter) (domain : HashDomain)
    (message : HashInput) : HashInput :=
  tweakBytes domain ++ bytesLE 16 parameter ++ message

namespace TargetSum

open scoped BigOperators

def sum (x : Encoding) : Nat := ∑ i, (x i).val

def Valid (x : Encoding) : Prop := sum x = targetSum

/-- The two unused digest bits accompany the 42 three-bit digits. -/
abbrev EncodingView := Encoding × Fin 4

def digitsPerHalf : Nat := numChains / 2

/-- Offset of a three-bit digit, skipping padding bits 63 and 127. -/
def digitOffset (i : ChainIndex) : Nat :=
  winternitzBits * i.val + if i.val < digitsPerHalf then 0 else 1

def digestEncoding (digest : Digest) : Encoding :=
  fun i => (digest.extractLsb' (digitOffset i) winternitzBits).toFin

def digestPadding (digest : Digest) : Fin 4 :=
  ⟨(if digest.getLsbD 63 then 1 else 0) +
    (if digest.getLsbD 127 then 2 else 0), by
      cases digest.getLsbD 63 <;> cases digest.getLsbD 127 <;> simp⟩

/-- The concrete little-endian layout used by `IncEnc`: 21 digits, one padding bit, 21 digits, and one padding bit. -/
def digestView (digest : Digest) : EncodingView :=
  (digestEncoding digest, digestPadding digest)

def ValidView (view : EncodingView) : Prop :=
  view.2 = 0 ∧ Valid view.1

noncomputable def decodeView (view : EncodingView) : Option Encoding := by
  classical
  exact if ValidView view then some view.1 else none

noncomputable def decodeDigest (digest : Digest) : Option Encoding :=
  decodeView (digestView digest)

end TargetSum

namespace Wots

/-- Walk `steps` edges of a domain-separated hash chain starting at `position`. -/
def walk {α : Type} (step : Nat → α → α) : Nat → Nat → α → α
  | _, 0, value => value
  | position, steps + 1, value => step (position + steps) (walk step position steps value)

end Wots

end XmssSecurity
