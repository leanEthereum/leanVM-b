import Mathlib.Data.BitVec

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
def verificationChainHashes : Nat := numChains * (chainLength - 1) - targetSum

theorem verificationChainHashes_eq : verificationChainHashes = 99 := by
  decide

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

theorem signingAttemptLimit_eq : signingAttemptLimit = 2 ^ 23 := rfl

theorem signingAttemptLimit_pos : 0 < signingAttemptLimit := by
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

def SecretKey.withoutPrecomputation
    (parameter : PublicParameter) (chainStart : Epoch → ChainIndex → Digest) :
    SecretKey :=
  ⟨parameter, chainStart, fun _ _ _ => 0, fun _ _ => 0⟩

structure Signature where
  randomness : Randomness
  chainValue : ChainIndex → Digest
  authPath : Fin treeHeight → Digest
deriving DecidableEq

end XmssSecurity
