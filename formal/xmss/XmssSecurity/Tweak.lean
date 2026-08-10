import XmssSecurity.Parameters
import Mathlib.Tactic.NormNum

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

@[simp]
theorem encodeTweak_extract_tag (fields : TweakFields) :
    (encodeTweak fields).extractLsb' 0 8 = fields.tag := by
  rw [encodeTweak]
  exact BitVec.extractLsb'_append_eq_right

@[simp]
theorem encodeTweak_extract_position (fields : TweakFields) :
    (encodeTweak fields).extractLsb' 8 32 = fields.position := by
  rw [encodeTweak, BitVec.extractLsb'_append_eq_of_le (by omega)]
  exact BitVec.extractLsb'_append_eq_right

@[simp]
theorem encodeTweak_extract_epoch (fields : TweakFields) :
    (encodeTweak fields).extractLsb' 40 32 = fields.epoch := by
  rw [encodeTweak, BitVec.extractLsb'_append_eq_of_le (by omega)]
  rw [BitVec.extractLsb'_append_eq_of_le (by omega)]
  exact BitVec.extractLsb'_append_eq_right

theorem encodeTweak_injective : Function.Injective encodeTweak := by
  intro left right heq
  have htag : left.tag = right.tag := by
    simpa using congrArg (BitVec.extractLsb' 0 8) heq
  have hposition : left.position = right.position := by
    simpa using congrArg (BitVec.extractLsb' 8 32) heq
  have hepoch : left.epoch = right.epoch := by
    simpa using congrArg (BitVec.extractLsb' 40 32) heq
  cases left
  cases right
  simp_all

theorem encodeTweak_eq_iff {left right : TweakFields} :
    encodeTweak left = encodeTweak right ↔ left = right :=
  encodeTweak_injective.eq_iff

abbrev ChainStep := Fin (chainLength - 1)
abbrev MerkleLevel := Fin treeHeight
abbrev MerkleNode := Fin lifetime

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

@[simp]
theorem hashDomainFields_tag (domain : HashDomain) :
    (hashDomainFields domain).tag = BitVec.ofNat 8 (hashDomainTag domain) := by
  cases domain <;> rfl

def hashDomainTweak (domain : HashDomain) : Tweak :=
  encodeTweak (hashDomainFields domain)

private theorem ofNat32_eq_of_lt {left right : Nat}
    (hleft : left < 2 ^ 32) (hright : right < 2 ^ 32)
    (heq : BitVec.ofNat 32 left = BitVec.ofNat 32 right) : left = right := by
  have := congrArg BitVec.toNat heq
  norm_num at hleft hright this ⊢
  omega

private theorem ofNat8_eq_of_lt {left right : Nat}
    (hleft : left < 2 ^ 8) (hright : right < 2 ^ 8)
    (heq : BitVec.ofNat 8 left = BitVec.ofNat 8 right) : left = right := by
  have := congrArg BitVec.toNat heq
  norm_num at hleft hright this ⊢
  omega

private theorem hashDomainTag_lt_8 (domain : HashDomain) : hashDomainTag domain < 2 ^ 8 := by
  cases domain <;> norm_num [hashDomainTag]

private theorem epoch_lt_32 (epoch : Epoch) : epoch.val < 2 ^ 32 := by
  change epoch.val < lifetime
  exact epoch.isLt

private theorem chainPosition_lt_32 (chain : ChainIndex) (step : ChainStep) :
    chainLength * chain.val + step.val < 2 ^ 32 := by
  have hchain := chain.isLt
  have hstep := step.isLt
  norm_num [chainLength, winternitzBits, numChains] at hchain hstep ⊢
  omega

private theorem merkleLevel_lt_32 (level : MerkleLevel) : level.val + 1 < 2 ^ 32 := by
  have hlevel := level.isLt
  norm_num [treeHeight] at hlevel ⊢
  omega

private theorem merkleNode_lt_32 (node : MerkleNode) : node.val < 2 ^ 32 := by
  change node.val < lifetime
  exact node.isLt

theorem hashDomainFields_injective : Function.Injective hashDomainFields := by
  intro left right heq
  have htagBits := congrArg TweakFields.tag heq
  rw [hashDomainFields_tag, hashDomainFields_tag] at htagBits
  have htag := ofNat8_eq_of_lt (hashDomainTag_lt_8 left) (hashDomainTag_lt_8 right) htagBits
  cases left <;> cases right <;> simp [hashDomainTag] at htag
  all_goals simp only [hashDomainFields] at heq
  · rename_i leftEpoch leftChain leftStep rightEpoch rightChain rightStep
    have hposition := congrArg TweakFields.position heq
    have hepoch := congrArg TweakFields.epoch heq
    have hpositionNat := ofNat32_eq_of_lt
      (chainPosition_lt_32 leftChain leftStep) (chainPosition_lt_32 rightChain rightStep) hposition
    have hepochNat := ofNat32_eq_of_lt (epoch_lt_32 leftEpoch) (epoch_lt_32 rightEpoch) hepoch
    have hleftChain := leftChain.isLt
    have hrightChain := rightChain.isLt
    have hleftStep := leftStep.isLt
    have hrightStep := rightStep.isLt
    norm_num [chainLength, winternitzBits, numChains] at hpositionNat hleftChain hrightChain hleftStep hrightStep
    congr
    · exact Fin.ext hepochNat
    · apply Fin.ext
      omega
    · apply Fin.ext
      omega
  · rename_i leftEpoch rightEpoch
    have hepoch := congrArg TweakFields.epoch heq
    exact congrArg HashDomain.leaf
      (Fin.ext (ofNat32_eq_of_lt (epoch_lt_32 leftEpoch) (epoch_lt_32 rightEpoch) hepoch))
  · rename_i leftLevel leftNode rightLevel rightNode
    have hposition := congrArg TweakFields.position heq
    have hnode := congrArg TweakFields.epoch heq
    have hlevelNat := ofNat32_eq_of_lt
      (merkleLevel_lt_32 leftLevel) (merkleLevel_lt_32 rightLevel) hposition
    have hnodeNat := ofNat32_eq_of_lt (merkleNode_lt_32 leftNode) (merkleNode_lt_32 rightNode) hnode
    congr
    · exact Fin.ext (by omega)
    · exact Fin.ext hnodeNat
  · rename_i leftEpoch rightEpoch
    have hepoch := congrArg TweakFields.epoch heq
    exact congrArg HashDomain.encoding
      (Fin.ext (ofNat32_eq_of_lt (epoch_lt_32 leftEpoch) (epoch_lt_32 rightEpoch) hepoch))

theorem hashDomainTweak_injective : Function.Injective hashDomainTweak :=
  encodeTweak_injective.comp hashDomainFields_injective

theorem hashDomainTweak_eq_iff {left right : HashDomain} :
    hashDomainTweak left = hashDomainTweak right ↔ left = right :=
  hashDomainTweak_injective.eq_iff

end XmssSecurity
