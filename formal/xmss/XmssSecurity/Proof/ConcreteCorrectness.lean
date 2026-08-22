import XmssSecurity.Proof.CacheReplayEval
import Mathlib.Data.Nat.Bitwise

open OracleSpec

namespace XmssSecurity.Concrete.CacheReplay

def pathNode (epoch : Epoch) (level : Nat) : MerkleNode :=
  Concrete.merkleNodeOfNat (epoch.val / 2 ^ level)

@[simp]
theorem pathNode_zero (epoch : Epoch) : pathNode epoch 0 = epoch := by
  apply Fin.ext
  simp only [pathNode, Concrete.merkleNodeOfNat, pow_zero, Nat.div_one]
  exact Nat.mod_eq_of_lt epoch.isLt

theorem testBit_div_pow (value level : Nat) :
    (value / 2 ^ level).testBit 0 = value.testBit level := by
  simpa only [Nat.zero_add] using (Nat.testBit_add value 0 level).symm

theorem div_pow_succ (value level : Nat) :
    value / 2 ^ (level + 1) = (value / 2 ^ level) / 2 := by
  rw [pow_succ, Nat.div_div_eq_div_mul]

private theorem even_parts (value : Nat) (hbit : value.testBit 0 = false) :
    value = 2 * (value / 2) ∧ value ^^^ 1 = 2 * (value / 2) + 1 := by
  have heven : Even value := Nat.even_iff.mpr
    (Nat.mod_two_eq_zero_iff_testBit_zero.mpr hbit)
  constructor
  · have h := Nat.bit_testBit_zero_shiftRight_one value
    rw [hbit, Nat.bit_false, Nat.shiftRight_one] at h
    exact h.symm
  · rw [Nat.xor_one_of_even heven]
    have h := Nat.bit_testBit_zero_shiftRight_one value
    rw [hbit, Nat.bit_false, Nat.shiftRight_one] at h
    exact congrArg (fun current => current + 1) h.symm

private theorem odd_parts (value : Nat) (hbit : value.testBit 0 = true) :
    value = 2 * (value / 2) + 1 ∧ value ^^^ 1 = 2 * (value / 2) := by
  have hodd : Odd value := Nat.odd_iff.mpr
    (Nat.mod_two_eq_one_iff_testBit_zero.mpr hbit)
  constructor
  · have h := Nat.bit_testBit_zero_shiftRight_one value
    rw [hbit, Nat.bit_true, Nat.shiftRight_one] at h
    exact h.symm
  · rw [Nat.xor_one_of_odd hodd]
    have h := Nat.bit_testBit_zero_shiftRight_one value
    rw [hbit, Nat.bit_true, Nat.shiftRight_one] at h
    calc
      value - 1 = (2 * (value / 2) + 1) - 1 :=
        congrArg (fun current => current - 1) h.symm
      _ = 2 * (value / 2) := by omega

theorem nodeIndex_eq_pathNode_succ (epoch : Epoch) (level : Nat) :
    CacheView.nodeIndex epoch level = pathNode epoch (level + 1) := by
  apply Fin.ext
  simp only [CacheView.nodeIndex, Concrete.nodeIndex, pathNode, Concrete.merkleNodeOfNat]
  exact (Nat.mod_eq_of_lt
    ((Nat.div_le_self epoch.val _).trans_lt epoch.isLt)).symm

theorem pathNode_children (epoch : Epoch) (level : Nat) (hlevel : level < treeHeight) :
    if epoch.val.testBit level then
      Concrete.childNode (pathNode epoch (level + 1)) false =
          Concrete.authenticationPathNode epoch ⟨level, hlevel⟩ ∧
        Concrete.childNode (pathNode epoch (level + 1)) true = pathNode epoch level
    else
      Concrete.childNode (pathNode epoch (level + 1)) false = pathNode epoch level ∧
        Concrete.childNode (pathNode epoch (level + 1)) true =
          Concrete.authenticationPathNode epoch ⟨level, hlevel⟩ := by
  let quotient := epoch.val / 2 ^ level
  have hquotient : quotient < lifetime :=
    (Nat.div_le_self epoch.val _).trans_lt epoch.isLt
  have hparent : (pathNode epoch (level + 1)).val = quotient / 2 := by
    simp only [pathNode, Concrete.merkleNodeOfNat]
    rw [div_pow_succ]
    exact Nat.mod_eq_of_lt
      ((Nat.div_le_self (epoch.val / 2 ^ level) _).trans_lt hquotient)
  have hcurrent : (pathNode epoch level).val = quotient := by
    simp [pathNode, Concrete.merkleNodeOfNat, quotient,
      Nat.mod_eq_of_lt hquotient]
  have hauth :
      (Concrete.authenticationPathNode epoch ⟨level, hlevel⟩).val =
        (quotient ^^^ 1) % lifetime := by
    rfl
  have hquotientBit : quotient.testBit 0 = epoch.val.testBit level := by
    exact testBit_div_pow epoch.val level
  by_cases hbit : epoch.val.testBit level = true
  · simp only [hbit, ↓reduceIte]
    obtain ⟨hcurrentParts, hauthParts⟩ := odd_parts quotient (hquotientBit.trans hbit)
    constructor
    · apply Fin.ext
      rw [hauth]
      simp only [Concrete.childNode, Concrete.merkleNodeOfNat, Bool.false_eq_true,
        ↓reduceIte, hparent]
      exact congrArg (fun value => value % lifetime) hauthParts.symm

    · apply Fin.ext
      rw [hcurrent]
      simp only [Concrete.childNode, Concrete.merkleNodeOfNat, ↓reduceIte, hparent]
      calc
        (2 * (quotient / 2) + 1) % lifetime = quotient % lifetime :=
          congrArg (fun value => value % lifetime) hcurrentParts.symm
        _ = quotient := Nat.mod_eq_of_lt hquotient
  · have hbitFalse : epoch.val.testBit level = false := Bool.eq_false_of_not_eq_true hbit
    simp only [hbitFalse, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨hcurrentParts, hauthParts⟩ := even_parts quotient
      (hquotientBit.trans hbitFalse)
    constructor
    · apply Fin.ext
      rw [hcurrent]
      simp only [Concrete.childNode, Concrete.merkleNodeOfNat, Bool.false_eq_true,
        ↓reduceIte, hparent]
      calc
        (2 * (quotient / 2) + 0) % lifetime = quotient % lifetime :=
          congrArg (fun value => value % lifetime) (by omega :
            2 * (quotient / 2) + 0 = quotient)
        _ = quotient := Nat.mod_eq_of_lt hquotient
    · apply Fin.ext
      rw [hauth]
      simp only [Concrete.childNode, Concrete.merkleNodeOfNat, ↓reduceIte, hparent]
      exact congrArg (fun value => value % lifetime) hauthParts.symm

theorem authentication_step_eq_treeNode (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) (level : Nat) (hlevel : level < treeHeight) :
    CacheView.nodeHash cache parameter epoch level
        (treeNode cache parameter secret level (pathNode epoch level))
        (treeNode cache parameter secret level
          (Concrete.authenticationPathNode epoch ⟨level, hlevel⟩)) =
      treeNode cache parameter secret (level + 1) (pathNode epoch (level + 1)) := by
  have hnode := nodeIndex_eq_pathNode_succ epoch level
  have hchildren := pathNode_children epoch level hlevel
  by_cases hbit : epoch.val.testBit level = true
  · simp only [hbit, ↓reduceIte] at hchildren
    rcases hchildren with ⟨hleft, hright⟩
    simp [CacheView.nodeHash, hlevel, CacheView.nodeInput,
      CacheView.authenticationNodePayload, CacheView.merkleHash,
      CacheView.merkleInput, treeNode_succ_eq, hbit, hnode, hleft, hright]
  · have hbitFalse : epoch.val.testBit level = false := Bool.eq_false_of_not_eq_true hbit
    simp only [hbitFalse, Bool.false_eq_true, ↓reduceIte] at hchildren
    rcases hchildren with ⟨hleft, hright⟩
    simp [CacheView.nodeHash, hlevel, CacheView.nodeInput,
      CacheView.authenticationNodePayload, CacheView.merkleHash,
      CacheView.merkleInput, treeNode_succ_eq, hbitFalse, hnode, hleft, hright]

theorem recover_signedChainValues (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (epoch : Epoch) (encoding : Encoding) :
    XmssSecurity.recoveredEndpoints
        (fun chain => CacheView.chainStep cache secretKey.parameter epoch chain)
        encoding (signedChainValues cache secretKey epoch encoding) =
      oneTimePublicKey cache secretKey.parameter secretKey.chainStart epoch := by
  funext chain
  exact Wots.recover_signChain_eq_publicChain
    (CacheView.chainStep cache secretKey.parameter epoch chain)
    (encoding chain) (secretKey.chainStart epoch chain)

theorem recoveredEndpoints_signWithEncoding (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (epoch : Epoch) (randomness : Randomness)
    (encoding : Encoding) :
    XmssSecurity.recoveredEndpoints
        (fun chain => CacheView.chainStep cache secretKey.parameter epoch chain)
        encoding (signWithEncoding cache secretKey epoch randomness encoding).chainValue =
      oneTimePublicKey cache secretKey.parameter secretKey.chainStart epoch := by
  exact recover_signedChainValues cache secretKey epoch encoding

theorem leafHash_recovered_signWithEncoding (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (epoch : Epoch) (randomness : Randomness)
    (encoding : Encoding) :
    CacheView.leafHash cache secretKey.parameter epoch
        (XmssSecurity.recoveredEndpoints
          (fun chain => CacheView.chainStep cache secretKey.parameter epoch chain)
          encoding (signWithEncoding cache secretKey epoch randomness encoding).chainValue) =
      leafAt cache secretKey.parameter secretKey.chainStart epoch := by
  rw [recoveredEndpoints_signWithEncoding]
  rfl

theorem authenticationPath_ascends_to_treeNode (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (epoch : Epoch) (randomness : Randomness)
    (encoding : Encoding) (levels : Nat) (hlevels : levels ≤ treeHeight) :
    Merkle.ascend (CacheView.nodeHash cache secretKey.parameter epoch)
        (Concrete.signaturePath
          (signWithEncoding cache secretKey epoch randomness encoding))
        0 levels (leafAt cache secretKey.parameter secretKey.chainStart epoch) =
      treeNode cache secretKey.parameter secretKey.chainStart levels
        (pathNode epoch levels) := by
  induction levels with
  | zero => simp [Merkle.ascend]
  | succ level ih =>
      have hlevel : level < treeHeight := Nat.lt_of_succ_le hlevels
      rw [Merkle.ascend, ih (Nat.le_of_succ_le hlevels)]
      simp only [Nat.zero_add]
      have hpath :
          Concrete.signaturePath
              (signWithEncoding cache secretKey epoch randomness encoding) level =
            treeNode cache secretKey.parameter secretKey.chainStart level
              (Concrete.authenticationPathNode epoch ⟨level, hlevel⟩) := by
        simp [Concrete.signaturePath, signWithEncoding, authenticationPath, hlevel]
      rw [hpath]
      exact authentication_step_eq_treeNode cache secretKey.parameter
        secretKey.chainStart epoch level hlevel

theorem authenticationPath_ascends_to_root (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (epoch : Epoch) (randomness : Randomness)
    (encoding : Encoding) :
    Merkle.ascend (CacheView.nodeHash cache secretKey.parameter epoch)
        (Concrete.signaturePath
          (signWithEncoding cache secretKey epoch randomness encoding))
        0 treeHeight (leafAt cache secretKey.parameter secretKey.chainStart epoch) =
      treeNode cache secretKey.parameter secretKey.chainStart treeHeight
        Concrete.rootNode := by
  rw [authenticationPath_ascends_to_treeNode cache secretKey epoch randomness encoding
    treeHeight le_rfl]
  congr 1
  apply Fin.ext
  have hdiv : epoch.val / 2 ^ treeHeight = 0 := by
    apply Nat.div_eq_of_lt
    change epoch.val < lifetime
    exact epoch.isLt
  simp [pathNode, Concrete.rootNode, Concrete.merkleNodeOfNat, hdiv]

def publicKeyFromCache (cache : QueryCache HashSpec) (secretKey : SecretKey) : PublicKey :=
  ⟨treeNode cache secretKey.parameter secretKey.chainStart treeHeight Concrete.rootNode,
    secretKey.parameter⟩

attribute [irreducible] publicKeyFromCache

theorem publicKey_eq_publicKeyFromCache (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (root : Digest)
    (hroot : root = treeNode cache secretKey.parameter secretKey.chainStart
      treeHeight Concrete.rootNode) :
    PublicKey.mk root secretKey.parameter = publicKeyFromCache cache secretKey := by
  rw [publicKeyFromCache]
  exact congrArg₂ PublicKey.mk hroot rfl

theorem verifyFromCache_signWithEncoding (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (epoch : Epoch) (message : Message)
    (randomness : Randomness) (encoding : Encoding)
    (hdecode : TargetSum.decodeDigest
      (CacheView.encodingHash cache secretKey.parameter epoch (message, randomness)) =
        some encoding) :
    Concrete.verifyFromCache cache (publicKeyFromCache cache secretKey) epoch message
      (signWithEncoding cache secretKey epoch randomness encoding) = true := by
  unfold publicKeyFromCache
  apply (Concrete.verifyFromCache_eq_true_iff _ _ _ _ _).2
  refine ⟨encoding, hdecode, ?_⟩
  rw [leafHash_recovered_signWithEncoding]
  exact authenticationPath_ascends_to_root cache secretKey epoch randomness encoding

end XmssSecurity.Concrete.CacheReplay
