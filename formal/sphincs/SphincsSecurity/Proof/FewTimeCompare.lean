import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.SignSupport

/-!
# Signing-transcript coverage of few-time openings

A transcript covers one few-time leaf when some successful signer invocation used the same index
and selected that leaf for the corresponding tree. The leak event is simultaneous coverage of all
fourteen trees, allowing a different transcript entry to cover each tree.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

theorem messageDigest_eq_of_index_leaves_eq {left right : MessageDigest}
    (hindex : digestIndex left = digestIndex right)
    (hleaves : digestLeaves left = digestLeaves right) : left = right := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit hbit
  by_cases hlow : bit < totalHeight
  · have h := congrArg (fun index : Index => (BitVec.ofFin index).getLsbD bit) hindex
    simpa only [digestIndex, BitVec.ofFin_toFin, BitVec.getLsbD_extractLsb', hlow, decide_true,
      Bool.true_and, Nat.zero_add] using h
  · let treeValue := (bit - totalHeight) / ftsTreeHeight
    have htreeValue : treeValue < ftsTrees := by
      simp only [treeValue, messageDigestBits, totalHeight, ftsTreeHeight, ftsTrees] at hbit ⊢
      omega
    let tree : DigestTree := ⟨treeValue, htreeValue⟩
    let offset := bit - (totalHeight + ftsTreeHeight * tree.val)
    have hoffset : offset < ftsTreeHeight := by
      simp only [offset, tree, treeValue, totalHeight, ftsTreeHeight]
      omega
    have h := congrArg (fun leaves : DigestTree → FtsLeaf =>
      (BitVec.ofFin (leaves tree)).getLsbD offset) hleaves
    simp only [digestLeaves, BitVec.ofFin_toFin, BitVec.getLsbD_extractLsb', hoffset,
      decide_true, Bool.true_and] at h
    have heq : totalHeight + ftsTreeHeight * tree.val + offset = bit := by
      simp only [offset, tree, treeValue, totalHeight, ftsTreeHeight]
      have hlow' : 26 ≤ bit := by simpa only [totalHeight] using Nat.le_of_not_gt hlow
      have hmul : 10 * ((bit - 26) / 10) ≤ bit - 26 := Nat.mul_div_le _ _
      omega
    rw [heq] at h
    exact h

def SignedFtsLeaf (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (signingLog : QueryLog SigningSpec) (index : Index)
    (tree : FtsTree) (leafIdx : FtsLeaf) : Prop :=
  ∃ (entry : (request : SignRequest) × SigningSpec.Range request) (signature : Signature)
      (leaves : DigestTree → FtsLeaf),
    entry ∈ signingLog
      ∧ entry.2 = some signature
      ∧ SuccessfulSignRun f cache secretKey entry.1 signature
      ∧ HonestFtsSignAt f cache secretKey entry.1 signature index leaves
      ∧ leaves (ftsIndexOf tree) = leafIdx

def FewTimeLeak (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (signingLog : QueryLog SigningSpec) (index : Index)
    (leaves : DigestTree → FtsLeaf) : Prop :=
  ∀ tree, SignedFtsLeaf f cache secretKey signingLog index tree (leaves (ftsIndexOf tree))

theorem fewTimeLeak_or_uncovered (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (signingLog : QueryLog SigningSpec) (index : Index)
    (leaves : DigestTree → FtsLeaf) :
    FewTimeLeak f cache secretKey signingLog index leaves
      ∨ ∃ tree, ¬ SignedFtsLeaf f cache secretKey signingLog index tree
        (leaves (ftsIndexOf tree)) := by
  classical
  by_cases hleak : FewTimeLeak f cache secretKey signingLog index leaves
  · exact Or.inl hleak
  · exact Or.inr (not_forall.mp hleak)

end SphincsSecurity.Concrete
