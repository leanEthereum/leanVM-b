import SphincsSecurity.Proof.Merkle

/-!
# The few-time signature

`Fts.recover` on an opening of the leaves the digest chooses reproduces `Fts.key`: each tree folds
back to its root, and the roots are hashed the same way on both sides.
-/

namespace SphincsSecurity.Concrete

open OracleComp

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index)

theorem ftsLeafOfNat_val (leaf : FtsLeaf) : ftsLeafOfNat leaf.val = leaf := by
  ext
  simp [ftsLeafOfNat, Nat.mod_eq_of_lt leaf.isLt]

/-- **Few-time tree correctness.** Folding an opened leaf with its siblings reproduces the tree. -/
theorem eval_ftsFold (tree : FtsTree) (secret : FtsLeaf → Digest) (leaf : FtsLeaf) (levels : Nat)
    (hlevels : levels ≤ ftsTreeHeight) :
    evalWithAnswerFn f (ftsFold parameter index tree leaf
        (fun level => evalWithAnswerFn f (ftsNode parameter index tree secret level.val
          (Nat.xor (leaf.val / 2 ^ level.val) 1))) levels
        (evalWithAnswerFn f (ftsLeafHash parameter index tree leaf (secret leaf))))
      = evalWithAnswerFn f (ftsNode parameter index tree secret levels (leaf.val / 2 ^ levels)) := by
  induction levels with
  | zero => simp [ftsLeafOfNat_val]
  | succ levels ih =>
      obtain ⟨j, hcase⟩ := index_sibling_cases (leaf.val / 2 ^ levels)
      have hj : leaf.val / 2 ^ (levels + 1) = j := by
        rw [div_pow_succ]
        rcases hcase with ⟨hc, _, _⟩ | ⟨hc, _, _⟩ <;> omega
      have hlevel : levels < ftsTreeHeight := by omega
      rw [ftsFold_succ_eq, ftsNode_succ_eq, evalWithAnswerFn_bind, ih (by omega), hj,
        evalWithAnswerFn_bind, evalWithAnswerFn_bind]
      rcases hcase with ⟨hc, hsibling, hmod⟩ | ⟨hc, hsibling, hmod⟩
      · have hbit : leaf.val.testBit levels = false := by
          rw [Bool.eq_false_iff, ne_eq, testBit_iff_div_mod]; omega
        rw [hbit, if_neg (by simp), hc]
        simp only [dif_pos hlevel, hsibling]
      · have hbit : leaf.val.testBit levels = true := by
          rw [testBit_iff_div_mod]; omega
        rw [hbit, if_pos rfl, hc]
        simp only [dif_pos hlevel, hsibling]

/-- **Few-time correctness.** The opening a signature carries recovers the few-time public key. -/
theorem eval_ftsRecover (leaves : DigestTree → FtsLeaf) (secret : FtsTree → FtsLeaf → Digest) :
    evalWithAnswerFn f (ftsRecover parameter index leaves
        (fun tree => secret tree (leaves (ftsIndexOf tree)))
        (evalWithAnswerFn f (ftsOpen parameter index leaves secret)))
      = evalWithAnswerFn f (ftsKey parameter index secret) := by
  have hroot : ∀ leaf : FtsLeaf, leaf.val / 2 ^ ftsTreeHeight = 0 := fun leaf =>
    Nat.div_eq_of_lt leaf.isLt
  have hfold : ∀ tree : FtsTree,
      evalWithAnswerFn f (ftsFold parameter index tree (leaves (ftsIndexOf tree))
          (fun level => evalWithAnswerFn f (ftsNode parameter index tree (secret tree) level.val
            (Nat.xor ((leaves (ftsIndexOf tree)).val / 2 ^ level.val) 1))) ftsTreeHeight
          (evalWithAnswerFn f (ftsLeafHash parameter index tree (leaves (ftsIndexOf tree))
            (secret tree (leaves (ftsIndexOf tree))))))
        = evalWithAnswerFn f (ftsNode parameter index tree (secret tree) ftsTreeHeight 0) := by
    intro tree
    rw [eval_ftsFold f parameter index tree (secret tree) (leaves (ftsIndexOf tree)) ftsTreeHeight
      (le_refl _), hroot]
  simp only [ftsRecover, ftsKey, ftsOpen, evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin,
    hfold]

end SphincsSecurity.Concrete
