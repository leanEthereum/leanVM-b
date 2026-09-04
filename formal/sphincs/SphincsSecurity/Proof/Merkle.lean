import SphincsSecurity.Proof.Arith
import SphincsSecurity.Proof.Eval
import SphincsSecurity.Proof.StatementLemmas

/-!
# A layer's tree

`Tree.fold` on the siblings of a leaf reaches the node the tree builds above it: at each level the
current value and the sibling are the two children of the node one level up, and the bit of the leaf
index that the fold tests is exactly which of them is the left child.
-/

namespace SphincsSecurity.Concrete

open OracleComp

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
  (secret : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex)

/-- **Merkle correctness.** Folding a leaf with its siblings reproduces the tree, at every height. -/
theorem eval_treeFold (levels : Nat) :
    evalWithAnswerFn f (treeFold parameter lay tree leaf
        (fun level => evalWithAnswerFn f (treeNode parameter lay tree secret level
          (Nat.xor (leaf.val / 2 ^ level) 1)))
        levels (evalWithAnswerFn f (treeNode parameter lay tree secret 0 leaf.val)))
      = evalWithAnswerFn f (treeNode parameter lay tree secret levels (leaf.val / 2 ^ levels)) := by
  induction levels with
  | zero => simp
  | succ levels ih =>
      obtain ⟨j, hcase⟩ := index_sibling_cases (leaf.val / 2 ^ levels)
      have hj : leaf.val / 2 ^ (levels + 1) = j := by
        rw [div_pow_succ]
        rcases hcase with ⟨hc, _, _⟩ | ⟨hc, _, _⟩ <;> omega
      rw [treeFold_succ_eq, treeNode_succ_eq, evalWithAnswerFn_bind, ih, hj,
        evalWithAnswerFn_bind, evalWithAnswerFn_bind]
      rcases hcase with ⟨hc, hsibling, hmod⟩ | ⟨hc, hsibling, hmod⟩
      · have hbit : leaf.val.testBit levels = false := by
          rw [Bool.eq_false_iff, ne_eq, testBit_iff_div_mod]; omega
        rw [hbit, if_neg (by simp), hc, xor_one_two_mul]
      · have hbit : leaf.val.testBit levels = true := by
          rw [testBit_iff_div_mod]; omega
        rw [hbit, if_pos rfl, hc, xor_one_two_mul_add_one]

end SphincsSecurity.Concrete
