import SphincsSecurity.Proof.OneTime
import SphincsSecurity.Proof.Merkle

/-!
# One layer of the hypertree

A layer's verifier half is `Ots.leaf` followed by `Tree.fold`. Together they turn the message the
layer signs into the layer's root, which is the message the layer above signs.
-/

namespace SphincsSecurity.Concrete

open OracleComp

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
  (secret : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex)

theorem leafOfNat_val : leafOfNat leaf.val = leaf := by
  ext
  simp [leafOfNat, Nat.mod_eq_of_lt leaf.isLt]

/-- The fold reads the path only below the height it folds. -/
theorem treeFold_congr {m : Type → Type} [Monad m] [HasQuery HashSpec m] (path path' : Nat → Digest)
    (levels : Nat) (hpath : ∀ level, level < levels → path level = path' level) (value : Digest) :
    treeFold (m := m) parameter lay tree leaf path levels value
      = treeFold (m := m) parameter lay tree leaf path' levels value := by
  induction levels with
  | zero => simp
  | succ levels ih =>
      rw [treeFold_succ_eq, treeFold_succ_eq, ih (fun level hlevel => hpath level (by omega)),
        hpath levels (by omega)]

/-- Folding a leaf's whole path reaches the layer's root. -/
theorem eval_treeFold_root (hleaf : leaf.val < 2 ^ layerHeight lay) :
    evalWithAnswerFn f (treeFold parameter lay tree leaf
        (fun level => evalWithAnswerFn f (treeNode parameter lay tree secret level
          (Nat.xor (leaf.val / 2 ^ level) 1)))
        (layerHeight lay) (evalWithAnswerFn f (treeNode parameter lay tree secret 0 leaf.val)))
      = evalWithAnswerFn f (treeRoot parameter lay tree secret) := by
  rw [eval_treeFold, treeRoot, Nat.div_eq_of_lt hleaf]

/-- **A layer.** Given a counter that encodes the message and a path that opens the leaf, the
verifier's half of a layer hands the layer's root to whatever follows it. -/
theorem eval_layer {α : Type} (message : Digest) (counter : Counter) (codeword : Encoding)
    (hencode : evalWithAnswerFn f (encode parameter lay tree leaf message counter) = some codeword)
    (hleaf : leaf.val < 2 ^ layerHeight lay) (path : Nat → Digest)
    (hpath : ∀ level, level < layerHeight lay → path level
      = evalWithAnswerFn f (treeNode parameter lay tree secret level
          (Nat.xor (leaf.val / 2 ^ level) 1)))
    (fail : OracleComp HashSpec α) (continuation : Digest → OracleComp HashSpec α) :
    evalWithAnswerFn f (do
        match ← otsLeaf parameter lay tree leaf message counter
            (fun chainIdx => evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0
              (codeword chainIdx).val (secret leaf chainIdx))) with
        | none => fail
        | some value => do
            let root ← treeFold parameter lay tree leaf path (layerHeight lay) value
            continuation root)
      = evalWithAnswerFn f (continuation
          (evalWithAnswerFn f (treeRoot parameter lay tree secret))) := by
  rw [evalWithAnswerFn_bind, eval_otsLeaf f parameter lay tree leaf (secret leaf) message counter
    codeword hencode]
  rw [evalWithAnswerFn_bind, treeFold_congr parameter lay tree leaf path _ _ hpath]
  rw [show evalWithAnswerFn f (do
        let endpoints ← oneTimePublicKey parameter lay tree leaf (secret leaf)
        leafHash parameter lay tree leaf endpoints)
      = evalWithAnswerFn f (treeNode parameter lay tree secret 0 leaf.val) by
    rw [treeNode_zero_eq, leafOfNat_val]]
  rw [eval_treeFold_root f parameter lay tree secret leaf hleaf]

end SphincsSecurity.Concrete
