import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Statement

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

end SphincsSecurity.Concrete
