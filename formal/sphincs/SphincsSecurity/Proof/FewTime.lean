import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Statement

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

end SphincsSecurity.Concrete
