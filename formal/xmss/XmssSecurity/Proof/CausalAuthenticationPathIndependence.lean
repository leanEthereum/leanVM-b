import XmssSecurity.Proof.ConcreteCorrectness
import XmssSecurity.Proof.TreeQueryBound

namespace XmssSecurity

theorem treeSubtreeValid_pathNode
    (epoch : Epoch) (levels : Nat) (hlevels : levels ≤ treeHeight) :
    TreeSubtreeValid levels
      (Concrete.CacheReplay.pathNode epoch levels) := by
  have hfactor :
      2 ^ (treeHeight - levels) * 2 ^ levels = lifetime := by
    rw [← pow_add, Nat.sub_add_cancel hlevels]
    rfl
  have hquotient : epoch.val / 2 ^ levels < 2 ^ (treeHeight - levels) := by
    rw [Nat.div_lt_iff_lt_mul (pow_pos (by omega) _)]
    rw [hfactor]
    exact epoch.isLt
  have hpath :
      (Concrete.CacheReplay.pathNode epoch levels).val =
        epoch.val / 2 ^ levels := by
    unfold Concrete.CacheReplay.pathNode Concrete.merkleNodeOfNat
    exact Nat.mod_eq_of_lt
      ((Nat.div_le_self epoch.val _).trans_lt epoch.isLt)
  unfold TreeSubtreeValid
  rw [hpath]
  nlinarith

theorem authenticationPathNode_subtreeValid
    (epoch : Epoch) (level : MerkleLevel) :
    TreeSubtreeValid level.val
      (Concrete.authenticationPathNode epoch level) := by
  have hparent : TreeSubtreeValid (level.val + 1)
      (Concrete.CacheReplay.pathNode epoch (level.val + 1)) :=
    treeSubtreeValid_pathNode epoch (level.val + 1) (by omega)
  have hchildren := Concrete.CacheReplay.pathNode_children
    epoch level.val level.isLt
  by_cases hbit : epoch.val.testBit level.val = true
  · rw [if_pos hbit] at hchildren
    have hvalid := childNode_subtreeValid level.val
      (Concrete.CacheReplay.pathNode epoch (level.val + 1)) false hparent
    rw [hchildren.1] at hvalid
    exact hvalid
  · rw [if_neg hbit] at hchildren
    have hvalid := childNode_subtreeValid level.val
      (Concrete.CacheReplay.pathNode epoch (level.val + 1)) true hparent
    rw [hchildren.2] at hvalid
    exact hvalid

end XmssSecurity
