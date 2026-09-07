import SphincsSecurity.Proof.HashPrefixBudget

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

theorem consumesHashQueries_lift_sequenceFin {α : Type} {n : Nat}
    (computation : Fin n → OracleComp HashSpec α) (cost : Fin n → Nat)
    (hcost : ∀ i, ConsumesHashQueries (liftM (computation i)) (cost i)) :
    ConsumesHashQueries (liftM (sequenceFin computation)) (∑ i, cost i) := by
  induction n with
  | zero =>
      rw [Fin.sum_univ_zero]
      exact consumesHashQueries_pure (Fin.elim0 : Fin 0 → α)
  | succ n ih =>
      rw [sequenceFin, liftM_bind, Fin.sum_univ_succ]
      apply consumesHashQueries_bind _ _ _ _ (hcost 0)
      intro head
      rw [liftM_bind]
      rw [← Nat.add_zero (∑ i : Fin n, cost i.succ)]
      apply consumesHashQueries_bind _ _ _ _ (ih _ _ (fun i => hcost i.succ))
      intro tail
      exact consumesHashQueries_pure _

theorem consumesHashQueries_ftsNode (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (secret : FtsLeaf → Digest) (level nodeIdx : Nat) :
    ConsumesHashQueries (liftM (ftsNode parameter index tree secret level nodeIdx : OracleComp HashSpec Digest))
      (2 ^ (level + 1) - 1) := by
  induction level generalizing nodeIdx with
  | zero =>
      rw [ftsNode_zero_eq]
      exact consumesHashQueries_tweakableHash parameter (.ftsLeaf index tree (ftsLeafOfNat nodeIdx)) (digestBytes (secret (ftsLeafOfNat nodeIdx)))
  | succ level ih =>
      rw [ftsNode_succ_eq, liftM_bind]
      have hpower : 0 < 2 ^ (level + 1) := by positivity
      have hcost : 2 ^ (level + 1 + 1) - 1 = (2 ^ (level + 1) - 1) + ((2 ^ (level + 1) - 1) + 1) := by
        rw [pow_succ]
        omega
      rw [hcost]
      apply consumesHashQueries_bind _ _ _ _ (ih _)
      intro left
      rw [liftM_bind]
      apply consumesHashQueries_bind _ _ _ _ (ih _)
      intro right
      exact consumesHashQueries_tweakableHash _ _ _

theorem consumesHashQueries_ftsOpen (parameter : PublicParameter) (index : Index)
    (leaves : DigestTree → FtsLeaf) (secret : FtsTree → FtsLeaf → Digest) :
    ConsumesHashQueries (liftM (ftsOpen parameter index leaves secret : OracleComp HashSpec _))
      (∑ _tree : FtsTree, ∑ level : Fin ftsTreeHeight, (2 ^ (level.val + 1) - 1)) := by
  unfold ftsOpen
  apply consumesHashQueries_lift_sequenceFin
  intro tree
  apply consumesHashQueries_lift_sequenceFin
  intro level
  exact consumesHashQueries_ftsNode _ _ _ _ _ _

theorem consumesHashQueries_ftsOpen_1024 (parameter : PublicParameter) (index : Index)
    (leaves : DigestTree → FtsLeaf) (secret : FtsTree → FtsLeaf → Digest) :
    ConsumesHashQueries (liftM (ftsOpen parameter index leaves secret : OracleComp HashSpec _)) 1024 :=
  ConsumesHashQueries.mono (consumesHashQueries_ftsOpen parameter index leaves secret) (by decide)

end SphincsSecurity.Concrete
