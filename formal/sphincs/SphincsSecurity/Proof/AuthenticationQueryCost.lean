import SphincsSecurity.Proof.InterleavedMass
import SphincsSecurity.Proof.StatementLemmas
import SphincsSecurity.Proof.RomQueryChargeBind

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem expected_hashQueries_lift_bind_of_constant
    (first : OracleComp HashSpec α) (next : α → OracleComp HashSpec β) (a b : Nat)
    (hfirst : ∀ cache, expectedQueryCharge (fun _ _ => 1) (liftM first) cache = a)
    (hnext : ∀ value cache, expectedQueryCharge (fun _ _ => 1) (liftM (next value)) cache = b)
    (cache : QueryCache HashSpec) :
    expectedQueryCharge (fun _ _ => 1) (liftM (first >>= next)) cache = (a + b : Nat) := by
  rw [liftM_bind, expectedQueryCharge_bind, hfirst]
  simp_rw [hnext]
  rw [ENNReal.tsum_mul_right, simulateQ_run_mass_of_query_mass romImpl romImpl_query_mass, one_mul, Nat.cast_add]

theorem expected_hashQueries_lift_sequenceFin {n : Nat}
    (computation : Fin n → OracleComp HashSpec α) (cost : Fin n → Nat)
    (hcost : ∀ index cache, expectedQueryCharge (fun _ _ => 1) (liftM (computation index)) cache = cost index)
    (cache : QueryCache HashSpec) :
    expectedQueryCharge (fun _ _ => 1) (liftM (sequenceFin computation)) cache = (∑ index, cost index : Nat) := by
  induction n generalizing cache with
  | zero => simp [sequenceFin]
  | succ n ih =>
      rw [sequenceFin, Fin.sum_univ_succ]
      apply expected_hashQueries_lift_bind_of_constant _ _ _ _ (hcost 0)
      intro head current
      rw [← Nat.add_zero (∑ index : Fin n, cost index.succ)]
      apply expected_hashQueries_lift_bind_of_constant _ _ _ _
        (fun before => ih (fun index => computation index.succ) (fun index => cost index.succ) (fun index => hcost index.succ) before)
      intro tail before
      simp

theorem expected_hashQueries_tweakableHash (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) (cache : QueryCache HashSpec) :
    expectedQueryCharge (fun _ _ => 1) (liftM (tweakableHash parameter domain payload : OracleComp HashSpec Digest)) cache = (1 : Nat) := by
  rw [Nat.cast_one]
  change expectedQueryCharge (fun _ _ => 1)
    ((liftM (OracleWorld.query (.inr (tweakableHashInput parameter domain payload))) : OracleComp OracleWorld HashOutput) >>=
      fun output => pure (truncateHash output)) cache = 1
  rw [expectedQueryCharge_query_bind]
  simp only [expectedQueryCharge_pure, mul_zero, tsum_zero, add_zero, hashQueryCharge, Sum.elim_inr]

theorem expected_hashQueries_chainWalk (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) (start steps : Nat) (value : Digest)
    (hsteps : start + steps ≤ chainLength - 1) (cache : QueryCache HashSpec) :
    expectedQueryCharge (fun _ _ => 1)
      (liftM (chainWalk parameter lay tree leafIdx chainIdx start steps value : OracleComp HashSpec Digest)) cache = steps := by
  induction steps generalizing cache with
  | zero => simp [chainWalk]
  | succ steps ih =>
      rw [chainWalk]
      apply expected_hashQueries_lift_bind_of_constant _ _ steps 1 (fun before => ih (by omega) before)
      intro previous before
      rw [dif_pos (show start + steps < chainLength - 1 by omega)]
      exact expected_hashQueries_tweakableHash _ _ _ _

theorem expected_hashQueries_oneTimePublicKey (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (secret : ChainIndex → Digest) (cache : QueryCache HashSpec) :
    expectedQueryCharge (fun _ _ => 1)
      (liftM (oneTimePublicKey parameter lay tree leafIdx secret : OracleComp HashSpec _)) cache = (294 : Nat) := by
  rw [oneTimePublicKey]
  have h := expected_hashQueries_lift_sequenceFin
    (fun chainIdx => (chainWalk parameter lay tree leafIdx chainIdx 0 (chainLength - 1) (secret chainIdx) : OracleComp HashSpec Digest))
    (fun _ => chainLength - 1)
    (fun chainIdx before => expected_hashQueries_chainWalk _ _ _ _ _ _ _ _ (by omega) before) cache
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    show numChains * (chainLength - 1) = 294 from rfl] using h

theorem expected_hashQueries_treeNode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (level nodeIdx : Nat) (cache : QueryCache HashSpec) :
    expectedQueryCharge (fun _ _ => 1)
      (liftM (treeNode parameter lay tree secret level nodeIdx : OracleComp HashSpec Digest)) cache =
        (296 * 2 ^ level - 1 : Nat) := by
  induction level generalizing nodeIdx cache with
  | zero =>
      rw [treeNode_zero_eq]
      exact expected_hashQueries_lift_bind_of_constant _ _ 294 1
        (expected_hashQueries_oneTimePublicKey _ _ _ _ _) (fun endpoints before => by
          rw [leafHash]
          exact expected_hashQueries_tweakableHash _ _ _ before) cache
  | succ level ih =>
      rw [treeNode_succ_eq]
      have hcost : 296 * 2 ^ (level + 1) - 1 = (296 * 2 ^ level - 1) + ((296 * 2 ^ level - 1) + 1) := by
        have hp : 0 < 2 ^ level := by positivity
        rw [pow_succ]
        omega
      rw [hcost]
      apply expected_hashQueries_lift_bind_of_constant _ _ _ _ (ih (2 * nodeIdx))
      intro left before
      apply expected_hashQueries_lift_bind_of_constant _ _ _ _ (ih (2 * nodeIdx + 1))
      intro right after
      exact expected_hashQueries_tweakableHash _ _ _ after

def authenticationHashCost (lay : Layer) : Nat :=
  ∑ level : Fin maxLayerHeight, if level.val < layerHeight lay then 296 * 2 ^ level.val - 1 else 0

theorem authenticationHashCost_ge32768 (lay : Layer) : 32768 ≤ authenticationHashCost lay := by
  revert lay
  decide

theorem expected_hashQueries_treePath (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (leafIdx : LeafIndex) (cache : QueryCache HashSpec) :
    expectedQueryCharge (fun _ _ => 1)
      (liftM (treePath parameter lay tree secret leafIdx : OracleComp HashSpec _)) cache = authenticationHashCost lay := by
  rw [treePath, authenticationHashCost]
  apply expected_hashQueries_lift_sequenceFin
  intro level before
  split_ifs
  · exact expected_hashQueries_treeNode _ _ _ _ _ _ before
  · simp

theorem expected_hashQueries_ftsNode (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (secret : FtsLeaf → Digest) (level nodeIdx : Nat) (cache : QueryCache HashSpec) :
    expectedQueryCharge (fun _ _ => 1)
      (liftM (ftsNode parameter index tree secret level nodeIdx : OracleComp HashSpec Digest)) cache =
        (2 ^ (level + 1) - 1 : Nat) := by
  induction level generalizing nodeIdx cache with
  | zero =>
      rw [ftsNode_zero_eq, ftsLeafHash]
      exact expected_hashQueries_tweakableHash _ _ _ cache
  | succ level ih =>
      rw [ftsNode_succ_eq]
      have hcost : 2 ^ (level + 1 + 1) - 1 = (2 ^ (level + 1) - 1) + ((2 ^ (level + 1) - 1) + 1) := by
        have hp : 0 < 2 ^ (level + 1) := by positivity
        rw [pow_succ]
        omega
      rw [hcost]
      apply expected_hashQueries_lift_bind_of_constant _ _ _ _ (ih (2 * nodeIdx))
      intro left before
      apply expected_hashQueries_lift_bind_of_constant _ _ _ _ (ih (2 * nodeIdx + 1))
      intro right after
      exact expected_hashQueries_tweakableHash _ _ _ after

theorem expected_hashQueries_ftsKey (parameter : PublicParameter) (index : Index)
    (secret : FtsTree → FtsLeaf → Digest) (cache : QueryCache HashSpec) :
    expectedQueryCharge (fun _ _ => 1) (liftM (ftsKey parameter index secret : OracleComp HashSpec Digest)) cache = (28659 : Nat) := by
  rw [ftsKey]
  apply expected_hashQueries_lift_bind_of_constant _ _ 28658 1
  · intro before
    have h := expected_hashQueries_lift_sequenceFin
      (fun tree => (ftsNode parameter index tree (secret tree) ftsTreeHeight 0 : OracleComp HashSpec Digest))
      (fun _ => 2 ^ (ftsTreeHeight + 1) - 1) (fun tree current => expected_hashQueries_ftsNode _ _ _ _ _ _ current) before
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      show (ftsTrees - 1) * (2 ^ (ftsTreeHeight + 1) - 1) = 28658 from rfl] using h
  · intro roots before
    exact expected_hashQueries_tweakableHash _ _ _ before

def layerMessageHashCost (lay : Layer) : Nat :=
  if hbelow : lay.val + 1 < numLayers then
    296 * 2 ^ layerHeight ⟨lay.val + 1, hbelow⟩ - 1
  else 28659

theorem layerMessageHashCost_ge24576 (lay : Layer) : 24576 ≤ layerMessageHashCost lay := by
  revert lay
  decide

theorem expected_hashQueries_layerMessage (key : SecretKey) (index : Index) (lay : Layer) (cache : QueryCache HashSpec) :
    expectedQueryCharge (fun _ _ => 1) (liftM (layerMessage key index lay : OracleComp HashSpec Digest)) cache = layerMessageHashCost lay := by
  rw [layerMessage, layerMessageHashCost]
  split_ifs
  · rw [treeRoot]
    exact expected_hashQueries_treeNode _ _ _ _ _ _ cache
  · exact expected_hashQueries_ftsKey _ _ _ cache

end SphincsSecurity.Concrete
