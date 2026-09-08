import SphincsSecurity.Proof.AuthenticationQueryCost
import SphincsSecurity.Proof.FtsSigningReserve

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem preExceptionSurvivalCost_reserved_chainWalk
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (start steps : Nat) (value : Digest) (hsteps : start + steps ≤ chainLength - 1) :
    PreExceptionSurvivalCost exception (nonMessageNonEncodingHashCharge parameter)
      (liftM (chainWalk parameter lay tree leafIdx chainIdx start steps value : OracleComp HashSpec Digest)) steps := by
  induction steps with
  | zero => exact preExceptionSurvivalCost_zero _ _ _
  | succ steps ih =>
      rw [chainWalk, liftM_bind]
      apply preExceptionSurvivalCost_bind _ _ _ _ steps 1 (ih (by omega))
      intro previous
      rw [dif_pos (show start + steps < chainLength - 1 by omega)]
      exact preExceptionSurvivalCost_reserved_tweakableHash _ _ _ _ (by simp [hashDomainFields]) (by simp [hashDomainFields])

theorem preExceptionSurvivalCost_reserved_oneTimePublicKey
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (secret : ChainIndex → Digest) :
    PreExceptionSurvivalCost exception (nonMessageNonEncodingHashCharge parameter)
      (liftM (oneTimePublicKey parameter lay tree leafIdx secret : OracleComp HashSpec _)) 294 := by
  rw [oneTimePublicKey]
  have h := preExceptionSurvivalCost_lift_sequenceFin exception (nonMessageNonEncodingHashCharge parameter)
    (fun chainIdx => (chainWalk parameter lay tree leafIdx chainIdx 0 (chainLength - 1) (secret chainIdx) : OracleComp HashSpec Digest))
    (fun _ => chainLength - 1)
    (fun chainIdx => preExceptionSurvivalCost_reserved_chainWalk _ _ _ _ _ _ _ _ _ (by omega))
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    show numChains * (chainLength - 1) = 294 from rfl] using h

theorem preExceptionSurvivalCost_reserved_treeNode
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (level nodeIdx : Nat) :
    PreExceptionSurvivalCost exception (nonMessageNonEncodingHashCharge parameter)
      (liftM (treeNode parameter lay tree secret level nodeIdx : OracleComp HashSpec Digest)) (296 * 2 ^ level - 1) := by
  induction level generalizing nodeIdx with
  | zero =>
      rw [treeNode_zero_eq, liftM_bind]
      apply preExceptionSurvivalCost_bind _ _ _ _ 294 1
        (preExceptionSurvivalCost_reserved_oneTimePublicKey _ _ _ _ _ _)
      intro endpoints
      rw [leafHash]
      exact preExceptionSurvivalCost_reserved_tweakableHash _ _ _ _ (by simp [hashDomainFields]) (by simp [hashDomainFields])
  | succ level ih =>
      rw [treeNode_succ_eq, liftM_bind]
      have hcost : 296 * 2 ^ (level + 1) - 1 = (296 * 2 ^ level - 1) + ((296 * 2 ^ level - 1) + 1) := by
        have hp : 0 < 2 ^ level := by positivity
        rw [pow_succ]
        omega
      rw [hcost]
      apply preExceptionSurvivalCost_bind _ _ _ _ _ _ (ih (2 * nodeIdx))
      intro left
      rw [liftM_bind]
      apply preExceptionSurvivalCost_bind _ _ _ _ _ _ (ih (2 * nodeIdx + 1))
      intro right
      exact preExceptionSurvivalCost_reserved_tweakableHash _ _ _ _ (by simp [hashDomainFields]) (by simp [hashDomainFields])

theorem preExceptionSurvivalCost_reserved_ftsKey
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (parameter : PublicParameter) (index : Index) (secret : FtsTree → FtsLeaf → Digest) :
    PreExceptionSurvivalCost exception (nonMessageNonEncodingHashCharge parameter)
      (liftM (ftsKey parameter index secret : OracleComp HashSpec Digest)) 28659 := by
  rw [ftsKey, liftM_bind]
  apply preExceptionSurvivalCost_bind _ _ _ _ 28658 1
  · have h := preExceptionSurvivalCost_lift_sequenceFin exception (nonMessageNonEncodingHashCharge parameter)
      (fun tree => (ftsNode parameter index tree (secret tree) ftsTreeHeight 0 : OracleComp HashSpec Digest))
      (fun _ => 2 ^ (ftsTreeHeight + 1) - 1) (fun tree => preExceptionSurvivalCost_reserved_ftsNode _ _ _ _ _ _ _)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      show (ftsTrees - 1) * (2 ^ (ftsTreeHeight + 1) - 1) = 28658 from rfl] using h
  · intro roots
    exact preExceptionSurvivalCost_reserved_tweakableHash _ _ _ _ (by simp [hashDomainFields]) (by simp [hashDomainFields])

theorem preExceptionSurvivalCost_reserved_layerMessage
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (key : SecretKey) (index : Index) (lay : Layer) :
    PreExceptionSurvivalCost exception (nonMessageNonEncodingHashCharge key.parameter)
      (liftM (layerMessage key index lay : OracleComp HashSpec Digest)) (layerMessageHashCost lay) := by
  rw [layerMessage, layerMessageHashCost]
  split_ifs
  · rw [treeRoot]
    exact preExceptionSurvivalCost_reserved_treeNode _ _ _ _ _ _ _
  · exact preExceptionSurvivalCost_reserved_ftsKey _ _ _ _

theorem preExceptionSurvivalCost_reserved_layerMessage_encodingBudget
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop) (key : SecretKey) (index : Index) (lay : Layer) :
    PreExceptionSurvivalCost exception (nonMessageNonEncodingHashCharge key.parameter)
      (liftM (layerMessage key index lay : OracleComp HashSpec Digest)) 24576 :=
  preExceptionSurvivalCost_mono _ _ _ _ _ (preExceptionSurvivalCost_reserved_layerMessage _ _ _ _) (layerMessageHashCost_ge24576 lay)

end SphincsSecurity.Concrete.FtsProbeSimulation
