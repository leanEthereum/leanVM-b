import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateRootCandidate

/-!
# Swapped-root signer state coupling

The selected root reveal is the only primitive whose returned digest differs in the two hidden
states. Its dedicated relation feeds the comparison root to both post-message signer continuations.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

theorem maskedTreeRoot_eq_ensure_reveal (lay : Layer) (tree : TreeIndex) :
    maskedTreeRoot lay tree = (do
      ensureTreeNode lay tree (layerHeight lay) 0
      revealPosition (layerRootPosition lay tree)) := by
  fin_cases lay <;>
    simp [maskedTreeRoot, maskedTreeNode, layerRootPosition, layerHeight,
      maxLayerHeight, leafOfNat] <;> congr 1

theorem chainValueCoordinate_ne_layerRoot
    {target : Position} (hroot : IsLayerRoot target)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (digit : Digit) :
    chainValueCoordinate lay tree leafIdx chainIdx digit ≠ .position target := by
  obtain ⟨rootLay, rootTree, rfl⟩ := hroot
  unfold chainValueCoordinate
  split <;> simp [layerRootPosition]

theorem pathNode_ne_layerRoot
    {target : Position} (hroot : IsLayerRoot target)
    (lay : Layer) (tree : TreeIndex) (current : Nat)
    (hcurrent : current < maxLayerHeight) (nodeIdx : LeafIndex)
    (hlt : current + 1 < layerHeight lay) :
    Position.node lay tree ⟨current, hcurrent⟩ nodeIdx ≠ target := by
  obtain ⟨rootLay, rootTree, rfl⟩ := hroot
  intro heq
  simp only [layerRootPosition, Position.node.injEq] at heq
  have hlay : lay = rootLay := heq.1
  subst rootLay
  have hlevel := congrArg Fin.val heq.2.2.1
  simp only at hlevel
  have hpos : 0 < layerHeight lay := by
    unfold layerHeight
    split <;> norm_num [maxLayerHeight]
  have hmax : 0 < maxLayerHeight := by norm_num [maxLayerHeight]
  omega

end SphincsSecurity.Concrete.OtsProbeSimulation
