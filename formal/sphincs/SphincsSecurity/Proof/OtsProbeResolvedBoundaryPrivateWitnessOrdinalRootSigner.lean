import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeOrigin
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootCache

/-!
# Layer-root signer comparison

Once a middle or bottom layer root has been materialized, recomputing that tree root returns the
same digest. A proof-only signer can therefore keep the concrete structural computation while
substituting an independent comparison root only in the upper encoding call.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

theorem layerMessage_root_witness_of_isLayerRoot
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (index : Index) (lay : Layer)
    (htarget : layerMessagePosition index lay = target) :
    ∃ below : Layer,
      maskedLayerMessage parameter ftsSecret index lay =
          maskedTreeRoot below (treeIndexAt index below) ∧
        layerMessagePosition index lay =
          layerRootPosition below (treeIndexAt index below) := by
  have hnotBottom : lay ≠ bottomLayer := by
    intro hbottom
    subst lay
    obtain ⟨rootLay, rootTree, hrootPosition⟩ := hroot
    rw [layerMessagePosition_bottom] at htarget
    rw [← htarget] at hrootPosition
    simp [layerRootPosition] at hrootPosition
  fin_cases lay
  · have hbelow : topLayer.val + 1 < numLayers := by
      norm_num [topLayer, numLayers]
    refine ⟨middleLayer, maskedLayerMessage_eq_of_lt' parameter ftsSecret index topLayer
      middleLayer hbelow (Fin.ext (by norm_num [topLayer, middleLayer, numLayers])), ?_⟩
    change layerMessagePosition index topLayer =
      layerRootPosition middleLayer (treeIndexAt index middleLayer)
    simp [layerRootPosition]
  · have hbelow : middleLayer.val + 1 < numLayers := by
      norm_num [middleLayer, numLayers]
    refine ⟨bottomLayer, maskedLayerMessage_eq_of_lt' parameter ftsSecret index middleLayer
      bottomLayer hbelow (Fin.ext (by norm_num [middleLayer, bottomLayer, numLayers])), ?_⟩
    change layerMessagePosition index middleLayer =
      layerRootPosition bottomLayer (treeIndexAt index bottomLayer)
    simp [layerRootPosition]
  · exact False.elim (hnotBottom rfl)

noncomputable def maskedSignLayerWithComparisonRoot
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer) (comparisonRoot : Digest) :
    StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))
      (Option (Counter × (ChainIndex → Digit))) := do
  let _ ← maskedLayerMessage parameter ftsSecret index lay
  maskedOtsLayerAfterMessage parameter index lay comparisonRoot

theorem not_encodingPositionNamesRoot_of_layerMessagePosition_ne
    (target : Position) (index : Index) (lay : Layer)
    (hne : layerMessagePosition index lay ≠ target) :
    ¬EncodingPositionNamesRoot target
      ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩ := by
  rintro ⟨otherIndex, htree, hleaf, _hnotBottom, htarget⟩
  apply hne
  rw [htarget]
  exact (layerMessagePosition_eq_of_position_eq otherIndex index lay htree hleaf).symm

theorem layer_ne_bottom_of_layerMessagePosition_isLayerRoot
    {target : Position} {index : Index} {lay : Layer}
    (htarget : layerMessagePosition index lay = target)
    (hroot : IsLayerRoot target) : lay ≠ bottomLayer := by
  intro hbottom
  subst lay
  obtain ⟨rootLay, rootTree, hrootPosition⟩ := hroot
  rw [layerMessagePosition_bottom] at htarget
  rw [← htarget] at hrootPosition
  simp [layerRootPosition] at hrootPosition

noncomputable def maskedSignLayerWithTargetComparison
    (parameter : PublicParameter) (target : Position) (comparisonRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer) :
    StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))
      (Option (Counter × (ChainIndex → Digit))) :=
  if layerMessagePosition index lay = target then
    maskedSignLayerWithComparisonRoot parameter ftsSecret index lay comparisonRoot
  else
    maskedSignLayer parameter ftsSecret index lay

end SphincsSecurity.Concrete.OtsProbeSimulation
