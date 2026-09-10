import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeNativeOrdinaryCache

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

theorem ordinaryCacheNativeCouples_ensureFullChain
    (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    OrdinaryCacheNativeCouples
      (ensureFullChain lay tree leafIdx chainIdx) := by
  unfold ensureFullChain
  exact (ordinaryCacheNativeCouples_sequenceFin _
    fun step => ordinaryCacheNativeCouples_ensureCoordinate
      (.position (.chain lay tree leafIdx chainIdx step))).bind fun _ =>
        ordinaryCacheNativeCouples_pure ()

theorem ordinaryCacheNativeCouples_ensureOtsLeaf
    (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) :
    OrdinaryCacheNativeCouples
      (ensureOtsLeaf lay tree leafIdx) := by
  unfold ensureOtsLeaf
  exact (ordinaryCacheNativeCouples_sequenceFin _
    fun chainIdx => ordinaryCacheNativeCouples_ensureFullChain
      lay tree leafIdx chainIdx).bind fun _ =>
        ordinaryCacheNativeCouples_ensureCoordinate
          (.position (.leaf lay tree leafIdx))

theorem ordinaryCacheNativeCouples_ensureTreeNode
    (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx,
      OrdinaryCacheNativeCouples
        (ensureTreeNode lay tree level nodeIdx)
  | 0, nodeIdx => by
      rw [ensureTreeNode]
      exact ordinaryCacheNativeCouples_ensureOtsLeaf lay tree
        (leafOfNat nodeIdx)
  | level + 1, nodeIdx => by
      rw [ensureTreeNode]
      exact (ordinaryCacheNativeCouples_ensureTreeNode lay tree
        level (2 * nodeIdx)).bind fun _ =>
          (ordinaryCacheNativeCouples_ensureTreeNode lay tree
            level (2 * nodeIdx + 1)).bind fun _ => by
              by_cases hlevel : level < maxLayerHeight
              · rw [dif_pos hlevel]
                exact ordinaryCacheNativeCouples_ensureCoordinate (.position (.node lay tree ⟨level, hlevel⟩ (leafOfNat nodeIdx)))
              · rw [dif_neg hlevel]
                exact ordinaryCacheNativeCouples_pure ()

theorem ordinaryCacheNativeCouples_ensureTreePath
    (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) :
    OrdinaryCacheNativeCouples
      (ensureTreePath lay tree leafIdx) := by
  unfold ensureTreePath
  exact (ordinaryCacheNativeCouples_sequenceFin _
    fun level => by
      by_cases hlevel : level.val < layerHeight lay
      · rw [if_pos hlevel]
        exact ordinaryCacheNativeCouples_ensureTreeNode lay tree
          level.val (Nat.xor (leafIdx.val / 2 ^ level.val) 1)
      · rw [if_neg hlevel]
        exact ordinaryCacheNativeCouples_pure ()).bind fun _ =>
          ordinaryCacheNativeCouples_pure ()

theorem ordinaryCacheNativeCouples_revealPublishedCoordinate
    (coordinate : Coordinate) :
    OrdinaryCacheNativeCouples
      (revealPublishedCoordinate coordinate) := by
  unfold revealPublishedCoordinate
  exact (ordinaryCacheNativeCouples_revealCoordinate
    coordinate).bind fun _ =>
      (ordinaryCacheNativeCouples_publishCoordinate
        coordinate).bind fun _ =>
          ordinaryCacheNativeCouples_pure _

theorem ordinaryCacheNativeCouples_revealLayerValues
    (index : Index) (lay : Layer)
    (encoding : ChainIndex → Digit) :
    OrdinaryCacheNativeCouples
      (revealLayerValues index lay encoding) := by
  unfold revealLayerValues
  apply (ordinaryCacheNativeCouples_sequenceFin _
    fun chainIdx => ordinaryCacheNativeCouples_revealPublishedCoordinate
        (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx
          (encoding chainIdx))).bind
  intro values
  apply (ordinaryCacheNativeCouples_sequenceFin _
    fun level => by
      by_cases hlevel : level.val < layerHeight lay
      · rw [if_pos hlevel]
        cases hzero : level.val with
        | zero =>
            exact ordinaryCacheNativeCouples_revealPublishedCoordinate (.position (.leaf lay (treeIndexAt index lay)
                (leafOfNat (Nat.xor (leafIndexAt index lay).val 1))))
        | succ current =>
            rw [Nat.add_one]
            simp only
            by_cases hcurrent : current < maxLayerHeight
            · rw [dif_pos hcurrent]
              exact ordinaryCacheNativeCouples_revealPublishedCoordinate (.position (.node lay (treeIndexAt index lay) ⟨current, hcurrent⟩
                  (leafOfNat (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
            · rw [dif_neg hcurrent]
              exact ordinaryCacheNativeCouples_pure 0
      · rw [if_neg hlevel]
        exact ordinaryCacheNativeCouples_pure 0).bind
  intro path
  exact ordinaryCacheNativeCouples_pure (values, path)

theorem ordinaryCacheNativeCouples_maskedTreeNode
    (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx,
      OrdinaryCacheNativeCouples
        (maskedTreeNode lay tree level nodeIdx)
  | level, nodeIdx => by
      unfold maskedTreeNode
      apply (ordinaryCacheNativeCouples_ensureTreeNode lay tree
        level nodeIdx).bind
      intro _
      cases level with
      | zero =>
          exact ordinaryCacheNativeCouples_revealPosition
            (.leaf lay tree (leafOfNat nodeIdx))
      | succ current =>
          rw [Nat.add_one]
          simp only
          by_cases hlevel : current < maxLayerHeight
          · rw [dif_pos hlevel]
            exact ordinaryCacheNativeCouples_revealPosition
              (.node lay tree ⟨current, hlevel⟩ (leafOfNat nodeIdx))
          · rw [dif_neg hlevel]
            exact ordinaryCacheNativeCouples_pure 0

theorem ordinaryCacheNativeCouples_maskedTreeRoot
    (lay : Layer) (tree : TreeIndex) :
    OrdinaryCacheNativeCouples
      (maskedTreeRoot lay tree) :=
  ordinaryCacheNativeCouples_maskedTreeNode lay tree
    (layerHeight lay) 0

theorem ordinaryCacheNativeCouples_revealPrivateLayerValues
    (index : Index) (lay : Layer)
    (encoding : ChainIndex → Digit) :
    OrdinaryCacheNativeCouples
      (revealPrivateLayerValues index lay encoding) := by
  unfold revealPrivateLayerValues
  apply (ordinaryCacheNativeCouples_sequenceFin _
    fun chainIdx => ordinaryCacheNativeCouples_revealCoordinate
        (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx
          (encoding chainIdx))).bind
  intro values
  apply (ordinaryCacheNativeCouples_sequenceFin _
    fun level => by
      by_cases hlevel : level.val < layerHeight lay
      · rw [if_pos hlevel]
        cases hzero : level.val with
        | zero =>
            exact ordinaryCacheNativeCouples_revealCoordinate (.position (.leaf lay (treeIndexAt index lay)
                (leafOfNat (Nat.xor (leafIndexAt index lay).val 1))))
        | succ current =>
            rw [Nat.add_one]
            simp only
            by_cases hcurrent : current < maxLayerHeight
            · rw [dif_pos hcurrent]
              exact ordinaryCacheNativeCouples_revealCoordinate (.position (.node lay (treeIndexAt index lay) ⟨current, hcurrent⟩
                  (leafOfNat (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
            · rw [dif_neg hcurrent]
              exact ordinaryCacheNativeCouples_pure 0
      · rw [if_neg hlevel]
        exact ordinaryCacheNativeCouples_pure 0).bind
  intro path
  exact ordinaryCacheNativeCouples_pure (values, path)

theorem ordinaryCacheNativeCouples_maskedLayerMessage (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) (lay : Layer) :
    OrdinaryCacheNativeCouples (maskedLayerMessage parameter ftsSecret index lay) := by
  unfold maskedLayerMessage
  by_cases hbelow : lay.val + 1 < numLayers
  · rw [dif_pos hbelow]
    exact ordinaryCacheNativeCouples_maskedTreeRoot _ _
  · rw [dif_neg hbelow]
    exact ordinaryCacheNativeCouples_ordinaryHash _

theorem ordinaryCacheNativeCouples_maskedOtsSignFrom (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest) :
    ∀ attempts counter, OrdinaryCacheNativeCouples
      (maskedOtsSignFrom parameter lay tree leafIdx message attempts counter)
  | 0, counter => by
      rw [maskedOtsSignFrom]
      exact ordinaryCacheNativeCouples_pure none
  | attempts + 1, counter => by
      rw [maskedOtsSignFrom]
      apply (ordinaryCacheNativeCouples_ordinaryHash _).bind
      intro encoded
      cases encoded with
      | none => exact ordinaryCacheNativeCouples_maskedOtsSignFrom parameter lay tree leafIdx message attempts (counter + 1)
      | some encoding =>
          exact (ordinaryCacheNativeCouples_sequenceFin _
            (fun chainIdx => ordinaryCacheNativeCouples_ensureChainPrefix lay tree leafIdx chainIdx (encoding chainIdx))).bind
              fun _ => ordinaryCacheNativeCouples_pure _

theorem ordinaryCacheNativeCouples_maskedSignLayer (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) (lay : Layer) :
    OrdinaryCacheNativeCouples (maskedSignLayer parameter ftsSecret index lay) := by
  unfold maskedSignLayer
  apply (ordinaryCacheNativeCouples_maskedLayerMessage parameter ftsSecret index lay).bind
  intro message
  apply (ordinaryCacheNativeCouples_maskedOtsSignFrom parameter lay (treeIndexAt index lay)
    (leafIndexAt index lay) message encodingAttemptLimit 0).bind
  intro selected
  cases selected with
  | none => exact ordinaryCacheNativeCouples_pure none
  | some selected =>
      exact (ordinaryCacheNativeCouples_ensureTreePath lay (treeIndexAt index lay) (leafIndexAt index lay)).bind
        fun _ => ordinaryCacheNativeCouples_pure (some selected)

theorem ordinaryCacheNativeCouples_chronologicalSignLayer (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) (lay : Layer) :
    OrdinaryCacheNativeCouples (maskedChronologicalSignLayer parameter ftsSecret index lay) := by
  unfold maskedChronologicalSignLayer
  apply (ordinaryCacheNativeCouples_maskedSignLayer parameter ftsSecret index lay).bind
  intro selected
  cases selected with
  | none => exact ordinaryCacheNativeCouples_pure none
  | some selected =>
      exact (ordinaryCacheNativeCouples_revealPrivateLayerValues index lay selected.2).bind
        fun values => ordinaryCacheNativeCouples_pure _

theorem ordinaryCacheNativeCouples_publishChronologicalSignature
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) (layers : Layer → Option ChronologicalLayerPart) :
    OrdinaryCacheNativeCouples (publishChronologicalSignature ftsSecret randomness index leaves ftsPath layers) := by
  unfold publishChronologicalSignature
  cases hparts : traverseOption layers with
  | none => exact ordinaryCacheNativeCouples_pure none
  | some parts =>
      exact (ordinaryCacheNativeCouples_sequenceFin _
        (fun lay => ordinaryCacheNativeCouples_revealLayerValues index lay (parts lay).encoding)).bind
          fun published => ordinaryCacheNativeCouples_pure _

theorem ordinaryCacheNativeCouples_chronologicalSignAfterDigest (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    OrdinaryCacheNativeCouples
      (maskedPublishedChronologicalSignAfterDigest parameter ftsSecret randomness index leaves) := by
  unfold maskedPublishedChronologicalSignAfterDigest maskedChronologicalSignLayers
  exact (ordinaryCacheNativeCouples_ordinaryHash _).bind fun ftsPath =>
    (ordinaryCacheNativeCouples_sequenceFin _
      (fun lay => ordinaryCacheNativeCouples_chronologicalSignLayer parameter ftsSecret index lay)).bind
        fun layers => ordinaryCacheNativeCouples_publishChronologicalSignature ftsSecret randomness index leaves ftsPath layers

theorem ordinaryCacheNativeCouples_chronologicalSign (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message) :
    OrdinaryCacheNativeCouples (maskedPublishedChronologicalSign parameter root ftsSecret message) := by
  unfold maskedPublishedChronologicalSign
  apply (ordinaryCacheNativeCouples_ordinaryRom _).bind
  intro selected
  cases selected with
  | none => exact ordinaryCacheNativeCouples_pure none
  | some selected =>
      exact ordinaryCacheNativeCouples_chronologicalSignAfterDigest parameter ftsSecret selected.1 selected.2.1 selected.2.2

end SphincsSecurity.Concrete.OtsProbeSimulation
