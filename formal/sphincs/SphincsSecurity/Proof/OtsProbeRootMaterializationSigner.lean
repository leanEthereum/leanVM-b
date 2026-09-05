import SphincsSecurity.Proof.OtsProbeRootMaterializationHash

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem rootMaterializationPreserving_maskedTreeNode
    (lay : Layer) (tree : TreeIndex) (level nodeIdx : Nat) (hbounded : level ≤ layerHeight lay) :
    RootMaterializationPreserving (maskedTreeNode lay tree level nodeIdx) := by
  unfold maskedTreeNode
  apply (RootMaterializationPreserving.of_administrative (resolvedAdministrative_ensureTreeNode lay tree level nodeIdx)).bind
  intro _
  cases level with
  | zero => exact rootMaterializationPreserving_revealPosition _ trivial
  | succ current =>
      rw [Nat.add_one]
      simp only
      split_ifs
      · exact rootMaterializationPreserving_revealPosition _ hbounded
      · exact .pure _

theorem rootMaterializationPreserving_maskedTreeRoot (lay : Layer) (tree : TreeIndex) :
    RootMaterializationPreserving (maskedTreeRoot lay tree) :=
  rootMaterializationPreserving_maskedTreeNode lay tree (layerHeight lay) 0 le_rfl

theorem layerBoundedPosition_of_chainValueCoordinate
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex) (digit : Digit)
    (position : Position) (hposition : chainValueCoordinate lay tree leafIdx chainIdx digit = .position position) :
    LayerBoundedPosition position := by
  unfold chainValueCoordinate at hposition
  split_ifs at hposition
  have heq := Coordinate.position.inj hposition
  subst position
  trivial

theorem rootMaterializationPreserving_revealPublishedCoordinate_bounded
    (coordinate : Coordinate) (hbounded : ∀ position, coordinate = .position position → LayerBoundedPosition position) :
    RootMaterializationPreserving (revealPublishedCoordinate coordinate) :=
  (rootMaterializationPreserving_revealCoordinate_bounded coordinate hbounded).bind fun value =>
    (rootMaterializationPreserving_publishCoordinate coordinate).bind fun _ => .pure value

theorem rootMaterializationPreserving_layerValues
    (reveal : Coordinate → StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) Digest)
    (hreveal : ∀ coordinate, (∀ position, coordinate = .position position → LayerBoundedPosition position) →
      RootMaterializationPreserving (reveal coordinate))
    (index : Index) (lay : Layer) (encoding : ChainIndex → Digit) :
    RootMaterializationPreserving (do
      let values ← sequenceFin fun chainIdx => reveal
        (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx (encoding chainIdx))
      let path ← sequenceFin fun level : Fin maxLayerHeight =>
        if level.val < layerHeight lay then
          match level.val with
          | 0 => reveal (.position (.leaf lay (treeIndexAt index lay) (leafOfNat (Nat.xor (leafIndexAt index lay).val 1))))
          | current + 1 =>
              if hcurrent : current < maxLayerHeight then
                reveal (.position (.node lay (treeIndexAt index lay) ⟨current, hcurrent⟩
                  (leafOfNat (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
              else pure 0
        else pure 0
      pure (values, path)) := by
  apply (rootMaterializationPreserving_sequenceFin _ (fun chainIdx => hreveal _
    (layerBoundedPosition_of_chainValueCoordinate lay _ _ chainIdx (encoding chainIdx)))).bind
  intro values
  apply (rootMaterializationPreserving_sequenceFin _ (fun level => ?_)).bind
  · intro path
    exact .pure (values, path)
  · by_cases hlevel : level.val < layerHeight lay
    · rw [if_pos hlevel]
      cases hzero : level.val with
      | zero =>
          apply hreveal
          intro position hposition
          cases Coordinate.position.inj hposition
          trivial
      | succ current =>
          rw [Nat.add_one]
          simp only
          split_ifs
          · apply hreveal
            intro position hposition
            cases Coordinate.position.inj hposition
            change current + 1 ≤ layerHeight lay
            omega
          · exact .pure _
    · rw [if_neg hlevel]
      exact .pure _

theorem rootMaterializationPreserving_revealPrivateLayerValues
    (index : Index) (lay : Layer) (encoding : ChainIndex → Digit) :
    RootMaterializationPreserving (revealPrivateLayerValues index lay encoding) :=
  rootMaterializationPreserving_layerValues revealCoordinate rootMaterializationPreserving_revealCoordinate_bounded index lay encoding

theorem rootMaterializationPreserving_revealLayerValues
    (index : Index) (lay : Layer) (encoding : ChainIndex → Digit) :
    RootMaterializationPreserving (revealLayerValues index lay encoding) :=
  rootMaterializationPreserving_layerValues revealPublishedCoordinate rootMaterializationPreserving_revealPublishedCoordinate_bounded index lay encoding

theorem rootMaterializationPreserving_maskedLayerMessage (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) (lay : Layer) :
    RootMaterializationPreserving (maskedLayerMessage parameter ftsSecret index lay) := by
  unfold maskedLayerMessage
  split_ifs
  · exact rootMaterializationPreserving_maskedTreeRoot _ _
  · exact rootMaterializationPreserving_ordinaryHash _

theorem rootMaterializationPreserving_maskedOtsSignFrom (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest) :
    ∀ attempts counter, RootMaterializationPreserving (maskedOtsSignFrom parameter lay tree leafIdx message attempts counter)
  | 0, counter => .pure none
  | attempts + 1, counter => by
      rw [maskedOtsSignFrom]
      apply (rootMaterializationPreserving_ordinaryHash _).bind
      intro encoded
      cases encoded with
      | none => exact rootMaterializationPreserving_maskedOtsSignFrom parameter lay tree leafIdx message attempts (counter + 1)
      | some encoding =>
          exact (rootMaterializationPreserving_sequenceFin _ (fun chainIdx =>
            RootMaterializationPreserving.of_administrative (resolvedAdministrative_ensureChainPrefix lay tree leafIdx chainIdx (encoding chainIdx)))).bind
              (fun _ => .pure _)

theorem rootMaterializationPreserving_maskedSignLayer (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) (lay : Layer) :
    RootMaterializationPreserving (maskedSignLayer parameter ftsSecret index lay) := by
  unfold maskedSignLayer
  apply (rootMaterializationPreserving_maskedLayerMessage parameter ftsSecret index lay).bind
  intro message
  apply (rootMaterializationPreserving_maskedOtsSignFrom parameter lay (treeIndexAt index lay)
    (leafIndexAt index lay) message encodingAttemptLimit 0).bind
  intro selected
  cases selected with
  | none => exact .pure none
  | some selected =>
      exact (RootMaterializationPreserving.of_administrative (resolvedAdministrative_ensureTreePath lay (treeIndexAt index lay) (leafIndexAt index lay))).bind
        (fun _ => .pure (some selected))

theorem rootMaterializationPreserving_chronologicalSignLayer (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) (lay : Layer) :
    RootMaterializationPreserving (maskedChronologicalSignLayer parameter ftsSecret index lay) := by
  unfold maskedChronologicalSignLayer
  apply (rootMaterializationPreserving_maskedSignLayer parameter ftsSecret index lay).bind
  intro selected
  cases selected with
  | none => exact .pure none
  | some selected => exact (rootMaterializationPreserving_revealPrivateLayerValues index lay selected.2).bind (fun _ => .pure _)

theorem rootMaterializationPreserving_publishChronologicalSignature
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) (layers : Layer → Option ChronologicalLayerPart) :
    RootMaterializationPreserving (publishChronologicalSignature ftsSecret randomness index leaves ftsPath layers) := by
  unfold publishChronologicalSignature
  cases traverseOption layers with
  | none => exact .pure none
  | some parts => exact (rootMaterializationPreserving_sequenceFin _
      (fun lay => rootMaterializationPreserving_revealLayerValues index lay (parts lay).encoding)).bind (fun _ => .pure _)

theorem rootMaterializationPreserving_chronologicalSignAfterDigest (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    RootMaterializationPreserving (maskedPublishedChronologicalSignAfterDigest parameter ftsSecret randomness index leaves) := by
  unfold maskedPublishedChronologicalSignAfterDigest maskedChronologicalSignLayers
  exact (rootMaterializationPreserving_ordinaryHash _).bind fun ftsPath =>
    (rootMaterializationPreserving_sequenceFin _ (fun lay => rootMaterializationPreserving_chronologicalSignLayer parameter ftsSecret index lay)).bind
      (fun layers => rootMaterializationPreserving_publishChronologicalSignature ftsSecret randomness index leaves ftsPath layers)

theorem rootMaterializationPreserving_chronologicalSign (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message) :
    RootMaterializationPreserving (maskedPublishedChronologicalSign parameter root ftsSecret message) := by
  unfold maskedPublishedChronologicalSign
  apply (rootMaterializationPreserving_ordinaryRom _).bind
  intro selected
  cases selected with
  | none => exact .pure none
  | some selected =>
      exact rootMaterializationPreserving_chronologicalSignAfterDigest parameter ftsSecret selected.1 selected.2.1 selected.2.2

end SphincsSecurity.Concrete.OtsProbeSimulation
