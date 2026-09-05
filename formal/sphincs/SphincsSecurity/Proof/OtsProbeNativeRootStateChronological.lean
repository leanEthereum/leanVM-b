import SphincsSecurity.Proof.OtsProbeNativeRootStateSigner

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

theorem nativeRootRelates_revealPrivateLayerValues
    (target : Position) (hroot : IsLayerRoot target)
    (leftOutput rightOutput : HashOutput)
    (index : Index) (lay : Layer) (encoding : ChainIndex → Digit) :
    NativeRootRelates target leftOutput rightOutput
      (revealPrivateLayerValues index lay encoding) (revealPrivateLayerValues index lay encoding) := by
  unfold revealPrivateLayerValues
  apply (nativeRootRelates_sequenceFin target leftOutput rightOutput _ _ fun chainIdx =>
    nativeRootRelates_revealCoordinate_of_ne target leftOutput rightOutput
      (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx
        (encoding chainIdx))
      (chainValueCoordinate_ne_layerRoot hroot lay (treeIndexAt index lay)
        (leafIndexAt index lay) chainIdx (encoding chainIdx))).bind
  intro leftValues rightValues hvalues
  subst rightValues
  apply (nativeRootRelates_sequenceFin target leftOutput rightOutput _ _ fun level => by
    by_cases hlevel : level.val < layerHeight lay
    · rw [if_pos hlevel]
      cases hzero : level.val with
      | zero =>
          exact nativeRootRelates_revealCoordinate_of_ne target leftOutput rightOutput
            (.position (.leaf lay (treeIndexAt index lay)
              (leafOfNat (Nat.xor (leafIndexAt index lay).val 1)))) (by
                obtain ⟨rootLay, rootTree, rfl⟩ := hroot
                simp [layerRootPosition])
      | succ current =>
          rw [Nat.add_one]
          simp only
          by_cases hcurrent : current < maxLayerHeight
          · rw [dif_pos hcurrent]
            exact nativeRootRelates_revealCoordinate_of_ne target leftOutput rightOutput
              (.position (.node lay (treeIndexAt index lay) ⟨current, hcurrent⟩
                (leafOfNat (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
              (by
                intro heq
                exact (pathNode_ne_layerRoot hroot lay (treeIndexAt index lay) current hcurrent _
                  (by omega)) (Coordinate.position.inj heq))
          · rw [dif_neg hcurrent]
            exact nativeRootRelates_pure target leftOutput rightOutput 0
    · rw [if_neg hlevel]
      exact nativeRootRelates_pure target leftOutput rightOutput 0).bind
  intro leftPath rightPath hpath
  subst rightPath
  exact nativeRootRelates_pure target leftOutput rightOutput (leftValues, leftPath)

theorem nativeRootRelates_chronologicalSignLayer_comparison_actual
    (parameter : PublicParameter) (target : Position) (hroot : IsLayerRoot target)
    (before after : HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) (lay : Layer) :
    NativeRootRelates target before after
      (maskedChronologicalSignLayerWithTargetComparison parameter target (truncateHash after) ftsSecret index lay)
      (maskedChronologicalSignLayer parameter ftsSecret index lay) := by
  unfold maskedChronologicalSignLayer maskedChronologicalSignLayerWithTargetComparison
  apply (nativeRootRelates_maskedSignLayerWithTargetComparison_actual parameter ftsSecret target hroot
    before after index lay).bind
  intro leftSelected rightSelected heq
  subst rightSelected
  cases leftSelected with
  | none => exact nativeRootRelates_pure target before after none
  | some selected =>
      apply (nativeRootRelates_revealPrivateLayerValues target hroot before after index lay selected.2).bind
      intro leftValues rightValues heq
      subst rightValues
      exact nativeRootRelates_pure target before after
        (some (⟨selected.1, selected.2, leftValues.1, leftValues.2⟩ : ChronologicalLayerPart))

theorem nativeRootRelates_publishChronologicalSignature
    (target : Position) (hroot : IsLayerRoot target) (before after : HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (layers : Layer → Option ChronologicalLayerPart) :
    NativeRootRelates target before after
      (publishChronologicalSignature ftsSecret randomness index leaves ftsPath layers)
      (publishChronologicalSignature ftsSecret randomness index leaves ftsPath layers) := by
  unfold publishChronologicalSignature
  cases hparts : traverseOption layers with
  | none => exact nativeRootRelates_pure target before after none
  | some parts =>
      apply (nativeRootRelates_sequenceFin target before after _ _
        (fun lay => nativeRootRelates_revealLayerValues target hroot before after index lay (parts lay).encoding)).bind
      intro leftValues rightValues heq
      subst rightValues
      exact nativeRootRelates_pure target before after _

theorem nativeRootRelates_chronologicalSignAfterDigest_comparison_actual
    (parameter : PublicParameter) (target : Position) (hroot : IsLayerRoot target)
    (before after : HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    NativeRootRelates target before after
      (maskedPublishedChronologicalSignAfterDigestWithTargetComparison parameter target (truncateHash after)
        ftsSecret randomness index leaves)
      (maskedPublishedChronologicalSignAfterDigest parameter ftsSecret randomness index leaves) := by
  unfold maskedPublishedChronologicalSignAfterDigest
    maskedPublishedChronologicalSignAfterDigestWithTargetComparison maskedChronologicalSignLayers
  apply (nativeRootRelates_simulateQ target before after ordinaryHashImpl ordinaryHashImpl
    (nativeRootRelates_ordinaryHashImpl target before after) (ftsOpen parameter index leaves (ftsSecret index))).bind
  intro leftPath rightPath hpath
  subst rightPath
  apply (nativeRootRelates_sequenceFin target before after _ _
    (fun lay => nativeRootRelates_chronologicalSignLayer_comparison_actual
      parameter target hroot before after ftsSecret index lay)).bind
  intro leftLayers rightLayers hlayers
  subst rightLayers
  exact nativeRootRelates_publishChronologicalSignature target hroot before after
    ftsSecret randomness index leaves leftPath leftLayers

theorem nativeRootRelates_chronologicalSign_comparison_actual
    (parameter : PublicParameter) (root : Digest) (target : Position) (hroot : IsLayerRoot target)
    (before after : HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message) :
    NativeRootRelates target before after
      (maskedPublishedChronologicalSignWithTargetComparison parameter root target (truncateHash after) ftsSecret message)
      (maskedPublishedChronologicalSign parameter root ftsSecret message) := by
  unfold maskedPublishedChronologicalSign maskedPublishedChronologicalSignWithTargetComparison
  apply (nativeRootRelates_simulateQ target before after ordinaryRomImpl ordinaryRomImpl
    (nativeRootRelates_ordinaryRomImpl target before after)
    (signDigestLoop digestAttemptLimit ⟨parameter, root, fun _ _ _ _ => 0, ftsSecret⟩ message)).bind
  intro leftSelected rightSelected heq
  subst rightSelected
  cases leftSelected with
  | none => exact nativeRootRelates_pure target before after none
  | some selected =>
      exact nativeRootRelates_chronologicalSignAfterDigest_comparison_actual parameter target hroot
        before after ftsSecret selected.1 selected.2.1 selected.2.2

end SphincsSecurity.Concrete.OtsProbeSimulation
