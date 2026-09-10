import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeNativeRootSigner

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

theorem rootEncodingNativeCouples_revealPrivateLayerValues
    (parameter : PublicParameter) (target : Position)
    (leftRoot rightRoot : Digest) (index : Index) (lay : Layer)
    (encoding : ChainIndex → Digit) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot
      (revealPrivateLayerValues index lay encoding) := by
  unfold revealPrivateLayerValues
  apply (rootEncodingNativeCouples_sequenceFin parameter target leftRoot rightRoot _
    fun chainIdx => rootEncodingNativeCouples_revealCoordinate parameter target
      leftRoot rightRoot
        (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx
          (encoding chainIdx))).bind
  intro values
  apply (rootEncodingNativeCouples_sequenceFin parameter target leftRoot rightRoot _
    fun level => by
      by_cases hlevel : level.val < layerHeight lay
      · rw [if_pos hlevel]
        cases hzero : level.val with
        | zero =>
            exact rootEncodingNativeCouples_revealCoordinate parameter target leftRoot
              rightRoot (.position (.leaf lay (treeIndexAt index lay)
                (leafOfNat (Nat.xor (leafIndexAt index lay).val 1))))
        | succ current =>
            rw [Nat.add_one]
            simp only
            by_cases hcurrent : current < maxLayerHeight
            · rw [dif_pos hcurrent]
              exact rootEncodingNativeCouples_revealCoordinate parameter target leftRoot
                rightRoot (.position (.node lay (treeIndexAt index lay) ⟨current, hcurrent⟩
                  (leafOfNat (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
            · rw [dif_neg hcurrent]
              exact rootEncodingNativeCouples_pure parameter target leftRoot rightRoot 0
      · rw [if_neg hlevel]
        exact rootEncodingNativeCouples_pure parameter target leftRoot rightRoot 0).bind
  intro path
  exact rootEncodingNativeCouples_pure parameter target leftRoot rightRoot (values, path)

noncomputable def maskedChronologicalSignLayerWithTargetComparison
    (parameter : PublicParameter) (target : Position) (comparisonRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) (lay : Layer) :
    StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))
      (Option ChronologicalLayerPart) := do
  match ← maskedSignLayerWithTargetComparison parameter target comparisonRoot ftsSecret index lay with
  | none => pure none
  | some (counter, encoding) => do
      let values ← revealPrivateLayerValues index lay encoding
      pure (some ⟨counter, encoding, values.1, values.2⟩)

theorem rootEncodingNativeRelatesStored_maskedChronologicalSignLayer_targetComparison
    (parameter : PublicParameter) (target : Position) (hroot : IsLayerRoot target)
    (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) (lay : Layer) :
    RootEncodingNativeRelatesStored parameter target leftRoot rightRoot
      (maskedChronologicalSignLayer parameter ftsSecret index lay)
      (maskedChronologicalSignLayerWithTargetComparison parameter target rightRoot ftsSecret index lay) := by
  unfold maskedChronologicalSignLayer maskedChronologicalSignLayerWithTargetComparison
  apply (rootEncodingNativeRelatesStored_maskedSignLayer_targetComparison parameter target hroot
    leftRoot rightRoot ftsSecret index lay).bind
  intro leftSelected rightSelected heq
  subst rightSelected
  cases leftSelected with
  | none => exact (rootEncodingNativeCouples_pure parameter target leftRoot rightRoot none).relates.toStored
  | some selected =>
      apply (rootEncodingNativeCouples_revealPrivateLayerValues parameter target leftRoot rightRoot
        index lay selected.2).relates.toStored.bind
      intro leftValues rightValues heq
      subst rightValues
      exact (rootEncodingNativeCouples_pure parameter target leftRoot rightRoot
        (some (⟨selected.1, selected.2, leftValues.1, leftValues.2⟩ : ChronologicalLayerPart))).relates.toStored

theorem rootEncodingNativeCouples_publishChronologicalSignature
    (parameter : PublicParameter) (target : Position) (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (layers : Layer → Option ChronologicalLayerPart) :
    RootEncodingNativeCouples parameter target leftRoot rightRoot
      (publishChronologicalSignature ftsSecret randomness index leaves ftsPath layers) := by
  unfold publishChronologicalSignature
  cases hparts : traverseOption layers with
  | none => exact rootEncodingNativeCouples_pure parameter target leftRoot rightRoot none
  | some parts =>
      exact (rootEncodingNativeCouples_sequenceFin parameter target leftRoot rightRoot
        (fun lay => revealLayerValues index lay (parts lay).encoding)
        (fun lay => rootEncodingNativeCouples_revealLayerValues parameter target leftRoot rightRoot
          index lay (parts lay).encoding)).bind fun published =>
            rootEncodingNativeCouples_pure parameter target leftRoot rightRoot _

noncomputable def maskedPublishedChronologicalSignAfterDigestWithTargetComparison
    (parameter : PublicParameter) (target : Position) (comparisonRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) (Option Signature) := do
  let ftsPath ← simulateQ ordinaryHashImpl (ftsOpen parameter index leaves (ftsSecret index))
  let layers ← sequenceFin fun lay =>
    maskedChronologicalSignLayerWithTargetComparison parameter target comparisonRoot ftsSecret index lay
  publishChronologicalSignature ftsSecret randomness index leaves ftsPath layers

theorem rootEncodingNativeRelatesStored_maskedPublishedChronologicalSignAfterDigest_targetComparison
    (parameter : PublicParameter) (target : Position) (hroot : IsLayerRoot target)
    (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    RootEncodingNativeRelatesStored parameter target leftRoot rightRoot
      (maskedPublishedChronologicalSignAfterDigest parameter ftsSecret randomness index leaves)
      (maskedPublishedChronologicalSignAfterDigestWithTargetComparison parameter target rightRoot
        ftsSecret randomness index leaves) := by
  unfold maskedPublishedChronologicalSignAfterDigest
    maskedPublishedChronologicalSignAfterDigestWithTargetComparison maskedChronologicalSignLayers
  apply (rootEncodingNativeCouples_ftsOpen parameter target leftRoot rightRoot index leaves
    (ftsSecret index)).relates.toStored.bind
  intro leftPath rightPath hpath
  subst rightPath
  apply (rootEncodingNativeRelatesStored_sequenceFin parameter target leftRoot rightRoot _ _
    (fun lay => rootEncodingNativeRelatesStored_maskedChronologicalSignLayer_targetComparison
      parameter target hroot leftRoot rightRoot ftsSecret index lay)).bind
  intro leftLayers rightLayers hlayers
  subst rightLayers
  exact (rootEncodingNativeCouples_publishChronologicalSignature parameter target leftRoot rightRoot
    ftsSecret randomness index leaves leftPath leftLayers).relates.toStored

noncomputable def maskedPublishedChronologicalSignWithTargetComparison
    (parameter : PublicParameter) (root : Digest) (target : Position) (comparisonRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message) :
    StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) (Option Signature) := do
  let secretKey : SecretKey := ⟨parameter, root, fun _ _ _ _ => 0, ftsSecret⟩
  match ← simulateQ ordinaryRomImpl (signDigestLoop digestAttemptLimit secretKey message) with
  | none => pure none
  | some (randomness, index, leaves) =>
      maskedPublishedChronologicalSignAfterDigestWithTargetComparison parameter target comparisonRoot
        ftsSecret randomness index leaves

theorem rootEncodingNativeRelatesStored_maskedPublishedChronologicalSign_targetComparison
    (parameter : PublicParameter) (root : Digest) (target : Position) (hroot : IsLayerRoot target)
    (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message) :
    RootEncodingNativeRelatesStored parameter target leftRoot rightRoot
      (maskedPublishedChronologicalSign parameter root ftsSecret message)
      (maskedPublishedChronologicalSignWithTargetComparison parameter root target rightRoot ftsSecret message) := by
  unfold maskedPublishedChronologicalSign maskedPublishedChronologicalSignWithTargetComparison
  apply (rootEncodingNativeCouples_signDigestLoop target leftRoot rightRoot
    ⟨parameter, root, fun _ _ _ _ => 0, ftsSecret⟩ message digestAttemptLimit).relates.toStored.bind
  intro leftSelected rightSelected heq
  subst rightSelected
  cases leftSelected with
  | none => exact (rootEncodingNativeCouples_pure parameter target leftRoot rightRoot none).relates.toStored
  | some selected =>
      exact rootEncodingNativeRelatesStored_maskedPublishedChronologicalSignAfterDigest_targetComparison
        parameter target hroot leftRoot rightRoot ftsSecret selected.1 selected.2.1 selected.2.2

end SphincsSecurity.Concrete.OtsProbeSimulation
