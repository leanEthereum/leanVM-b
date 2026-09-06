import SphincsSecurity.Proof.JointProbeEncodingCacheSupport
import SphincsSecurity.Proof.OtsProbeStableExecutionCache

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
attribute [local irreducible] JointEncodingCacheMonotone
set_option backward.isDefEq.respectTransparency false

theorem jointEncodingCacheMonotone_bottomAndPublication
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (upper : Fin (numLayers - 1) → Option OtsProbeSimulation.ChronologicalLayerPart) (root : Digest) :
    JointEncodingCacheMonotone (jointSourceBottomAndPublication parameter randomness index leaves ftsPath upper root) := by
  unfold jointSourceBottomAndPublication
  exact (jointEncodingCacheMonotone_nativeBlock _
    (OtsProbeSimulation.ordinaryCacheMonotoneSupport_maskedChronologicalLayerAfterMessage parameter index bottomLayer root)).bind
      fun bottom => jointEncodingCacheMonotone_publication parameter randomness index leaves ftsPath (Fin.snoc upper bottom)

theorem jointEncodingCacheMonotone_keyAndPublication
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (upper : Fin (numLayers - 1) → Option OtsProbeSimulation.ChronologicalLayerPart) :
    JointEncodingCacheMonotone (jointSourceKeyAndPublication parameter randomness index leaves ftsPath upper) := by
  unfold jointSourceKeyAndPublication
  exact (jointEncodingCacheMonotone_ftsBlock _ (encodingCacheMonotoneSupport_maskedFtsKey parameter index)).bind
    (jointEncodingCacheMonotone_bottomAndPublication parameter randomness index leaves ftsPath upper)

theorem jointEncodingCacheMonotone_layersAndPublication
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) :
    JointEncodingCacheMonotone (jointSourceLayersAndPublication parameter randomness index leaves ftsPath) := by
  unfold jointSourceLayersAndPublication
  exact (jointEncodingCacheMonotone_nativeBlock _
    (OtsProbeSimulation.ordinaryCacheMonotoneSupport_maskedUpperChronologicalLayers parameter index)).bind
      (jointEncodingCacheMonotone_keyAndPublication parameter randomness index leaves ftsPath)

theorem jointEncodingCacheMonotone_signAfterDigest
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    JointEncodingCacheMonotone (jointSourceSignAfterDigest parameter randomness index leaves) := by
  unfold jointSourceSignAfterDigest
  exact (jointEncodingCacheMonotone_ftsBlock _ (encodingCacheMonotoneSupport_maskedFtsOpen parameter index leaves)).bind
    (jointEncodingCacheMonotone_layersAndPublication parameter randomness index leaves)

theorem jointEncodingCacheMonotone_sign (parameter : PublicParameter) (root : Digest) (message : Message) :
    JointEncodingCacheMonotone (jointSourceSign parameter root message) := by
  unfold jointSourceSign
  apply (jointEncodingCacheMonotone_nativeBlock _ (OtsProbeSimulation.ordinaryCacheMonotoneSupport_simulateQ_ordinaryRomImpl _)).bind
  intro selected
  cases selected with
  | none => exact jointEncodingCacheMonotone_nativeBlock _ (OtsProbeSimulation.OrdinaryCacheMonotoneSupport.pure _)
  | some selected => exact jointEncodingCacheMonotone_signAfterDigest parameter selected.1 selected.2.1 selected.2.2

end SphincsSecurity.Concrete.FtsProbeSimulation
