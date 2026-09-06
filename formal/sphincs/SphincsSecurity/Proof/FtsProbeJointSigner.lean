import SphincsSecurity.Proof.FtsProbeJointSignerBottom

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] maskedFtsKey maskedFtsOpen
  OtsProbeSimulation.maskedUpperChronologicalLayers OtsProbeSimulation.maskedChronologicalLayerAfterMessage

noncomputable def maskedJointKeyAndPublication
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (upper : Fin (numLayers - 1) → Option OtsProbeSimulation.ChronologicalLayerPart) : NativeFtsStep (Option Signature) :=
  bindNativeSteps (liftFtsBlock (maskedFtsKey parameter index))
    (maskedJointBottomAndPublication parameter randomness index leaves ftsPath upper)

theorem coupled_maskedJointKeyAndPublication
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (upper : Fin (numLayers - 1) → Option OtsProbeSimulation.ChronologicalLayerPart)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache) :
    NativeStepCoupledAt parameter table state ftsFuel
      (maskedJointKeyAndPublication parameter randomness index leaves ftsPath upper)
      (do
        let root ← simulateQ OtsProbeSimulation.ordinaryHashImpl (ftsKey parameter index (fun tree leaf => table (index, tree, leaf)))
        let bottom ← OtsProbeSimulation.maskedChronologicalLayerAfterMessage parameter index bottomLayer root
        OtsProbeSimulation.publishChronologicalSignature (fun index tree leaf => table (index, tree, leaf))
          randomness index leaves ftsPath (Fin.snoc upper bottom)) context fuel history cache ftsCache := by
  unfold maskedJointKeyAndPublication
  apply nativeStepCoupledAt_bind parameter table state ftsFuel _ _ _ _ context fuel history cache ftsCache hclean
    (liftFtsBlock_probeFree _ context fuel history cache (maskedFtsKey_probeFree parameter index))
  · exact projectNativeStepCache_liftFtsBlock parameter table state ftsFuel ftsCache _ _
      (coupled_maskedFtsKey parameter table state ftsFuel index hclean ftsCache) context fuel history cache
  · intro finalState entry finalCache hresult
    have hclean' := tableHits_false_of_mem_runDetailed_probeFree table state finalState ftsFuel _
      (liftFtsBlock_probeFree _ context fuel history cache (maskedFtsKey_probeFree parameter index) ftsCache)
      hclean _ hresult
    have hsynced' := revealedSynced_liftFtsBlock parameter table state finalState ftsFuel _
      context fuel history cache ftsCache finalCache (some entry) hclean hsynced
      (maskedFtsKey_stateFree parameter index) (maskedFtsKey_cachePreserving parameter index) hresult
    have hcached := hiddenIndexCached_liftFtsKey parameter table index state finalState ftsFuel
      context fuel history cache ftsCache finalCache (some entry) hclean hresult
    exact coupled_maskedJointBottomAndPublication parameter table randomness index leaves ftsPath upper entry.value.1
      finalState ftsFuel entry.context entry.remaining entry.history entry.value.2 finalCache hclean' hsynced' hcached

noncomputable def maskedJointLayersAndPublication
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest) : NativeFtsStep (Option Signature) :=
  bindNativeSteps (liftNativeBlock (OtsProbeSimulation.maskedUpperChronologicalLayers parameter index))
    (maskedJointKeyAndPublication parameter randomness index leaves ftsPath)

theorem coupled_maskedJointLayersAndPublication
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache) :
    NativeStepCoupledAt parameter table state ftsFuel
      (maskedJointLayersAndPublication parameter randomness index leaves ftsPath)
      (do
        let upper ← OtsProbeSimulation.maskedUpperChronologicalLayers parameter index
        let root ← simulateQ OtsProbeSimulation.ordinaryHashImpl (ftsKey parameter index (fun tree leaf => table (index, tree, leaf)))
        let bottom ← OtsProbeSimulation.maskedChronologicalLayerAfterMessage parameter index bottomLayer root
        OtsProbeSimulation.publishChronologicalSignature (fun index tree leaf => table (index, tree, leaf))
          randomness index leaves ftsPath (Fin.snoc upper bottom)) context fuel history cache ftsCache := by
  unfold maskedJointLayersAndPublication
  apply nativeStepCoupledAt_bind parameter table state ftsFuel _ _ _ _ context fuel history cache ftsCache hclean
    (liftNativeBlock_probeFree _ context fuel history cache)
  · exact projectNativeStepCache_liftNativeBlock parameter table state ftsFuel ftsCache _
      (cacheMapCommutes_native_maskedUpperChronologicalLayers parameter table ftsCache index)
      context fuel history cache hclean
  · intro finalState entry finalCache hresult
    obtain ⟨hstate, hsynced', _⟩ := invariants_liftNativeBlock parameter table state finalState ftsFuel _
      (fun cache => cacheMapCommutes_native_maskedUpperChronologicalLayers parameter table cache index)
      context fuel history cache ftsCache finalCache (some entry) hsynced hresult
    exact coupled_maskedJointKeyAndPublication parameter table randomness index leaves ftsPath entry.value.1
      finalState ftsFuel entry.context entry.remaining entry.history entry.value.2 finalCache (by simpa [hstate] using hclean) hsynced'

noncomputable def maskedJointSignAfterDigest
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    NativeFtsStep (Option Signature) :=
  bindNativeSteps (liftFtsBlock (maskedFtsOpen parameter index leaves))
    (maskedJointLayersAndPublication parameter randomness index leaves)

theorem coupled_maskedJointSignAfterDigest
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache) :
    NativeStepCoupledAt parameter table state ftsFuel
      (maskedJointSignAfterDigest parameter randomness index leaves)
      (OtsProbeSimulation.maskedPublishedChronologicalSignAfterDigest parameter
        (fun index tree leaf => table (index, tree, leaf)) randomness index leaves) context fuel history cache ftsCache := by
  rw [OtsProbeSimulation.maskedPublishedChronologicalSignAfterDigest_eq_ftsBoundary]
  unfold maskedJointSignAfterDigest
  apply nativeStepCoupledAt_bind parameter table state ftsFuel _ _ _ _ context fuel history cache ftsCache hclean
    (liftFtsBlock_probeFree _ context fuel history cache (maskedFtsOpen_probeFree parameter index leaves))
  · exact projectNativeStepCache_liftFtsBlock parameter table state ftsFuel ftsCache _ _
      (coupled_maskedFtsOpen parameter table state ftsFuel index leaves hclean ftsCache) context fuel history cache
  · intro finalState entry finalCache hresult
    have hclean' := tableHits_false_of_mem_runDetailed_probeFree table state finalState ftsFuel _
      (liftFtsBlock_probeFree _ context fuel history cache (maskedFtsOpen_probeFree parameter index leaves) ftsCache)
      hclean _ hresult
    have hsynced' := revealedSynced_liftFtsBlock parameter table state finalState ftsFuel _
      context fuel history cache ftsCache finalCache (some entry) hclean hsynced
      (maskedFtsOpen_stateFree parameter index leaves) (maskedFtsOpen_cachePreserving parameter index leaves) hresult
    exact coupled_maskedJointLayersAndPublication parameter table randomness index leaves entry.value.1
      finalState ftsFuel entry.context entry.remaining entry.history entry.value.2 finalCache hclean' hsynced'

end SphincsSecurity.Concrete.FtsProbeSimulation
