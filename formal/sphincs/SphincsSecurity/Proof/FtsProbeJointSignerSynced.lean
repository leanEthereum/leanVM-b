import SphincsSecurity.Proof.FtsProbeJointSignerProbeFree
import SphincsSecurity.Proof.FtsProbeStepSupport

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] maskedFtsKey maskedFtsOpen signDigestLoop
  OtsProbeSimulation.maskedUpperChronologicalLayers OtsProbeSimulation.maskedChronologicalLayerAfterMessage

theorem revealedSynced_maskedJointBottomAndPublication
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (upper : Fin (numLayers - 1) → Option OtsProbeSimulation.ChronologicalLayerPart) (root : Digest)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache finalCache : SplitHashCache) (result : NativePublicationResult)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache) (hcached : HiddenIndexCached index ftsCache)
    (hresult : .done false finalState (result, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel
        ((maskedJointBottomAndPublication parameter randomness index leaves ftsPath upper root context fuel history cache).run ftsCache))) :
    RevealedSynced parameter table finalState finalCache := by
  unfold maskedJointBottomAndPublication at hresult
  refine preserves_bindNativeSteps table state finalState ftsFuel _ _ context fuel history cache ftsCache finalCache result
    (RevealedSynced parameter table) hclean (liftNativeBlock_probeFree _ context fuel history cache) ?_ ?_ hresult
  · intro stepState entry stepCache hleft
    exact (invariants_liftNativeBlock parameter table state stepState ftsFuel _
      (fun cache => cacheMapCommutes_native_maskedChronologicalLayerAfterMessage parameter table cache index bottomLayer root)
      context fuel history cache ftsCache stepCache entry hsynced hleft).2.1
  · intro stepState entry stepCache hleft hnext
    obtain ⟨hstate, hsynced', hhidden⟩ := invariants_liftNativeBlock parameter table state stepState ftsFuel _
      (fun cache => cacheMapCommutes_native_maskedChronologicalLayerAfterMessage parameter table cache index bottomLayer root)
      context fuel history cache ftsCache stepCache (some entry) hsynced hleft
    have hcached' : HiddenIndexCached index stepCache := by
      intro tree leaf
      simpa only [hhidden] using hcached tree leaf
    exact (invariants_revealAfterNativeBody parameter table index leaves stepState finalState ftsFuel stepCache finalCache _ result
      (by simpa [hstate] using hclean) hsynced' hcached' hnext).2.1

theorem revealedSynced_maskedJointKeyAndPublication
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (upper : Fin (numLayers - 1) → Option OtsProbeSimulation.ChronologicalLayerPart)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache finalCache : SplitHashCache) (result : NativePublicationResult)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache)
    (hresult : .done false finalState (result, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel
        ((maskedJointKeyAndPublication parameter randomness index leaves ftsPath upper context fuel history cache).run ftsCache))) :
    RevealedSynced parameter table finalState finalCache := by
  unfold maskedJointKeyAndPublication at hresult
  refine preserves_bindNativeSteps table state finalState ftsFuel _ _ context fuel history cache ftsCache finalCache result
    (RevealedSynced parameter table) hclean
    (liftFtsBlock_probeFree _ context fuel history cache (maskedFtsKey_probeFree parameter index)) ?_ ?_ hresult
  · intro stepState entry stepCache hleft
    exact revealedSynced_liftFtsBlock parameter table state stepState ftsFuel _ context fuel history cache ftsCache stepCache entry
      hclean hsynced (maskedFtsKey_stateFree parameter index) (maskedFtsKey_cachePreserving parameter index) hleft
  · intro stepState entry stepCache hleft hnext
    have hclean' := tableHits_false_of_mem_runDetailed_probeFree table state stepState ftsFuel _
      (liftFtsBlock_probeFree _ context fuel history cache (maskedFtsKey_probeFree parameter index) ftsCache) hclean _ hleft
    have hsynced' := revealedSynced_liftFtsBlock parameter table state stepState ftsFuel _
      context fuel history cache ftsCache stepCache (some entry) hclean hsynced
      (maskedFtsKey_stateFree parameter index) (maskedFtsKey_cachePreserving parameter index) hleft
    have hcached := hiddenIndexCached_liftFtsKey parameter table index state stepState ftsFuel
      context fuel history cache ftsCache stepCache (some entry) hclean hleft
    exact revealedSynced_maskedJointBottomAndPublication parameter table randomness index leaves ftsPath upper entry.value.1
      stepState finalState ftsFuel entry.context entry.remaining entry.history entry.value.2 stepCache finalCache result
      hclean' hsynced' hcached hnext

theorem revealedSynced_maskedJointLayersAndPublication
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache finalCache : SplitHashCache) (result : NativePublicationResult)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache)
    (hresult : .done false finalState (result, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel
        ((maskedJointLayersAndPublication parameter randomness index leaves ftsPath context fuel history cache).run ftsCache))) :
    RevealedSynced parameter table finalState finalCache := by
  unfold maskedJointLayersAndPublication at hresult
  refine preserves_bindNativeSteps table state finalState ftsFuel _ _ context fuel history cache ftsCache finalCache result
    (RevealedSynced parameter table) hclean (liftNativeBlock_probeFree _ context fuel history cache) ?_ ?_ hresult
  · intro stepState entry stepCache hleft
    exact (invariants_liftNativeBlock parameter table state stepState ftsFuel _
      (fun cache => cacheMapCommutes_native_maskedUpperChronologicalLayers parameter table cache index)
      context fuel history cache ftsCache stepCache entry hsynced hleft).2.1
  · intro stepState entry stepCache hleft hnext
    obtain ⟨hstate, hsynced', _⟩ := invariants_liftNativeBlock parameter table state stepState ftsFuel _
      (fun cache => cacheMapCommutes_native_maskedUpperChronologicalLayers parameter table cache index)
      context fuel history cache ftsCache stepCache (some entry) hsynced hleft
    exact revealedSynced_maskedJointKeyAndPublication parameter table randomness index leaves ftsPath entry.value.1
      stepState finalState ftsFuel entry.context entry.remaining entry.history entry.value.2 stepCache finalCache result
      (by simpa [hstate] using hclean) hsynced' hnext

theorem revealedSynced_maskedJointSignAfterDigest
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache finalCache : SplitHashCache) (result : NativePublicationResult)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache)
    (hresult : .done false finalState (result, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel
        ((maskedJointSignAfterDigest parameter randomness index leaves context fuel history cache).run ftsCache))) :
    RevealedSynced parameter table finalState finalCache := by
  unfold maskedJointSignAfterDigest at hresult
  refine preserves_bindNativeSteps table state finalState ftsFuel _ _ context fuel history cache ftsCache finalCache result
    (RevealedSynced parameter table) hclean
    (liftFtsBlock_probeFree _ context fuel history cache (maskedFtsOpen_probeFree parameter index leaves)) ?_ ?_ hresult
  · intro stepState entry stepCache hleft
    exact revealedSynced_liftFtsBlock parameter table state stepState ftsFuel _ context fuel history cache ftsCache stepCache entry
      hclean hsynced (maskedFtsOpen_stateFree parameter index leaves) (maskedFtsOpen_cachePreserving parameter index leaves) hleft
  · intro stepState entry stepCache hleft hnext
    have hclean' := tableHits_false_of_mem_runDetailed_probeFree table state stepState ftsFuel _
      (liftFtsBlock_probeFree _ context fuel history cache (maskedFtsOpen_probeFree parameter index leaves) ftsCache) hclean _ hleft
    have hsynced' := revealedSynced_liftFtsBlock parameter table state stepState ftsFuel _
      context fuel history cache ftsCache stepCache (some entry) hclean hsynced
      (maskedFtsOpen_stateFree parameter index leaves) (maskedFtsOpen_cachePreserving parameter index leaves) hleft
    exact revealedSynced_maskedJointLayersAndPublication parameter table randomness index leaves entry.value.1
      stepState finalState ftsFuel entry.context entry.remaining entry.history entry.value.2 stepCache finalCache result
      hclean' hsynced' hnext

theorem revealedSynced_maskedJointSign
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → Digest) (message : Message)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache finalCache : SplitHashCache) (result : NativePublicationResult)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache)
    (hresult : .done false finalState (result, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel
        ((maskedJointSign parameter root message context fuel history cache).run ftsCache))) :
    RevealedSynced parameter table finalState finalCache := by
  unfold maskedJointSign at hresult
  refine preserves_bindNativeSteps table state finalState ftsFuel _ _ context fuel history cache ftsCache finalCache result
    (RevealedSynced parameter table) hclean (liftNativeBlock_probeFree _ context fuel history cache) ?_ ?_ hresult
  · intro stepState entry stepCache hleft
    exact (invariants_liftNativeBlock parameter table state stepState ftsFuel _
      (fun cache => cacheMapCommutes_native_signDigestLoop (jointDigestKey parameter root) table cache message digestAttemptLimit)
      context fuel history cache ftsCache stepCache entry hsynced hleft).2.1
  · intro stepState entry stepCache hleft hnext
    obtain ⟨hstate, hsynced', _⟩ := invariants_liftNativeBlock parameter table state stepState ftsFuel _
      (fun cache => cacheMapCommutes_native_signDigestLoop (jointDigestKey parameter root) table cache message digestAttemptLimit)
      context fuel history cache ftsCache stepCache (some entry) hsynced hleft
    cases hselected : entry.value.1 with
    | none =>
        simp only [hselected] at hnext
        exact (invariants_liftNativeBlock parameter table stepState finalState ftsFuel _
          (fun cache => OtsProbeSimulation.CacheMapCommutes.pure _ none)
          entry.context entry.remaining entry.history entry.value.2 stepCache finalCache result hsynced' hnext).2.1
    | some selected =>
        simp only [hselected] at hnext
        exact revealedSynced_maskedJointSignAfterDigest parameter table selected.1 selected.2.1 selected.2.2
          stepState finalState ftsFuel entry.context entry.remaining entry.history entry.value.2 stepCache finalCache result
          (by simpa [hstate] using hclean) hsynced' hnext

end SphincsSecurity.Concrete.FtsProbeSimulation
