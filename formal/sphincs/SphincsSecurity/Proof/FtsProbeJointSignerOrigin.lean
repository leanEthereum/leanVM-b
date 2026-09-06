import SphincsSecurity.Proof.FtsProbeStepState

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] maskedFtsKey maskedFtsOpen signDigestLoop
  OtsProbeSimulation.maskedUpperChronologicalLayers OtsProbeSimulation.maskedChronologicalLayerAfterMessage

theorem revealedOnlyFrom_bindNativeSteps
    (table : Coordinate → Digest) (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (left : NativeFtsStep α) (next : α → NativeFtsStep β)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache finalCache : SplitHashCache) (result : NativeStepResult β)
    (allowed : Coordinate → Prop)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hfree : ProbeFree (left context fuel history cache))
    (hstate : ∀ stepState entry stepCache,
      .done false stepState (entry, stepCache) ∈ support
        (AdaptiveRevealProbe.runDetailed table state ftsFuel ((left context fuel history cache).run ftsCache)) →
      stepState = state)
    (hnext : ∀ stepState entry stepCache,
      .done false stepState (some entry, stepCache) ∈ support
        (AdaptiveRevealProbe.runDetailed table state ftsFuel ((left context fuel history cache).run ftsCache)) →
      .done false finalState (result, finalCache) ∈ support
        (AdaptiveRevealProbe.runDetailed table stepState ftsFuel
          ((next entry.value.1 entry.context entry.remaining entry.history entry.value.2).run stepCache)) →
      RevealedOnlyFrom stepState finalState allowed)
    (hresult : .done false finalState (result, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel ((bindNativeSteps left next context fuel history cache).run ftsCache))) :
    RevealedOnlyFrom state finalState allowed := by
  refine preserves_bindNativeSteps table state finalState ftsFuel left next context fuel history cache ftsCache finalCache result
    (fun finalState _ => RevealedOnlyFrom state finalState allowed) hclean hfree ?_ ?_ hresult
  · intro stepState entry stepCache hleft
    rw [hstate stepState entry stepCache hleft]
    exact fun _ _ h => Or.inl h
  · intro stepState entry stepCache hleft hright
    have horigin := hnext stepState entry stepCache hleft hright
    simpa only [hstate stepState (some entry) stepCache hleft] using horigin

theorem revealedOnlyFrom_maskedJointBottomAndPublication
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
    RevealedOnlyFrom state finalState (PublishedNativeCoordinate index leaves result) := by
  unfold maskedJointBottomAndPublication at hresult
  refine revealedOnlyFrom_bindNativeSteps table state finalState ftsFuel _ _ context fuel history cache ftsCache finalCache result
    (PublishedNativeCoordinate index leaves result) hclean (liftNativeBlock_probeFree _ context fuel history cache) ?_ ?_ hresult
  · intro stepState entry stepCache hleft
    exact state_eq_liftNativeBlock table state stepState ftsFuel _
      context fuel history cache ftsCache stepCache entry hleft
  · intro stepState entry stepCache hleft hnext
    obtain ⟨hstate, hsynced', hhidden⟩ := invariants_liftNativeBlock parameter table state stepState ftsFuel _
      (fun cache => cacheMapCommutes_native_maskedChronologicalLayerAfterMessage parameter table cache index bottomLayer root)
      context fuel history cache ftsCache stepCache (some entry) hsynced hleft
    have hcached' : HiddenIndexCached index stepCache := by
      intro tree leaf
      simpa only [hhidden] using hcached tree leaf
    exact revealedOnlyFrom_revealAfterNativeBody parameter table index leaves stepState finalState ftsFuel stepCache finalCache _ result
      (by simpa [hstate] using hclean) hsynced' hcached' hnext

theorem revealedOnlyFrom_maskedJointKeyAndPublication
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
    RevealedOnlyFrom state finalState (PublishedNativeCoordinate index leaves result) := by
  unfold maskedJointKeyAndPublication at hresult
  refine revealedOnlyFrom_bindNativeSteps table state finalState ftsFuel _ _ context fuel history cache ftsCache finalCache result
    (PublishedNativeCoordinate index leaves result) hclean
    (liftFtsBlock_probeFree _ context fuel history cache (maskedFtsKey_probeFree parameter index)) ?_ ?_ hresult
  · intro stepState entry stepCache hleft
    exact state_eq_liftFtsBlock table state stepState ftsFuel _ context fuel history cache ftsCache stepCache entry
      hclean (maskedFtsKey_stateFree parameter index) hleft
  · intro stepState entry stepCache hleft hnext
    have hclean' := tableHits_false_of_mem_runDetailed_probeFree table state stepState ftsFuel _
      (liftFtsBlock_probeFree _ context fuel history cache (maskedFtsKey_probeFree parameter index) ftsCache) hclean _ hleft
    have hsynced' := revealedSynced_liftFtsBlock parameter table state stepState ftsFuel _
      context fuel history cache ftsCache stepCache (some entry) hclean hsynced
      (maskedFtsKey_stateFree parameter index) (maskedFtsKey_cachePreserving parameter index) hleft
    have hcached := hiddenIndexCached_liftFtsKey parameter table index state stepState ftsFuel
      context fuel history cache ftsCache stepCache (some entry) hclean hleft
    exact revealedOnlyFrom_maskedJointBottomAndPublication parameter table randomness index leaves ftsPath upper entry.value.1
      stepState finalState ftsFuel entry.context entry.remaining entry.history entry.value.2 stepCache finalCache result
      hclean' hsynced' hcached hnext

theorem revealedOnlyFrom_maskedJointLayersAndPublication
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
    RevealedOnlyFrom state finalState (PublishedNativeCoordinate index leaves result) := by
  unfold maskedJointLayersAndPublication at hresult
  refine revealedOnlyFrom_bindNativeSteps table state finalState ftsFuel _ _ context fuel history cache ftsCache finalCache result
    (PublishedNativeCoordinate index leaves result) hclean (liftNativeBlock_probeFree _ context fuel history cache) ?_ ?_ hresult
  · intro stepState entry stepCache hleft
    exact state_eq_liftNativeBlock table state stepState ftsFuel _
      context fuel history cache ftsCache stepCache entry hleft
  · intro stepState entry stepCache hleft hnext
    obtain ⟨hstate, hsynced', _⟩ := invariants_liftNativeBlock parameter table state stepState ftsFuel _
      (fun cache => cacheMapCommutes_native_maskedUpperChronologicalLayers parameter table cache index)
      context fuel history cache ftsCache stepCache (some entry) hsynced hleft
    exact revealedOnlyFrom_maskedJointKeyAndPublication parameter table randomness index leaves ftsPath entry.value.1
      stepState finalState ftsFuel entry.context entry.remaining entry.history entry.value.2 stepCache finalCache result
      (by simpa [hstate] using hclean) hsynced' hnext

theorem revealedOnlyFrom_maskedJointSignAfterDigest
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
    RevealedOnlyFrom state finalState (PublishedNativeCoordinate index leaves result) := by
  unfold maskedJointSignAfterDigest at hresult
  refine revealedOnlyFrom_bindNativeSteps table state finalState ftsFuel _ _ context fuel history cache ftsCache finalCache result
    (PublishedNativeCoordinate index leaves result) hclean
    (liftFtsBlock_probeFree _ context fuel history cache (maskedFtsOpen_probeFree parameter index leaves)) ?_ ?_ hresult
  · intro stepState entry stepCache hleft
    exact state_eq_liftFtsBlock table state stepState ftsFuel _ context fuel history cache ftsCache stepCache entry
      hclean (maskedFtsOpen_stateFree parameter index leaves) hleft
  · intro stepState entry stepCache hleft hnext
    have hclean' := tableHits_false_of_mem_runDetailed_probeFree table state stepState ftsFuel _
      (liftFtsBlock_probeFree _ context fuel history cache (maskedFtsOpen_probeFree parameter index leaves) ftsCache) hclean _ hleft
    have hsynced' := revealedSynced_liftFtsBlock parameter table state stepState ftsFuel _
      context fuel history cache ftsCache stepCache (some entry) hclean hsynced
      (maskedFtsOpen_stateFree parameter index leaves) (maskedFtsOpen_cachePreserving parameter index leaves) hleft
    exact revealedOnlyFrom_maskedJointLayersAndPublication parameter table randomness index leaves entry.value.1
      stepState finalState ftsFuel entry.context entry.remaining entry.history entry.value.2 stepCache finalCache result
      hclean' hsynced' hnext

end SphincsSecurity.Concrete.FtsProbeSimulation
