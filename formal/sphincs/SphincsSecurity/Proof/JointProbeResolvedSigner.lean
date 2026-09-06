import SphincsSecurity.Proof.JointProbeResolvedPublication

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] maskedFtsKey maskedFtsOpen signDigestLoop
  OtsProbeSimulation.maskedUpperChronologicalLayers OtsProbeSimulation.maskedChronologicalLayerAfterMessage

theorem runJointResolved_nativeBlock_probeFree
    (computation : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache) :
    (runJointResolved ((jointSourceNativeBlock computation).run cache) context fuel otsTable).IsQueryBoundP AdaptiveRevealProbe.IsProbe 0 := by
  dsimp only [jointSourceNativeBlock, StateT.run]
  rw [runJointResolved_map, runJointResolved_native, isQueryBoundP_map_iff]
  exact AdaptiveRevealProbe.liftProbComp_isProbeBound _ 0

theorem runJointResolved_ftsBlock_probeFree
    (computation : StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) α) (hfree : ProbeFree computation)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache) :
    (runJointResolved ((jointSourceFtsBlock computation).run cache) context fuel otsTable).IsQueryBoundP AdaptiveRevealProbe.IsProbe 0 := by
  dsimp only [jointSourceFtsBlock, StateT.run]
  rw [runJointResolved_map, runJointResolved_fts, isQueryBoundP_map_iff, isQueryBoundP_map_iff]
  exact hfree cache.2

theorem jointResolvedCoupledAt_bottomAndPublication
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (upper : Fin (numLayers - 1) → Option OtsProbeSimulation.ChronologicalLayerPart) (root : Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state cache.2) (hcached : HiddenIndexCached index cache.2) :
    JointResolvedCoupledAt parameter table state ftsFuel
      (jointSourceBottomAndPublication parameter randomness index leaves ftsPath upper root)
      (do
        let bottom ← OtsProbeSimulation.maskedChronologicalLayerAfterMessage parameter index bottomLayer root
        OtsProbeSimulation.publishChronologicalSignature (fun index tree leaf => table (index, tree, leaf))
          randomness index leaves ftsPath (Fin.snoc upper bottom)) context fuel otsTable cache := by
  unfold jointSourceBottomAndPublication
  apply jointResolvedCoupledAt_bind_probeFree parameter table state ftsFuel _ _ _ _ context fuel otsTable cache
    (runJointResolved_nativeBlock_probeFree _ context fuel otsTable cache)
  · exact jointResolvedCoupledAt_nativeBlock parameter table state ftsFuel _
      (fun cache => cacheMapCommutes_native_maskedChronologicalLayerAfterMessage parameter table cache index bottomLayer root)
      context fuel otsTable cache hclean
  · intro finalState entry hresult
    obtain ⟨hstate, hsynced', hhidden⟩ := invariants_jointSourceNativeBlock parameter table state finalState ftsFuel _
      (fun cache => cacheMapCommutes_native_maskedChronologicalLayerAfterMessage parameter table cache index bottomLayer root)
      context fuel otsTable cache entry hsynced hresult
    have hcached' : HiddenIndexCached index entry.value.2.2 := by
      intro tree leaf
      simpa only [hhidden] using hcached tree leaf
    exact jointResolvedCoupledAt_publication parameter table randomness index leaves ftsPath (Fin.snoc upper entry.value.1)
      finalState ftsFuel entry.context entry.remaining entry.table entry.value.2 (by simpa [hstate] using hclean) hsynced' hcached'

theorem jointResolvedCoupledAt_keyAndPublication
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (upper : Fin (numLayers - 1) → Option OtsProbeSimulation.ChronologicalLayerPart)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (hclean : AdaptiveRevealProbe.tableHits state table = false) (hsynced : RevealedSynced parameter table state cache.2) :
    JointResolvedCoupledAt parameter table state ftsFuel
      (jointSourceKeyAndPublication parameter randomness index leaves ftsPath upper)
      (do
        let root ← simulateQ OtsProbeSimulation.ordinaryHashImpl (ftsKey parameter index (fun tree leaf => table (index, tree, leaf)))
        let bottom ← OtsProbeSimulation.maskedChronologicalLayerAfterMessage parameter index bottomLayer root
        OtsProbeSimulation.publishChronologicalSignature (fun index tree leaf => table (index, tree, leaf))
          randomness index leaves ftsPath (Fin.snoc upper bottom)) context fuel otsTable cache := by
  unfold jointSourceKeyAndPublication
  have hfree := runJointResolved_ftsBlock_probeFree _ (maskedFtsKey_probeFree parameter index) context fuel otsTable cache
  apply jointResolvedCoupledAt_bind_probeFree parameter table state ftsFuel _ _ _ _ context fuel otsTable cache hfree
  · exact jointResolvedCoupledAt_ftsBlock parameter table state ftsFuel _ _
      (nativeResolvedCoupled_maskedFtsKey parameter table state ftsFuel index hclean) context fuel otsTable cache
  · intro finalState entry hresult
    have hclean' := tableHits_false_of_mem_runDetailed_probeFree table state finalState ftsFuel _ hfree hclean _ hresult
    have hsynced' := revealedSynced_jointSourceFtsBlock parameter table state finalState ftsFuel _
      context fuel otsTable cache entry hclean hsynced (maskedFtsKey_stateFree parameter index)
      (maskedFtsKey_cachePreserving parameter index) hresult
    have hcached := hiddenIndexCached_jointSourceFtsKey parameter table index state finalState ftsFuel
      context fuel otsTable cache entry hclean hresult
    exact jointResolvedCoupledAt_bottomAndPublication parameter table randomness index leaves ftsPath upper entry.value.1
      finalState ftsFuel entry.context entry.remaining entry.table entry.value.2 hclean' hsynced' hcached

theorem jointResolvedCoupledAt_layersAndPublication
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (hclean : AdaptiveRevealProbe.tableHits state table = false) (hsynced : RevealedSynced parameter table state cache.2) :
    JointResolvedCoupledAt parameter table state ftsFuel (jointSourceLayersAndPublication parameter randomness index leaves ftsPath)
      (do
        let upper ← OtsProbeSimulation.maskedUpperChronologicalLayers parameter index
        let root ← simulateQ OtsProbeSimulation.ordinaryHashImpl (ftsKey parameter index (fun tree leaf => table (index, tree, leaf)))
        let bottom ← OtsProbeSimulation.maskedChronologicalLayerAfterMessage parameter index bottomLayer root
        OtsProbeSimulation.publishChronologicalSignature (fun index tree leaf => table (index, tree, leaf))
          randomness index leaves ftsPath (Fin.snoc upper bottom)) context fuel otsTable cache := by
  unfold jointSourceLayersAndPublication
  apply jointResolvedCoupledAt_bind_probeFree parameter table state ftsFuel _ _ _ _ context fuel otsTable cache
    (runJointResolved_nativeBlock_probeFree _ context fuel otsTable cache)
  · exact jointResolvedCoupledAt_nativeBlock parameter table state ftsFuel _
      (fun cache => cacheMapCommutes_native_maskedUpperChronologicalLayers parameter table cache index) context fuel otsTable cache hclean
  · intro finalState entry hresult
    obtain ⟨hstate, hsynced', _⟩ := invariants_jointSourceNativeBlock parameter table state finalState ftsFuel _
      (fun cache => cacheMapCommutes_native_maskedUpperChronologicalLayers parameter table cache index)
      context fuel otsTable cache entry hsynced hresult
    exact jointResolvedCoupledAt_keyAndPublication parameter table randomness index leaves ftsPath entry.value.1
      finalState ftsFuel entry.context entry.remaining entry.table entry.value.2 (by simpa [hstate] using hclean) hsynced'

theorem jointResolvedCoupledAt_signAfterDigest
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (hclean : AdaptiveRevealProbe.tableHits state table = false) (hsynced : RevealedSynced parameter table state cache.2) :
    JointResolvedCoupledAt parameter table state ftsFuel (jointSourceSignAfterDigest parameter randomness index leaves)
      (OtsProbeSimulation.maskedPublishedChronologicalSignAfterDigest parameter (fun index tree leaf => table (index, tree, leaf))
        randomness index leaves) context fuel otsTable cache := by
  rw [OtsProbeSimulation.maskedPublishedChronologicalSignAfterDigest_eq_ftsBoundary]
  unfold jointSourceSignAfterDigest
  have hfree := runJointResolved_ftsBlock_probeFree _ (maskedFtsOpen_probeFree parameter index leaves) context fuel otsTable cache
  apply jointResolvedCoupledAt_bind_probeFree parameter table state ftsFuel _ _ _ _ context fuel otsTable cache hfree
  · exact jointResolvedCoupledAt_ftsBlock parameter table state ftsFuel _ _
      (nativeResolvedCoupled_maskedFtsOpen parameter table state ftsFuel index leaves hclean) context fuel otsTable cache
  · intro finalState entry hresult
    have hclean' := tableHits_false_of_mem_runDetailed_probeFree table state finalState ftsFuel _ hfree hclean _ hresult
    have hsynced' := revealedSynced_jointSourceFtsBlock parameter table state finalState ftsFuel _
      context fuel otsTable cache entry hclean hsynced (maskedFtsOpen_stateFree parameter index leaves)
      (maskedFtsOpen_cachePreserving parameter index leaves) hresult
    exact jointResolvedCoupledAt_layersAndPublication parameter table randomness index leaves entry.value.1
      finalState ftsFuel entry.context entry.remaining entry.table entry.value.2 hclean' hsynced'

theorem jointResolvedCoupledAt_sign
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → Digest) (message : Message)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (hclean : AdaptiveRevealProbe.tableHits state table = false) (hsynced : RevealedSynced parameter table state cache.2) :
    JointResolvedCoupledAt parameter table state ftsFuel (jointSourceSign parameter root message)
      (OtsProbeSimulation.maskedPublishedChronologicalSign parameter root (fun index tree leaf => table (index, tree, leaf)) message)
      context fuel otsTable cache := by
  have hloop : signDigestLoop digestAttemptLimit
      (⟨parameter, root, fun _ _ _ _ => 0, fun index tree leaf => table (index, tree, leaf)⟩ : SecretKey) message =
      signDigestLoop digestAttemptLimit (jointDigestKey parameter root) message :=
    signDigestLoop_secretKeyWithFtsTable digestAttemptLimit (jointDigestKey parameter root) table message
  unfold OtsProbeSimulation.maskedPublishedChronologicalSign
  dsimp only
  rw [hloop]
  unfold jointSourceSign
  apply jointResolvedCoupledAt_bind_probeFree parameter table state ftsFuel _ _ _ _ context fuel otsTable cache
    (runJointResolved_nativeBlock_probeFree _ context fuel otsTable cache)
  · exact jointResolvedCoupledAt_nativeBlock parameter table state ftsFuel _
      (fun cache => cacheMapCommutes_native_signDigestLoop (jointDigestKey parameter root) table cache message digestAttemptLimit)
      context fuel otsTable cache hclean
  · intro finalState entry hresult
    obtain ⟨hstate, hsynced', _⟩ := invariants_jointSourceNativeBlock parameter table state finalState ftsFuel _
      (fun cache => cacheMapCommutes_native_signDigestLoop (jointDigestKey parameter root) table cache message digestAttemptLimit)
      context fuel otsTable cache entry hsynced hresult
    have hclean' : AdaptiveRevealProbe.tableHits finalState table = false := by simpa [hstate] using hclean
    cases hselected : entry.value.1 with
    | none =>
        exact jointResolvedCoupledAt_nativeBlock parameter table finalState ftsFuel (pure none)
          (fun _ => OtsProbeSimulation.CacheMapCommutes.pure _ none) entry.context entry.remaining entry.table entry.value.2 hclean'
    | some selected =>
        rcases selected with ⟨randomness, index, leaves⟩
        exact jointResolvedCoupledAt_signAfterDigest parameter table randomness index leaves finalState ftsFuel
          entry.context entry.remaining entry.table entry.value.2 hclean' hsynced'

end SphincsSecurity.Concrete.FtsProbeSimulation
