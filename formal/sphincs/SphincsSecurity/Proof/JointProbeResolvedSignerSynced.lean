import SphincsSecurity.Proof.JointProbeResolvedSupport

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] maskedFtsKey maskedFtsOpen signDigestLoop
  OtsProbeSimulation.maskedUpperChronologicalLayers OtsProbeSimulation.maskedChronologicalLayerAfterMessage

theorem revealedSynced_jointSourceBottomAndPublication
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (upper : Fin (numLayers - 1) → Option OtsProbeSimulation.ChronologicalLayerPart) (root : Digest)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (result : ResolvedRunResult (Option Signature × JointSourceCache))
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state cache.2) (hcached : HiddenIndexCached index cache.2)
    (hresult : .done false finalState (some result) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel
        (runJointResolved ((jointSourceBottomAndPublication parameter randomness index leaves ftsPath upper root).run cache) context fuel otsTable))) :
    RevealedSynced parameter table finalState result.value.2.2 := by
  unfold jointSourceBottomAndPublication at hresult
  obtain ⟨stepState, entry, hleft, hnext⟩ := mem_support_jointResolved_bind_done_some table state finalState ftsFuel _ _
    context fuel otsTable cache result hclean (runJointResolved_nativeBlock_probeFree _ context fuel otsTable cache) hresult
  obtain ⟨hstate, hsynced', hhidden⟩ := invariants_jointSourceNativeBlock parameter table state stepState ftsFuel _
    (fun cache => cacheMapCommutes_native_maskedChronologicalLayerAfterMessage parameter table cache index bottomLayer root)
    context fuel otsTable cache entry hsynced hleft
  have hcached' : HiddenIndexCached index entry.value.2.2 := by
    intro tree leaf
    simpa only [hhidden] using hcached tree leaf
  exact revealedSynced_jointSourcePublication parameter table randomness index leaves ftsPath (Fin.snoc upper entry.value.1)
    stepState finalState ftsFuel entry.context entry.remaining entry.table entry.value.2 result
    (by simpa [hstate] using hclean) hsynced' hcached' hnext

theorem revealedSynced_jointSourceKeyAndPublication
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (upper : Fin (numLayers - 1) → Option OtsProbeSimulation.ChronologicalLayerPart)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (result : ResolvedRunResult (Option Signature × JointSourceCache))
    (hclean : AdaptiveRevealProbe.tableHits state table = false) (hsynced : RevealedSynced parameter table state cache.2)
    (hresult : .done false finalState (some result) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel
        (runJointResolved ((jointSourceKeyAndPublication parameter randomness index leaves ftsPath upper).run cache) context fuel otsTable))) :
    RevealedSynced parameter table finalState result.value.2.2 := by
  unfold jointSourceKeyAndPublication at hresult
  have hfree := runJointResolved_ftsBlock_probeFree _ (maskedFtsKey_probeFree parameter index) context fuel otsTable cache
  obtain ⟨stepState, entry, hleft, hnext⟩ := mem_support_jointResolved_bind_done_some table state finalState ftsFuel _ _
    context fuel otsTable cache result hclean hfree hresult
  have hclean' := tableHits_false_of_mem_runDetailed_probeFree table state stepState ftsFuel _ hfree hclean _ hleft
  have hsynced' := revealedSynced_jointSourceFtsBlock parameter table state stepState ftsFuel _ context fuel otsTable cache entry
    hclean hsynced (maskedFtsKey_stateFree parameter index) (maskedFtsKey_cachePreserving parameter index) hleft
  have hcached := hiddenIndexCached_jointSourceFtsKey parameter table index state stepState ftsFuel context fuel otsTable cache entry hclean hleft
  exact revealedSynced_jointSourceBottomAndPublication parameter table randomness index leaves ftsPath upper entry.value.1
    stepState finalState ftsFuel entry.context entry.remaining entry.table entry.value.2 result hclean' hsynced' hcached hnext

theorem revealedSynced_jointSourceLayersAndPublication
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (result : ResolvedRunResult (Option Signature × JointSourceCache))
    (hclean : AdaptiveRevealProbe.tableHits state table = false) (hsynced : RevealedSynced parameter table state cache.2)
    (hresult : .done false finalState (some result) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel
        (runJointResolved ((jointSourceLayersAndPublication parameter randomness index leaves ftsPath).run cache) context fuel otsTable))) :
    RevealedSynced parameter table finalState result.value.2.2 := by
  unfold jointSourceLayersAndPublication at hresult
  obtain ⟨stepState, entry, hleft, hnext⟩ := mem_support_jointResolved_bind_done_some table state finalState ftsFuel _ _
    context fuel otsTable cache result hclean (runJointResolved_nativeBlock_probeFree _ context fuel otsTable cache) hresult
  obtain ⟨hstate, hsynced', _⟩ := invariants_jointSourceNativeBlock parameter table state stepState ftsFuel _
    (fun cache => cacheMapCommutes_native_maskedUpperChronologicalLayers parameter table cache index)
    context fuel otsTable cache entry hsynced hleft
  exact revealedSynced_jointSourceKeyAndPublication parameter table randomness index leaves ftsPath entry.value.1
    stepState finalState ftsFuel entry.context entry.remaining entry.table entry.value.2 result (by simpa [hstate] using hclean) hsynced' hnext

theorem revealedSynced_jointSourceSignAfterDigest
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (result : ResolvedRunResult (Option Signature × JointSourceCache))
    (hclean : AdaptiveRevealProbe.tableHits state table = false) (hsynced : RevealedSynced parameter table state cache.2)
    (hresult : .done false finalState (some result) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel
        (runJointResolved ((jointSourceSignAfterDigest parameter randomness index leaves).run cache) context fuel otsTable))) :
    RevealedSynced parameter table finalState result.value.2.2 := by
  unfold jointSourceSignAfterDigest at hresult
  have hfree := runJointResolved_ftsBlock_probeFree _ (maskedFtsOpen_probeFree parameter index leaves) context fuel otsTable cache
  obtain ⟨stepState, entry, hleft, hnext⟩ := mem_support_jointResolved_bind_done_some table state finalState ftsFuel _ _
    context fuel otsTable cache result hclean hfree hresult
  have hclean' := tableHits_false_of_mem_runDetailed_probeFree table state stepState ftsFuel _ hfree hclean _ hleft
  have hsynced' := revealedSynced_jointSourceFtsBlock parameter table state stepState ftsFuel _ context fuel otsTable cache entry
    hclean hsynced (maskedFtsOpen_stateFree parameter index leaves) (maskedFtsOpen_cachePreserving parameter index leaves) hleft
  exact revealedSynced_jointSourceLayersAndPublication parameter table randomness index leaves entry.value.1
    stepState finalState ftsFuel entry.context entry.remaining entry.table entry.value.2 result hclean' hsynced' hnext

theorem revealedSynced_jointSourceSign
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → Digest) (message : Message)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (result : ResolvedRunResult (Option Signature × JointSourceCache))
    (hclean : AdaptiveRevealProbe.tableHits state table = false) (hsynced : RevealedSynced parameter table state cache.2)
    (hresult : .done false finalState (some result) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel
        (runJointResolved ((jointSourceSign parameter root message).run cache) context fuel otsTable))) :
    RevealedSynced parameter table finalState result.value.2.2 := by
  unfold jointSourceSign at hresult
  obtain ⟨stepState, entry, hleft, hnext⟩ := mem_support_jointResolved_bind_done_some table state finalState ftsFuel _ _
    context fuel otsTable cache result hclean (runJointResolved_nativeBlock_probeFree _ context fuel otsTable cache) hresult
  obtain ⟨hstate, hsynced', _⟩ := invariants_jointSourceNativeBlock parameter table state stepState ftsFuel _
    (fun cache => cacheMapCommutes_native_signDigestLoop (jointDigestKey parameter root) table cache message digestAttemptLimit)
    context fuel otsTable cache entry hsynced hleft
  have hclean' : AdaptiveRevealProbe.tableHits stepState table = false := by simpa [hstate] using hclean
  cases hselected : entry.value.1 with
  | none =>
      simp only [hselected] at hnext
      exact (invariants_jointSourceNativeBlock parameter table stepState finalState ftsFuel _
        (fun _ => OtsProbeSimulation.CacheMapCommutes.pure _ none) entry.context entry.remaining entry.table entry.value.2
        result hsynced' hnext).2.1
  | some selected =>
      rcases selected with ⟨randomness, index, leaves⟩
      simp only [hselected] at hnext
      exact revealedSynced_jointSourceSignAfterDigest parameter table randomness index leaves stepState finalState ftsFuel
        entry.context entry.remaining entry.table entry.value.2 result hclean' hsynced' hnext

end SphincsSecurity.Concrete.FtsProbeSimulation
