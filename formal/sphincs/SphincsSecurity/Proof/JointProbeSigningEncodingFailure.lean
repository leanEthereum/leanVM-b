import SphincsSecurity.Proof.JointProbePublicationFailureSupport

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] jointSourcePublication jointSourceKeyAndPublication jointSourceBottomAndPublication
attribute [local irreducible] runJointResolved AdaptiveRevealProbe.runRaw
attribute [local irreducible] OtsProbeSimulation.runResolvedFromTable OtsProbeSimulation.maskedUpperChronologicalLayers
set_option backward.isDefEq.respectTransparency false

theorem upper_failed_or_exhausted_of_mem_failed_jointBottomAndPublication
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (upper : Fin (numLayers - 1) → Option OtsProbeSimulation.ChronologicalLayerPart) (root : Digest)
    (table : Coordinate → Digest) (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel remaining : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (entry : ResolvedRunResult (Option Signature × JointSourceCache))
    (hresult : .done finalState remaining (some entry) ∈ support (AdaptiveRevealProbe.runRaw table state ftsFuel
      (runJointResolved ((jointSourceBottomAndPublication parameter randomness index leaves ftsPath upper root).run cache)
        context fuel otsTable))) (hfailed : entry.value.1 = none) :
    (∃ lay, upper lay = none) ∨ AnyEncodingInputsExhausted (ordinaryQueryCache entry.value.2.2) := by
  rw [jointSourceBottomAndPublication] at hresult
  obtain ⟨middleState, middleFuel, middle, hmiddle, hpublication⟩ := mem_support_jointSource_bind_raw_done
    table state finalState ftsFuel remaining _ _ context fuel otsTable cache entry hresult
  have hpreserve := jointEncodingCacheMonotone_publication parameter randomness index leaves ftsPath (Fin.snoc upper middle.value.1)
    table middleState middleFuel middle.context middle.remaining middle.table middle.value.2 finalState remaining entry hpublication
  obtain ⟨lay, hfailedLayer⟩ := failed_layer_of_mem_failed_jointPublication parameter randomness index leaves ftsPath
    (Fin.snoc upper middle.value.1) table middleState finalState middleFuel remaining
    middle.context middle.remaining middle.table middle.value.2 entry hpublication hfailed
  obtain ⟨native, hnative, _, _, rfl⟩ := mem_support_jointSourceNativeBlock_raw_done
    table state middleState ftsFuel middleFuel _ context fuel otsTable cache middle hmiddle
  revert hfailedLayer
  refine Fin.lastCases ?_ (fun upperLay => ?_) lay
  · intro hbottom
    right
    apply hpreserve.exhausted
    refine ⟨parameter, ⟨bottomLayer, treeIndexAt index bottomLayer, leafIndexAt index bottomLayer⟩, root, ?_⟩
    exact OtsProbeSimulation.encodingInputsExhausted_of_mem_failed_chronologicalLayerAfterMessage
      parameter index bottomLayer root context fuel otsTable (prepareNativeCache cache.2 cache.1) native hnative
      (by simpa only [Fin.snoc_last, packResolvedNativeBlock] using hbottom)
  · intro hupper
    exact Or.inl ⟨upperLay, by simpa only [Fin.snoc_castSucc] using hupper⟩

theorem upper_failed_or_exhausted_of_mem_failed_jointKeyAndPublication
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (upper : Fin (numLayers - 1) → Option OtsProbeSimulation.ChronologicalLayerPart)
    (table : Coordinate → Digest) (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel remaining : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (entry : ResolvedRunResult (Option Signature × JointSourceCache))
    (hresult : .done finalState remaining (some entry) ∈ support (AdaptiveRevealProbe.runRaw table state ftsFuel
      (runJointResolved ((jointSourceKeyAndPublication parameter randomness index leaves ftsPath upper).run cache)
        context fuel otsTable))) (hfailed : entry.value.1 = none) :
    (∃ lay, upper lay = none) ∨ AnyEncodingInputsExhausted (ordinaryQueryCache entry.value.2.2) := by
  rw [jointSourceKeyAndPublication] at hresult
  obtain ⟨middleState, middleFuel, middle, hmiddle, hrest⟩ := mem_support_jointSource_bind_raw_done
    table state finalState ftsFuel remaining _ _ context fuel otsTable cache entry hresult
  exact upper_failed_or_exhausted_of_mem_failed_jointBottomAndPublication parameter randomness index leaves ftsPath upper middle.value.1
    table middleState finalState middleFuel remaining middle.context middle.remaining middle.table middle.value.2 entry hrest hfailed

theorem anyEncodingInputsExhausted_of_mem_failed_jointLayersAndPublication
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (table : Coordinate → Digest) (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel remaining : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (entry : ResolvedRunResult (Option Signature × JointSourceCache))
    (hresult : .done finalState remaining (some entry) ∈ support (AdaptiveRevealProbe.runRaw table state ftsFuel
      (runJointResolved ((jointSourceLayersAndPublication parameter randomness index leaves ftsPath).run cache)
        context fuel otsTable))) (hfailed : entry.value.1 = none) :
    AnyEncodingInputsExhausted (ordinaryQueryCache entry.value.2.2) := by
  rw [jointSourceLayersAndPublication] at hresult
  obtain ⟨middleState, middleFuel, middle, hmiddle, hrest⟩ := mem_support_jointSource_bind_raw_done
    table state finalState ftsFuel remaining _ _ context fuel otsTable cache entry hresult
  have hpreserve := jointEncodingCacheMonotone_keyAndPublication parameter randomness index leaves ftsPath middle.value.1
    table middleState middleFuel middle.context middle.remaining middle.table middle.value.2 finalState remaining entry hrest
  have hfailure := upper_failed_or_exhausted_of_mem_failed_jointKeyAndPublication parameter randomness index leaves ftsPath middle.value.1
    table middleState finalState middleFuel remaining middle.context middle.remaining middle.table middle.value.2 entry hrest hfailed
  rcases hfailure with ⟨lay, hfailedLayer⟩ | hexhausted
  · obtain ⟨native, hnative, _, _, rfl⟩ := mem_support_jointSourceNativeBlock_raw_done
      table state middleState ftsFuel middleFuel _ context fuel otsTable cache middle hmiddle
    change native.value.1 lay = none at hfailedLayer
    exact hpreserve.exhausted (OtsProbeSimulation.anyEncodingInputsExhausted_of_mem_upperChronologicalLayers_none
      parameter index context fuel otsTable (prepareNativeCache cache.2 cache.1) native hnative lay hfailedLayer)
  · exact hexhausted

theorem anyEncodingInputsExhausted_of_mem_failed_jointSignAfterDigest
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (table : Coordinate → Digest) (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel remaining : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (entry : ResolvedRunResult (Option Signature × JointSourceCache))
    (hresult : .done finalState remaining (some entry) ∈ support (AdaptiveRevealProbe.runRaw table state ftsFuel
      (runJointResolved ((jointSourceSignAfterDigest parameter randomness index leaves).run cache) context fuel otsTable)))
    (hfailed : entry.value.1 = none) : AnyEncodingInputsExhausted (ordinaryQueryCache entry.value.2.2) := by
  rw [jointSourceSignAfterDigest] at hresult
  obtain ⟨middleState, middleFuel, middle, hmiddle, hrest⟩ := mem_support_jointSource_bind_raw_done
    table state finalState ftsFuel remaining _ _ context fuel otsTable cache entry hresult
  exact anyEncodingInputsExhausted_of_mem_failed_jointLayersAndPublication parameter randomness index leaves middle.value.1
    table middleState finalState middleFuel remaining middle.context middle.remaining middle.table middle.value.2 entry hrest hfailed

end SphincsSecurity.Concrete.FtsProbeSimulation
