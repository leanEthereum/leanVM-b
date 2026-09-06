import SphincsSecurity.Proof.JointProbePublicationChainCoverage

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex ChainsPublishedOutside ChainOutsideLayerPart MaterializedChainsPublished)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] runJointResolved AdaptiveRevealProbe.runRaw OtsProbeSimulation.runResolvedFromTable
attribute [local irreducible] jointSourcePublication jointSourceKeyAndPublication jointSourceBottomAndPublication
attribute [local irreducible] OtsProbeSimulation.maskedUpperChronologicalLayers
set_option backward.isDefEq.respectTransparency false

theorem materializedChainsPublished_of_successful_jointBottomAndPublication
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (upper : Fin (numLayers - 1) → Option OtsProbeSimulation.ChronologicalLayerPart) (root : Digest)
    (table : Coordinate → Digest) (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel remaining : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (entry : ResolvedRunResult (Option Signature × JointSourceCache))
    (hpublic : ChainsPublishedOutside (fun coordinate => ∀ lay, ChainOutsideLayerPart coordinate index lay.castSucc (upper lay)) context)
    (hresult : .done finalState remaining (some entry) ∈ support (AdaptiveRevealProbe.runRaw table state ftsFuel
      (runJointResolved ((jointSourceBottomAndPublication parameter randomness index leaves ftsPath upper root).run cache)
        context fuel otsTable))) (hsuccess : entry.value.1 ≠ none) : MaterializedChainsPublished entry.context := by
  rw [jointSourceBottomAndPublication] at hresult
  obtain ⟨middleState, middleFuel, middle, hmiddle, hpublication⟩ := mem_support_jointSource_bind_raw_done
    table state finalState ftsFuel remaining _ _ context fuel otsTable cache entry hresult
  obtain ⟨native, hnative, _, _, rfl⟩ := mem_support_jointSourceNativeBlock_raw_done
    table state middleState ftsFuel middleFuel _ context fuel otsTable cache middle hmiddle
  have hcovered := OtsProbeSimulation.chainsPublishedOutside_chronologicalLayerAfterMessage _ parameter index bottomLayer root
    context fuel otsTable (prepareNativeCache cache.2 cache.1) native hpublic hnative
  apply materializedChainsPublished_of_successful_jointPublication parameter randomness index leaves ftsPath (Fin.snoc upper native.value.1)
    table middleState finalState middleFuel remaining native.context native.remaining native.table
    (native.value.2, withNativeOrdinaryCache cache.2 native.value.2) entry _ hpublication hsuccess
  apply hcovered.mono
  intro coordinate houtside
  constructor
  · intro lay
    simpa only [Fin.snoc_castSucc] using houtside lay.castSucc
  · have hbottom : (Fin.snoc upper native.value.1 : Layer → Option OtsProbeSimulation.ChronologicalLayerPart) bottomLayer = native.value.1 :=
      Fin.snoc_last (α := fun _ => Option OtsProbeSimulation.ChronologicalLayerPart) native.value.1 upper
    simpa only [hbottom] using houtside bottomLayer

theorem materializedChainsPublished_of_successful_jointKeyAndPublication
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (upper : Fin (numLayers - 1) → Option OtsProbeSimulation.ChronologicalLayerPart)
    (table : Coordinate → Digest) (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel remaining : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (entry : ResolvedRunResult (Option Signature × JointSourceCache))
    (hpublic : ChainsPublishedOutside (fun coordinate => ∀ lay, ChainOutsideLayerPart coordinate index lay.castSucc (upper lay)) context)
    (hresult : .done finalState remaining (some entry) ∈ support (AdaptiveRevealProbe.runRaw table state ftsFuel
      (runJointResolved ((jointSourceKeyAndPublication parameter randomness index leaves ftsPath upper).run cache)
        context fuel otsTable))) (hsuccess : entry.value.1 ≠ none) : MaterializedChainsPublished entry.context := by
  rw [jointSourceKeyAndPublication] at hresult
  obtain ⟨middleState, middleFuel, middle, hmiddle, hrest⟩ := mem_support_jointSource_bind_raw_done
    table state finalState ftsFuel remaining _ _ context fuel otsTable cache entry hresult
  obtain ⟨root, finalCache, rfl, _⟩ := mem_support_jointSourceFtsBlock_raw_done
    table state middleState ftsFuel middleFuel _ context fuel otsTable cache middle hmiddle
  exact materializedChainsPublished_of_successful_jointBottomAndPublication parameter randomness index leaves ftsPath upper root
    table middleState finalState middleFuel remaining context fuel otsTable (cache.1, finalCache) entry hpublic hrest hsuccess

theorem materializedChainsPublished_of_successful_jointLayersAndPublication
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (table : Coordinate → Digest) (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel remaining : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (entry : ResolvedRunResult (Option Signature × JointSourceCache)) (hpublic : MaterializedChainsPublished context)
    (hresult : .done finalState remaining (some entry) ∈ support (AdaptiveRevealProbe.runRaw table state ftsFuel
      (runJointResolved ((jointSourceLayersAndPublication parameter randomness index leaves ftsPath).run cache)
        context fuel otsTable))) (hsuccess : entry.value.1 ≠ none) : MaterializedChainsPublished entry.context := by
  rw [jointSourceLayersAndPublication] at hresult
  obtain ⟨middleState, middleFuel, middle, hmiddle, hrest⟩ := mem_support_jointSource_bind_raw_done
    table state finalState ftsFuel remaining _ _ context fuel otsTable cache entry hresult
  obtain ⟨native, hnative, _, _, rfl⟩ := mem_support_jointSourceNativeBlock_raw_done
    table state middleState ftsFuel middleFuel _ context fuel otsTable cache middle hmiddle
  have hcovered := OtsProbeSimulation.chainsPublishedOutside_upperChronologicalLayers (fun _ => True) parameter index
    context fuel otsTable (prepareNativeCache cache.2 cache.1) native (hpublic.outside _) hnative
  exact materializedChainsPublished_of_successful_jointKeyAndPublication parameter randomness index leaves ftsPath native.value.1
    table middleState finalState middleFuel remaining native.context native.remaining native.table
    (native.value.2, withNativeOrdinaryCache cache.2 native.value.2) entry
    (hcovered.mono (fun _ h => ⟨True.intro, h⟩)) hrest hsuccess

theorem materializedChainsPublished_of_successful_jointSignAfterDigest
    (parameter : PublicParameter) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (table : Coordinate → Digest) (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel remaining : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (entry : ResolvedRunResult (Option Signature × JointSourceCache)) (hpublic : MaterializedChainsPublished context)
    (hresult : .done finalState remaining (some entry) ∈ support (AdaptiveRevealProbe.runRaw table state ftsFuel
      (runJointResolved ((jointSourceSignAfterDigest parameter randomness index leaves).run cache) context fuel otsTable)))
    (hsuccess : entry.value.1 ≠ none) : MaterializedChainsPublished entry.context := by
  rw [jointSourceSignAfterDigest] at hresult
  obtain ⟨middleState, middleFuel, middle, hmiddle, hrest⟩ := mem_support_jointSource_bind_raw_done
    table state finalState ftsFuel remaining _ _ context fuel otsTable cache entry hresult
  obtain ⟨path, finalCache, rfl, _⟩ := mem_support_jointSourceFtsBlock_raw_done
    table state middleState ftsFuel middleFuel _ context fuel otsTable cache middle hmiddle
  exact materializedChainsPublished_of_successful_jointLayersAndPublication parameter randomness index leaves path
    table middleState finalState middleFuel remaining context fuel otsTable (cache.1, finalCache) entry hpublic hrest hsuccess

end SphincsSecurity.Concrete.FtsProbeSimulation
