import SphincsSecurity.Proof.JointProbeSigningPublicationInvariant
import SphincsSecurity.Proof.OtsProbeEncodingCacheHash

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex MaterializedChainsPublished)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] runJointResolved AdaptiveRevealProbe.runRaw OtsProbeSimulation.runResolvedFromTable
set_option backward.isDefEq.respectTransparency false

theorem jointPublicationInvariant_of_mem_hashQuery
    (parameter : PublicParameter) (input : HashInput)
    (table : Coordinate → Digest) (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel remaining : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (entry : ResolvedRunResult (HashOutput × JointSourceCache)) (hinvariant : JointPublicationInvariant context cache)
    (hresult : .done finalState remaining (some entry) ∈ support (AdaptiveRevealProbe.runRaw table state ftsFuel
      (runJointResolved ((jointSourceHashQuery parameter input).run cache) context fuel otsTable))) :
    JointPublicationInvariant entry.context entry.value.2 := by
  unfold jointSourceHashQuery at hresult
  cases hdecode : decodeProbe? parameter input with
  | none =>
      simp only [hdecode] at hresult
      obtain ⟨native, hnative, _, _, rfl⟩ := mem_support_jointSourceNativeBlock_raw_done
        table state finalState ftsFuel remaining _ context fuel otsTable cache entry hresult
      rcases hinvariant with hpublic | hexhausted
      · exact Or.inl (OtsProbeSimulation.resolvedPreservesChainMaterialization_probingHashQuery parameter input
          context (prepareNativeCache cache.2 cache.1) fuel otsTable native hpublic hnative)
      · have hcache := OtsProbeSimulation.encodingCacheExtends_of_mem_probingHashQuery parameter input
          context fuel otsTable (prepareNativeCache cache.2 cache.1) native hnative
        rw [prepareNativeCache, OtsProbeSimulation.ordinaryQueryCache_replaceOrdinaryCache] at hcache
        exact Or.inr (hcache.exhausted hexhausted)
  | some probe =>
      simp only [hdecode] at hresult
      obtain ⟨value, finalCache, rfl, hvalue⟩ := mem_support_jointSourceFtsBlock_raw_done
        table state finalState ftsFuel remaining _ context fuel otsTable cache entry hresult
      rcases hinvariant with hpublic | hexhausted
      · exact Or.inl hpublic
      · exact Or.inr (((encodingCacheMonotoneSupport_probingHashQuery parameter input).raw
          table state finalState ftsFuel remaining cache.2 (value, finalCache) hvalue).exhausted hexhausted)

theorem jointPublicationInvariant_of_mem_uniform
    (n : Nat)
    (table : Coordinate → Digest) (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel remaining : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (entry : ResolvedRunResult (Fin (n + 1) × JointSourceCache)) (hinvariant : JointPublicationInvariant context cache)
    (hresult : .done finalState remaining (some entry) ∈ support (AdaptiveRevealProbe.runRaw table state ftsFuel
      (runJointResolved ((jointSourceNativeBlock (OtsProbeSimulation.splitUniformImpl n)).run cache) context fuel otsTable))) :
    JointPublicationInvariant entry.context entry.value.2 := by
  rcases hinvariant with hpublic | hexhausted
  · obtain ⟨native, hnative, _, _, rfl⟩ := mem_support_jointSourceNativeBlock_raw_done
      table state finalState ftsFuel remaining _ context fuel otsTable cache entry hresult
    apply Or.inl
    exact (OtsProbeSimulation.ResolvedPreservesChainMaterialization.of_preservesCoordinate
      (fun coordinate => OtsProbeSimulation.resolvedPreservesCoordinate_splitUniformImpl coordinate n))
      context (prepareNativeCache cache.2 cache.1) fuel otsTable native hpublic hnative
  · have hmonotone := (OtsProbeSimulation.ordinaryCacheSupport_of_cacheMapCommutes
      (fun _ => OtsProbeSimulation.CacheMapCommutes.liftM _ (LazyRevealProbe.uniformQuery n))).monotone
    exact Or.inr ((jointEncodingCacheMonotone_nativeBlock _ hmonotone
      table state ftsFuel context fuel otsTable cache finalState remaining entry hresult).exhausted hexhausted)

theorem jointPublicationInvariant_of_mem_outerQuery
    (parameter : PublicParameter) (root : Digest) (input : (OracleWorld + SigningSpec).Domain)
    (table : Coordinate → Digest) (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel remaining : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (entry : ResolvedRunResult ((OracleWorld + SigningSpec).Range input × JointSourceCache))
    (hinvariant : JointPublicationInvariant context cache)
    (hresult : .done finalState remaining (some entry) ∈ support (AdaptiveRevealProbe.runRaw table state ftsFuel
      (runJointResolved ((jointSourceOuterQuery parameter root input).run cache) context fuel otsTable))) :
    JointPublicationInvariant entry.context entry.value.2 := by
  cases input with
  | inl input =>
      cases input with
      | inl n =>
          exact jointPublicationInvariant_of_mem_uniform n table state finalState ftsFuel remaining
            context fuel otsTable cache entry hinvariant hresult
      | inr input =>
          exact jointPublicationInvariant_of_mem_hashQuery parameter input table state finalState ftsFuel remaining
            context fuel otsTable cache entry hinvariant hresult
  | inr message =>
      exact jointPublicationInvariant_of_mem_sign parameter root message table state finalState ftsFuel remaining
        context fuel otsTable cache entry hinvariant hresult

end SphincsSecurity.Concrete.FtsProbeSimulation
