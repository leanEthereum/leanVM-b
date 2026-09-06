import SphincsSecurity.Proof.OtsProbeQueryCacheMap
import SphincsSecurity.Proof.FtsProbeStepComposition

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem cacheMapCommutes_native_resolveKnownInput
    (parameter : PublicParameter) (table : Coordinate → Digest) (ftsCache : SplitHashCache)
    (coordinate : OtsProbeSimulation.Coordinate) (input : HashInput) (hordinary : IsOrdinaryInput parameter table input) :
    OtsProbeSimulation.CacheMapCommutes (nativeCacheProjection parameter table ftsCache)
      (OtsProbeSimulation.resolveKnownInput parameter coordinate input) := by
  unfold OtsProbeSimulation.resolveKnownInput
  apply (OtsProbeSimulation.cacheMapCommutes_peekTableInput _ parameter coordinate).bind
  intro known
  cases known with
  | none => exact cacheMapCommutes_native_ordinaryHash parameter table ftsCache input hordinary
  | some known =>
      simp only
      split
      · apply (OtsProbeSimulation.cacheMapCommutes_revealCoordinateOutput _
          (nativeCacheProjection_commutesWithHiddenUpdates parameter table ftsCache) coordinate).bind
        intro output
        apply (OtsProbeSimulation.CacheMapCommutes.liftM _ (LazyRevealProbe.publishQuery coordinate)).bind
        intro _
        apply (OtsProbeSimulation.CacheMapCommutes.modify _ _
          (fun cache => nativeCacheProjection_update_ordinary parameter table ftsCache cache input output hordinary)).bind
        intro _
        exact OtsProbeSimulation.CacheMapCommutes.pure _ output
      · exact cacheMapCommutes_native_ordinaryHash parameter table ftsCache input hordinary

theorem cacheMapCommutes_native_probingHashQuery
    (parameter : PublicParameter) (table : Coordinate → Digest) (ftsCache : SplitHashCache)
    (input : HashInput) (hordinary : IsOrdinaryInput parameter table input) :
    OtsProbeSimulation.CacheMapCommutes (nativeCacheProjection parameter table ftsCache)
      (OtsProbeSimulation.probingHashQuery parameter input) :=
  OtsProbeSimulation.cacheMapCommutes_probingHashQuery _ parameter input
    (fun coordinate => cacheMapCommutes_native_resolveKnownInput parameter table ftsCache coordinate input hordinary)
    (cacheMapCommutes_native_ordinaryHash parameter table ftsCache input hordinary)

theorem nativeStepCoupledAt_ordinaryQuery
    (parameter : PublicParameter) (table : Coordinate → Digest) (input : HashInput)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hdecode : decodeProbe? parameter input = none) :
    NativeStepCoupledAt parameter table state ftsFuel
      (liftNativeBlock (OtsProbeSimulation.probingHashQuery parameter input))
      (OtsProbeSimulation.probingHashQuery parameter input) context fuel history cache ftsCache :=
  projectNativeStepCache_liftNativeBlock parameter table state ftsFuel ftsCache _
    (cacheMapCommutes_native_probingHashQuery parameter table ftsCache input
      (isOrdinaryInput_of_decode_none parameter table input hdecode)) context fuel history cache hclean

theorem invariants_nativeOrdinaryQuery
    (parameter : PublicParameter) (table : Coordinate → Digest) (input : HashInput)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache finalCache : SplitHashCache) (result : NativeStepResult HashOutput)
    (hdecode : decodeProbe? parameter input = none)
    (hsynced : RevealedSynced parameter table state ftsCache)
    (hresult : .done false finalState (result, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel
        ((liftNativeBlock (OtsProbeSimulation.probingHashQuery parameter input) context fuel history cache).run ftsCache))) :
    finalState = state ∧ RevealedSynced parameter table finalState finalCache ∧
      ∀ coordinate, finalCache (.hiddenLeaf coordinate) = ftsCache (.hiddenLeaf coordinate) :=
  invariants_liftNativeBlock parameter table state finalState ftsFuel _
    (fun cache => cacheMapCommutes_native_probingHashQuery parameter table cache input
      (isOrdinaryInput_of_decode_none parameter table input hdecode)) context fuel history cache ftsCache finalCache result hsynced hresult

end SphincsSecurity.Concrete.FtsProbeSimulation
