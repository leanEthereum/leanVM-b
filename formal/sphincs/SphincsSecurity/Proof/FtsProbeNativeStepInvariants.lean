import SphincsSecurity.Proof.FtsProbeNativeStep

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem cacheAfterNativeBlock_hidden (cache : SplitHashCache) (result : NativeStepResult α) (coordinate : Coordinate) :
    cacheAfterNativeBlock cache result (.hiddenLeaf coordinate) = cache (.hiddenLeaf coordinate) := by
  cases result <;> rfl

theorem invariants_liftNativeBlock
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (computation : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α)
    (hcommutes : ∀ cache, OtsProbeSimulation.CacheMapCommutes (nativeCacheProjection parameter table cache) computation)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache finalCache : SplitHashCache) (result : NativeStepResult α)
    (hsynced : RevealedSynced parameter table state ftsCache)
    (hresult : .done false finalState (result, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel ((liftNativeBlock computation context fuel history cache).run ftsCache))) :
    finalState = state ∧ RevealedSynced parameter table finalState finalCache ∧
      ∀ coordinate, finalCache (.hiddenLeaf coordinate) = ftsCache (.hiddenLeaf coordinate) := by
  rw [runDetailed_liftNativeBlock, support_map] at hresult
  obtain ⟨native, hnative, heq⟩ := hresult
  simp only [AdaptiveRevealProbe.DetailedResult.done.injEq, Prod.mk.injEq] at heq
  obtain ⟨_, hstate, hresult, hcache⟩ := heq
  subst finalState
  subst result
  subst finalCache
  refine ⟨rfl, ?_, cacheAfterNativeBlock_hidden ftsCache native⟩
  cases native with
  | none => exact hsynced
  | some entry =>
      exact revealedSynced_afterNativeBlock parameter table state ftsCache cache computation hcommutes
        context fuel history entry hsynced hnative

theorem hiddenIndexCached_afterNativeBlock (index : Index) (cache : SplitHashCache) (result : NativeStepResult α)
    (hcached : HiddenIndexCached index cache) :
    HiddenIndexCached index (cacheAfterNativeBlock cache result) := by
  intro tree leaf
  simpa only [cacheAfterNativeBlock_hidden] using hcached tree leaf

end SphincsSecurity.Concrete.FtsProbeSimulation
