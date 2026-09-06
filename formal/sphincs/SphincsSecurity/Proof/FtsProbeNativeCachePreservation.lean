import SphincsSecurity.Proof.FtsProbeNativeLayerCache

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def ordinaryQueryCache (cache : SplitHashCache) : QueryCache HashSpec := fun input => cache (.ordinary input)

def prepareNativeCache (ftsCache : SplitHashCache) (otsCache : OtsProbeSimulation.SplitHashCache) : OtsProbeSimulation.SplitHashCache :=
  OtsProbeSimulation.replaceOrdinaryCache otsCache (ordinaryQueryCache ftsCache)

theorem withNativeOrdinaryCache_prepare (ftsCache : SplitHashCache) (otsCache : OtsProbeSimulation.SplitHashCache) :
    withNativeOrdinaryCache ftsCache (prepareNativeCache ftsCache otsCache) = ftsCache := by
  funext key
  cases key <;> rfl

theorem nativeCacheProjection_prepare (parameter : PublicParameter) (table : Coordinate → Digest)
    (ftsCache : SplitHashCache) (otsCache : OtsProbeSimulation.SplitHashCache) :
    nativeCacheProjection parameter table ftsCache (prepareNativeCache ftsCache otsCache) =
      OtsProbeSimulation.replaceOrdinaryCache otsCache (mergedCache parameter table ftsCache) := by
  rw [nativeCacheProjection, withNativeOrdinaryCache_prepare, prepareNativeCache,
    OtsProbeSimulation.replaceOrdinaryCache_replace]

def cacheFromOrdinary (parameter : PublicParameter) (table : Coordinate → Digest) (ordinary : QueryCache HashSpec) : SplitHashCache
  | .ordinary input => ordinary input
  | .hiddenLeaf coordinate => ordinary (hiddenInput parameter table coordinate)

theorem mergedCache_fromOrdinary (parameter : PublicParameter) (table : Coordinate → Digest) (ordinary : QueryCache HashSpec) :
    mergedCache parameter table (cacheFromOrdinary parameter table ordinary) = ordinary := by
  funext input
  unfold mergedCache
  cases hdecode : decodeProbe? parameter input with
  | none => rfl
  | some probe =>
      simp only
      split_ifs with hhit
      · have hprobe := probe_eq_tableProbe_of_candidate table probe hhit
        have hinput := (decodeProbe?_eq_some_iff parameter input probe).1 hdecode
        rw [hprobe] at hinput
        change hiddenInput parameter table (probe.index, probe.tree, probe.leafIdx) = input at hinput
        change ordinary (hiddenInput parameter table (probe.index, probe.tree, probe.leafIdx)) = ordinary input
        rw [hinput]
      · rfl

theorem nativeCacheProjection_fromOrdinary (parameter : PublicParameter) (table : Coordinate → Digest)
    (cache : OtsProbeSimulation.SplitHashCache) :
    nativeCacheProjection parameter table (cacheFromOrdinary parameter table (OtsProbeSimulation.ordinaryQueryCache cache)) cache = cache := by
  have hcache : withNativeOrdinaryCache
      (cacheFromOrdinary parameter table (OtsProbeSimulation.ordinaryQueryCache cache)) cache =
      cacheFromOrdinary parameter table (OtsProbeSimulation.ordinaryQueryCache cache) := by
    funext key
    cases key <;> rfl
  rw [nativeCacheProjection, hcache, mergedCache_fromOrdinary, OtsProbeSimulation.replaceOrdinaryCache_self]

theorem nativeCacheProjection_hiddenInput (parameter : PublicParameter) (table : Coordinate → Digest)
    (ftsCache : SplitHashCache) (otsCache : OtsProbeSimulation.SplitHashCache) (coordinate : Coordinate) :
    nativeCacheProjection parameter table ftsCache otsCache (.ordinary (hiddenInput parameter table coordinate)) =
      ftsCache (.hiddenLeaf coordinate) := by
  change mergedCache parameter table (withNativeOrdinaryCache ftsCache otsCache) (hiddenInput parameter table coordinate) = _
  rw [mergedCache_hiddenInput]
  rfl

theorem hiddenInput_preserved_of_historyPrefix
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (computation : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α)
    (hcommutes : ∀ ftsCache, OtsProbeSimulation.CacheMapCommutes (nativeCacheProjection parameter table ftsCache) computation)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (result : OtsProbeSimulation.HistoryResolvedPrefix (α × OtsProbeSimulation.SplitHashCache))
    (hresult : some result ∈ support (OtsProbeSimulation.runResolvedHistoryPrefix
      (OtsProbeSimulation.eraseProbeQueries (computation.run cache)) context fuel history))
    (coordinate : Coordinate) :
    result.value.2 (.ordinary (hiddenInput parameter table coordinate)) = cache (.ordinary (hiddenInput parameter table coordinate)) := by
  let shadow := cacheFromOrdinary parameter table (OtsProbeSimulation.ordinaryQueryCache cache)
  have hmap := (hcommutes shadow).historyPrefix context fuel history cache
  rw [nativeCacheProjection_fromOrdinary] at hmap
  rw [hmap, support_map] at hresult
  obtain ⟨entry, _, heq⟩ := hresult
  cases entry with
  | none => simp at heq
  | some entry =>
      simp only [Option.map_some, Option.some.injEq] at heq
      subst result
      exact nativeCacheProjection_hiddenInput parameter table shadow entry.value.2 coordinate

theorem revealedSynced_afterNativeBlock
    (parameter : PublicParameter) (table : Coordinate → Digest) (state : AdaptiveRevealProbe.State Coordinate)
    (ftsCache : SplitHashCache) (otsCache : OtsProbeSimulation.SplitHashCache)
    (computation : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α)
    (hcommutes : ∀ cache, OtsProbeSimulation.CacheMapCommutes (nativeCacheProjection parameter table cache) computation)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (result : OtsProbeSimulation.HistoryResolvedPrefix (α × OtsProbeSimulation.SplitHashCache))
    (hsynced : RevealedSynced parameter table state ftsCache)
    (hresult : some result ∈ support (OtsProbeSimulation.runResolvedHistoryPrefix
      (OtsProbeSimulation.eraseProbeQueries (computation.run (prepareNativeCache ftsCache otsCache))) context fuel history)) :
    RevealedSynced parameter table state (withNativeOrdinaryCache ftsCache result.value.2) := by
  intro coordinate value hvalue
  obtain ⟨hvalue, output, hhidden, hordinary⟩ := hsynced coordinate value hvalue
  refine ⟨hvalue, output, hhidden, ?_⟩
  exact (hiddenInput_preserved_of_historyPrefix parameter table computation hcommutes context fuel history
    (prepareNativeCache ftsCache otsCache) result hresult coordinate).trans hordinary

end SphincsSecurity.Concrete.FtsProbeSimulation
