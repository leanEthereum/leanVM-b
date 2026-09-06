import SphincsSecurity.Proof.OtsProbeCacheMap

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def withNativeOrdinaryCache (ftsCache : SplitHashCache) (otsCache : OtsProbeSimulation.SplitHashCache) : SplitHashCache
  | .ordinary input => otsCache (.ordinary input)
  | .hiddenLeaf coordinate => ftsCache (.hiddenLeaf coordinate)

noncomputable def nativeCacheProjection (parameter : PublicParameter) (table : Coordinate → Digest)
    (ftsCache : SplitHashCache) (otsCache : OtsProbeSimulation.SplitHashCache) : OtsProbeSimulation.SplitHashCache :=
  OtsProbeSimulation.replaceOrdinaryCache otsCache (mergedCache parameter table (withNativeOrdinaryCache ftsCache otsCache))

theorem nativeCacheProjection_hidden (parameter : PublicParameter) (table : Coordinate → Digest)
    (ftsCache : SplitHashCache) (otsCache : OtsProbeSimulation.SplitHashCache) (coordinate : OtsProbeSimulation.Coordinate) :
    nativeCacheProjection parameter table ftsCache otsCache (.hidden coordinate) = otsCache (.hidden coordinate) := rfl

theorem nativeCacheProjection_ordinary (parameter : PublicParameter) (table : Coordinate → Digest)
    (ftsCache : SplitHashCache) (otsCache : OtsProbeSimulation.SplitHashCache) (input : HashInput)
    (hordinary : IsOrdinaryInput parameter table input) :
    nativeCacheProjection parameter table ftsCache otsCache (.ordinary input) = otsCache (.ordinary input) :=
  mergedCache_eq_ordinary_of_isOrdinary parameter table (withNativeOrdinaryCache ftsCache otsCache) input hordinary

theorem withNativeOrdinaryCache_update_hidden
    (ftsCache : SplitHashCache) (otsCache : OtsProbeSimulation.SplitHashCache)
    (coordinate : OtsProbeSimulation.Coordinate) (output : HashOutput) :
    withNativeOrdinaryCache ftsCache (Function.update otsCache (.hidden coordinate) (some output)) =
      withNativeOrdinaryCache ftsCache otsCache := by
  funext key
  cases key <;> simp [withNativeOrdinaryCache, Function.update]

theorem withNativeOrdinaryCache_update_ordinary
    (ftsCache : SplitHashCache) (otsCache : OtsProbeSimulation.SplitHashCache) (input : HashInput) (output : HashOutput) :
    withNativeOrdinaryCache ftsCache (Function.update otsCache (.ordinary input) (some output)) =
      Function.update (withNativeOrdinaryCache ftsCache otsCache) (.ordinary input) (some output) := by
  funext key
  cases key with
  | hiddenLeaf coordinate => simp [withNativeOrdinaryCache, Function.update]
  | ordinary other =>
      by_cases heq : other = input <;> simp [withNativeOrdinaryCache, Function.update, heq]

theorem nativeCacheProjection_update_hidden (parameter : PublicParameter) (table : Coordinate → Digest)
    (ftsCache : SplitHashCache) (otsCache : OtsProbeSimulation.SplitHashCache)
    (coordinate : OtsProbeSimulation.Coordinate) (output : HashOutput) :
    nativeCacheProjection parameter table ftsCache (Function.update otsCache (.hidden coordinate) (some output)) =
      Function.update (nativeCacheProjection parameter table ftsCache otsCache) (.hidden coordinate) (some output) := by
  simp only [nativeCacheProjection, withNativeOrdinaryCache_update_hidden, OtsProbeSimulation.replaceOrdinaryCache_update_hidden]

theorem nativeCacheProjection_update_ordinary (parameter : PublicParameter) (table : Coordinate → Digest)
    (ftsCache : SplitHashCache) (otsCache : OtsProbeSimulation.SplitHashCache) (input : HashInput) (output : HashOutput)
    (hordinary : IsOrdinaryInput parameter table input) :
    nativeCacheProjection parameter table ftsCache (Function.update otsCache (.ordinary input) (some output)) =
      Function.update (nativeCacheProjection parameter table ftsCache otsCache) (.ordinary input) (some output) := by
  rw [nativeCacheProjection, withNativeOrdinaryCache_update_ordinary, mergedCache_update_ordinary parameter table _ input output hordinary]
  funext key
  cases key with
  | hidden coordinate => simp [nativeCacheProjection, OtsProbeSimulation.replaceOrdinaryCache, Function.update]
  | ordinary other =>
      by_cases heq : other = input <;>
        simp [nativeCacheProjection, OtsProbeSimulation.replaceOrdinaryCache, Function.update, QueryCache.cacheQuery, heq]

theorem cacheMapCommutes_native_ordinaryHash (parameter : PublicParameter) (table : Coordinate → Digest)
    (ftsCache : SplitHashCache) (input : HashInput) (hordinary : IsOrdinaryInput parameter table input) :
    OtsProbeSimulation.CacheMapCommutes (nativeCacheProjection parameter table ftsCache)
      (OtsProbeSimulation.ordinaryHashImpl input) := by
  intro cache
  change (OtsProbeSimulation.splitHashQuery (.ordinary input)).run (nativeCacheProjection parameter table ftsCache cache) = _
  rw [OtsProbeSimulation.splitHashQuery_run_eq]
  change _ = (fun result => (result.1, nativeCacheProjection parameter table ftsCache result.2)) <$>
    (OtsProbeSimulation.splitHashQuery (.ordinary input)).run cache
  rw [OtsProbeSimulation.splitHashQuery_run_eq, nativeCacheProjection_ordinary parameter table ftsCache cache input hordinary]
  cases hlookup : cache (.ordinary input) with
  | some output => simp only [map_pure]
  | none =>
      rw [map_bind]
      apply bind_congr
      intro output
      simp only [map_pure, nativeCacheProjection_update_ordinary parameter table ftsCache cache input output hordinary]

theorem cacheMapCommutes_native_simulateQ_ordinaryHash
    (parameter : PublicParameter) (table : Coordinate → Digest) (ftsCache : SplitHashCache)
    (computation : OracleComp HashSpec α) (hordinary : OrdinaryOnly parameter table computation) :
    OtsProbeSimulation.CacheMapCommutes (nativeCacheProjection parameter table ftsCache)
      (simulateQ OtsProbeSimulation.ordinaryHashImpl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      simpa only [simulateQ_pure] using OtsProbeSimulation.CacheMapCommutes.pure (nativeCacheProjection parameter table ftsCache) value
  | query_bind input next ih =>
      rw [OrdinaryOnly, isQueryBoundP_query_bind_iff] at hordinary
      rw [simulateQ_bind, simulateQ_spec_query]
      exact (cacheMapCommutes_native_ordinaryHash parameter table ftsCache input
        (by simpa [NonOrdinaryInput] using hordinary.1)).bind fun output =>
          ih output (by simpa [OrdinaryOnly, NonOrdinaryInput] using hordinary.2 output)

end SphincsSecurity.Concrete.FtsProbeSimulation
