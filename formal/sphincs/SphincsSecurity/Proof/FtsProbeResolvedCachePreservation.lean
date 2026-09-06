import SphincsSecurity.Proof.FtsProbeNativeResolved
import SphincsSecurity.Proof.FtsProbeNativeCachePreservation

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

theorem CacheMapCommutes.resolved
    {rewrite : SplitHashCache → SplitHashCache}
    {computation : StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) α}
    (h : CacheMapCommutes rewrite computation)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    runResolvedFromTable context fuel table (computation.run (rewrite cache)) =
      Option.map (fun (entry : ResolvedRunResult (α × SplitHashCache)) =>
        { entry with value := (entry.value.1, rewrite entry.value.2) }) <$>
        runResolvedFromTable context fuel table (computation.run cache) := by
  rw [h, runResolvedFromTable_map]

end SphincsSecurity.Concrete.OtsProbeSimulation

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem hiddenInput_preserved_of_resolved
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (computation : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α)
    (hcommutes : ∀ ftsCache, OtsProbeSimulation.CacheMapCommutes (nativeCacheProjection parameter table ftsCache) computation)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsProbeSimulation.OtsSecretIndex → HashOutput)
    (cache : OtsProbeSimulation.SplitHashCache) (result : OtsProbeSimulation.ResolvedRunResult (α × OtsProbeSimulation.SplitHashCache))
    (hresult : some result ∈ support (OtsProbeSimulation.runResolvedFromTable context fuel otsTable (computation.run cache)))
    (coordinate : Coordinate) :
    result.value.2 (.ordinary (hiddenInput parameter table coordinate)) = cache (.ordinary (hiddenInput parameter table coordinate)) := by
  let shadow := cacheFromOrdinary parameter table (OtsProbeSimulation.ordinaryQueryCache cache)
  have hmap := (hcommutes shadow).resolved context fuel otsTable cache
  rw [nativeCacheProjection_fromOrdinary] at hmap
  rw [hmap, support_map] at hresult
  obtain ⟨entry, _, heq⟩ := hresult
  cases entry with
  | none => simp at heq
  | some entry =>
      simp only [Option.map_some, Option.some.injEq] at heq
      subst result
      exact nativeCacheProjection_hiddenInput parameter table shadow entry.value.2 coordinate

theorem revealedSynced_afterResolvedNativeBlock
    (parameter : PublicParameter) (table : Coordinate → Digest) (state : AdaptiveRevealProbe.State Coordinate)
    (ftsCache : SplitHashCache) (otsCache : OtsProbeSimulation.SplitHashCache)
    (computation : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α)
    (hcommutes : ∀ cache, OtsProbeSimulation.CacheMapCommutes (nativeCacheProjection parameter table cache) computation)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsProbeSimulation.OtsSecretIndex → HashOutput)
    (result : OtsProbeSimulation.ResolvedRunResult (α × OtsProbeSimulation.SplitHashCache))
    (hsynced : RevealedSynced parameter table state ftsCache)
    (hresult : some result ∈ support (OtsProbeSimulation.runResolvedFromTable context fuel otsTable (computation.run (prepareNativeCache ftsCache otsCache)))) :
    RevealedSynced parameter table state (withNativeOrdinaryCache ftsCache result.value.2) := by
  intro coordinate value hvalue
  obtain ⟨hvalue, output, hhidden, hordinary⟩ := hsynced coordinate value hvalue
  refine ⟨hvalue, output, hhidden, ?_⟩
  exact (hiddenInput_preserved_of_resolved parameter table computation hcommutes context fuel otsTable
    (prepareNativeCache ftsCache otsCache) result hresult coordinate).trans hordinary

end SphincsSecurity.Concrete.FtsProbeSimulation
