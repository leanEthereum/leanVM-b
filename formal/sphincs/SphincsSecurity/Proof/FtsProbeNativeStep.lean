import SphincsSecurity.Proof.FtsProbeNativeCachePreservation
import SphincsSecurity.Proof.AdaptiveRevealProbeLift

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (HistoryResolvedPrefix replaceHistoryOrdinaryCache)

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2000

abbrev NativeStepResult (α : Type) := Option (HistoryResolvedPrefix (α × OtsProbeSimulation.SplitHashCache))

def cacheAfterNativeBlock (cache : SplitHashCache) : NativeStepResult α → SplitHashCache
  | none => cache
  | some entry => withNativeOrdinaryCache cache entry.value.2

noncomputable def projectNativeStepCache (parameter : PublicParameter) (table : Coordinate → Digest) :
    AdaptiveRevealProbe.DetailedResult Coordinate (NativeStepResult α × SplitHashCache) → NativeStepResult α
  | .stopped _ => none
  | .done true _ _ => none
  | .done false _ (result, cache) => result.map (replaceHistoryOrdinaryCache (mergedCache parameter table cache))

noncomputable def liftNativeBlock
    (computation : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) :
    StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) (NativeStepResult α) := do
  let ftsCache ← get
  let result ← liftM (AdaptiveRevealProbe.liftProbComp (Coordinate := Coordinate)
    (OtsProbeSimulation.runResolvedHistoryPrefix
      (OtsProbeSimulation.eraseProbeQueries (computation.run (prepareNativeCache ftsCache cache))) context fuel history))
  set (cacheAfterNativeBlock ftsCache result)
  pure result

theorem liftNativeBlock_run
    (computation : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache) :
    (liftNativeBlock computation context fuel history cache).run ftsCache =
      AdaptiveRevealProbe.liftProbComp
        (OtsProbeSimulation.runResolvedHistoryPrefix
          (OtsProbeSimulation.eraseProbeQueries (computation.run (prepareNativeCache ftsCache cache))) context fuel history) >>=
        fun result => pure (result, cacheAfterNativeBlock ftsCache result) := by
  simp [liftNativeBlock, StateT.run_bind]

theorem liftNativeBlock_probeFree
    (computation : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) :
    ProbeFree (liftNativeBlock computation context fuel history cache) := by
  intro ftsCache
  rw [liftNativeBlock_run, bind_pure_comp, isQueryBoundP_map_iff]
  exact AdaptiveRevealProbe.liftProbComp_isProbeBound _ 0

theorem runDetailed_liftNativeBlock
    (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (computation : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache) :
    AdaptiveRevealProbe.runDetailed table state ftsFuel ((liftNativeBlock computation context fuel history cache).run ftsCache) =
      (fun result => AdaptiveRevealProbe.DetailedResult.done (AdaptiveRevealProbe.tableHits state table) state
        (result, cacheAfterNativeBlock ftsCache result)) <$>
        OtsProbeSimulation.runResolvedHistoryPrefix
          (OtsProbeSimulation.eraseProbeQueries (computation.run (prepareNativeCache ftsCache cache))) context fuel history := by
  rw [liftNativeBlock_run, AdaptiveRevealProbe.runDetailed_liftProbComp_bind]
  rfl

theorem projectNativeStepCache_done_clean
    (parameter : PublicParameter) (table : Coordinate → Digest) (state : AdaptiveRevealProbe.State Coordinate)
    (ftsCache : SplitHashCache) (result : NativeStepResult α)
    (hclean : AdaptiveRevealProbe.tableHits state table = false) :
    projectNativeStepCache parameter table (.done (AdaptiveRevealProbe.tableHits state table) state
      (result, cacheAfterNativeBlock ftsCache result)) =
      result.map (fun entry => { entry with value :=
        (entry.value.1, nativeCacheProjection parameter table ftsCache entry.value.2) }) := by
  rw [hclean]
  cases result <;> rfl

theorem projectNativeStepCache_liftNativeBlock
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat) (ftsCache : SplitHashCache)
    (computation : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α)
    (hcommutes : OtsProbeSimulation.CacheMapCommutes (nativeCacheProjection parameter table ftsCache) computation)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache)
    (hclean : AdaptiveRevealProbe.tableHits state table = false) :
    projectNativeStepCache parameter table <$>
      AdaptiveRevealProbe.runDetailed table state ftsFuel ((liftNativeBlock computation context fuel history cache).run ftsCache) =
      OtsProbeSimulation.runResolvedHistoryPrefix
        (OtsProbeSimulation.eraseProbeQueries
          (computation.run (OtsProbeSimulation.replaceOrdinaryCache cache (mergedCache parameter table ftsCache)))) context fuel history := by
  have hnative := hcommutes.historyPrefix context fuel history (prepareNativeCache ftsCache cache)
  rw [nativeCacheProjection_prepare] at hnative
  rw [hnative, runDetailed_liftNativeBlock, Functor.map_map]
  apply congrArg (fun f => f <$> OtsProbeSimulation.runResolvedHistoryPrefix
    (OtsProbeSimulation.eraseProbeQueries (computation.run (prepareNativeCache ftsCache cache))) context fuel history)
  funext result
  exact projectNativeStepCache_done_clean parameter table state ftsCache result hclean

end SphincsSecurity.Concrete.FtsProbeSimulation
