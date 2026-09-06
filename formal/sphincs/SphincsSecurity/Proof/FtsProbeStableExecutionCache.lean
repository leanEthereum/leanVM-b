import SphincsSecurity.Proof.FtsProbeJointExecution
import SphincsSecurity.Proof.OtsProbeStableExecutionCache

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem NativeStepRelAt.mem_support_native
    {parameter : PublicParameter} {table : Coordinate → Digest}
    {state finalState : AdaptiveRevealProbe.State Coordinate} {ftsFuel : Nat}
    {masked : NativeFtsStep α}
    {native : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α}
    {context : OtsProbeSimulation.DeferredContext} {fuel : Nat} {history : List OtsProbeSimulation.Probe}
    {cache : OtsProbeSimulation.SplitHashCache} {ftsCache finalCache : SplitHashCache}
    {entry : OtsProbeSimulation.HistoryResolvedPrefix (α × OtsProbeSimulation.SplitHashCache)}
    (h : NativeStepRelAt parameter table state ftsFuel masked native context fuel history cache ftsCache)
    (hresult : .done false finalState (some entry, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel ((masked context fuel history cache).run ftsCache))) :
    some (OtsProbeSimulation.replaceHistoryOrdinaryCache (mergedCache parameter table finalCache) entry) ∈ support
      (OtsProbeSimulation.runResolvedHistoryPrefix
        (OtsProbeSimulation.eraseProbeQueries
          (native.run (OtsProbeSimulation.replaceOrdinaryCache cache (mergedCache parameter table ftsCache)))) context fuel history) := by
  obtain ⟨result, hnative, hrelation⟩ := OtsProbeSimulation.exists_right_of_relTriple_of_mem_support h hresult
  rcases hrelation with hhit | heq
  · cases hhit
  · rw [← heq] at hnative
    exact hnative

def StableMergedCacheLE (parameter : PublicParameter) (table : Coordinate → Digest)
    (initial final : SplitHashCache) : Prop :=
  OtsProbeSimulation.StableOrdinaryCacheLE parameter
    (OtsProbeSimulation.replaceOrdinaryCache OtsProbeSimulation.emptySplitHashCache (mergedCache parameter table initial))
    (OtsProbeSimulation.replaceOrdinaryCache OtsProbeSimulation.emptySplitHashCache (mergedCache parameter table final))

theorem stableMergedCacheLE_maskedJointComputation
    (parameter : PublicParameter) (root : Digest) (table : Coordinate → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache finalCache : SplitHashCache)
    (entry : OtsProbeSimulation.HistoryResolvedPrefix (α × OtsProbeSimulation.SplitHashCache))
    (hbound : computation.IsQueryBoundP OtsProbeSimulation.IsOuterHash ftsFuel)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache)
    (hresult : .done false finalState (some entry, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel
        ((maskedJointComputation parameter root computation context fuel history cache).run ftsCache))) :
    StableMergedCacheLE parameter table ftsCache finalCache := by
  have hnative := (nativeStepRelAt_maskedJointComputation parameter root table computation state ftsFuel
    context fuel history cache ftsCache hbound hclean hsynced).mem_support_native hresult
  exact OtsProbeSimulation.stableHistoryCacheSupport_nativeComputation parameter root
    (fun index tree leaf => table (index, tree, leaf)) computation context fuel history _ _ hnative

end SphincsSecurity.Concrete.FtsProbeSimulation
