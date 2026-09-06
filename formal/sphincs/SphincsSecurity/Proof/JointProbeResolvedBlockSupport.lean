import SphincsSecurity.Proof.JointProbeResolvedBind

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
open OtsProbeSimulation (ResolvedRunResult OtsSecretIndex)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] maskedFtsKey maskedFtsOpen

def packResolvedNativeBlock (cache : SplitHashCache) (entry : ResolvedRunResult (α × OtsProbeSimulation.SplitHashCache)) :
    ResolvedRunResult (α × JointSourceCache) :=
  ⟨entry.context, entry.remaining, (entry.value.1, entry.value.2, withNativeOrdinaryCache cache entry.value.2), entry.table⟩

theorem runDetailed_jointSourceNativeBlock
    (table : Coordinate → Digest) (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (computation : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache) :
    AdaptiveRevealProbe.runDetailed table state ftsFuel
      (runJointResolved ((jointSourceNativeBlock computation).run cache) context fuel otsTable) =
      (fun result => AdaptiveRevealProbe.DetailedResult.done (AdaptiveRevealProbe.tableHits state table) state
        (result.map (packResolvedNativeBlock cache.2))) <$>
        OtsProbeSimulation.runResolvedFromTable context fuel otsTable (computation.run (prepareNativeCache cache.2 cache.1)) := by
  conv_lhs => dsimp only [jointSourceNativeBlock, StateT.run]
  rw [runJointResolved_map, runJointResolved_native]
  simp only [map_eq_bind_pure_comp, AdaptiveRevealProbe.runDetailed_liftProbComp_bind]
  rfl

theorem invariants_jointSourceNativeBlock
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (computation : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α)
    (hcommutes : ∀ cache, OtsProbeSimulation.CacheMapCommutes (nativeCacheProjection parameter table cache) computation)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (entry : ResolvedRunResult (α × JointSourceCache)) (hsynced : RevealedSynced parameter table state cache.2)
    (hresult : .done false finalState (some entry) ∈ support (AdaptiveRevealProbe.runDetailed table state ftsFuel
      (runJointResolved ((jointSourceNativeBlock computation).run cache) context fuel otsTable))) :
    finalState = state ∧ RevealedSynced parameter table finalState entry.value.2.2 ∧
      ∀ coordinate, entry.value.2.2 (.hiddenLeaf coordinate) = cache.2 (.hiddenLeaf coordinate) := by
  rw [runDetailed_jointSourceNativeBlock, support_map] at hresult
  obtain ⟨result, hresult, heq⟩ := hresult
  cases result with
  | none => simp at heq
  | some result =>
      simp only [Option.map_some, AdaptiveRevealProbe.DetailedResult.done.injEq, Option.some.injEq] at heq
      obtain ⟨_, hstate, hentry⟩ := heq
      subst finalState
      subst entry
      exact ⟨rfl, revealedSynced_afterResolvedNativeBlock parameter table state cache.2 cache.1 computation hcommutes
        context fuel otsTable result hsynced hresult, fun _ => rfl⟩

def wrapResolvedFtsBlock (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput)
    (cache : OtsProbeSimulation.SplitHashCache) : AdaptiveRevealProbe.DetailedResult Coordinate (α × SplitHashCache) →
      AdaptiveRevealProbe.DetailedResult Coordinate (Option (ResolvedRunResult (α × JointSourceCache))) :=
  AdaptiveRevealProbe.DetailedResult.mapValue (fun result => some ⟨context, fuel, (result.1, cache, result.2), otsTable⟩)

theorem runDetailed_jointSourceFtsBlock
    (table : Coordinate → Digest) (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (computation : StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache) :
    AdaptiveRevealProbe.runDetailed table state ftsFuel
      (runJointResolved ((jointSourceFtsBlock computation).run cache) context fuel otsTable) =
      wrapResolvedFtsBlock context fuel otsTable cache.1 <$>
        AdaptiveRevealProbe.runDetailed table state ftsFuel (computation.run cache.2) := by
  conv_lhs => dsimp only [jointSourceFtsBlock, StateT.run]
  rw [runJointResolved_map, runJointResolved_fts, Functor.map_map, AdaptiveRevealProbe.runDetailed_mapValue]
  rfl

theorem mem_support_jointSourceFtsBlock_done
    (table : Coordinate → Digest) (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (computation : StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (entry : ResolvedRunResult (α × JointSourceCache))
    (hresult : .done false finalState (some entry) ∈ support (AdaptiveRevealProbe.runDetailed table state ftsFuel
      (runJointResolved ((jointSourceFtsBlock computation).run cache) context fuel otsTable))) :
    ∃ value finalCache, entry = ⟨context, fuel, (value, cache.1, finalCache), otsTable⟩ ∧
      .done false finalState (value, finalCache) ∈ support (AdaptiveRevealProbe.runDetailed table state ftsFuel (computation.run cache.2)) := by
  rw [runDetailed_jointSourceFtsBlock, support_map] at hresult
  obtain ⟨result, hresult, heq⟩ := hresult
  cases result with
  | stopped hit => simp [wrapResolvedFtsBlock, AdaptiveRevealProbe.DetailedResult.mapValue] at heq
  | done hit resultState value =>
      simp only [wrapResolvedFtsBlock, AdaptiveRevealProbe.DetailedResult.mapValue,
        AdaptiveRevealProbe.DetailedResult.done.injEq, Option.some.injEq] at heq
      obtain ⟨hhit, hstate, hentry⟩ := heq
      subst hit
      subst finalState
      subst entry
      exact ⟨value.1, value.2, rfl, hresult⟩

theorem revealedSynced_jointSourceFtsBlock
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (computation : StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (entry : ResolvedRunResult (α × JointSourceCache))
    (hclean : AdaptiveRevealProbe.tableHits state table = false) (hsynced : RevealedSynced parameter table state cache.2)
    (hstateFree : StateFree computation) (hpreserving : CachePreserving computation)
    (hresult : .done false finalState (some entry) ∈ support (AdaptiveRevealProbe.runDetailed table state ftsFuel
      (runJointResolved ((jointSourceFtsBlock computation).run cache) context fuel otsTable))) :
    RevealedSynced parameter table finalState entry.value.2.2 := by
  obtain ⟨value, finalCache, rfl, hvalue⟩ := mem_support_jointSourceFtsBlock_done table state finalState ftsFuel computation
    context fuel otsTable cache entry hresult
  exact revealedSynced_of_mem_runDetailed_stateFree parameter table state finalState ftsFuel cache.2 finalCache value
    computation hclean hsynced hstateFree hpreserving hvalue

theorem hiddenIndexCached_jointSourceFtsKey
    (parameter : PublicParameter) (table : Coordinate → Digest) (index : Index)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (otsTable : OtsSecretIndex → HashOutput) (cache : JointSourceCache)
    (entry : ResolvedRunResult (Digest × JointSourceCache)) (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hresult : .done false finalState (some entry) ∈ support (AdaptiveRevealProbe.runDetailed table state ftsFuel
      (runJointResolved ((jointSourceFtsBlock (maskedFtsKey parameter index)).run cache) context fuel otsTable))) :
    HiddenIndexCached index entry.value.2.2 := by
  obtain ⟨value, finalCache, rfl, hvalue⟩ := mem_support_jointSourceFtsBlock_done table state finalState ftsFuel _
    context fuel otsTable cache entry hresult
  exact hiddenLeaves_cached_of_mem_runDetailed_maskedFtsKey parameter table state finalState ftsFuel
    cache.2 finalCache index value hclean hvalue

end SphincsSecurity.Concrete.FtsProbeSimulation
