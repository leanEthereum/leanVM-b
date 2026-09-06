import SphincsSecurity.Proof.FtsProbeNativeStepInvariants

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (HistoryResolvedPrefix ordinaryHistoryResult)

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def liftFtsBlock
    (computation : StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) :
    StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) (NativeStepResult α) :=
  (fun value => some (⟨context, fuel, (value, cache), history⟩ : HistoryResolvedPrefix (α × OtsProbeSimulation.SplitHashCache))) <$> computation

theorem liftFtsBlock_probeFree
    (computation : StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (hfree : ProbeFree computation) :
    ProbeFree (liftFtsBlock computation context fuel history cache) := hfree.map _

theorem projectNativeStepCache_ftsValue
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache)
    (result : AdaptiveRevealProbe.DetailedResult Coordinate (α × SplitHashCache)) :
    projectNativeStepCache parameter table (result.mapValue (fun value =>
      (some (⟨context, fuel, (value.1, cache), history⟩ : HistoryResolvedPrefix (α × OtsProbeSimulation.SplitHashCache)), value.2))) =
      (projectDetailedCache parameter table result).bind (ordinaryHistoryResult context fuel history cache) := by
  cases result with
  | stopped hit => rfl
  | done hit finalState value => cases hit <;> rfl

theorem projectNativeStepCache_liftFtsBlock
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat) (ftsCache : SplitHashCache)
    (masked : StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) α)
    (ordinary : OracleComp HashSpec α)
    (hcoupled : CoupledAt parameter table state ftsFuel masked
      (simulateQ (randomOracle : QueryImpl HashSpec _) ordinary) ftsCache)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) :
    projectNativeStepCache parameter table <$>
      AdaptiveRevealProbe.runDetailed table state ftsFuel ((liftFtsBlock masked context fuel history cache).run ftsCache) =
      OtsProbeSimulation.runResolvedHistoryPrefix
        (OtsProbeSimulation.eraseProbeQueries
          ((simulateQ OtsProbeSimulation.ordinaryHashImpl ordinary).run
            (OtsProbeSimulation.replaceOrdinaryCache cache (mergedCache parameter table ftsCache)))) context fuel history := by
  rw [OtsProbeSimulation.runErasedHistoryPrefix_simulateQ_ordinaryHashImpl,
    OtsProbeSimulation.ordinaryQueryCache_replaceOrdinaryCache]
  have hm := congrArg (fun computation =>
    (fun result => result.bind (ordinaryHistoryResult context fuel history cache)) <$> computation) hcoupled
  simp only [Functor.map_map, Option.bind_some] at hm
  rw [liftFtsBlock, StateT.run_map, AdaptiveRevealProbe.runDetailed_mapValue, Functor.map_map]
  have hproject : (fun result => projectNativeStepCache parameter table
      (result.mapValue (fun value =>
        (some (⟨context, fuel, (value.1, cache), history⟩ : HistoryResolvedPrefix (α × OtsProbeSimulation.SplitHashCache)), value.2)))) =
      (fun result => (projectDetailedCache parameter table result).bind (ordinaryHistoryResult context fuel history cache)) :=
    funext (projectNativeStepCache_ftsValue parameter table context fuel history cache)
  change (fun (result : AdaptiveRevealProbe.DetailedResult Coordinate (α × SplitHashCache)) => projectNativeStepCache parameter table
    (result.mapValue (fun value =>
      (some (⟨context, fuel, (value.1, cache), history⟩ : HistoryResolvedPrefix (α × OtsProbeSimulation.SplitHashCache)), value.2)))) <$> _ = _
  rw [hproject, hm]
  congr 1

theorem mem_support_liftFtsBlock_done
    (table : Coordinate → Digest) (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (computation : StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache finalCache : SplitHashCache) (result : NativeStepResult α)
    (hresult : .done false finalState (result, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel ((liftFtsBlock computation context fuel history cache).run ftsCache))) :
    ∃ value, result = some (⟨context, fuel, (value, cache), history⟩ : HistoryResolvedPrefix (α × OtsProbeSimulation.SplitHashCache)) ∧
      .done false finalState (value, finalCache) ∈ support (AdaptiveRevealProbe.runDetailed table state ftsFuel (computation.run ftsCache)) := by
  rw [liftFtsBlock, StateT.run_map, AdaptiveRevealProbe.runDetailed_mapValue, support_map] at hresult
  obtain ⟨detailed, hdetailed, heq⟩ := hresult
  cases detailed with
  | stopped hit => simp [AdaptiveRevealProbe.DetailedResult.mapValue] at heq
  | done hit selectedState value =>
      simp only [AdaptiveRevealProbe.DetailedResult.mapValue, AdaptiveRevealProbe.DetailedResult.done.injEq,
        Prod.mk.injEq] at heq
      obtain ⟨hhit, hstate, hvalue, hcache⟩ := heq
      subst hit
      subst finalState
      subst finalCache
      subst result
      exact ⟨value.1, rfl, hdetailed⟩

end SphincsSecurity.Concrete.FtsProbeSimulation
