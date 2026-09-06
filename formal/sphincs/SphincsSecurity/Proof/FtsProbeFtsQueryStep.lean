import SphincsSecurity.Proof.FtsProbeStepComposition
import SphincsSecurity.Proof.FtsProbeNativeQuery

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def NativeStepCleanRel (parameter : PublicParameter) (table : Coordinate → Digest)
    (masked : AdaptiveRevealProbe.DetailedResult Coordinate (NativeStepResult α × SplitHashCache))
    (native : NativeStepResult α) : Prop :=
  masked.hit = true ∨ projectNativeStepCache parameter table masked = native

def wrapFtsQueryStep
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) :
    AdaptiveRevealProbe.DetailedResult Coordinate (α × SplitHashCache) →
      AdaptiveRevealProbe.DetailedResult Coordinate (NativeStepResult α × SplitHashCache) :=
  AdaptiveRevealProbe.DetailedResult.mapValue (fun value =>
    (some (⟨context, fuel, (value.1, cache), history⟩ : OtsProbeSimulation.HistoryResolvedPrefix (α × OtsProbeSimulation.SplitHashCache)), value.2))

theorem nativeStepCleanRel_wrapFtsQueryStep
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache)
    (result : AdaptiveRevealProbe.DetailedResult Coordinate (α × SplitHashCache)) (native : NativeStepResult α)
    (h : NativeCleanStepRel parameter table context fuel history cache result native) :
    NativeStepCleanRel parameter table (wrapFtsQueryStep context fuel history cache result) native := by
  rcases h with hhit | ⟨ordinary, hnative, hclean⟩
  · left
    cases result <;> exact hhit
  · right
    cases result with
    | stopped hit => exact False.elim hclean
    | done hit finalState value =>
        rcases hclean with ⟨rfl, rfl, _, _⟩
        exact hnative.symm

theorem relTriple_nativeStep_ftsQuery
    (parameter : PublicParameter) (table : Coordinate → Digest) (input : HashInput) (probe : FtsSecretProbe)
    (state : AdaptiveRevealProbe.State Coordinate) (remaining : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache : SplitHashCache)
    (hdecode : decodeProbe? parameter input = some probe)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache) :
    RelTriple
      (AdaptiveRevealProbe.runDetailed table state (remaining + 1)
        ((liftFtsBlock (probingHashQuery parameter input) context fuel history cache).run ftsCache))
      (OtsProbeSimulation.runResolvedHistoryPrefix
        (OtsProbeSimulation.eraseProbeQueries
          ((OtsProbeSimulation.probingHashQuery parameter input).run
            (OtsProbeSimulation.replaceOrdinaryCache cache (mergedCache parameter table ftsCache)))) context fuel history)
      (NativeStepCleanRel parameter table) := by
  have h := relTriple_nativeHistory_ftsProbe parameter table state remaining ftsCache input probe context fuel history
    (OtsProbeSimulation.replaceOrdinaryCache cache (mergedCache parameter table ftsCache)) hdecode hclean hsynced
    (OtsProbeSimulation.ordinaryQueryCache_replaceOrdinaryCache _ _)
  have hrel := relTriple_post_mono h (R' := fun result native => NativeStepCleanRel parameter table
    (wrapFtsQueryStep context fuel history cache result) native) (fun result native hstep => by
      have hstep' : NativeCleanStepRel parameter table context fuel history cache result native := by
        rcases hstep with hhit | ⟨ordinary, hnative, hclean⟩
        · exact Or.inl hhit
        · refine Or.inr ⟨ordinary, ?_, hclean⟩
          simpa only [OtsProbeSimulation.ordinaryHistoryResult, OtsProbeSimulation.replaceOrdinaryCache_replace] using hnative
      exact nativeStepCleanRel_wrapFtsQueryStep parameter table context fuel history cache result native hstep')
  have hm := relTriple_map (f := wrapFtsQueryStep context fuel history cache) (g := id) hrel
  simpa only [liftFtsBlock, StateT.run_map, AdaptiveRevealProbe.runDetailed_mapValue, id_map, wrapFtsQueryStep] using hm

end SphincsSecurity.Concrete.FtsProbeSimulation
