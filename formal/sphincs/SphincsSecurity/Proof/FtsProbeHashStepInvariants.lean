import SphincsSecurity.Proof.FtsProbeStepComposition

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable

theorem revealedSynced_liftFtsBlock
    (parameter : PublicParameter) (table : Coordinate → Digest)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (computation : StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache finalCache : SplitHashCache) (result : NativeStepResult α)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hsynced : RevealedSynced parameter table state ftsCache)
    (hstateFree : StateFree computation) (hpreserving : CachePreserving computation)
    (hresult : .done false finalState (result, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel ((liftFtsBlock computation context fuel history cache).run ftsCache))) :
    RevealedSynced parameter table finalState finalCache := by
  obtain ⟨value, _, hvalue⟩ := mem_support_liftFtsBlock_done table state finalState ftsFuel computation
    context fuel history cache ftsCache finalCache result hresult
  exact revealedSynced_of_mem_runDetailed_stateFree parameter table state finalState ftsFuel
    ftsCache finalCache value computation hclean hsynced hstateFree hpreserving hvalue

theorem hiddenIndexCached_liftFtsKey
    (parameter : PublicParameter) (table : Coordinate → Digest) (index : Index)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache finalCache : SplitHashCache) (result : NativeStepResult Digest)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hresult : .done false finalState (result, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel ((liftFtsBlock (maskedFtsKey parameter index)
        context fuel history cache).run ftsCache))) :
    HiddenIndexCached index finalCache := by
  generalize hcomputation : maskedFtsKey parameter index = computation at hresult
  obtain ⟨value, _, hvalue⟩ := mem_support_liftFtsBlock_done (α := Digest) table state finalState ftsFuel
    computation context fuel history cache ftsCache finalCache result hresult
  rw [← hcomputation] at hvalue
  exact hiddenLeaves_cached_of_mem_runDetailed_maskedFtsKey parameter table state finalState ftsFuel
    ftsCache finalCache index value hclean hvalue

end SphincsSecurity.Concrete.FtsProbeSimulation
