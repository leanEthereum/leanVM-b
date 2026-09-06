import SphincsSecurity.Proof.FtsProbeJointSignerSynced

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem state_eq_liftNativeBlock
    (table : Coordinate → Digest) (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (computation : StateT OtsProbeSimulation.SplitHashCache (OracleComp (LazyRevealProbe.World OtsProbeSimulation.Coordinate)) α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache finalCache : SplitHashCache) (result : NativeStepResult α)
    (hresult : .done false finalState (result, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel ((liftNativeBlock computation context fuel history cache).run ftsCache))) :
    finalState = state := by
  rw [runDetailed_liftNativeBlock, support_map] at hresult
  obtain ⟨entry, _, heq⟩ := hresult
  exact (AdaptiveRevealProbe.DetailedResult.done.inj heq).2.1.symm

theorem state_eq_liftFtsBlock
    (table : Coordinate → Digest) (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (computation : StateT SplitHashCache (OracleComp (AdaptiveRevealProbe.World Coordinate)) α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache finalCache : SplitHashCache) (result : NativeStepResult α)
    (hclean : AdaptiveRevealProbe.tableHits state table = false) (hstateFree : StateFree computation)
    (hresult : .done false finalState (result, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel ((liftFtsBlock computation context fuel history cache).run ftsCache))) :
    finalState = state := by
  obtain ⟨value, _, hvalue⟩ := mem_support_liftFtsBlock_done table state finalState ftsFuel computation
    context fuel history cache ftsCache finalCache result hresult
  obtain ⟨raw, heq⟩ := AdaptiveRevealProbe.runDetailed_stateFree_support table state ftsFuel
    (computation.run ftsCache) (hstateFree ftsCache) hclean _ hvalue
  exact (AdaptiveRevealProbe.DetailedResult.done.inj heq).2.1

end SphincsSecurity.Concrete.FtsProbeSimulation
