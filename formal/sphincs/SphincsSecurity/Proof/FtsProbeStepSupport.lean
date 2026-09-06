import SphincsSecurity.Proof.FtsProbeStepComposition

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem mem_support_bindNativeSteps_done
    (table : Coordinate → Digest) (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (left : NativeFtsStep α) (next : α → NativeFtsStep β)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache finalCache : SplitHashCache) (result : NativeStepResult β)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hfree : ProbeFree (left context fuel history cache))
    (hresult : .done false finalState (result, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel ((bindNativeSteps left next context fuel history cache).run ftsCache))) :
    (result = none ∧ .done false finalState (none, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel ((left context fuel history cache).run ftsCache))) ∨
    ∃ stepState entry stepCache,
      .done false stepState (some entry, stepCache) ∈ support
        (AdaptiveRevealProbe.runDetailed table state ftsFuel ((left context fuel history cache).run ftsCache)) ∧
      .done false finalState (result, finalCache) ∈ support
        (AdaptiveRevealProbe.runDetailed table stepState ftsFuel
          ((next entry.value.1 entry.context entry.remaining entry.history entry.value.2).run stepCache)) := by
  rw [bindNativeSteps, StateT.run_bind,
    AdaptiveRevealProbe.runDetailed_bind_probeFree table state ftsFuel _ _ (hfree ftsCache), mem_support_bind_iff] at hresult
  obtain ⟨detailed, hleft, hnext⟩ := hresult
  obtain ⟨stepState, value, heq, hstepClean⟩ :=
    AdaptiveRevealProbe.runDetailed_probeFree_support table state ftsFuel _ (hfree ftsCache) hclean detailed hleft
  subst detailed
  rcases value with ⟨entry, stepCache⟩
  cases entry with
  | none =>
      simp only [StateT.run_pure, AdaptiveRevealProbe.runDetailed, construct_pure, hstepClean,
        mem_support_pure_iff, AdaptiveRevealProbe.DetailedResult.done.injEq, Prod.mk.injEq] at hnext
      obtain ⟨_, hstate, hresult, hcache⟩ := hnext
      subst finalState
      subst result
      subst finalCache
      exact Or.inl ⟨rfl, hleft⟩
  | some entry => exact Or.inr ⟨stepState, entry, stepCache, hleft, hnext⟩

theorem preserves_bindNativeSteps
    (table : Coordinate → Digest) (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel : Nat)
    (left : NativeFtsStep α) (next : α → NativeFtsStep β)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache finalCache : SplitHashCache) (result : NativeStepResult β)
    (invariant : AdaptiveRevealProbe.State Coordinate → SplitHashCache → Prop)
    (hclean : AdaptiveRevealProbe.tableHits state table = false)
    (hfree : ProbeFree (left context fuel history cache))
    (hleft : ∀ stepState entry stepCache,
      .done false stepState (entry, stepCache) ∈ support
        (AdaptiveRevealProbe.runDetailed table state ftsFuel ((left context fuel history cache).run ftsCache)) →
      invariant stepState stepCache)
    (hnext : ∀ stepState entry stepCache,
      .done false stepState (some entry, stepCache) ∈ support
        (AdaptiveRevealProbe.runDetailed table state ftsFuel ((left context fuel history cache).run ftsCache)) →
      .done false finalState (result, finalCache) ∈ support
        (AdaptiveRevealProbe.runDetailed table stepState ftsFuel
          ((next entry.value.1 entry.context entry.remaining entry.history entry.value.2).run stepCache)) →
      invariant finalState finalCache)
    (hresult : .done false finalState (result, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel ((bindNativeSteps left next context fuel history cache).run ftsCache))) :
    invariant finalState finalCache := by
  rcases mem_support_bindNativeSteps_done table state finalState ftsFuel left next context fuel history cache
    ftsCache finalCache result hclean hfree hresult with ⟨_, hleftResult⟩ | ⟨stepState, entry, stepCache, hleftResult, hnextResult⟩
  · exact hleft finalState none finalCache hleftResult
  · exact hnext stepState entry stepCache hleftResult hnextResult

end SphincsSecurity.Concrete.FtsProbeSimulation
