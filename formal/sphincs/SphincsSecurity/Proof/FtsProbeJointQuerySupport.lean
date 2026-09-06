import SphincsSecurity.Proof.FtsProbeJointContinuation

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem mem_support_bindNativeSteps_hashQuery_some
    (parameter : PublicParameter) (table : Coordinate → Digest) (input : HashInput)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (remaining : Nat)
    (next : HashOutput → NativeFtsStep α)
    (context : OtsProbeSimulation.DeferredContext) (fuel : Nat) (history : List OtsProbeSimulation.Probe)
    (cache : OtsProbeSimulation.SplitHashCache) (ftsCache finalCache : SplitHashCache)
    (result : OtsProbeSimulation.HistoryResolvedPrefix (α × OtsProbeSimulation.SplitHashCache))
    (hresult : .done false finalState (some result, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state (remaining + 1)
        ((bindNativeSteps (maskedJointHashQuery parameter input) next context fuel history cache).run ftsCache))) :
    ∃ stepState entry stepCache,
      .done false stepState (some entry, stepCache) ∈ support
        (AdaptiveRevealProbe.runDetailed table state (remaining + 1)
          ((maskedJointHashQuery parameter input context fuel history cache).run ftsCache)) ∧
      .done false finalState (some result, finalCache) ∈ support
        (AdaptiveRevealProbe.runDetailed table stepState (jointHashRemaining parameter input remaining)
          ((next entry.value.1 entry.context entry.remaining entry.history entry.value.2).run stepCache)) := by
  rw [bindNativeSteps, StateT.run_bind, runDetailed_maskedJointHashQuery_bind, mem_support_bind_iff] at hresult
  obtain ⟨detailed, hleft, hnext⟩ := hresult
  cases detailed with
  | stopped hit => simp at hnext
  | done hit stepState value =>
      rcases value with ⟨entry, stepCache⟩
      cases entry with
      | none => simp [StateT.run_pure, AdaptiveRevealProbe.runDetailed] at hnext
      | some entry =>
          have hhit := AdaptiveRevealProbe.tableHits_of_mem_runDetailed_done table state stepState (remaining + 1) _ hit _ hleft
          cases hit with
          | false => exact ⟨stepState, entry, stepCache, hleft, hnext⟩
          | true =>
              have hbad := runDetailed_hit_eq_true_of_tableHits_eq_true table stepState
                (jointHashRemaining parameter input remaining) _ hhit _ hnext
              cases hbad

end SphincsSecurity.Concrete.FtsProbeSimulation
