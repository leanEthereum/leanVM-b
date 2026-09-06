import SphincsSecurity.Proof.JointProbeOuterCost

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

theorem erasedHistoryPrefix_fields (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (entry : HistoryResolvedPrefix α)
    (hentry : some entry ∈ support (runResolvedHistoryPrefix (eraseProbeQueries computation) context 0 [])) :
    entry.remaining = 0 ∧ entry.history = [] := by
  induction computation using OracleComp.inductionOn generalizing context with
  | pure value =>
      simp only [eraseProbeQueries, construct_pure, runResolvedHistoryPrefix, mem_support_pure_iff, Option.some.injEq] at hentry
      cases hentry
      exact ⟨rfl, rfl⟩
  | query_bind input next ih =>
      rw [eraseProbeQueries_query_bind, runResolvedHistoryPrefix_bind, mem_support_bind_iff] at hentry
      obtain ⟨result, hresult, htail⟩ := hentry
      cases result with
      | none => simp at htail
      | some result =>
          have hf := erasedHistoryQueryStep_fields input context result hresult
          dsimp only at htail
          rw [hf.1, hf.2] at htail
          exact ih result.value result.context htail

end SphincsSecurity.Concrete.OtsProbeSimulation

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
open OtsProbeSimulation (HistoryResolvedPrefix)
set_option backward.isDefEq.respectTransparency false

theorem runJointErasedHistory_raw_fields (table : Coordinate → Digest) (computation : OracleComp JointProbeWorld α)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel remaining : Nat)
    (context : OtsProbeSimulation.DeferredContext) (entry : HistoryResolvedPrefix α)
    (hresult : .done finalState remaining (some entry) ∈ support
      (AdaptiveRevealProbe.runRaw table state ftsFuel (runJointErasedHistory computation context 0 []))) :
    entry.remaining = 0 ∧ entry.history = [] := by
  have hmap : some (⟨entry.context, entry.remaining, (finalState, remaining, entry.value), entry.history⟩ :
      HistoryResolvedPrefix (AdaptiveRevealProbe.State Coordinate × Nat × α)) ∈ support
      (rawJointHistory <$> AdaptiveRevealProbe.runRaw table state ftsFuel (runJointErasedHistory computation context 0 [])) := by
    rw [support_map]
    exact ⟨_, hresult, rfl⟩
  rw [runJointFtsRaw_erasedHistory_commute, support_map] at hmap
  obtain ⟨native, hnative, heq⟩ := hmap
  cases native with
  | none => simp [flattenRawHistory] at heq
  | some native =>
      have hf := OtsProbeSimulation.erasedHistoryPrefix_fields _ context native hnative
      cases hvalue : native.value with
      | stopped hit => simp [flattenRawHistory, hvalue] at heq
      | done returnedState returnedFuel value =>
          simp only [flattenRawHistory, hvalue, Option.some.injEq] at heq
          have hremaining := congrArg HistoryResolvedPrefix.remaining heq
          have hhistory := congrArg HistoryResolvedPrefix.history heq
          exact ⟨hremaining.symm.trans hf.1, hhistory.symm.trans hf.2⟩

theorem JointSourceImplements.raw_fields {source : JointSource α} {step : NativeFtsStep α}
    (hsource : JointSourceImplements source step) (table : Coordinate → Digest)
    (state finalState : AdaptiveRevealProbe.State Coordinate) (ftsFuel remaining : Nat)
    (context : OtsProbeSimulation.DeferredContext) (cache : JointSourceCache) (finalCache : SplitHashCache)
    (entry : HistoryResolvedPrefix (α × OtsProbeSimulation.SplitHashCache))
    (hresult : .done finalState remaining (some entry, finalCache) ∈ support
      (AdaptiveRevealProbe.runRaw table state ftsFuel ((step context 0 [] cache.1).run cache.2))) :
    entry.remaining = 0 ∧ entry.history = [] := by
  apply runJointErasedHistory_raw_fields table (source.run cache) state finalState ftsFuel remaining context
    (⟨entry.context, entry.remaining, (entry.value.1, entry.value.2, finalCache), entry.history⟩ : HistoryResolvedPrefix (α × JointSourceCache))
  rw [hsource, AdaptiveRevealProbe.runRaw_mapValue, support_map]
  exact ⟨_, hresult, rfl⟩

theorem jointOuterQuery_erased_fields (parameter : PublicParameter) (root : Digest) (table : Coordinate → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (state finalState : AdaptiveRevealProbe.State Coordinate)
    (ftsFuel : Nat) (hpositive : OtsProbeSimulation.IsOuterHash input → 0 < ftsFuel)
    (context : OtsProbeSimulation.DeferredContext) (cache : JointSourceCache) (finalCache : SplitHashCache)
    (entry : HistoryResolvedPrefix ((OracleWorld + SigningSpec).Range input × OtsProbeSimulation.SplitHashCache)) (hit : Bool)
    (hresult : .done hit finalState (some entry, finalCache) ∈ support
      (AdaptiveRevealProbe.runDetailed table state ftsFuel ((jointOuterQuery parameter root input context 0 [] cache.1).run cache.2))) :
    entry.remaining = 0 ∧ entry.history = [] := by
  apply (jointSourceOuterQuery_implements parameter root input).raw_fields table state finalState ftsFuel
    (jointOuterRemaining parameter input ftsFuel) context cache finalCache entry
  rw [runRaw_jointOuterQuery_eq_detailed parameter root table input state ftsFuel hpositive, support_map]
  exact ⟨_, hresult, rfl⟩

end SphincsSecurity.Concrete.FtsProbeSimulation
