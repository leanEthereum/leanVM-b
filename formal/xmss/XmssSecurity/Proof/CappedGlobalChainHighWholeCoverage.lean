import XmssSecurity.Proof.CappedGlobalChainHighSigningCoverage

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

def GlobalMonitoredCausalStateCovered
    (covered : Set GlobalChainValueIndex)
    (state : GlobalMonitoredCausalState) : Prop :=
  GlobalCausalRevealsCovered covered state.causal ∧
    GlobalCausalTraceRevealsCovered covered state.trace

theorem simulate_eagerTrace_globalCausalUniformImpl_support_state_trace
    (table : GlobalChainValueIndex → Digest) (n : Nat)
    (state : GlobalCausalHashState)
    (result : (Fin (n + 1) × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalUniformImpl n).run state)).run)) :
    result.1.2 = state ∧ result.2 = [] := by
  rw [simulate_eagerTrace_globalCausalUniformImpl, support_map] at hresult
  obtain ⟨output, _houtput, rfl⟩ := hresult
  exact ⟨rfl, rfl⟩

theorem monitorGlobalCausalTrace_support_covered
    (table : GlobalChainValueIndex → Digest)
    (computation : GlobalCausalHashState → ProbComp
      ((α × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
    (state : GlobalMonitoredCausalState)
    (covered : Set GlobalChainValueIndex)
    (hcovered : GlobalMonitoredCausalStateCovered covered state)
    (result : α × GlobalMonitoredCausalState)
    (hresult : result ∈ support
      ((monitorGlobalCausalTrace table computation).run state))
    (hstep : ∀ raw ∈ support (computation state.causal),
      GlobalCausalResultCovered covered raw) :
    GlobalMonitoredCausalStateCovered covered result.2 := by
  rw [monitorGlobalCausalTrace_run, support_map] at hresult
  obtain ⟨raw, hraw, rfl⟩ := hresult
  have hrawCovered := hstep raw hraw
  exact ⟨hrawCovered.1, hcovered.2.append hrawCovered.2⟩

theorem globalHighMonitoredBaseMappedAdversaryImpl_support_cache_le
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalMonitoredCausalState)
    (result : (OracleWorld + SigningSpec).Range input ×
      GlobalMonitoredCausalState)
    (hresult : result ∈ support
      ((globalHighMonitoredBaseMappedAdversaryImpl right input).run state)) :
    state.causal.cache ≤ result.2.causal.cache := by
  rcases input with (n | hashInput) | request
  · unfold globalHighMonitoredBaseMappedAdversaryImpl at hresult
    rw [monitorGlobalCausalTrace_run, support_map] at hresult
    obtain ⟨raw, hraw, rfl⟩ := hresult
    have hstate :=
      simulate_eagerTrace_globalCausalUniformImpl_support_state_trace
        right.1.2 n state.causal raw hraw
    simp [globalMonitoredCausalResult, hstate.1]
  · unfold globalHighMonitoredBaseMappedAdversaryImpl at hresult
    rw [monitorGlobalCausalTrace_run, support_map] at hresult
    obtain ⟨raw, hraw, rfl⟩ := hresult
    exact
      simulate_eagerTrace_globalCausalAttackerHashQueryFromHigh_support_cache_le
        right.1.2 (globalChainValueHighTableOfEdges right.2)
          right.1.1.secretKey hashInput state.causal raw hraw
  · unfold globalHighMonitoredBaseMappedAdversaryImpl at hresult
    rw [monitorGlobalCausalTrace_run, support_map] at hresult
    obtain ⟨raw, hraw, rfl⟩ := hresult
    exact
      (simulate_eagerTrace_globalFilteredCausalSigningQuery_stateExtends
        right.1.2 right.1.1 request state.causal raw hraw).1

set_option maxRecDepth 100000 in
theorem globalHighMonitoredBaseMappedAdversaryImpl_support_covered_of_final
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalMonitoredCausalState)
    (covered : Set GlobalChainValueIndex)
    (finalCache : QueryCache HashSpec)
    (hcovered : GlobalMonitoredCausalStateCovered covered state)
    (hforward : GlobalChainValueIndicesForwardClosed covered)
    (result : (OracleWorld + SigningSpec).Range input ×
      GlobalMonitoredCausalState)
    (hcacheLe : result.2.causal.cache ≤ finalCache)
    (hdirect : ∀ request signature encoding chain,
      AttackerAction.sign request (some signature) ∈
        attackerActionFragment input result.1 →
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash finalCache
          right.1.1.secretKey.parameter request.epoch
          (request.message, signature.randomness)) = some encoding →
      (chain, request.epoch, encoding chain) ∈ covered)
    (hresult : result ∈ support
      ((globalHighMonitoredBaseMappedAdversaryImpl right input).run state)) :
    GlobalMonitoredCausalStateCovered covered result.2 := by
  rcases input with (n | hashInput) | request
  · unfold globalHighMonitoredBaseMappedAdversaryImpl at hresult
    apply monitorGlobalCausalTrace_support_covered right.1.2 _ state covered
      hcovered result hresult
    intro raw hraw
    have hstate :=
      simulate_eagerTrace_globalCausalUniformImpl_support_state_trace
        right.1.2 n state.causal raw hraw
    constructor
    · simpa [hstate.1] using hcovered.1
    · simp [hstate.2, GlobalCausalTraceRevealsCovered]
  · unfold globalHighMonitoredBaseMappedAdversaryImpl at hresult
    apply monitorGlobalCausalTrace_support_covered right.1.2 _ state covered
      hcovered result hresult
    intro raw hraw
    exact
      simulate_eagerTrace_globalCausalAttackerHashQueryFromHigh_support_covered
        right.1.2 (globalChainValueHighTableOfEdges right.2)
          right.1.1.secretKey hashInput state.causal covered hcovered.1 hforward
            raw hraw
  · unfold globalHighMonitoredBaseMappedAdversaryImpl at hresult
    rw [monitorGlobalCausalTrace_run, support_map] at hresult
    obtain ⟨raw, hraw, rfl⟩ := hresult
    have hrawCovered :=
      simulate_eagerTrace_globalFilteredCausalSigningQuery_support_covered_of_final
        right.1.2 right.1.1 request state.causal covered finalCache raw
          hcovered.1 (by
            simpa [globalMonitoredCausalResult] using hcacheLe)
          (by
            intro returnedSignature encoding chain hreturned hdecode
            apply hdirect request returnedSignature encoding chain
            · simp [globalMonitoredCausalResult, attackerActionFragment,
                hreturned]
            · exact hdecode)
          hraw
    exact ⟨hrawCovered.1, hcovered.2.append hrawCovered.2⟩

theorem globalHighMonitoredMappedAdversaryImpl_support_cache_le
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalMonitoredTracedState)
    (result : (OracleWorld + SigningSpec).Range input ×
      GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((globalHighMonitoredMappedAdversaryImpl right input).run state)) :
    state.1.causal.cache ≤ result.2.1.causal.cache := by
  unfold globalHighMonitoredMappedAdversaryImpl actionTracedStateImpl at hresult
  change result ∈ support (do
    let baseResult ←
      (globalHighMonitoredBaseMappedAdversaryImpl right input).run state.1
    pure (baseResult.1,
      (baseResult.2, state.2 ++ attackerActionFragment input baseResult.1)))
      at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨baseResult, hbaseResult, hfinal⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  exact globalHighMonitoredBaseMappedAdversaryImpl_support_cache_le right
    input state.1 baseResult hbaseResult

set_option maxRecDepth 100000 in
theorem globalHighMonitoredMappedAdversaryImpl_support_covered_of_final
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalMonitoredTracedState)
    (covered : Set GlobalChainValueIndex)
    (finalCache : QueryCache HashSpec)
    (hcovered : GlobalMonitoredCausalStateCovered covered state.1)
    (hforward : GlobalChainValueIndicesForwardClosed covered)
    (result : (OracleWorld + SigningSpec).Range input ×
      GlobalMonitoredTracedState)
    (hcacheLe : result.2.1.causal.cache ≤ finalCache)
    (hdirect : ∀ request signature encoding chain,
      AttackerAction.sign request (some signature) ∈ result.2.2 →
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash finalCache
          right.1.1.secretKey.parameter request.epoch
          (request.message, signature.randomness)) = some encoding →
      (chain, request.epoch, encoding chain) ∈ covered)
    (hresult : result ∈ support
      ((globalHighMonitoredMappedAdversaryImpl right input).run state)) :
    GlobalMonitoredCausalStateCovered covered result.2.1 := by
  unfold globalHighMonitoredMappedAdversaryImpl actionTracedStateImpl at hresult
  change result ∈ support (do
    let baseResult ←
      (globalHighMonitoredBaseMappedAdversaryImpl right input).run state.1
    pure (baseResult.1,
      (baseResult.2, state.2 ++ attackerActionFragment input baseResult.1)))
      at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨baseResult, hbaseResult, hfinal⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  apply globalHighMonitoredBaseMappedAdversaryImpl_support_covered_of_final
    right input state.1 covered finalCache hcovered hforward baseResult hcacheLe
  · intro request signature encoding chain haction hdecode
    apply hdirect request signature encoding chain
    · exact List.mem_append_right state.2 haction
    · exact hdecode
  · exact hbaseResult

theorem globalHighMonitoredMappedAdversaryImpl_preserves_cache_extension
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (initialCache : QueryCache HashSpec) :
    QueryImpl.PreservesInv (globalHighMonitoredMappedAdversaryImpl right)
      (fun state : GlobalMonitoredTracedState =>
        initialCache ≤ state.1.causal.cache) := by
  intro input state hstate result hresult
  exact hstate.trans
    (globalHighMonitoredMappedAdversaryImpl_support_cache_le right input state
      result hresult)

theorem globalHighMonitoredMappedAdversaryImpl_preserves_trace_extension
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (initialTrace : AttackerActionTrace) :
    QueryImpl.PreservesInv (globalHighMonitoredMappedAdversaryImpl right)
      (fun state : GlobalMonitoredTracedState =>
        ∀ action ∈ initialTrace, action ∈ state.2) := by
  intro input state hstate result hresult
  unfold globalHighMonitoredMappedAdversaryImpl actionTracedStateImpl at hresult
  change result ∈ support (do
    let baseResult ←
      (globalHighMonitoredBaseMappedAdversaryImpl right input).run state.1
    pure (baseResult.1,
      (baseResult.2, state.2 ++ attackerActionFragment input baseResult.1)))
      at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨baseResult, _hbaseResult, hfinal⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  intro action haction
  exact List.mem_append_left _ (hstate action haction)

theorem simulate_globalHighMonitoredMappedAdversary_support_cache_le
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : GlobalMonitoredTracedState)
    (result : α × GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((simulateQ (globalHighMonitoredMappedAdversaryImpl right)
        computation).run state)) :
    state.1.causal.cache ≤ result.2.1.causal.cache := by
  exact OracleComp.simulateQ_run_preservesInv
    (globalHighMonitoredMappedAdversaryImpl right)
    (fun current : GlobalMonitoredTracedState =>
      state.1.causal.cache ≤ current.1.causal.cache)
    (globalHighMonitoredMappedAdversaryImpl_preserves_cache_extension right
      state.1.causal.cache) computation state le_rfl result hresult

theorem simulate_globalHighMonitoredMappedAdversary_support_trace_le
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : GlobalMonitoredTracedState)
    (result : α × GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((simulateQ (globalHighMonitoredMappedAdversaryImpl right)
        computation).run state)) :
    ∀ action ∈ state.2, action ∈ result.2.2 := by
  exact OracleComp.simulateQ_run_preservesInv
    (globalHighMonitoredMappedAdversaryImpl right)
    (fun current : GlobalMonitoredTracedState =>
      ∀ action ∈ state.2, action ∈ current.2)
    (globalHighMonitoredMappedAdversaryImpl_preserves_trace_extension right
      state.2) computation state (by simp) result hresult

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 1000000 in
theorem simulate_globalHighMonitoredMappedAdversary_support_covered_of_final
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : GlobalMonitoredTracedState)
    (covered : Set GlobalChainValueIndex)
    (finalCache : QueryCache HashSpec)
    (finalTrace : AttackerActionTrace)
    (hcovered : GlobalMonitoredCausalStateCovered covered state.1)
    (hforward : GlobalChainValueIndicesForwardClosed covered)
    (hdirect : ∀ request signature encoding chain,
      AttackerAction.sign request (some signature) ∈ finalTrace →
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash finalCache
          right.1.1.secretKey.parameter request.epoch
          (request.message, signature.randomness)) = some encoding →
      (chain, request.epoch, encoding chain) ∈ covered)
    (result : α × GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((simulateQ (globalHighMonitoredMappedAdversaryImpl right)
        computation).run state))
    (hcacheLe : result.2.1.causal.cache ≤ finalCache)
    (htraceLe : ∀ action, action ∈ result.2.2 → action ∈ finalTrace) :
    GlobalMonitoredCausalStateCovered covered result.2.1 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact hcovered
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, StateT.run_bind] at hresult
      rw [mem_support_bind_iff] at hresult
      obtain ⟨head, hhead, htail⟩ := hresult
      have hheadCacheLe : head.2.1.causal.cache ≤ finalCache :=
        (simulate_globalHighMonitoredMappedAdversary_support_cache_le right
          (next head.1) head.2 result htail).trans hcacheLe
      have hheadTraceLe : ∀ action, action ∈ head.2.2 →
          action ∈ finalTrace := by
        intro action haction
        apply htraceLe action
        exact simulate_globalHighMonitoredMappedAdversary_support_trace_le right
          (next head.1) head.2 result htail action haction
      have hheadCovered :=
        globalHighMonitoredMappedAdversaryImpl_support_covered_of_final right
          input state covered finalCache hcovered hforward head hheadCacheLe
            (fun request signature encoding chain haction hdecode =>
              hdirect request signature encoding chain
                (hheadTraceLe _ haction) hdecode)
            hhead
      exact ih head.1 head.2 hheadCovered result htail hcacheLe htraceLe

theorem globalHighMonitoredVerifierImpl_support_cache_le
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (input : OracleWorld.Domain) (state : GlobalMonitoredTracedState)
    (result : OracleWorld.Range input × GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((globalHighMonitoredVerifierImpl right input).run state)) :
    state.1.causal.cache ≤ result.2.1.causal.cache := by
  unfold globalHighMonitoredVerifierImpl at hresult
  simp only [StateT.run_mk] at hresult
  rw [support_map] at hresult
  obtain ⟨baseResult, hbaseResult, rfl⟩ := hresult
  exact globalHighMonitoredBaseMappedAdversaryImpl_support_cache_le right
    (.inl input) state.1 baseResult hbaseResult

theorem globalHighMonitoredVerifierImpl_support_covered
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (input : OracleWorld.Domain) (state : GlobalMonitoredTracedState)
    (covered : Set GlobalChainValueIndex)
    (hcovered : GlobalMonitoredCausalStateCovered covered state.1)
    (hforward : GlobalChainValueIndicesForwardClosed covered)
    (result : OracleWorld.Range input × GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((globalHighMonitoredVerifierImpl right input).run state)) :
    GlobalMonitoredCausalStateCovered covered result.2.1 := by
  unfold globalHighMonitoredVerifierImpl at hresult
  simp only [StateT.run_mk] at hresult
  rw [support_map] at hresult
  obtain ⟨baseResult, hbaseResult, rfl⟩ := hresult
  apply globalHighMonitoredBaseMappedAdversaryImpl_support_covered_of_final
    right (.inl input) state.1 covered baseResult.2.causal.cache hcovered
      hforward baseResult le_rfl
  · intro request signature encoding chain haction _hdecode
    rcases input with n | hashInput
    · simp [attackerActionFragment] at haction
    · simp [attackerActionFragment] at haction
  · exact hbaseResult

theorem globalHighMonitoredVerifierImpl_preserves_cache_extension
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (initialCache : QueryCache HashSpec) :
    QueryImpl.PreservesInv (globalHighMonitoredVerifierImpl right)
      (fun state : GlobalMonitoredTracedState =>
        initialCache ≤ state.1.causal.cache) := by
  intro input state hstate result hresult
  exact hstate.trans
    (globalHighMonitoredVerifierImpl_support_cache_le right input state result
      hresult)

theorem globalHighMonitoredVerifierImpl_preserves_covered
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (covered : Set GlobalChainValueIndex)
    (hforward : GlobalChainValueIndicesForwardClosed covered) :
    QueryImpl.PreservesInv (globalHighMonitoredVerifierImpl right)
      (fun state : GlobalMonitoredTracedState =>
        GlobalMonitoredCausalStateCovered covered state.1) := by
  intro input state hstate result hresult
  exact globalHighMonitoredVerifierImpl_support_covered right input state
    covered hstate hforward result hresult

theorem globalHighMonitoredVerifierImpl_preserves_attacker_trace
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (initialTrace : AttackerActionTrace) :
    QueryImpl.PreservesInv (globalHighMonitoredVerifierImpl right)
      (fun state : GlobalMonitoredTracedState => state.2 = initialTrace) := by
  intro input state hstate result hresult
  unfold globalHighMonitoredVerifierImpl at hresult
  simp only [StateT.run_mk] at hresult
  rw [support_map] at hresult
  obtain ⟨baseResult, _hbaseResult, rfl⟩ := hresult
  exact hstate

theorem simulate_globalHighMonitoredVerifier_support_cache_le
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (computation : OracleComp OracleWorld α)
    (state : GlobalMonitoredTracedState)
    (result : α × GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((simulateQ (globalHighMonitoredVerifierImpl right) computation).run
        state)) :
    state.1.causal.cache ≤ result.2.1.causal.cache := by
  exact OracleComp.simulateQ_run_preservesInv
    (globalHighMonitoredVerifierImpl right)
    (fun current : GlobalMonitoredTracedState =>
      state.1.causal.cache ≤ current.1.causal.cache)
    (globalHighMonitoredVerifierImpl_preserves_cache_extension right
      state.1.causal.cache) computation state le_rfl result hresult

theorem simulate_globalHighMonitoredVerifier_support_covered
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (computation : OracleComp OracleWorld α)
    (state : GlobalMonitoredTracedState)
    (covered : Set GlobalChainValueIndex)
    (hcovered : GlobalMonitoredCausalStateCovered covered state.1)
    (hforward : GlobalChainValueIndicesForwardClosed covered)
    (result : α × GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((simulateQ (globalHighMonitoredVerifierImpl right) computation).run
        state)) :
    GlobalMonitoredCausalStateCovered covered result.2.1 := by
  exact OracleComp.simulateQ_run_preservesInv
    (globalHighMonitoredVerifierImpl right)
    (fun current : GlobalMonitoredTracedState =>
      GlobalMonitoredCausalStateCovered covered current.1)
    (globalHighMonitoredVerifierImpl_preserves_covered right covered hforward)
      computation state hcovered result hresult

theorem simulate_globalHighMonitoredVerifier_support_attacker_trace_eq
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (computation : OracleComp OracleWorld α)
    (state : GlobalMonitoredTracedState)
    (result : α × GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((simulateQ (globalHighMonitoredVerifierImpl right) computation).run
        state)) :
    result.2.2 = state.2 := by
  exact OracleComp.simulateQ_run_preservesInv
    (globalHighMonitoredVerifierImpl right)
    (fun current : GlobalMonitoredTracedState => current.2 = state.2)
    (globalHighMonitoredVerifierImpl_preserves_attacker_trace right state.2)
      computation state rfl result hresult

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 2000000 in
theorem globalHighMonitoredDetailedExecution_support_returnedCovered
    (adversary : Adversary)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (result : (Forgery × Bool) × GlobalMonitoredTracedState)
    (hresult : result ∈ support
      (globalHighMonitoredDetailedExecution adversary right)) :
    GlobalMonitoredCausalStateCovered
      (GlobalReturnedChainValueCovered result.2.1.causal.cache
        right.1.1.secretKey result.2.2.toSigningLog) result.2.1 := by
  unfold globalHighMonitoredDetailedExecution at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨handled, hhandled, hresult⟩ := hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨verified, hvertified, hresult⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hresult
  subst result
  let covered := GlobalReturnedChainValueCovered
    verified.2.1.causal.cache right.1.1.secretKey
      verified.2.2.toSigningLog
  have hforward : GlobalChainValueIndicesForwardClosed covered :=
    globalReturnedChainValueCovered_forwardClosed verified.2.1.causal.cache
      right.1.1.secretKey verified.2.2.toSigningLog
  have hinitial : GlobalMonitoredCausalStateCovered covered
      ⟨globalFilteredCausalKeygenState right.1.1,
        some AdaptiveRevealMonitor.State.empty, []⟩ := by
    constructor
    · intro index value hrevealed
      simp [globalFilteredCausalKeygenState] at hrevealed
    · simp [GlobalCausalTraceRevealsCovered]
  have hhandledCacheLe : handled.2.1.causal.cache ≤
      verified.2.1.causal.cache :=
    simulate_globalHighMonitoredVerifier_support_cache_le right
      (Concrete.scheme.verify right.1.1.publicKey handled.1.epoch
        handled.1.message handled.1.signature) handled.2 verified hvertified
  have hhandledCovered : GlobalMonitoredCausalStateCovered covered
      handled.2.1 := by
    apply simulate_globalHighMonitoredMappedAdversary_support_covered_of_final
      right (adversary.main right.1.1.publicKey)
        (⟨globalFilteredCausalKeygenState right.1.1,
          some AdaptiveRevealMonitor.State.empty, []⟩, [])
        covered verified.2.1.causal.cache verified.2.2 hinitial hforward
    · intro request signature encoding chain haction hdecode
      exact globalReturnedChainValueCovered_contains_returned
        verified.2.1.causal.cache right.1.1.secretKey
          verified.2.2.toSigningLog request signature encoding
            (verified.2.2.sign_mem_toSigningLog request signature haction)
              hdecode chain
    · exact hhandled
    · exact hhandledCacheLe
    · intro action haction
      rw [simulate_globalHighMonitoredVerifier_support_attacker_trace_eq right
        (Concrete.scheme.verify right.1.1.publicKey handled.1.epoch
          handled.1.message handled.1.signature) handled.2 verified hvertified]
      exact haction
  exact simulate_globalHighMonitoredVerifier_support_covered right
    (Concrete.scheme.verify right.1.1.publicKey handled.1.epoch
      handled.1.message handled.1.signature) handled.2 covered hhandledCovered
        hforward verified hvertified

end XmssSecurity.CappedChain
