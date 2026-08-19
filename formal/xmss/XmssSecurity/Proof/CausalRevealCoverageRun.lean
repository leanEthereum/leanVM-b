import XmssSecurity.Proof.CausalRevealCoverage
import XmssSecurity.Proof.CausalInstalledAdversaryRun
import XmssSecurity.Proof.CausalInstalledVerifierRun

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

set_option maxRecDepth 100000

theorem simulate_causalLazyActionTracedImpl_support_cache_le
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CausalHashState)
    (result : (((α × AttackerActionTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : result ∈ support
      ((((simulateQ
        (causalLazyActionTracedImpl publicKey secretKey chain)
          computation).run).run state).run)) :
    state.cache ≤ result.1.2.cache := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, WriterT.run_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact le_rfl
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, OracleQuery.input_query,
        WriterT.run_bind', StateT.run_bind] at hresult
      rw [mem_support_bind_iff] at hresult
      obtain ⟨handled, hhandled, hrest⟩ := hresult
      rw [support_map] at hrest
      obtain ⟨restWithActionTrace, hrestWithActionTrace, rfl⟩ := hrest
      rw [StateT.run_map, WriterT.run_map', support_map]
        at hrestWithActionTrace
      obtain ⟨rest, hrest, rfl⟩ := hrestWithActionTrace
      change handled ∈ support
        (causalLazyActionTracedStep publicKey secretKey chain input state)
        at hhandled
      exact (causalLazyActionTracedStep_support_cache_le
        publicKey secretKey chain input state handled hhandled).trans
          (ih handled.1.1.1 handled.1.2 rest hrest)

theorem simulate_causalLazyActionTracedImpl_support_resultCovered_of_final
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CausalHashState)
    (covered : Set ChainValueIndex) (finalCache : QueryCache HashSpec)
    (finalTrace : AttackerActionTrace)
    (hcovered : CausalRevealsCovered covered state)
    (hforward : ChainValueIndicesForwardClosed covered)
    (hdirect : ∀ request signature encoding,
      AttackerAction.sign request (some signature) ∈ finalTrace →
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash finalCache secretKey.parameter
          request.epoch
          (request.message, signature.randomness)) = some encoding →
      (request.epoch, encoding chain) ∈ covered)
    (result : (((α × AttackerActionTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : result ∈ support
      ((((simulateQ
        (causalLazyActionTracedImpl publicKey secretKey chain)
          computation).run).run state).run))
    (hcacheLe : result.1.2.cache ≤ finalCache)
    (htraceLe : ∀ action, action ∈ result.1.1.2 → action ∈ finalTrace) :
    CausalResultCovered covered result := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, WriterT.run_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨hcovered, by simp [CausalTraceRevealsCovered]⟩
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, OracleQuery.input_query,
        WriterT.run_bind', StateT.run_bind] at hresult
      rw [mem_support_bind_iff] at hresult
      obtain ⟨handled, hhandled, hrest⟩ := hresult
      rw [support_map] at hrest
      obtain ⟨restWithActionTrace, hrestWithActionTrace, rfl⟩ := hrest
      rw [StateT.run_map, WriterT.run_map', support_map]
        at hrestWithActionTrace
      obtain ⟨rest, hrest, rfl⟩ := hrestWithActionTrace
      have hhandledCacheLe : handled.1.2.cache ≤ finalCache := by
        exact (simulate_causalLazyActionTracedImpl_support_cache_le
          publicKey secretKey chain (next handled.1.1.1) handled.1.2 rest
            hrest).trans hcacheLe
      have hhandledTraceLe : ∀ action,
          action ∈ handled.1.1.2 → action ∈ finalTrace := by
        intro action haction
        apply htraceLe action
        exact List.mem_append_left rest.1.1.2 haction
      have hhandledCovered :=
        causalLazyActionTracedStep_support_resultCovered_of_final
          publicKey secretKey chain input state covered finalCache hcovered
            hforward handled hhandledCacheLe
            (fun request signature encoding haction hdecode =>
              hdirect request signature encoding
                (hhandledTraceLe _ haction) hdecode)
            hhandled
      have hrestTraceLe : ∀ action,
          action ∈ rest.1.1.2 → action ∈ finalTrace := by
        intro action haction
        apply htraceLe action
        exact List.mem_append_right handled.1.1.2 haction
      have hrestCovered := ih handled.1.1.1 handled.1.2
        hhandledCovered.1 rest hrest hcacheLe hrestTraceLe
      exact ⟨hrestCovered.1,
        hhandledCovered.2.append hrestCovered.2⟩

theorem simulate_causalLazyVerifierImpl_support_cache_le
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (computation : OracleComp OracleWorld α)
    (state : CausalHashState)
    (result : ((α × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : result ∈ support
      (((simulateQ (causalLazyVerifierImpl publicKey secretKey chain)
        computation).run state).run)) :
    state.cache ≤ result.1.2.cache := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure,
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact le_rfl
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, OracleQuery.input_query,
        StateT.run_bind, WriterT.run_bind'] at hresult
      rw [mem_support_bind_iff] at hresult
      obtain ⟨handled, hhandled, hrest⟩ := hresult
      rw [support_map] at hrest
      obtain ⟨rest, hrest, rfl⟩ := hrest
      change handled ∈ support
        (causalLazyVerifierStep publicKey secretKey chain input state)
        at hhandled
      exact (causalLazyMappedStep_support_cache_le
        publicKey secretKey chain (.inl input) state handled hhandled).trans
          (ih handled.1.1 handled.1.2 rest hrest)

theorem simulate_causalLazyVerifierImpl_support_resultCovered
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (computation : OracleComp OracleWorld α)
    (state : CausalHashState) (covered : Set ChainValueIndex)
    (hcovered : CausalRevealsCovered covered state)
    (hforward : ChainValueIndicesForwardClosed covered)
    (result : ((α × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : result ∈ support
      (((simulateQ (causalLazyVerifierImpl publicKey secretKey chain)
        computation).run state).run)) :
    CausalResultCovered covered result := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure,
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨hcovered, by simp [CausalTraceRevealsCovered]⟩
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, OracleQuery.input_query,
        StateT.run_bind, WriterT.run_bind'] at hresult
      rw [mem_support_bind_iff] at hresult
      obtain ⟨handled, hhandled, hrest⟩ := hresult
      rw [support_map] at hrest
      obtain ⟨rest, hrest, rfl⟩ := hrest
      change handled ∈ support
        (causalLazyVerifierStep publicKey secretKey chain input state)
        at hhandled
      have hhandledCovered := causalLazyMappedStep_support_resultCovered
        publicKey secretKey chain (.inl input) state covered hcovered hforward
          (fun request signature resultCache encoding heq => by cases heq)
          handled hhandled
      have hrestCovered := ih handled.1.1 handled.1.2 hhandledCovered.1
        rest hrest
      exact ⟨hrestCovered.1,
        hhandledCovered.2.append hrestCovered.2⟩

end XmssSecurity

set_option maxRecDepth 100000
