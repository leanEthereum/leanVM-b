import XmssSecurity.CappedGlobalCausalRevealCoverage
import XmssSecurity.CappedGlobalCausalInstalledVerifierRun

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

set_option maxRecDepth 200000

theorem globalCausalLazyVerifierStep_uniform
    (publicKey : PublicKey) (secretKey : SecretKey)
    (n : Nat) (state : GlobalCausalHashState) :
    globalCausalLazyVerifierStep publicKey secretKey (.inl n) state =
      (fun output => ((output, state),
        ([] : RevealProbeOracleSimulation.ActionTrace
          GlobalChainValueIndex))) <$>
        (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) := rfl

theorem simulate_globalCausalLazyActionTracedImpl_support_cache_le
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : GlobalCausalHashState)
    (result : (((α × AttackerActionTrace) × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
    (hresult : result ∈ support
      ((((simulateQ
        (globalCausalLazyActionTracedImpl publicKey secretKey)
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
        (globalCausalLazyActionTracedStep publicKey secretKey input state)
        at hhandled
      exact (globalCausalLazyActionTracedStep_support_cache_le
        publicKey secretKey input state handled hhandled).trans
          (ih handled.1.1.1 handled.1.2 rest hrest)

theorem simulate_globalCausalLazyActionTracedImpl_support_resultCovered_of_final
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : GlobalCausalHashState)
    (covered : Set GlobalChainValueIndex)
    (finalCache : QueryCache HashSpec) (finalTrace : AttackerActionTrace)
    (hcovered : GlobalCausalRevealsCovered covered state)
    (hforward : GlobalChainValueIndicesForwardClosed covered)
    (hdirect : ∀ request signature encoding chain,
      AttackerAction.sign request (some signature) ∈ finalTrace →
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash finalCache secretKey.parameter
          request.epoch
          (request.message, signature.randomness)) = some encoding →
      (chain, request.epoch, encoding chain) ∈ covered)
    (result : (((α × AttackerActionTrace) × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
    (hresult : result ∈ support
      ((((simulateQ
        (globalCausalLazyActionTracedImpl publicKey secretKey)
          computation).run).run state).run))
    (hcacheLe : result.1.2.cache ≤ finalCache)
    (htraceLe : ∀ action, action ∈ result.1.1.2 → action ∈ finalTrace) :
    GlobalCausalResultCovered covered result := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, WriterT.run_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨hcovered, by simp [GlobalCausalTraceRevealsCovered]⟩
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
        exact (simulate_globalCausalLazyActionTracedImpl_support_cache_le
          publicKey secretKey (next handled.1.1.1) handled.1.2 rest hrest).trans
            hcacheLe
      have hhandledTraceLe : ∀ action,
          action ∈ handled.1.1.2 → action ∈ finalTrace := by
        intro action haction
        apply htraceLe action
        exact List.mem_append_left rest.1.1.2 haction
      have hhandledCovered :=
        globalCausalLazyActionTracedStep_support_resultCovered_of_final
          publicKey secretKey input state covered finalCache hcovered hforward
            handled hhandledCacheLe
            (fun request signature encoding chain haction hdecode =>
              hdirect request signature encoding chain
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

theorem simulate_globalCausalLazyVerifierImpl_support_cache_le
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp OracleWorld α)
    (state : GlobalCausalHashState)
    (result : ((α × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
    (hresult : result ∈ support
      (((simulateQ (globalCausalLazyVerifierImpl publicKey secretKey)
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
        (globalCausalLazyVerifierStep publicKey secretKey input state)
        at hhandled
      exact (globalCausalLazyMappedStep_support_cache_le
        publicKey secretKey (.inl input) state handled hhandled).trans
          (ih handled.1.1 handled.1.2 rest hrest)

theorem simulate_globalCausalLazyVerifierImpl_support_resultCovered
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp OracleWorld α)
    (state : GlobalCausalHashState)
    (covered : Set GlobalChainValueIndex)
    (hcovered : GlobalCausalRevealsCovered covered state)
    (hforward : GlobalChainValueIndicesForwardClosed covered)
    (result : ((α × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
    (hresult : result ∈ support
      (((simulateQ (globalCausalLazyVerifierImpl publicKey secretKey)
        computation).run state).run)) :
    GlobalCausalResultCovered covered result := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure,
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨hcovered, by simp [GlobalCausalTraceRevealsCovered]⟩
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, OracleQuery.input_query,
        StateT.run_bind, WriterT.run_bind'] at hresult
      rw [mem_support_bind_iff] at hresult
      obtain ⟨handled, hhandled, hrest⟩ := hresult
      rw [support_map] at hrest
      obtain ⟨rest, hrest, rfl⟩ := hrest
      change handled ∈ support
        (globalCausalLazyVerifierStep publicKey secretKey input state)
        at hhandled
      have hhandledCovered :=
        globalCausalLazyMappedStep_support_resultCovered
          publicKey secretKey (.inl input) state covered hcovered hforward
            (by
              intro request signature resultCache encoding chain heq
              cases heq)
            handled hhandled
      have hrestCovered := ih handled.1.1 handled.1.2
        hhandledCovered.1 rest hrest
      exact ⟨hrestCovered.1,
        hhandledCovered.2.append hrestCovered.2⟩

end XmssSecurity.CappedChain
