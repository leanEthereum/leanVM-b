import XmssSecurity.CappedGlobalCausalRevealCoverageRun
import XmssSecurity.CappedGlobalCausalInstalledDetailedGame

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

set_option maxRecDepth 200000

theorem globalCausalLazyDetailedGameAfterKeygen_support_cache_le
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (state : GlobalCausalHashState)
    (result : ((((Forgery × Bool) × AttackerActionTrace) ×
      GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
    (hresult : result ∈ support
      (globalCausalLazyDetailedGameAfterKeygen adversary publicKey secretKey
        state)) :
    state.cache ≤ result.1.2.cache := by
  unfold globalCausalLazyDetailedGameAfterKeygen at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨handled, hhandled, hcontinuation⟩ := hresult
  rw [mem_support_bind_iff] at hcontinuation
  obtain ⟨verified, hverified, hpure⟩ := hcontinuation
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  exact (simulate_globalCausalLazyActionTracedImpl_support_cache_le
    publicKey secretKey (adversary.main publicKey) state handled hhandled).trans
      (simulate_globalCausalLazyVerifierImpl_support_cache_le
        publicKey secretKey
          (Concrete.scheme.verify publicKey handled.1.1.1.epoch
            handled.1.1.1.message handled.1.1.1.signature)
          handled.1.2 verified hverified)

theorem globalCausalLazyDetailedGameAfterKeygen_support_resultCovered_of_final
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (state : GlobalCausalHashState) (covered : Set GlobalChainValueIndex)
    (hcovered : GlobalCausalRevealsCovered covered state)
    (hforward : GlobalChainValueIndicesForwardClosed covered)
    (result : ((((Forgery × Bool) × AttackerActionTrace) ×
      GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
    (hdirect : ∀ request signature encoding chain,
      AttackerAction.sign request (some signature) ∈ result.1.1.2 →
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash result.1.2.cache secretKey.parameter
          request.epoch
          (request.message, signature.randomness)) = some encoding →
      (chain, request.epoch, encoding chain) ∈ covered)
    (hresult : result ∈ support
      (globalCausalLazyDetailedGameAfterKeygen adversary publicKey secretKey
        state)) :
    GlobalCausalResultCovered covered result := by
  unfold globalCausalLazyDetailedGameAfterKeygen at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨handled, hhandled, hcontinuation⟩ := hresult
  rw [mem_support_bind_iff] at hcontinuation
  obtain ⟨verified, hverified, hpure⟩ := hcontinuation
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  have hhandledCacheLe : handled.1.2.cache ≤ verified.1.2.cache :=
    simulate_globalCausalLazyVerifierImpl_support_cache_le
      publicKey secretKey
        (Concrete.scheme.verify publicKey handled.1.1.1.epoch
          handled.1.1.1.message handled.1.1.1.signature)
        handled.1.2 verified hverified
  have hhandledCovered :=
    simulate_globalCausalLazyActionTracedImpl_support_resultCovered_of_final
      publicKey secretKey (adversary.main publicKey) state covered
        verified.1.2.cache handled.1.1.2 hcovered hforward
        (fun request signature encoding chain haction hdecode =>
          hdirect request signature encoding chain haction hdecode)
        handled hhandled hhandledCacheLe (fun action haction => haction)
  have hverifiedCovered :=
    simulate_globalCausalLazyVerifierImpl_support_resultCovered
      publicKey secretKey
        (Concrete.scheme.verify publicKey handled.1.1.1.epoch
          handled.1.1.1.message handled.1.1.1.signature)
        handled.1.2 covered hhandledCovered.1 hforward verified hverified
  exact ⟨hverifiedCovered.1,
    hhandledCovered.2.append hverifiedCovered.2⟩

theorem globalCausalLazyDetailedGameAfterKeygen_support_returnedCovered
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (state : GlobalCausalHashState)
    (hinitial : ∀ index, state.revealed index = none)
    (result : ((((Forgery × Bool) × AttackerActionTrace) ×
      GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
    (hresult : result ∈ support
      (globalCausalLazyDetailedGameAfterKeygen adversary publicKey secretKey
        state)) :
    GlobalCausalResultCovered
      (GlobalReturnedChainValueCovered result.1.2.cache secretKey
        result.1.1.2.toSigningLog) result := by
  apply globalCausalLazyDetailedGameAfterKeygen_support_resultCovered_of_final
    adversary publicKey secretKey state
      (GlobalReturnedChainValueCovered result.1.2.cache secretKey
        result.1.1.2.toSigningLog)
  · intro index value hrevealed
    rw [hinitial index] at hrevealed
    cases hrevealed
  · exact globalReturnedChainValueCovered_forwardClosed
      result.1.2.cache secretKey result.1.1.2.toSigningLog
  · intro request signature encoding chain haction hdecode
    exact globalReturnedChainValueCovered_contains_returned
      result.1.2.cache secretKey result.1.1.2.toSigningLog request signature
        encoding
        (result.1.1.2.sign_mem_toSigningLog request signature haction)
        hdecode chain
  · exact hresult

end XmssSecurity.CappedChain
