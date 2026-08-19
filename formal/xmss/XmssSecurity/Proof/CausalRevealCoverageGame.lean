import XmssSecurity.Proof.CausalRevealCoverageRun
import XmssSecurity.Proof.CausalInstalledDetailedGame

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

set_option maxRecDepth 100000

theorem causalLazyDetailedGameAfterKeygen_support_cache_le
    (adversary : Adversary Concrete.singleAttemptScheme)
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (state : CausalHashState)
    (result : ((((Forgery × Bool) × AttackerActionTrace) ×
      CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : result ∈ support
      (causalLazyDetailedGameAfterKeygen adversary publicKey secretKey chain
        state)) :
    state.cache ≤ result.1.2.cache := by
  unfold causalLazyDetailedGameAfterKeygen at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨handled, hhandled, hcontinuation⟩ := hresult
  rw [mem_support_bind_iff] at hcontinuation
  obtain ⟨verified, hverified, hpure⟩ := hcontinuation
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  exact (simulate_causalLazyActionTracedImpl_support_cache_le
    publicKey secretKey chain (adversary.main publicKey) state handled
      hhandled).trans
    (simulate_causalLazyVerifierImpl_support_cache_le
      publicKey secretKey chain
        (Concrete.singleAttemptScheme.verify publicKey handled.1.1.1.epoch
          handled.1.1.1.message handled.1.1.1.signature)
        handled.1.2 verified hverified)

theorem causalLazyDetailedGameAfterKeygen_support_resultCovered_of_final
    (adversary : Adversary Concrete.singleAttemptScheme)
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (state : CausalHashState) (covered : Set ChainValueIndex)
    (hcovered : CausalRevealsCovered covered state)
    (hforward : ChainValueIndicesForwardClosed covered)
    (result : ((((Forgery × Bool) × AttackerActionTrace) ×
      CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hdirect : ∀ request signature encoding,
      AttackerAction.sign request (some signature) ∈ result.1.1.2 →
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash result.1.2.cache secretKey.parameter
          request.epoch
          (request.message, signature.randomness)) = some encoding →
      (request.epoch, encoding chain) ∈ covered)
    (hresult : result ∈ support
      (causalLazyDetailedGameAfterKeygen adversary publicKey secretKey chain
        state)) :
    CausalResultCovered covered result := by
  unfold causalLazyDetailedGameAfterKeygen at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨handled, hhandled, hcontinuation⟩ := hresult
  rw [mem_support_bind_iff] at hcontinuation
  obtain ⟨verified, hverified, hpure⟩ := hcontinuation
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  have hhandledCacheLe : handled.1.2.cache ≤ verified.1.2.cache :=
    simulate_causalLazyVerifierImpl_support_cache_le
      publicKey secretKey chain
        (Concrete.singleAttemptScheme.verify publicKey handled.1.1.1.epoch
          handled.1.1.1.message handled.1.1.1.signature)
        handled.1.2 verified hverified
  have hhandledCovered :=
    simulate_causalLazyActionTracedImpl_support_resultCovered_of_final
      publicKey secretKey chain (adversary.main publicKey) state covered
        verified.1.2.cache handled.1.1.2 hcovered hforward
        (fun request signature encoding haction hdecode =>
          hdirect request signature encoding haction hdecode)
        handled hhandled hhandledCacheLe
        (fun action haction => haction)
  have hverifiedCovered :=
    simulate_causalLazyVerifierImpl_support_resultCovered
      publicKey secretKey chain
        (Concrete.singleAttemptScheme.verify publicKey handled.1.1.1.epoch
          handled.1.1.1.message handled.1.1.1.signature)
        handled.1.2 covered hhandledCovered.1 hforward verified hverified
  exact ⟨hverifiedCovered.1,
    hhandledCovered.2.append hverifiedCovered.2⟩

theorem causalLazyDetailedGameAfterKeygen_support_returnedCovered
    (adversary : Adversary Concrete.singleAttemptScheme)
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (state : CausalHashState)
    (hinitial : ∀ index, state.revealed index = none)
    (result : ((((Forgery × Bool) × AttackerActionTrace) ×
      CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : result ∈ support
      (causalLazyDetailedGameAfterKeygen adversary publicKey secretKey chain
        state)) :
    CausalResultCovered
      (ReturnedChainValueCovered result.1.2.cache secretKey
        result.1.1.2.toSigningLog chain) result := by
  apply causalLazyDetailedGameAfterKeygen_support_resultCovered_of_final
    adversary publicKey secretKey chain state
      (ReturnedChainValueCovered result.1.2.cache secretKey
        result.1.1.2.toSigningLog chain)
  · intro index value hrevealed
    rw [hinitial index] at hrevealed
    cases hrevealed
  · exact returnedChainValueCovered_forwardClosed
      result.1.2.cache secretKey result.1.1.2.toSigningLog chain
  · intro request signature encoding haction hdecode
    exact returnedChainValueCovered_contains_returned
      result.1.2.cache secretKey result.1.1.2.toSigningLog chain request
        signature encoding
        (result.1.1.2.sign_mem_toSigningLog request signature haction)
        hdecode
  · exact hresult

end XmssSecurity

set_option maxRecDepth 100000
