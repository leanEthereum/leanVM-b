import XmssSecurity.Proof.CausalStateInvariant
import XmssSecurity.Proof.CausalStrategyEagerSteps

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

theorem simulate_eagerImpl_causalHashQuery_support_revealsAgree
    (table : ChainValueIndex → Digest) (input : HashInput)
    (state : CausalHashState) (result : HashOutput × CausalHashState)
    (hagrees : CausalRevealsAgree table state)
  (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        ((causalHashQuery input).run state))) :
    CausalRevealsAgree table result.2 := by
  rw [causalHashQuery_run, simulateQ_map,
    RevealProbeOracleSimulation.simulate_eagerImpl_liftProbComp] at hresult
  simp only [support_map] at hresult
  obtain ⟨hashResult, _hhashResult, rfl⟩ := hresult
  exact hagrees.setCache hashResult.2

theorem simulate_eagerImpl_causalAttackerHashQuery_support_revealsAgree
    (table : ChainValueIndex → Digest) (secretKey : SecretKey)
    (chain : ChainIndex) (input : HashInput) (state : CausalHashState)
    (result : HashOutput × CausalHashState)
    (hagrees : CausalRevealsAgree table state)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        ((causalAttackerHashQuery secretKey chain input).run state))) :
    CausalRevealsAgree table result.2 := by
  rw [causalAttackerHashQuery_run] at hresult
  generalize hplan : causalAttackerHashPlan secretKey chain input state = plan at hresult
  cases plan with
  | cached output =>
      simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact hagrees.causalRecordedState secretKey chain input
  | redirect output =>
      simp only at hresult
      subst result
      exact (hagrees.causalRecordedState secretKey chain input).setCache _
  | fresh =>
      exact simulate_eagerImpl_causalHashQuery_support_revealsAgree table input
        (causalRecordedState secretKey chain input state) result
        (hagrees.causalRecordedState secretKey chain input) hresult
  | reveal index =>
      unfold causalRevealHashQuery at hresult
      rw [simulateQ_bind,
        RevealProbeOracleSimulation.simulate_eagerImpl_revealQuery,
        pure_bind, simulateQ_bind,
        RevealProbeOracleSimulation.simulate_eagerImpl_liftProbComp] at hresult
      rw [mem_support_bind_iff] at hresult
      obtain ⟨output, _houtput, hpure⟩ := hresult
      subst result
      exact hagrees.causalRevealResultState secretKey chain input index
        (table index) output rfl

theorem simulate_eagerImpl_revealFixedChainSignatureOption_support_revealsAgree
    (table : ChainValueIndex → Digest) (secretKey : SecretKey)
    (chain : ChainIndex) (request : SignRequest)
    (signatureOption : Option Signature) (state : CausalHashState)
    (result : Option Signature × CausalHashState)
    (hagrees : CausalRevealsAgree table state)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        ((revealFixedChainSignatureOption secretKey chain request
          signatureOption).run state))) :
    CausalRevealsAgree table result.2 := by
  cases signatureOption with
  | none =>
      change result ∈ support
        (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
          (pure (none, state))) at hresult
      simp only [simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact hagrees
  | some signature =>
      change result ∈ support
        (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
          (match TargetSum.decodeDigest
              (Concrete.CacheView.encodingHash state.cache secretKey.parameter
                request.epoch (request.message, signature.randomness)) with
          | none => pure (some signature, state)
          | some encoding =>
              let index := (request.epoch, encoding chain)
              do
                let value ← RevealProbeOracleSimulation.revealQuery index
                pure (some (replaceSignatureChainValue signature chain value),
                  state.recordReveal index value))) at hresult
      split at hresult
      · simp only [simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hresult
        subst result
        exact hagrees
      · rename_i encoding hdecode
        rw [simulateQ_bind,
          RevealProbeOracleSimulation.simulate_eagerImpl_revealQuery,
          pure_bind] at hresult
        simp only [simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hresult
        subst result
        exact hagrees.recordReveal (request.epoch, encoding chain)
          (table (request.epoch, encoding chain)) rfl

end XmssSecurity
