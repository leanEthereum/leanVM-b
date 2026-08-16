import XmssSecurity.CappedChain.CausalInstalledTable
import XmssSecurity.CappedChain.CausalSigningProjection
import XmssSecurity.CappedChain.CausalStateInvariant

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

theorem simulate_eagerImpl_causalHashQuery_support_revealsLe
    (table : ChainValueIndex → Digest) (input : HashInput)
    (state : CausalHashState) (result : HashOutput × CausalHashState)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        ((causalHashQuery input).run state))) :
    CausalRevealsLe state result.2 := by
  rw [causalHashQuery_run, simulateQ_map,
    RevealProbeOracleSimulation.simulate_eagerImpl_liftProbComp,
    support_map] at hresult
  obtain ⟨hashResult, _hhashResult, rfl⟩ := hresult
  exact CausalRevealsLe.setCache state hashResult.2

theorem simulate_eagerImpl_causalAttackerHashQuery_support_revealsLe
    (table : ChainValueIndex → Digest) (secretKey : SecretKey)
    (chain : ChainIndex) (input : HashInput) (state : CausalHashState)
    (result : HashOutput × CausalHashState)
    (hagrees : CausalRevealsAgree table state)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        ((causalAttackerHashQuery secretKey chain input).run state))) :
    CausalRevealsLe state result.2 := by
  generalize hplan : causalAttackerHashPlan secretKey chain input state = plan
  cases plan with
  | cached output =>
      rw [causalAttackerHashQuery_run, hplan] at hresult
      simp only [simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact CausalRevealsLe.causalRecordedState secretKey chain input state
  | redirect output =>
      rw [causalAttackerHashQuery_run, hplan] at hresult
      simp only [simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact (CausalRevealsLe.causalRecordedState
        secretKey chain input state).trans (CausalRevealsLe.setCache _ _)
  | fresh =>
      rw [causalAttackerHashQuery_run, hplan] at hresult
      exact (CausalRevealsLe.causalRecordedState
        secretKey chain input state).trans
          (simulate_eagerImpl_causalHashQuery_support_revealsLe
            table input (causalRecordedState secretKey chain input state)
              result hresult)
  | reveal index =>
      rw [causalAttackerHashQuery_run, hplan] at hresult
      unfold causalRevealHashQuery at hresult
      rw [simulateQ_bind,
        RevealProbeOracleSimulation.simulate_eagerImpl_revealQuery,
        pure_bind, simulateQ_bind,
        RevealProbeOracleSimulation.simulate_eagerImpl_liftProbComp,
        mem_support_bind_iff] at hresult
      obtain ⟨output, _houtput, hpure⟩ := hresult
      subst result
      apply CausalRevealsLe.causalRevealResultState
      intro previous hprevious
      exact (hagrees index previous hprevious).symm

theorem simulate_eagerImpl_revealFixedChainSignatureOption_support_revealsLe
    (table : ChainValueIndex → Digest) (secretKey : SecretKey)
    (chain : ChainIndex) (request : SignRequest)
    (signatureOption : Option Signature) (state : CausalHashState)
    (result : Option Signature × CausalHashState)
    (hagrees : CausalRevealsAgree table state)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        ((revealFixedChainSignatureOption secretKey chain request
          signatureOption).run state))) :
    CausalRevealsLe state result.2 := by
  cases signatureOption with
  | none =>
      change result ∈ support
        (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
          (pure (none, state))) at hresult
      simp only [simulateQ_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact CausalRevealsLe.refl state
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
        exact CausalRevealsLe.refl state
      · rename_i encoding hdecode
        rw [simulateQ_bind,
          RevealProbeOracleSimulation.simulate_eagerImpl_revealQuery,
          pure_bind] at hresult
        simp only [simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hresult
        subst result
        apply CausalRevealsLe.recordReveal
        intro previous hprevious
        exact (hagrees (request.epoch, encoding chain) previous hprevious).symm

theorem simulate_eagerImpl_causalSigningQueryAfterRealRom_support_revealsLe
    (table : ChainValueIndex → Digest)
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (request : SignRequest) (state : CausalHashState)
    (result : Option Signature × CausalHashState)
    (hagrees : CausalRevealsAgree table state)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        (causalSigningQueryAfterRealRom
          publicKey secretKey chain request state))) :
    CausalRevealsLe state result.2 := by
  unfold causalSigningQueryAfterRealRom at hresult
  rw [simulateQ_bind,
    RevealProbeOracleSimulation.simulate_eagerImpl_liftProbComp,
    mem_support_bind_iff] at hresult
  obtain ⟨signed, _hsigned, hrest⟩ := hresult
  exact (CausalRevealsLe.setCache state signed.2).trans
    (simulate_eagerImpl_revealFixedChainSignatureOption_support_revealsLe
      table secretKey chain request signed.1 { state with cache := signed.2 }
        result (hagrees.setCache signed.2) hrest)

end XmssSecurity.CappedChain
