import XmssSecurity.CausalSigningProjection
import XmssSecurity.CausalCacheInvariant
import XmssSecurity.CausalStrategyEagerSteps

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

noncomputable local instance causalSigningSampleableChainTable :
    SampleableType (ChainValueIndex → Digest) :=
  SampleableType.ofFintype (ChainValueIndex → Digest)

theorem simulate_eagerTrace_causalSigningQueryAfterRealRom
    (table : ChainValueIndex → Digest)
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (request : SignRequest) (state : CausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (causalSigningQueryAfterRealRom publicKey secretKey chain request state)).run =
    ((simulateQ xmssRomImpl
      (Concrete.scheme.sign publicKey secretKey request.epoch request.message)).run
        state.cache >>= fun signed =>
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((revealFixedChainSignatureOption secretKey chain request signed.1).run
          { state with cache := signed.2 })).run) := by
  unfold causalSigningQueryAfterRealRom
  rw [simulateQ_bind, WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply, List.nil_append]
  rw [show (Prod.map id
    (fun trace : RevealProbeOracleSimulation.ActionTrace ChainValueIndex => trace)) = id
      from rfl, Function.comp_id]
  simp

theorem simulate_eagerImpl_revealFixedChainSignatureOption_support_cacheExtendsKeygen
    (table : ChainValueIndex → Digest) (secretKey : SecretKey)
    (chain : ChainIndex) (request : SignRequest)
    (signatureOption : Option Signature) (state : CausalHashState)
    (result : Option Signature × CausalHashState)
    (hextends : CausalCacheExtendsKeygen state)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        ((revealFixedChainSignatureOption secretKey chain request
          signatureOption).run state))) :
    CausalCacheExtendsKeygen result.2 := by
  cases signatureOption with
  | none =>
      change result ∈ support
        (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
          (pure (none, state))) at hresult
      simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact hextends
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
        exact hextends
      · rename_i encoding hdecode
        rw [simulateQ_bind,
          RevealProbeOracleSimulation.simulate_eagerImpl_revealQuery,
          pure_bind] at hresult
        simp only [simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hresult
        subst result
        exact hextends.recordReveal _ _

theorem simulate_eagerImpl_causalSigningQueryAfterRealRom_support_cacheExtendsKeygen
    (table : ChainValueIndex → Digest)
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (request : SignRequest) (state : CausalHashState)
    (result : Option Signature × CausalHashState)
    (hextends : CausalCacheExtendsKeygen state)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        (causalSigningQueryAfterRealRom
          publicKey secretKey chain request state))) :
    CausalCacheExtendsKeygen result.2 := by
  unfold causalSigningQueryAfterRealRom at hresult
  rw [simulateQ_bind,
    RevealProbeOracleSimulation.simulate_eagerImpl_liftProbComp,
    mem_support_bind_iff] at hresult
  obtain ⟨signed, hsigned, hrest⟩ := hresult
  apply simulate_eagerImpl_revealFixedChainSignatureOption_support_cacheExtendsKeygen
    table secretKey chain request signed.1 { state with cache := signed.2 }
      result
  · apply hextends.setCache
    exact xmssRom_cache_le
      (Concrete.scheme.sign publicKey secretKey request.epoch request.message)
        state.cache signed hsigned
  · exact hrest

theorem causalSigningResult_chainValue_eq_keygenChainValueTable
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.keygen).run ∅))
    (state : CausalHashState) (hkeyCache : keyResult.2 ≤ state.cache)
    (request : SignRequest) (signature : Signature)
    (resultCache : QueryCache HashSpec)
    (hsigned : (some signature, resultCache) ∈ support
      ((simulateQ xmssRomImpl
        (Concrete.scheme.sign keyResult.1.1 keyResult.1.2
          request.epoch request.message)).run state.cache))
    (chain : ChainIndex) :
    ∃ encoding,
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash resultCache keyResult.1.2.parameter
          request.epoch (request.message, signature.randomness)) = some encoding ∧
      signature.chainValue chain =
        keygenChainValueTable keyResult.2 keyResult.1.2 chain
          (request.epoch, encoding chain) := by
  have hresultCache : state.cache ≤ resultCache :=
    xmssRom_cache_le
      (Concrete.scheme.sign keyResult.1.1 keyResult.1.2
        request.epoch request.message)
      state.cache (some signature, resultCache) hsigned
  obtain ⟨encoding, hdecode, hsignature⟩ := concrete_sign_support_replay
    keyResult.1.1 keyResult.1.2 request state.cache resultCache resultCache
      signature hsigned le_rfl
  refine ⟨encoding, hdecode, ?_⟩
  rw [hsignature]
  exact Concrete.CacheReplay.signWithEncoding_chainValue_eq_keygenChainValueTable
    keyResult hkeygen resultCache (hkeyCache.trans hresultCache)
      request.epoch signature.randomness encoding chain

theorem simulate_eagerTrace_revealSigningResult_with_keygenTable
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.keygen).run ∅))
    (state : CausalHashState) (hkeyCache : keyResult.2 ≤ state.cache)
    (request : SignRequest) (signature : Signature)
    (resultCache : QueryCache HashSpec)
    (hsigned : (some signature, resultCache) ∈ support
      ((simulateQ xmssRomImpl
        (Concrete.scheme.sign keyResult.1.1 keyResult.1.2
          request.epoch request.message)).run state.cache))
    (chain : ChainIndex) :
    ∃ encoding,
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash resultCache keyResult.1.2.parameter
          request.epoch (request.message, signature.randomness)) = some encoding ∧
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl
          (keygenChainValueTable keyResult.2 keyResult.1.2 chain))
        ((revealFixedChainSignatureOption keyResult.1.2 chain request
          (some signature)).run { state with cache := resultCache })).run =
        pure (((some signature,
          ({ state with cache := resultCache }).recordReveal
            (request.epoch, encoding chain) (signature.chainValue chain))),
          [RevealProbeOracleSimulation.ObservedAction.reveal
            (request.epoch, encoding chain) (signature.chainValue chain)]) := by
  obtain ⟨encoding, hdecode, hvalue⟩ :=
    causalSigningResult_chainValue_eq_keygenChainValueTable
      keyResult hkeygen state hkeyCache request signature resultCache hsigned chain
  refine ⟨encoding, hdecode, ?_⟩
  apply simulate_eagerTrace_revealFixedChainSignatureOption_some_of_agrees
    (keygenChainValueTable keyResult.2 keyResult.1.2 chain)
      keyResult.1.2 chain request signature { state with cache := resultCache }
      encoding hdecode
  exact hvalue.symm

noncomputable def causalResampledSigningContinuation
    (secretKey : SecretKey) (chain : ChainIndex) (request : SignRequest)
    (state : CausalHashState)
    (signed : Option Signature × QueryCache HashSpec)
    (continuation : (ChainValueIndex → Digest) →
      ((Option Signature × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    ProbComp α :=
  let signedState := { state with cache := signed.2 }
  match signed.1 with
  | none => do
      let table ← $ᵗ (ChainValueIndex → Digest)
      continuation table ((none, signedState), [])
  | some signature =>
      match TargetSum.decodeDigest
          (Concrete.CacheView.encodingHash signedState.cache secretKey.parameter
            request.epoch (request.message, signature.randomness)) with
      | none => do
          let table ← $ᵗ (ChainValueIndex → Digest)
          continuation table ((some signature, signedState), [])
      | some encoding => do
          let value ← $ᵗ Digest
          let base ← $ᵗ (ChainValueIndex → Digest)
          let index := (request.epoch, encoding chain)
          let table := Function.update base index value
          continuation table ((some
            (replaceSignatureChainValue signature chain value),
              signedState.recordReveal index value),
            [RevealProbeOracleSimulation.ObservedAction.reveal index value])

theorem evalDist_uniformTable_simulate_eagerTrace_causalSigningQueryAfterRealRom_continuation
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (request : SignRequest) (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      ((Option Signature × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    𝒟[do
      let table ← $ᵗ (ChainValueIndex → Digest)
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        (causalSigningQueryAfterRealRom publicKey secretKey chain request state)).run
      continuation table result] =
    𝒟[(simulateQ xmssRomImpl
      (Concrete.scheme.sign publicKey secretKey request.epoch request.message)).run
        state.cache >>= fun signed =>
      causalResampledSigningContinuation secretKey chain request state signed
        continuation] := by
  calc
    𝒟[do
      let table ← $ᵗ (ChainValueIndex → Digest)
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        (causalSigningQueryAfterRealRom publicKey secretKey chain request state)).run
      continuation table result] =
        𝒟[do
          let table ← $ᵗ (ChainValueIndex → Digest)
          let signed ← (simulateQ xmssRomImpl
            (Concrete.scheme.sign publicKey secretKey request.epoch request.message)).run
              state.cache
          let result ← (simulateQ
            (RevealProbeOracleSimulation.eagerTraceImpl table)
            ((revealFixedChainSignatureOption secretKey chain request signed.1).run
              { state with cache := signed.2 })).run
          continuation table result] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro table
      rw [simulate_eagerTrace_causalSigningQueryAfterRealRom]
      simp only [bind_assoc]
    _ = 𝒟[(simulateQ xmssRomImpl
          (Concrete.scheme.sign publicKey secretKey request.epoch request.message)).run
            state.cache >>= fun signed => do
          let table ← $ᵗ (ChainValueIndex → Digest)
          let result ← (simulateQ
            (RevealProbeOracleSimulation.eagerTraceImpl table)
            ((revealFixedChainSignatureOption secretKey chain request signed.1).run
              { state with cache := signed.2 })).run
          continuation table result] :=
      OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    _ = _ := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro signed
      rcases signed with ⟨signatureOption, cache⟩
      cases signatureOption with
      | none =>
          simp [causalResampledSigningContinuation,
            revealFixedChainSignatureOption_run,
            RevealProbeOracleSimulation.eagerTraceImpl]
      | some signature =>
          cases hdecode : TargetSum.decodeDigest
              (Concrete.CacheView.encodingHash cache secretKey.parameter
                request.epoch (request.message, signature.randomness)) with
          | none =>
              simp [causalResampledSigningContinuation,
                revealFixedChainSignatureOption_run, hdecode,
                RevealProbeOracleSimulation.eagerTraceImpl]
          | some encoding =>
              simpa [causalResampledSigningContinuation, hdecode] using
                (evalDist_uniformTable_simulate_eagerTrace_revealFixedChainSignatureOption_some_of_decode
                  secretKey chain request signature { state with cache := cache }
                  encoding hdecode continuation)

noncomputable def causalEagerSigningStep
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (request : SignRequest) (state : CausalHashState) :
    ProbComp ((ChainValueIndex → Digest) ×
      ((Option Signature × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) := do
  let table ← $ᵗ (ChainValueIndex → Digest)
  let result ← (simulateQ
    (RevealProbeOracleSimulation.eagerTraceImpl table)
    (causalSigningQueryAfterRealRom
      publicKey secretKey chain request state)).run
  pure (table, result)

noncomputable def causalResampledSigningStep
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (request : SignRequest) (state : CausalHashState) :
    ProbComp ((ChainValueIndex → Digest) ×
      ((Option Signature × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) :=
  (simulateQ xmssRomImpl
    (Concrete.scheme.sign publicKey secretKey request.epoch request.message)).run
      state.cache >>= fun signed =>
    causalResampledSigningContinuation secretKey chain request state signed
      (fun table result => pure (table, result))

theorem evalDist_causalEagerSigningStep_eq_resampled
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (request : SignRequest) (state : CausalHashState) :
    𝒟[causalEagerSigningStep
      publicKey secretKey chain request state] =
    𝒟[causalResampledSigningStep
      publicKey secretKey chain request state] := by
  unfold causalEagerSigningStep causalResampledSigningStep
  exact
    evalDist_uniformTable_simulate_eagerTrace_causalSigningQueryAfterRealRom_continuation
      publicKey secretKey chain request state
      (fun table result => pure (table, result))

theorem evalDist_causalEagerSigningStep_continuation_eq_resampled
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (request : SignRequest) (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      ((Option Signature × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    𝒟[causalEagerSigningStep publicKey secretKey chain request state >>=
      fun result => continuation result.1 result.2] =
    𝒟[causalResampledSigningStep publicKey secretKey chain request state >>=
      fun result => continuation result.1 result.2] := by
  rw [evalDist_bind, evalDist_causalEagerSigningStep_eq_resampled,
    ← evalDist_bind]

end XmssSecurity
