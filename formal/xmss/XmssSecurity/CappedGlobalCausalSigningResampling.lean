import XmssSecurity.CappedGlobalCausalSigningProjection
import XmssSecurity.CappedGlobalCausalStrategyEagerSteps

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

noncomputable local instance globalCausalSigningSampleableChainTable :
    SampleableType (GlobalChainValueIndex → Digest) :=
  SampleableType.ofFintype (GlobalChainValueIndex → Digest)

noncomputable def sampleGlobalSignatureTable
    (request : SignRequest) (encoding : ChainIndex → Digit) :
    List ChainIndex → ProbComp (GlobalChainValueIndex → Digest)
  | [] => $ᵗ (GlobalChainValueIndex → Digest)
  | chain :: chains => do
      let value ← $ᵗ Digest
      let base ← sampleGlobalSignatureTable request encoding chains
      pure (Function.update base
        (chain, request.epoch, encoding chain) value)

set_option maxRecDepth 10000 in
theorem evalDist_sampleGlobalSignatureTable_eq_uniform
    (request : SignRequest) (encoding : ChainIndex → Digit)
    (chains : List ChainIndex) :
    𝒟[sampleGlobalSignatureTable request encoding chains] =
      𝒟[$ᵗ (GlobalChainValueIndex → Digest)] := by
  induction chains with
  | nil => rfl
  | cons chain chains ih =>
      unfold sampleGlobalSignatureTable
      calc
        𝒟[do
          let value ← $ᵗ Digest
          let base ← sampleGlobalSignatureTable request encoding chains
          pure (Function.update base
            (chain, request.epoch, encoding chain) value)] =
            𝒟[do
              let value ← $ᵗ Digest
              let base ← $ᵗ (GlobalChainValueIndex → Digest)
              pure (Function.update base
                (chain, request.epoch, encoding chain) value)] := by
          conv_lhs => rw [evalDist_bind]
          conv_rhs => rw [evalDist_bind]
          apply bind_congr
          intro value
          simpa [map_eq_bind_pure_comp] using
            (evalDist_map_eq_of_evalDist_eq ih
              (fun base => Function.update base
                (chain, request.epoch, encoding chain) value))
        _ = 𝒟[$ᵗ (GlobalChainValueIndex → Digest)] :=
          evalDist_uniformSample_bind_update
            (D := GlobalChainValueIndex) (R := Digest)
            (chain, request.epoch, encoding chain)

theorem revealGlobalSignatureOption_run
    (secretKey : SecretKey) (request : SignRequest)
    (signatureOption : Option Signature) (state : GlobalCausalHashState) :
    (revealGlobalSignatureOption secretKey request signatureOption).run state =
      (match signatureOption with
      | none => pure (none, state)
      | some signature =>
          match TargetSum.decodeDigest
              (Concrete.CacheView.encodingHash state.cache secretKey.parameter
                request.epoch (request.message, signature.randomness)) with
          | none => pure (some signature, state)
          | some encoding => do
              let revealed ← (revealGlobalSignatureChains request encoding
                allChains signature).run state
              pure (some revealed.1, revealed.2)) := by
  cases signatureOption <;> rfl

theorem simulate_eagerTrace_revealGlobalSignatureOption_some_of_decode
    (table : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (request : SignRequest)
    (signature : Signature) (state : GlobalCausalHashState)
    (encoding : ChainIndex → Digit)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash state.cache secretKey.parameter
        request.epoch (request.message, signature.randomness)) = some encoding) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      ((revealGlobalSignatureOption secretKey request (some signature)).run
        state)).run =
      pure (((some (globalSignatureRevealResult table request encoding
        allChains signature state).1,
          (globalSignatureRevealResult table request encoding
            allChains signature state).2),
        globalSignatureRevealTrace table request encoding allChains)) := by
  rw [revealGlobalSignatureOption_run]
  simp only [hdecode]
  rw [simulateQ_bind, WriterT.run_bind',
    simulate_eagerTrace_revealGlobalSignatureChains]
  simp

theorem simulate_eagerTrace_globalCausalSigningQueryAfterRealRom
    (table : GlobalChainValueIndex → Digest)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (request : SignRequest) (state : GlobalCausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (globalCausalSigningQueryAfterRealRom
        publicKey secretKey request state)).run =
    ((simulateQ xmssRomImpl
      (Concrete.cappedScheme.sign publicKey secretKey request.epoch request.message)).run
        state.cache >>= fun signed =>
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((revealGlobalSignatureOption secretKey request signed.1).run
          { state with cache := signed.2 })).run) := by
  unfold globalCausalSigningQueryAfterRealRom
  rw [simulateQ_bind, WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply, List.nil_append]
  rw [show (Prod.map id
    (fun trace : RevealProbeOracleSimulation.ActionTrace
      GlobalChainValueIndex => trace)) = id from rfl, Function.comp_id]
  simp

noncomputable def globalCausalResampledSigningContinuation
    (secretKey : SecretKey) (request : SignRequest)
    (state : GlobalCausalHashState)
    (signed : Option Signature × QueryCache HashSpec)
    (continuation : (GlobalChainValueIndex → Digest) →
      ((Option Signature × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) → ProbComp α) :
    ProbComp α :=
  let signedState := { state with cache := signed.2 }
  match signed.1 with
  | none => do
      let table ← $ᵗ (GlobalChainValueIndex → Digest)
      continuation table ((none, signedState), [])
  | some signature =>
      match TargetSum.decodeDigest
          (Concrete.CacheView.encodingHash signedState.cache secretKey.parameter
            request.epoch (request.message, signature.randomness)) with
      | none => do
          let table ← $ᵗ (GlobalChainValueIndex → Digest)
          continuation table ((some signature, signedState), [])
      | some encoding => do
          let table ← sampleGlobalSignatureTable request encoding allChains
          let revealed := globalSignatureRevealResult table request encoding
            allChains signature signedState
          continuation table ((some revealed.1, revealed.2),
            globalSignatureRevealTrace table request encoding allChains)

set_option maxRecDepth 10000 in
theorem evalDist_uniformGlobalTable_simulate_eagerTrace_globalCausalSigningQueryAfterRealRom_continuation
    (publicKey : PublicKey) (secretKey : SecretKey)
    (request : SignRequest) (state : GlobalCausalHashState)
    (continuation : (GlobalChainValueIndex → Digest) →
      ((Option Signature × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) → ProbComp α) :
    𝒟[do
      let table ← $ᵗ (GlobalChainValueIndex → Digest)
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalCausalSigningQueryAfterRealRom
          publicKey secretKey request state)).run
      continuation table result] =
    𝒟[(simulateQ xmssRomImpl
      (Concrete.cappedScheme.sign publicKey secretKey request.epoch request.message)).run
        state.cache >>= fun signed =>
      globalCausalResampledSigningContinuation secretKey request state signed
        continuation] := by
  calc
    𝒟[do
      let table ← $ᵗ (GlobalChainValueIndex → Digest)
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalCausalSigningQueryAfterRealRom
          publicKey secretKey request state)).run
      continuation table result] =
        𝒟[do
          let table ← $ᵗ (GlobalChainValueIndex → Digest)
          let signed ← (simulateQ xmssRomImpl
            (Concrete.cappedScheme.sign publicKey secretKey request.epoch request.message)).run
              state.cache
          let result ← (simulateQ
            (RevealProbeOracleSimulation.eagerTraceImpl table)
            ((revealGlobalSignatureOption secretKey request signed.1).run
              { state with cache := signed.2 })).run
          continuation table result] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro table
      rw [simulate_eagerTrace_globalCausalSigningQueryAfterRealRom]
      simp only [bind_assoc]
    _ = 𝒟[(simulateQ xmssRomImpl
          (Concrete.cappedScheme.sign publicKey secretKey request.epoch request.message)).run
            state.cache >>= fun signed => do
          let table ← $ᵗ (GlobalChainValueIndex → Digest)
          let result ← (simulateQ
            (RevealProbeOracleSimulation.eagerTraceImpl table)
            ((revealGlobalSignatureOption secretKey request signed.1).run
              { state with cache := signed.2 })).run
          continuation table result] :=
      OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    _ = _ := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro signed
      rcases signed with ⟨signatureOption, cache⟩
      cases signatureOption with
      | none =>
          simp [globalCausalResampledSigningContinuation,
            revealGlobalSignatureOption_run,
            RevealProbeOracleSimulation.eagerTraceImpl]
      | some signature =>
          cases hdecode : TargetSum.decodeDigest
              (Concrete.CacheView.encodingHash cache secretKey.parameter
                request.epoch (request.message, signature.randomness)) with
          | none =>
              simp [globalCausalResampledSigningContinuation,
                revealGlobalSignatureOption_run, hdecode,
                RevealProbeOracleSimulation.eagerTraceImpl]
          | some encoding =>
              let finish := fun table : GlobalChainValueIndex → Digest =>
                continuation table
                  ((some (globalSignatureRevealResult table request encoding
                      allChains signature { state with cache := cache }).1,
                    (globalSignatureRevealResult table request encoding
                      allChains signature { state with cache := cache }).2),
                    globalSignatureRevealTrace table request encoding allChains)
              calc
                𝒟[do
                  let table ← $ᵗ (GlobalChainValueIndex → Digest)
                  let result ← (simulateQ
                    (RevealProbeOracleSimulation.eagerTraceImpl table)
                    ((revealGlobalSignatureOption secretKey request
                      (some signature)).run
                        { state with cache := cache })).run
                  continuation table result] =
                    𝒟[($ᵗ (GlobalChainValueIndex → Digest)) >>= finish] := by
                      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                      intro table
                      rw [simulate_eagerTrace_revealGlobalSignatureOption_some_of_decode
                        table secretKey request signature
                          { state with cache := cache } encoding hdecode]
                      simp [finish]
                _ = 𝒟[sampleGlobalSignatureTable request encoding allChains >>=
                      finish] := by
                      conv_lhs => rw [evalDist_bind]
                      conv_rhs => rw [evalDist_bind]
                      rw [evalDist_sampleGlobalSignatureTable_eq_uniform]
                _ = 𝒟[globalCausalResampledSigningContinuation
                      secretKey request state (some signature, cache)
                        continuation] := by
                      simp [globalCausalResampledSigningContinuation,
                        hdecode, finish]

noncomputable def globalCausalEagerSigningStep
    (publicKey : PublicKey) (secretKey : SecretKey)
    (request : SignRequest) (state : GlobalCausalHashState) :
    ProbComp ((GlobalChainValueIndex → Digest) ×
      ((Option Signature × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) := do
  let table ← $ᵗ (GlobalChainValueIndex → Digest)
  let result ← (simulateQ
    (RevealProbeOracleSimulation.eagerTraceImpl table)
    (globalCausalSigningQueryAfterRealRom
      publicKey secretKey request state)).run
  pure (table, result)

noncomputable def globalCausalResampledSigningStep
    (publicKey : PublicKey) (secretKey : SecretKey)
    (request : SignRequest) (state : GlobalCausalHashState) :
    ProbComp ((GlobalChainValueIndex → Digest) ×
      ((Option Signature × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) :=
  (simulateQ xmssRomImpl
    (Concrete.cappedScheme.sign publicKey secretKey request.epoch request.message)).run
      state.cache >>= fun signed =>
    globalCausalResampledSigningContinuation secretKey request state signed
      (fun table result => pure (table, result))

theorem evalDist_globalCausalEagerSigningStep_eq_resampled
    (publicKey : PublicKey) (secretKey : SecretKey)
    (request : SignRequest) (state : GlobalCausalHashState) :
    𝒟[globalCausalEagerSigningStep
      publicKey secretKey request state] =
    𝒟[globalCausalResampledSigningStep
      publicKey secretKey request state] := by
  unfold globalCausalEagerSigningStep globalCausalResampledSigningStep
  exact
    evalDist_uniformGlobalTable_simulate_eagerTrace_globalCausalSigningQueryAfterRealRom_continuation
      publicKey secretKey request state
      (fun table result => pure (table, result))

theorem evalDist_globalCausalEagerSigningStep_continuation_eq_resampled
    (publicKey : PublicKey) (secretKey : SecretKey)
    (request : SignRequest) (state : GlobalCausalHashState)
    (continuation : (GlobalChainValueIndex → Digest) →
      ((Option Signature × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) → ProbComp α) :
    𝒟[globalCausalEagerSigningStep publicKey secretKey request state >>=
      fun result => continuation result.1 result.2] =
    𝒟[globalCausalResampledSigningStep publicKey secretKey request state >>=
      fun result => continuation result.1 result.2] := by
  rw [evalDist_bind, evalDist_globalCausalEagerSigningStep_eq_resampled,
    ← evalDist_bind]

end XmssSecurity.CappedChain
