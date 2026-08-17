import XmssSecurity.CappedChain.CausalInstalledTableGame
import XmssSecurity.CappedChain.CausalSigningResampling

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

noncomputable local instance causalInstalledSampleableChainTable :
    SampleableType (ChainValueIndex → Digest) :=
  SampleableType.ofFintype (ChainValueIndex → Digest)

noncomputable def causalLazyAttackerHashStep
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState) :
    ProbComp ((HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :=
  match causalAttackerHashPlan secretKey chain input state with
  | .cached output =>
      pure ((output, causalRecordedState secretKey chain input state), [])
  | .redirect output =>
      pure ((output,
        { (causalRecordedState secretKey chain input state) with
          cache := (causalRecordedState secretKey chain input state).cache.cacheQuery
            input output }), [])
  | .fresh => do
      let hashResult ← (randomOracle input).run
        (causalRecordedState secretKey chain input state).cache
      pure ((hashResult.1,
        { (causalRecordedState secretKey chain input state) with
          cache := hashResult.2 }), [])
  | .reveal index =>
      match state.revealed index with
      | some value => do
          let output ← Rom.sampleHashOutputWithDigest value
          pure ((output, causalRevealResultState secretKey chain input state
            index value output),
            [RevealProbeOracleSimulation.ObservedAction.reveal index value])
      | none => do
          let output ← $ᵗ HashOutput
          let value := truncateHash output
          pure ((output, causalRevealResultState secretKey chain input state
            index value output),
            [RevealProbeOracleSimulation.ObservedAction.reveal index value])

noncomputable def causalInstalledRevealContinuation
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState) (index : ChainValueIndex)
    (continuation : (ChainValueIndex → Digest) →
      ((HashOutput × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α)
    (base : ChainValueIndex → Digest) (value : Digest)
    (output : HashOutput) : ProbComp α :=
  continuation
    (causalInstalledTable
      (causalRevealResultState secretKey chain input state index value output) base)
    ((output, causalRevealResultState secretKey chain input state
      index value output),
      [RevealProbeOracleSimulation.ObservedAction.reveal index value])

theorem causalInstalledRevealContinuation_update_base
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState) (index : ChainValueIndex)
    (continuation : (ChainValueIndex → Digest) →
      ((HashOutput × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α)
    (base : ChainValueIndex → Digest) (value : Digest)
    (output : HashOutput) :
    causalInstalledRevealContinuation secretKey chain input state index
        continuation (Function.update base index value) value output =
      causalInstalledRevealContinuation secretKey chain input state index
        continuation base value output := by
  unfold causalInstalledRevealContinuation
  rw [causalInstalledTable_update_base_of_revealed
    (causalRevealResultState secretKey chain input state index value output)
    base index value value
    (causalRevealResultState_revealed_self
      secretKey chain input state index value output)]

noncomputable def causalProgrammedRevealContinuation
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState) (index : ChainValueIndex)
    (continuation : (ChainValueIndex → Digest) →
      ((HashOutput × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    ProbComp α := do
  let output ← $ᵗ HashOutput
  let base ← $ᵗ (ChainValueIndex → Digest)
  let value := truncateHash output
  causalInstalledRevealContinuation secretKey chain input state index
    continuation (Function.update base index value) value output

noncomputable def causalFreshBaseRevealContinuation
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState) (index : ChainValueIndex)
    (continuation : (ChainValueIndex → Digest) →
      ((HashOutput × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    ProbComp α := do
  let output ← $ᵗ HashOutput
  let base ← $ᵗ (ChainValueIndex → Digest)
  let value := truncateHash output
  causalInstalledRevealContinuation secretKey chain input state index
    continuation base value output

theorem evalDist_causalProgrammedRevealContinuation_eq_freshBase
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState) (index : ChainValueIndex)
    (continuation : (ChainValueIndex → Digest) →
      ((HashOutput × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    𝒟[causalProgrammedRevealContinuation secretKey chain input state
      index continuation] =
    𝒟[causalFreshBaseRevealContinuation secretKey chain input state
      index continuation] := by
  unfold causalProgrammedRevealContinuation causalFreshBaseRevealContinuation
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro output
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro base
  rw [causalInstalledRevealContinuation_update_base]

set_option maxRecDepth 100000 in
theorem evalDist_installed_causalAttackerHashQuery_continuation_eq_lazy
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      ((HashOutput × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    𝒟[do
      let base ← $ᵗ (ChainValueIndex → Digest)
      let table := causalInstalledTable state base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((causalAttackerHashQuery secretKey chain input).run state)).run
      continuation (causalInstalledTable result.1.2 base) result] =
    𝒟[do
      let result ← causalLazyAttackerHashStep secretKey chain input state
      let base ← $ᵗ (ChainValueIndex → Digest)
      continuation (causalInstalledTable result.1.2 base) result] := by
  generalize hplan : causalAttackerHashPlan secretKey chain input state = plan
  cases plan with
  | cached output =>
      simp only [causalLazyAttackerHashStep, hplan, pure_bind]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro base
      simp_rw [causalAttackerHashQuery_run, hplan]
      simp
  | redirect output =>
      simp only [causalLazyAttackerHashStep, hplan, pure_bind]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro base
      simp_rw [causalAttackerHashQuery_run, hplan]
      simp
  | fresh =>
      simp only [causalLazyAttackerHashStep, hplan, pure_bind]
      calc
        _ = 𝒟[do
            let base ← $ᵗ (ChainValueIndex → Digest)
            let hashResult ← (randomOracle input).run
              (causalRecordedState secretKey chain input state).cache
            continuation
              (causalInstalledTable
                { (causalRecordedState secretKey chain input state) with
                  cache := hashResult.2 } base)
              ((hashResult.1,
                { (causalRecordedState secretKey chain input state) with
                  cache := hashResult.2 }), [])] := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro base
          simp_rw [causalAttackerHashQuery_run, hplan]
          rw [
            simulate_eagerTrace_causalHashQuery]
          simp [map_eq_bind_pure_comp]
        _ = _ := by
          rw [OracleComp.DeferredSampling.evalDist_bind_comm]
          simp [bind_assoc]
  | reveal index =>
      cases hrevealed : state.revealed index with
      | some value =>
          simp only [causalLazyAttackerHashStep, hplan, hrevealed, pure_bind]
          calc
            _ = 𝒟[do
                let base ← $ᵗ (ChainValueIndex → Digest)
                let output ← Rom.sampleHashOutputWithDigest value
                continuation
                  (causalInstalledTable
                    (causalRevealResultState secretKey chain input state
                      index value output) base)
                  ((output, causalRevealResultState secretKey chain input state
                    index value output),
                    [RevealProbeOracleSimulation.ObservedAction.reveal
                      index value])] := by
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro base
              simp_rw [causalAttackerHashQuery_run, hplan]
              unfold causalRevealHashQuery
              rw [RevealProbeOracleSimulation.simulate_eagerTrace_reveal_then_liftProbComp]
              simp [causalInstalledTable_of_revealed state base index value hrevealed,
                map_eq_bind_pure_comp]
            _ = _ := by
              rw [OracleComp.DeferredSampling.evalDist_bind_comm]
              simp [bind_assoc]
      | none =>
          simp only [causalLazyAttackerHashStep, hplan, hrevealed, pure_bind]
          calc
            _ = 𝒟[do
                let base ← $ᵗ (ChainValueIndex → Digest)
                let output ← Rom.sampleHashOutputWithDigest (base index)
                let value := base index
                causalInstalledRevealContinuation secretKey chain input state
                  index continuation base value output] := by
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro base
              simp_rw [causalAttackerHashQuery_run, hplan]
              unfold causalRevealHashQuery
              rw [RevealProbeOracleSimulation.simulate_eagerTrace_reveal_then_liftProbComp]
              simp [causalInstalledTable_of_not_revealed
                state base index hrevealed, causalInstalledRevealContinuation,
                map_eq_bind_pure_comp]
            _ = 𝒟[causalProgrammedRevealContinuation
                secretKey chain input state index continuation] := by
              unfold causalProgrammedRevealContinuation
              exact
                (RevealProbeOracleSimulation.evalDist_uniformTable_bind_programmedCoordinate_continuation
                  index (causalInstalledRevealContinuation
                    secretKey chain input state index continuation))
            _ = 𝒟[causalFreshBaseRevealContinuation
                secretKey chain input state index continuation] :=
              evalDist_causalProgrammedRevealContinuation_eq_freshBase
                secretKey chain input state index continuation
            _ = _ := by
              unfold causalFreshBaseRevealContinuation
              simp [causalInstalledRevealContinuation, bind_assoc]

noncomputable def causalLazyRevealSignatureOption
    (secretKey : SecretKey) (chain : ChainIndex) (request : SignRequest)
    (signatureOption : Option Signature) (state : CausalHashState) :
    ProbComp ((Option Signature × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :=
  match signatureOption with
  | none => pure ((none, state), [])
  | some signature =>
      match TargetSum.decodeDigest
          (Concrete.CacheView.encodingHash state.cache secretKey.parameter
            request.epoch (request.message, signature.randomness)) with
      | none => pure ((some signature, state), [])
      | some encoding =>
          let index := (request.epoch, encoding chain)
          match state.revealed index with
          | some value =>
              pure ((some (replaceSignatureChainValue signature chain value),
                state.recordReveal index value),
                [RevealProbeOracleSimulation.ObservedAction.reveal index value])
          | none => do
              let value ← $ᵗ Digest
              pure ((some (replaceSignatureChainValue signature chain value),
                state.recordReveal index value),
                [RevealProbeOracleSimulation.ObservedAction.reveal index value])

noncomputable def causalInstalledSignatureContinuation
    (chain : ChainIndex) (request : SignRequest) (signature : Signature)
    (state : CausalHashState) (index : ChainValueIndex)
    (continuation : (ChainValueIndex → Digest) →
      ((Option Signature × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α)
    (base : ChainValueIndex → Digest) (value : Digest) : ProbComp α :=
  continuation (causalInstalledTable (state.recordReveal index value) base)
    ((some (replaceSignatureChainValue signature chain value),
      state.recordReveal index value),
      [RevealProbeOracleSimulation.ObservedAction.reveal index value])

theorem causalInstalledSignatureContinuation_update_base
    (chain : ChainIndex) (request : SignRequest) (signature : Signature)
    (state : CausalHashState) (index : ChainValueIndex)
    (continuation : (ChainValueIndex → Digest) →
      ((Option Signature × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α)
    (base : ChainValueIndex → Digest) (value : Digest) :
    causalInstalledSignatureContinuation chain request signature state index
        continuation (Function.update base index value) value =
      causalInstalledSignatureContinuation chain request signature state index
        continuation base value := by
  unfold causalInstalledSignatureContinuation
  rw [causalInstalledTable_update_base_of_revealed
    (state.recordReveal index value) base index value value]
  simp [CausalHashState.recordReveal]

set_option maxRecDepth 100000 in
theorem evalDist_installed_revealFixedChainSignatureOption_continuation_eq_lazy
    (secretKey : SecretKey) (chain : ChainIndex) (request : SignRequest)
    (signatureOption : Option Signature) (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      ((Option Signature × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    𝒟[do
      let base ← $ᵗ (ChainValueIndex → Digest)
      let table := causalInstalledTable state base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((revealFixedChainSignatureOption secretKey chain request
          signatureOption).run state)).run
      continuation (causalInstalledTable result.1.2 base) result] =
    𝒟[do
      let result ← causalLazyRevealSignatureOption
        secretKey chain request signatureOption state
      let base ← $ᵗ (ChainValueIndex → Digest)
      continuation (causalInstalledTable result.1.2 base) result] := by
  cases signatureOption with
  | none =>
      simp [causalLazyRevealSignatureOption,
        revealFixedChainSignatureOption_run,
        RevealProbeOracleSimulation.eagerTraceImpl]
  | some signature =>
      cases hdecode : TargetSum.decodeDigest
          (Concrete.CacheView.encodingHash state.cache secretKey.parameter
            request.epoch (request.message, signature.randomness)) with
      | none =>
          simp [causalLazyRevealSignatureOption,
            revealFixedChainSignatureOption_run, hdecode,
            RevealProbeOracleSimulation.eagerTraceImpl]
      | some encoding =>
          let index : ChainValueIndex := (request.epoch, encoding chain)
          cases hrevealed : state.revealed index with
          | some value =>
              have hrevealed' : state.revealed
                  (request.epoch, encoding chain) = some value := by
                simpa [index] using hrevealed
              simp only [causalLazyRevealSignatureOption, hdecode, hrevealed',
                pure_bind]
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro base
              rw [simulate_eagerTrace_revealFixedChainSignatureOption_some_of_decode
                (causalInstalledTable state base) secretKey chain request signature
                  state encoding hdecode]
              simp [index, causalInstalledTable_of_revealed
                state base index value hrevealed,
                causalInstalledSignatureContinuation]
          | none =>
              have hrevealed' : state.revealed
                  (request.epoch, encoding chain) = none := by
                simpa [index] using hrevealed
              simp only [causalLazyRevealSignatureOption, hdecode, hrevealed',
                pure_bind]
              calc
                _ = 𝒟[do
                    let base ← $ᵗ (ChainValueIndex → Digest)
                    let value := base index
                    causalInstalledSignatureContinuation chain request signature
                      state index continuation base value] := by
                  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                  intro base
                  rw [simulate_eagerTrace_revealFixedChainSignatureOption_some_of_decode
                    (causalInstalledTable state base) secretKey chain request
                      signature state encoding hdecode]
                  simp [index, causalInstalledTable_of_not_revealed
                    state base index hrevealed,
                    causalInstalledSignatureContinuation]
                _ = 𝒟[do
                    let value ← $ᵗ Digest
                    let base ← $ᵗ (ChainValueIndex → Digest)
                    causalInstalledSignatureContinuation chain request signature
                      state index continuation
                        (Function.update base index value) value] := by
                  exact
                    RevealProbeOracleSimulation.evalDist_uniformTable_bind_coordinate_continuation
                      index (causalInstalledSignatureContinuation
                        chain request signature state index continuation)
                _ = 𝒟[do
                    let value ← $ᵗ Digest
                    let base ← $ᵗ (ChainValueIndex → Digest)
                    causalInstalledSignatureContinuation chain request signature
                      state index continuation base value] := by
                  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                  intro value
                  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                  intro base
                  rw [causalInstalledSignatureContinuation_update_base]
                _ = _ := by
                  simp [causalLazyRevealSignatureOption, hdecode, hrevealed',
                    causalInstalledSignatureContinuation, index, bind_assoc]

noncomputable def causalLazySigningQuery
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (request : SignRequest) (state : CausalHashState) :
    ProbComp ((Option Signature × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) := do
  let signed ← (simulateQ xmssRomImpl
    (Concrete.scheme.sign publicKey secretKey request.epoch request.message)).run
      state.cache
  causalLazyRevealSignatureOption secretKey chain request signed.1
    { state with cache := signed.2 }

set_option maxRecDepth 100000 in
theorem evalDist_installed_causalSigningQueryAfterRealRom_continuation_eq_lazy
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (request : SignRequest) (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      ((Option Signature × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    𝒟[do
      let base ← $ᵗ (ChainValueIndex → Digest)
      let table := causalInstalledTable state base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        (causalSigningQueryAfterRealRom
          publicKey secretKey chain request state)).run
      continuation (causalInstalledTable result.1.2 base) result] =
    𝒟[do
      let result ← causalLazySigningQuery
        publicKey secretKey chain request state
      let base ← $ᵗ (ChainValueIndex → Digest)
      continuation (causalInstalledTable result.1.2 base) result] := by
  unfold causalLazySigningQuery
  calc
    _ = 𝒟[do
        let base ← $ᵗ (ChainValueIndex → Digest)
        let signed ← (simulateQ xmssRomImpl
          (Concrete.scheme.sign publicKey secretKey request.epoch
            request.message)).run state.cache
        let signedState := { state with cache := signed.2 }
        let result ← (simulateQ
          (RevealProbeOracleSimulation.eagerTraceImpl
            (causalInstalledTable signedState base))
          ((revealFixedChainSignatureOption secretKey chain request
            signed.1).run signedState)).run
        continuation (causalInstalledTable result.1.2 base) result] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro base
      simp_rw [simulate_eagerTrace_causalSigningQueryAfterRealRom]
      simp [causalInstalledTable_setCache, bind_assoc]
    _ = 𝒟[do
        let signed ← (simulateQ xmssRomImpl
          (Concrete.scheme.sign publicKey secretKey request.epoch
            request.message)).run state.cache
        let base ← $ᵗ (ChainValueIndex → Digest)
        let signedState := { state with cache := signed.2 }
        let result ← (simulateQ
          (RevealProbeOracleSimulation.eagerTraceImpl
            (causalInstalledTable signedState base))
          ((revealFixedChainSignatureOption secretKey chain request
            signed.1).run signedState)).run
        continuation (causalInstalledTable result.1.2 base) result] :=
      OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    _ = _ := by
      simp only [bind_assoc]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro signed
      exact
        evalDist_installed_revealFixedChainSignatureOption_continuation_eq_lazy
          secretKey chain request signed.1 { state with cache := signed.2 }
            continuation

end XmssSecurity.CappedChain
