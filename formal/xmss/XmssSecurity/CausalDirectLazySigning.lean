import XmssSecurity.CausalDirectStepCoupling

open OracleComp OracleSpec

namespace XmssSecurity

noncomputable local instance directLazySigningSampleableChainTable :
    SampleableType (ChainValueIndex → Digest) :=
  SampleableType.ofFintype (ChainValueIndex → Digest)

noncomputable def filteredEagerSigningReveal
    (table : ChainValueIndex → Digest)
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (request : SignRequest) (randomness : Randomness)
    (encodingOption : Option Encoding) (state : CausalHashState) :
    ProbComp ((Option Signature × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :=
  match encodingOption with
  | none => pure ((none, state), [])
  | some encoding =>
      let index := (request.epoch, encoding selected)
      let value := table index
      let signature := replaceSignatureChainValue
        (Concrete.CacheReplay.signWithEncoding keyView.cache keyView.secretKey
          request.epoch randomness encoding) selected value
      pure ((some signature, state.recordReveal index value),
        [.reveal index value])

noncomputable def filteredDirectLazySigningReveal
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (request : SignRequest) (randomness : Randomness)
    (encodingOption : Option Encoding) (state : CausalHashState) :
    ProbComp ((Option Signature × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) := do
  match encodingOption with
  | none => pure ((none, state), [])
  | some encoding =>
      let index := (request.epoch, encoding selected)
      match state.revealed index with
      | some value =>
          let signature := replaceSignatureChainValue
            (Concrete.CacheReplay.signWithEncoding keyView.cache
              keyView.secretKey request.epoch randomness encoding)
            selected value
          pure ((some signature, state.recordReveal index value),
            [.reveal index value])
      | none => do
          let value ← $ᵗ Digest
          let signature := replaceSignatureChainValue
            (Concrete.CacheReplay.signWithEncoding keyView.cache
              keyView.secretKey request.epoch randomness encoding)
            selected value
          pure ((some signature, state.recordReveal index value),
            [.reveal index value])

noncomputable def filteredEagerSigningQuery
    (table : ChainValueIndex → Digest)
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (request : SignRequest) (state : CausalHashState) :
    ProbComp ((Option Signature × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) := do
  let randomness ← Concrete.signingRandomness
  let encoded ← (simulateQ randomOracle
    (Concrete.encodingHash keyView.secretKey.parameter request.epoch
      request.message randomness)).run state.cache
  filteredEagerSigningReveal table keyView selected request randomness
    (TargetSum.decodeDigest encoded.1) { state with cache := encoded.2 }

noncomputable def filteredDirectLazySigningQuery
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (request : SignRequest) (state : CausalHashState) :
    ProbComp ((Option Signature × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) := do
  let randomness ← Concrete.signingRandomness
  let encoded ← (simulateQ randomOracle
    (Concrete.encodingHash keyView.secretKey.parameter request.epoch
      request.message randomness)).run state.cache
  filteredDirectLazySigningReveal keyView selected request randomness
    (TargetSum.decodeDigest encoded.1) { state with cache := encoded.2 }

set_option maxRecDepth 100000 in
theorem simulate_eagerTrace_filteredCausalSigningQuery
    (table : ChainValueIndex → Digest)
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (request : SignRequest) (state : CausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (filteredCausalSigningQuery keyView selected request state)).run =
        filteredEagerSigningQuery table keyView selected request state := by
  unfold filteredCausalSigningQuery filteredEagerSigningQuery
  rw [simulateQ_bind, WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply, List.nil_append]
  apply bind_congr
  intro randomness
  rw [simulateQ_bind, WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply, List.nil_append]
  apply bind_congr
  intro encoded
  cases hdecode : TargetSum.decodeDigest encoded.1 with
  | none => simp [filteredEagerSigningReveal]
  | some encoding =>
      simp only [filteredEagerSigningReveal]
      rw [simulateQ_bind, WriterT.run_bind',
        RevealProbeOracleSimulation.simulate_eagerTrace_revealQuery]
      simp

noncomputable def filteredInstalledSigningContinuation
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (request : SignRequest) (randomness : Randomness) (encoding : Encoding)
    (state : CausalHashState) (index : ChainValueIndex)
    (continuation : (ChainValueIndex → Digest) →
      ((Option Signature × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α)
    (base : ChainValueIndex → Digest) (value : Digest) : ProbComp α :=
  let finalState := state.recordReveal index value
  let signature := replaceSignatureChainValue
    (Concrete.CacheReplay.signWithEncoding keyView.cache keyView.secretKey
      request.epoch randomness encoding) selected value
  continuation (causalInstalledTable finalState base)
    ((some signature, finalState), [.reveal index value])

theorem filteredInstalledSigningContinuation_update_base
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (request : SignRequest) (randomness : Randomness) (encoding : Encoding)
    (state : CausalHashState) (index : ChainValueIndex)
    (continuation : (ChainValueIndex → Digest) →
      ((Option Signature × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α)
    (base : ChainValueIndex → Digest) (value : Digest) :
    filteredInstalledSigningContinuation keyView selected request randomness
        encoding state index continuation (Function.update base index value) value =
      filteredInstalledSigningContinuation keyView selected request randomness
        encoding state index continuation base value := by
  unfold filteredInstalledSigningContinuation
  dsimp only
  have hrevealed :
      (state.recordReveal index value).revealed index = some value := by
    simp [CausalHashState.recordReveal]
  rw [causalInstalledTable_update_base_of_revealed
    (state.recordReveal index value) base index value value hrevealed]

theorem causalInstalledTable_recordReveal_installed
    (state : CausalHashState) (base : ChainValueIndex → Digest)
    (index : ChainValueIndex) :
    causalInstalledTable
        (state.recordReveal index (causalInstalledTable state base index)) base =
      causalInstalledTable state base := by
  rw [causalInstalledTable_recordReveal]
  funext candidate
  by_cases heq : candidate = index
  · subst candidate
    simp only [Function.update_self]
  · simp only [Function.update_of_ne heq]

theorem filteredEagerSigningReveal_support_installedTable
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (request : SignRequest) (randomness : Randomness)
    (encodingOption : Option Encoding) (state : CausalHashState)
    (base : ChainValueIndex → Digest)
    (result : (Option Signature × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      (filteredEagerSigningReveal (causalInstalledTable state base)
        keyView selected request randomness encodingOption state)) :
    causalInstalledTable result.1.2 base =
      causalInstalledTable state base := by
  cases encodingOption with
  | none =>
      simp [filteredEagerSigningReveal] at hresult
      subst result
      rfl
  | some encoding =>
      simp [filteredEagerSigningReveal] at hresult
      subst result
      exact causalInstalledTable_recordReveal_installed state base
        (request.epoch, encoding selected)

set_option maxRecDepth 100000 in
theorem evalDist_installed_filteredSigningReveal_continuation_eq_lazy
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (request : SignRequest) (randomness : Randomness)
    (encodingOption : Option Encoding) (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      ((Option Signature × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    𝒟[do
      let base ← $ᵗ (ChainValueIndex → Digest)
      let result ← filteredEagerSigningReveal (causalInstalledTable state base)
        keyView selected request randomness encodingOption state
      continuation (causalInstalledTable result.1.2 base) result] =
    𝒟[do
      let result ← filteredDirectLazySigningReveal keyView selected request
        randomness encodingOption state
      let base ← $ᵗ (ChainValueIndex → Digest)
      continuation (causalInstalledTable result.1.2 base) result] := by
  cases encodingOption with
  | none =>
      simp [filteredEagerSigningReveal, filteredDirectLazySigningReveal]
  | some encoding =>
      let index : ChainValueIndex := (request.epoch, encoding selected)
      cases hrevealed : state.revealed index with
      | some value =>
          simp only [filteredEagerSigningReveal,
            filteredDirectLazySigningReveal, index, hrevealed, pure_bind]
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro base
          have hvalue := causalInstalledTable_of_revealed
            state base index value hrevealed
          simp [index, hvalue]
      | none =>
          simp only [filteredEagerSigningReveal,
            filteredDirectLazySigningReveal, index, hrevealed, pure_bind]
          calc
            _ = 𝒟[do
                let base ← $ᵗ (ChainValueIndex → Digest)
                let value := base index
                filteredInstalledSigningContinuation keyView selected request
                  randomness encoding state index continuation base value] := by
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro base
              rw [causalInstalledTable_of_not_revealed state base index hrevealed]
              simp [index, filteredInstalledSigningContinuation]

            _ = 𝒟[do
                let value ← $ᵗ Digest
                let base ← $ᵗ (ChainValueIndex → Digest)
                filteredInstalledSigningContinuation keyView selected request
                  randomness encoding state index continuation
                    (Function.update base index value) value] := by
              exact
                RevealProbeOracleSimulation.evalDist_uniformTable_bind_coordinate_continuation
                  index (filteredInstalledSigningContinuation keyView selected
                    request randomness encoding state index continuation)
            _ = 𝒟[do
                let value ← $ᵗ Digest
                let base ← $ᵗ (ChainValueIndex → Digest)
                filteredInstalledSigningContinuation keyView selected request
                  randomness encoding state index continuation base value] := by
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro value
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro base
              rw [filteredInstalledSigningContinuation_update_base]
            _ = _ := by
              simp [index, filteredInstalledSigningContinuation]

set_option maxRecDepth 100000 in
theorem evalDist_installed_filteredSigningReveal_fixedContinuation_eq_lazy
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (request : SignRequest) (randomness : Randomness)
    (encodingOption : Option Encoding) (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      ((Option Signature × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    𝒟[do
      let base ← $ᵗ (ChainValueIndex → Digest)
      let table := causalInstalledTable state base
      let result ← filteredEagerSigningReveal table keyView selected request
        randomness encodingOption state
      continuation table result] =
    𝒟[do
      let result ← filteredDirectLazySigningReveal keyView selected request
        randomness encodingOption state
      let base ← $ᵗ (ChainValueIndex → Digest)
      continuation (causalInstalledTable result.1.2 base) result] := by
  calc
    _ = 𝒟[do
        let base ← $ᵗ (ChainValueIndex → Digest)
        let result ← filteredEagerSigningReveal
          (causalInstalledTable state base) keyView selected request randomness
            encodingOption state
        continuation (causalInstalledTable result.1.2 base) result] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro base
      apply RevealProbeOracleSimulation.evalDist_bind_congr_of_support
      intro result hresult
      rw [filteredEagerSigningReveal_support_installedTable keyView selected
        request randomness encodingOption state base result hresult]
    _ = _ :=
      evalDist_installed_filteredSigningReveal_continuation_eq_lazy
        keyView selected request randomness encodingOption state continuation

set_option maxRecDepth 100000 in
theorem evalDist_installed_filteredCausalSigningQuery_continuation_eq_lazy
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (request : SignRequest) (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      ((Option Signature × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    𝒟[do
      let base ← $ᵗ (ChainValueIndex → Digest)
      let table := causalInstalledTable state base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredCausalSigningQuery keyView selected request state)).run
      continuation (causalInstalledTable result.1.2 base) result] =
    𝒟[do
      let result ← filteredDirectLazySigningQuery
        keyView selected request state
      let base ← $ᵗ (ChainValueIndex → Digest)
      continuation (causalInstalledTable result.1.2 base) result] := by
  calc
    _ = 𝒟[do
        let base ← $ᵗ (ChainValueIndex → Digest)
        let result ← filteredEagerSigningQuery
          (causalInstalledTable state base) keyView selected request state
        continuation (causalInstalledTable result.1.2 base) result] := by
        apply OracleComp.DeferredSampling.evalDist_bind_congr_left
        intro base
        simp only
        rw [simulate_eagerTrace_filteredCausalSigningQuery]
    _ = _ := by
      unfold filteredEagerSigningQuery filteredDirectLazySigningQuery
      simp only [bind_assoc]
      rw [OracleComp.DeferredSampling.evalDist_bind_comm]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro randomness
      rw [OracleComp.DeferredSampling.evalDist_bind_comm]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro encoded
      exact evalDist_installed_filteredSigningReveal_continuation_eq_lazy
        keyView selected request randomness (TargetSum.decodeDigest encoded.1)
          { state with cache := encoded.2 } continuation

set_option maxRecDepth 100000 in
theorem evalDist_installed_filteredCausalSigningQuery_fixedContinuation_eq_lazy
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (request : SignRequest) (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      ((Option Signature × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    𝒟[do
      let base ← $ᵗ (ChainValueIndex → Digest)
      let table := causalInstalledTable state base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredCausalSigningQuery keyView selected request state)).run
      continuation table result] =
    𝒟[do
      let result ← filteredDirectLazySigningQuery
        keyView selected request state
      let base ← $ᵗ (ChainValueIndex → Digest)
      continuation (causalInstalledTable result.1.2 base) result] := by
  calc
    _ = 𝒟[do
        let base ← $ᵗ (ChainValueIndex → Digest)
        let result ← filteredEagerSigningQuery
          (causalInstalledTable state base) keyView selected request state
        continuation (causalInstalledTable state base) result] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro base
      simp only
      rw [simulate_eagerTrace_filteredCausalSigningQuery]
    _ = _ := by
      unfold filteredEagerSigningQuery filteredDirectLazySigningQuery
      simp only [bind_assoc]
      rw [OracleComp.DeferredSampling.evalDist_bind_comm]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro randomness
      rw [OracleComp.DeferredSampling.evalDist_bind_comm]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro encoded
      simpa only [causalInstalledTable_setCache] using
        (evalDist_installed_filteredSigningReveal_fixedContinuation_eq_lazy
          keyView selected request randomness (TargetSum.decodeDigest encoded.1)
            { state with cache := encoded.2 } continuation)

end XmssSecurity
