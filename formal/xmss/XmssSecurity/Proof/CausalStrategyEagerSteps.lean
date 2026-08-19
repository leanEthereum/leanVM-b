import XmssSecurity.Proof.CausalStrategyProgram

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

noncomputable local instance causalEagerSampleableChainTable :
    SampleableType (ChainValueIndex → Digest) :=
  SampleableType.ofFintype (ChainValueIndex → Digest)

theorem evalDist_programmedCausalReveal_eq_uniformHashOutput
    (state : CausalHashState) (index : ChainValueIndex) (input : HashInput) :
    evalDist (do
      let target ← $ᵗ Digest
      let output ← Rom.sampleHashOutputWithDigest target
      pure (output,
        { (state.recordReveal index target) with
          cache := state.cache.cacheQuery input output })) =
    evalDist (do
      let output ← $ᵗ HashOutput
      pure (output,
        { (state.recordReveal index (truncateHash output)) with
          cache := state.cache.cacheQuery input output })) := by
  simpa [Rom.sampledHashOutputWithDigest, bind_assoc] using
    (Rom.evalDist_sampledHashOutputWithDigest_bind_eq_uniform_bind
      (fun programmed => pure (programmed.2,
        { (state.recordReveal index programmed.1) with
          cache := state.cache.cacheQuery input programmed.2 })))

theorem evalDist_uniformTable_simulate_eagerTrace_reveal_programmed_continuation
    (index : ChainValueIndex) (finish : Digest → HashOutput → α)
    (continuation : (ChainValueIndex → Digest) →
      (α × RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp β) :
    𝒟[do
      let table ← $ᵗ (ChainValueIndex → Digest)
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table) (do
          let value ← RevealProbeOracleSimulation.revealQuery index
          let output ← RevealProbeOracleSimulation.liftProbComp
            (Rom.sampleHashOutputWithDigest value)
          pure (finish value output))).run
      continuation table result] =
    𝒟[do
      let output ← $ᵗ HashOutput
      let base ← $ᵗ (ChainValueIndex → Digest)
      let table := Function.update base index (truncateHash output)
      continuation table (finish (truncateHash output) output,
        [RevealProbeOracleSimulation.ObservedAction.reveal
          index (truncateHash output)])] := by
  calc
    𝒟[do
      let table ← $ᵗ (ChainValueIndex → Digest)
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table) (do
          let value ← RevealProbeOracleSimulation.revealQuery index
          let output ← RevealProbeOracleSimulation.liftProbComp
            (Rom.sampleHashOutputWithDigest value)
          pure (finish value output))).run
      continuation table result] =
        𝒟[do
          let table ← $ᵗ (ChainValueIndex → Digest)
          let output ← Rom.sampleHashOutputWithDigest (table index)
          continuation table (finish (table index) output,
            [RevealProbeOracleSimulation.ObservedAction.reveal
              index (table index)])] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro table
      rw [RevealProbeOracleSimulation.simulate_eagerTrace_reveal_then_liftProbComp]
      simp [map_eq_bind_pure_comp, bind_assoc]
    _ = _ :=
      RevealProbeOracleSimulation.evalDist_uniformTable_bind_programmedCoordinate_continuation
        index (fun table value output =>
          continuation table (finish value output,
            [RevealProbeOracleSimulation.ObservedAction.reveal index value]))

theorem evalDist_uniformTable_simulate_eagerTrace_reveal_programmed
    (index : ChainValueIndex) (finish : Digest → HashOutput → α) :
    𝒟[do
      let table ← $ᵗ (ChainValueIndex → Digest)
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table) (do
          let value ← RevealProbeOracleSimulation.revealQuery index
          let output ← RevealProbeOracleSimulation.liftProbComp
            (Rom.sampleHashOutputWithDigest value)
          pure (finish value output))).run
      pure (table, result)] =
    𝒟[do
      let output ← $ᵗ HashOutput
      let base ← $ᵗ (ChainValueIndex → Digest)
      let table := Function.update base index (truncateHash output)
      pure (table, (finish (truncateHash output) output,
        [RevealProbeOracleSimulation.ObservedAction.reveal
          index (truncateHash output)]))] := by
  exact evalDist_uniformTable_simulate_eagerTrace_reveal_programmed_continuation
    index finish (fun table result => pure (table, result))

theorem causalAttackerHashPlan_eq_cached
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState) (output : HashOutput)
    (hcache : state.cache input = some output) :
    causalAttackerHashPlan secretKey chain input state = .cached output := by
  simp [causalAttackerHashPlan, hcache]

theorem causalAttackerHashPlan_reveal_cache_none
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState) (index : ChainValueIndex)
    (hplan : causalAttackerHashPlan secretKey chain input state = .reveal index) :
    state.cache input = none := by
  cases hcache : state.cache input with
  | none => rfl
  | some output =>
      rw [causalAttackerHashPlan, hcache] at hplan
      simp at hplan

theorem chainInputProbe?_leafInput
    (parameter : PublicParameter) (chain : ChainIndex)
    (epoch : Epoch) (endpoints : ChainIndex → Digest) :
    chainInputProbe? parameter chain
      (Concrete.CacheView.leafInput parameter epoch endpoints) = none := by
  unfold chainInputProbe?
  split
  · rename_i hexists
    obtain ⟨data, hdata⟩ := hexists
    have hdomain := domain_eq_of_tweakableHashInput_eq parameter hdata
    simp at hdomain
  · rfl

theorem causalAttackerHashPlan_eq_reveal_chainInput
    (secretKey : SecretKey) (chain : ChainIndex)
    (epoch : Epoch) (step : ChainStep) (value : Digest)
    (state : CausalHashState)
    (hcache : state.cache
      (Concrete.CacheView.chainInput secretKey.parameter epoch chain step value) = none)
    (hrevealed : state.revealed (epoch, chainStepDigit step) = some value) :
    causalAttackerHashPlan secretKey chain
      (Concrete.CacheView.chainInput secretKey.parameter epoch chain step value) state =
        .reveal (epoch, chainStepNextDigit step) := by
  rw [causalAttackerHashPlan, hcache, chainInputProbe?_chainInput]
  unfold causalUncachedAttackerHashPlan
  simp only [hrevealed]
  simp only [if_true]
  split
  · rfl
  · rename_i hnext
    exact (hnext (chainStepNextDigit step).isLt).elim

theorem causalAttackerHashPlan_eq_redirect
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState) (output : HashOutput)
    (hcache : state.cache input = none)
    (hchain : chainInputProbe? secretKey.parameter chain input = none)
    (htarget : state.keygenCache
      (keygenLeafTargetInput secretKey state.keygenCache input) = some output) :
    causalAttackerHashPlan secretKey chain input state = .redirect output := by
  unfold causalAttackerHashPlan
  rw [hcache, hchain]
  unfold causalUncachedAttackerHashPlan
  unfold causalLeafHashPlan
  rw [htarget]

theorem simulate_eagerImpl_causalAttackerHashQuery_cached
    (table : ChainValueIndex → Digest) (secretKey : SecretKey)
    (chain : ChainIndex) (input : HashInput) (state : CausalHashState)
    (output : HashOutput) (hcache : state.cache input = some output) :
    simulateQ (RevealProbeOracleSimulation.eagerImpl table)
      ((causalAttackerHashQuery secretKey chain input).run state) =
        pure (output, causalRecordedState secretKey chain input state) := by
  rw [causalAttackerHashQuery_run,
    causalAttackerHashPlan_eq_cached secretKey chain input state output hcache]
  rfl

theorem simulate_eagerTrace_causalAttackerHashQuery_cached
    (table : ChainValueIndex → Digest) (secretKey : SecretKey)
    (chain : ChainIndex) (input : HashInput) (state : CausalHashState)
    (output : HashOutput) (hcache : state.cache input = some output) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      ((causalAttackerHashQuery secretKey chain input).run state)).run =
        pure ((output, causalRecordedState secretKey chain input state),
          ([] : RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) := by
  rw [causalAttackerHashQuery_run,
    causalAttackerHashPlan_eq_cached secretKey chain input state output hcache]
  rfl

theorem simulate_eagerTrace_causalAttackerHashQuery_fresh_eq_causalHashQuery
    (table : ChainValueIndex → Digest) (secretKey : SecretKey)
    (chain : ChainIndex) (input : HashInput) (state : CausalHashState)
    (hplan : causalAttackerHashPlan secretKey chain input state = .fresh) :
    simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((causalAttackerHashQuery secretKey chain input).run state) =
      simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((causalHashQuery input).run
          (causalRecordedState secretKey chain input state)) := by
  rw [causalAttackerHashQuery_run, hplan]

theorem simulate_eagerTrace_causalHashQuery
    (table : ChainValueIndex → Digest) (input : HashInput)
    (state : CausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      ((causalHashQuery input).run state)).run =
      (fun result : HashOutput × QueryCache HashSpec =>
        ((result.1, { state with cache := result.2 }),
          ([] : RevealProbeOracleSimulation.ActionTrace ChainValueIndex))) <$>
        ((randomOracle input).run state.cache) := by
  rw [causalHashQuery_run, simulateQ_map, WriterT.run_map',
    RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp]
  simp [Functor.map_map]

theorem simulate_eagerTrace_causalAttackerHashQuery_reveal_eq
    (table : ChainValueIndex → Digest) (secretKey : SecretKey)
    (chain : ChainIndex) (input : HashInput) (state : CausalHashState)
    (index : ChainValueIndex)
    (hplan : causalAttackerHashPlan secretKey chain input state = .reveal index) :
    simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((causalAttackerHashQuery secretKey chain input).run state) =
      simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table) (do
        let value ← RevealProbeOracleSimulation.revealQuery index
        let output ← RevealProbeOracleSimulation.liftProbComp
          (Rom.sampleHashOutputWithDigest value)
        pure (output, causalRevealResultState secretKey chain input state
          index value output)) := by
  rw [causalAttackerHashQuery_run, hplan]
  rfl

theorem evalDist_uniformTable_simulate_eagerTrace_causalAttackerHashQuery_reveal_continuation
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState) (index : ChainValueIndex)
    (hplan : causalAttackerHashPlan secretKey chain input state = .reveal index)
    (continuation : (ChainValueIndex → Digest) →
      ((HashOutput × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    𝒟[do
      let table ← $ᵗ (ChainValueIndex → Digest)
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((causalAttackerHashQuery secretKey chain input).run state)).run
      continuation table result] =
    𝒟[do
      let output ← $ᵗ HashOutput
      let base ← $ᵗ (ChainValueIndex → Digest)
      let value := truncateHash output
      let table := Function.update base index value
      continuation table ((output, causalRevealResultState secretKey chain input state
        index value output),
        [RevealProbeOracleSimulation.ObservedAction.reveal index value])] := by
  calc
    𝒟[do
      let table ← $ᵗ (ChainValueIndex → Digest)
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((causalAttackerHashQuery secretKey chain input).run state)).run
      continuation table result] =
        𝒟[do
          let table ← $ᵗ (ChainValueIndex → Digest)
          let result ← (simulateQ
            (RevealProbeOracleSimulation.eagerTraceImpl table) (do
              let value ← RevealProbeOracleSimulation.revealQuery index
              let output ← RevealProbeOracleSimulation.liftProbComp
                (Rom.sampleHashOutputWithDigest value)
              pure (output, causalRevealResultState secretKey chain input state
                index value output))).run
          continuation table result] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro table
      rw [simulate_eagerTrace_causalAttackerHashQuery_reveal_eq
        table secretKey chain input state index hplan]
    _ = _ :=
      evalDist_uniformTable_simulate_eagerTrace_reveal_programmed_continuation
        index
        (fun value output =>
          (output, causalRevealResultState secretKey chain input state
            index value output))
        continuation

theorem evalDist_uniformTable_simulate_eagerTrace_causalAttackerHashQuery_reveal
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState) (index : ChainValueIndex)
    (hplan : causalAttackerHashPlan secretKey chain input state = .reveal index) :
    𝒟[do
      let table ← $ᵗ (ChainValueIndex → Digest)
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((causalAttackerHashQuery secretKey chain input).run state)).run
      pure (table, result)] =
    𝒟[do
      let output ← $ᵗ HashOutput
      let base ← $ᵗ (ChainValueIndex → Digest)
      let value := truncateHash output
      let table := Function.update base index value
      pure (table, ((output, causalRevealResultState secretKey chain input state
        index value output),
        [RevealProbeOracleSimulation.ObservedAction.reveal index value]))] := by
  exact
    evalDist_uniformTable_simulate_eagerTrace_causalAttackerHashQuery_reveal_continuation
      secretKey chain input state index hplan
      (fun table result => pure (table, result))

theorem simulate_eagerTrace_causalAttackerHashQuery_redirect_eq
    (table : ChainValueIndex → Digest) (secretKey : SecretKey)
    (chain : ChainIndex) (input : HashInput) (state : CausalHashState)
    (output : HashOutput)
    (hplan : causalAttackerHashPlan secretKey chain input state = .redirect output) :
    simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((causalAttackerHashQuery secretKey chain input).run state) =
      pure (output,
        { (causalRecordedState secretKey chain input state) with
          cache := (causalRecordedState secretKey chain input state).cache.cacheQuery
            input output }) := by
  rw [causalAttackerHashQuery_run, hplan]
  rfl

theorem simulate_eagerImpl_causalAttackerHashQuery_revealedChain
    (table : ChainValueIndex → Digest) (secretKey : SecretKey)
    (chain : ChainIndex) (epoch : Epoch) (step : ChainStep) (value : Digest)
    (state : CausalHashState)
    (hcache : state.cache
      (Concrete.CacheView.chainInput secretKey.parameter epoch chain step value) = none)
    (hrevealed : state.revealed (epoch, chainStepDigit step) = some value) :
    simulateQ (RevealProbeOracleSimulation.eagerImpl table)
      ((causalAttackerHashQuery secretKey chain
        (Concrete.CacheView.chainInput secretKey.parameter epoch chain step value)).run
          state) =
      (Rom.sampleHashOutputWithDigest
        (table (epoch, chainStepNextDigit step)) >>= fun output =>
        pure (output, causalRevealResultState secretKey chain
          (Concrete.CacheView.chainInput secretKey.parameter epoch chain step value)
          state (epoch, chainStepNextDigit step)
          (table (epoch, chainStepNextDigit step)) output)) := by
  rw [causalAttackerHashQuery_run,
    causalAttackerHashPlan_eq_reveal_chainInput secretKey chain epoch step value
      state hcache hrevealed]
  unfold causalRevealHashQuery
  rw [
    simulateQ_bind, RevealProbeOracleSimulation.simulate_eagerImpl_revealQuery,
    pure_bind, simulateQ_bind,
    RevealProbeOracleSimulation.simulate_eagerImpl_liftProbComp]
  rfl

theorem simulate_eagerImpl_causalAttackerHashQuery_redirect
    (table : ChainValueIndex → Digest) (secretKey : SecretKey)
    (chain : ChainIndex) (input : HashInput) (state : CausalHashState)
    (output : HashOutput)
    (hcache : state.cache input = none)
    (hchain : chainInputProbe? secretKey.parameter chain input = none)
    (htarget : state.keygenCache
      (keygenLeafTargetInput secretKey state.keygenCache input) = some output) :
    simulateQ (RevealProbeOracleSimulation.eagerImpl table)
      ((causalAttackerHashQuery secretKey chain input).run state) =
        pure (output,
          { (causalRecordedState secretKey chain input state) with
            cache := (causalRecordedState secretKey chain input state).cache.cacheQuery
              input output }) := by
  rw [causalAttackerHashQuery_run,
    causalAttackerHashPlan_eq_redirect secretKey chain input state output
      hcache hchain htarget]
  rfl

theorem simulate_eagerImpl_causalAttackerHashQuery_leafRedirect
    (table : ChainValueIndex → Digest) (secretKey : SecretKey)
    (chain : ChainIndex) (epoch : Epoch) (endpoints : ChainIndex → Digest)
    (state : CausalHashState) (output : HashOutput)
    (hcache : state.cache
      (Concrete.CacheView.leafInput secretKey.parameter epoch endpoints) = none)
    (htarget : state.keygenCache
      (Concrete.CacheView.leafInput secretKey.parameter epoch
        (Concrete.CacheReplay.oneTimePublicKey state.keygenCache
          secretKey.parameter secretKey.chainStart epoch)) = some output) :
    simulateQ (RevealProbeOracleSimulation.eagerImpl table)
      ((causalAttackerHashQuery secretKey chain
        (Concrete.CacheView.leafInput secretKey.parameter epoch endpoints)).run state) =
      pure (output,
        { (causalRecordedState secretKey chain
            (Concrete.CacheView.leafInput secretKey.parameter epoch endpoints) state) with
          cache := (causalRecordedState secretKey chain
            (Concrete.CacheView.leafInput secretKey.parameter epoch endpoints) state).cache.cacheQuery
              (Concrete.CacheView.leafInput secretKey.parameter epoch endpoints) output }) := by
  apply simulate_eagerImpl_causalAttackerHashQuery_redirect
  · exact hcache
  · exact chainInputProbe?_leafInput secretKey.parameter chain epoch endpoints
  · rw [keygenLeafTargetInput_leafInput]
    exact htarget


theorem revealFixedChainSignatureOption_run
    (secretKey : SecretKey) (chain : ChainIndex) (request : SignRequest)
    (signatureOption : Option Signature) (state : CausalHashState) :
    (revealFixedChainSignatureOption secretKey chain request signatureOption).run
        state =
      (match signatureOption with
      | none => pure (none, state)
      | some signature =>
          match TargetSum.decodeDigest
              (Concrete.CacheView.encodingHash state.cache secretKey.parameter
                request.epoch (request.message, signature.randomness)) with
          | none => pure (some signature, state)
          | some encoding =>
              let index := (request.epoch, encoding chain)
              do
                let value ← RevealProbeOracleSimulation.revealQuery index
                pure (some (replaceSignatureChainValue signature chain value),
                  state.recordReveal index value)) := by
  cases signatureOption <;> rfl

theorem simulate_eagerTrace_revealFixedChainSignatureOption_some_of_decode
    (table : ChainValueIndex → Digest)
    (secretKey : SecretKey) (chain : ChainIndex) (request : SignRequest)
    (signature : Signature) (state : CausalHashState) (encoding : Encoding)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash state.cache secretKey.parameter
        request.epoch (request.message, signature.randomness)) = some encoding) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      ((revealFixedChainSignatureOption secretKey chain request (some signature)).run
        state)).run =
      pure (((some (replaceSignatureChainValue signature chain
        (table (request.epoch, encoding chain))),
          state.recordReveal (request.epoch, encoding chain)
            (table (request.epoch, encoding chain)))),
        [RevealProbeOracleSimulation.ObservedAction.reveal
          (request.epoch, encoding chain)
          (table (request.epoch, encoding chain))]) := by
  rw [revealFixedChainSignatureOption_run]
  simp only [hdecode]
  rw [simulateQ_bind,
    WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_revealQuery]
  simp

theorem simulate_eagerTrace_revealFixedChainSignatureOption_some_of_agrees
    (table : ChainValueIndex → Digest)
    (secretKey : SecretKey) (chain : ChainIndex) (request : SignRequest)
    (signature : Signature) (state : CausalHashState) (encoding : Encoding)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash state.cache secretKey.parameter
        request.epoch (request.message, signature.randomness)) = some encoding)
    (hagrees : table (request.epoch, encoding chain) =
      signature.chainValue chain) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      ((revealFixedChainSignatureOption secretKey chain request (some signature)).run
        state)).run =
      pure (((some signature,
        state.recordReveal (request.epoch, encoding chain)
          (signature.chainValue chain))),
        [RevealProbeOracleSimulation.ObservedAction.reveal
          (request.epoch, encoding chain) (signature.chainValue chain)]) := by
  rw [simulate_eagerTrace_revealFixedChainSignatureOption_some_of_decode
    table secretKey chain request signature state encoding hdecode,
    hagrees, replaceSignatureChainValue_self]

theorem evalDist_uniformTable_simulate_eagerTrace_revealFixedChainSignatureOption_some_of_decode
    (secretKey : SecretKey) (chain : ChainIndex) (request : SignRequest)
    (signature : Signature) (state : CausalHashState) (encoding : Encoding)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash state.cache secretKey.parameter
        request.epoch (request.message, signature.randomness)) = some encoding)
    (continuation : (ChainValueIndex → Digest) →
      ((Option Signature × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    𝒟[do
      let table ← $ᵗ (ChainValueIndex → Digest)
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((revealFixedChainSignatureOption secretKey chain request (some signature)).run
          state)).run
      continuation table result] =
    𝒟[do
      let value ← $ᵗ Digest
      let base ← $ᵗ (ChainValueIndex → Digest)
      let index := (request.epoch, encoding chain)
      let table := Function.update base index value
      continuation table (((some
        (replaceSignatureChainValue signature chain value),
          state.recordReveal index value)),
        [RevealProbeOracleSimulation.ObservedAction.reveal index value])] := by
  let index : ChainValueIndex := (request.epoch, encoding chain)
  calc
    𝒟[do
      let table ← $ᵗ (ChainValueIndex → Digest)
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((revealFixedChainSignatureOption secretKey chain request (some signature)).run
          state)).run
      continuation table result] =
        𝒟[do
          let table ← $ᵗ (ChainValueIndex → Digest)
          continuation table (((some
            (replaceSignatureChainValue signature chain (table index)),
              state.recordReveal index (table index))),
            [RevealProbeOracleSimulation.ObservedAction.reveal
              index (table index)])] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro table
      rw [simulate_eagerTrace_revealFixedChainSignatureOption_some_of_decode
        table secretKey chain request signature state encoding hdecode]
      simp [index]
    _ = _ :=
      RevealProbeOracleSimulation.evalDist_uniformTable_bind_coordinate_continuation
        index (fun table value =>
          continuation table (((some
            (replaceSignatureChainValue signature chain value),
              state.recordReveal index value)),
            [RevealProbeOracleSimulation.ObservedAction.reveal index value]))

end XmssSecurity
