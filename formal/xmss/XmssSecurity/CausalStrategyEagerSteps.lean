import XmssSecurity.CausalStrategyProgram

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

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

theorem causalAttackerHashPlan_eq_cached
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState) (output : HashOutput)
    (hcache : state.cache input = some output) :
    causalAttackerHashPlan secretKey chain input state = .cached output := by
  simp [causalAttackerHashPlan, hcache]

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
        pure (output,
          { ((causalRecordedState secretKey chain
              (Concrete.CacheView.chainInput secretKey.parameter epoch chain step value)
              state).recordReveal
                (epoch, chainStepNextDigit step)
                (table (epoch, chainStepNextDigit step))) with
            cache := (causalRecordedState secretKey chain
              (Concrete.CacheView.chainInput secretKey.parameter epoch chain step value)
              state).cache.cacheQuery
                (Concrete.CacheView.chainInput secretKey.parameter epoch chain step value)
                output })) := by
  rw [causalAttackerHashQuery_run,
    causalAttackerHashPlan_eq_reveal_chainInput secretKey chain epoch step value
      state hcache hrevealed,
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

end XmssSecurity
