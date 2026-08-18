import XmssSecurity.CappedGlobalCausalInstalledAdversaryRun

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

noncomputable local instance globalCausalInstalledVerifierRunSampleableTable :
    SampleableType (GlobalChainValueIndex → Digest) :=
  SampleableType.ofFintype (GlobalChainValueIndex → Digest)

theorem globalCausalMappedAdversaryAfterRealRomImpl_world_run
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : OracleWorld.Domain) (state : GlobalCausalHashState) :
    (globalCausalMappedAdversaryAfterRealRomImpl publicKey secretKey
      (.inl input)).run state =
        (globalCausalVerifierXmssRomImpl secretKey input).run state := by
  cases input <;> rfl

noncomputable def globalCausalLazyVerifierStep
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : OracleWorld.Domain) (state : GlobalCausalHashState) :
    ProbComp (((OracleWorld.Range input) × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :=
  globalCausalLazyMappedStep publicKey secretKey (.inl input) state

noncomputable def globalCausalLazyVerifierImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl OracleWorld
      (StateT GlobalCausalHashState
        (WriterT
          (RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
          ProbComp)) :=
  fun input state => WriterT.mk
    (globalCausalLazyVerifierStep publicKey secretKey input state)

theorem globalCausalLazyVerifierImpl_run
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : OracleWorld.Domain) (state : GlobalCausalHashState) :
    ((globalCausalLazyVerifierImpl publicKey secretKey input).run state).run =
      globalCausalLazyVerifierStep publicKey secretKey input state := rfl

theorem simulate_eagerTrace_globalCausalVerifierXmssRomImpl_step_support_installedTable
    (base : GlobalChainValueIndex → Digest)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : OracleWorld.Domain) (state : GlobalCausalHashState)
    (result : ((OracleWorld.Range input × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl
        (globalCausalInstalledTable state base))
        ((globalCausalVerifierXmssRomImpl secretKey input).run state)).run)) :
    globalCausalInstalledTable result.1.2 base =
      globalCausalInstalledTable state base := by
  rw [← globalCausalMappedAdversaryAfterRealRomImpl_world_run
    publicKey secretKey input state] at hresult
  exact
    simulate_eagerTrace_globalCausalMappedAdversaryAfterRealRomImpl_support_installedTable
      base publicKey secretKey (.inl input) state result hresult

set_option maxRecDepth 200000 in
theorem evalDist_installed_globalCausalVerifierXmssRomImpl_step_fixedContinuation_eq_lazy
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : OracleWorld.Domain) (state : GlobalCausalHashState)
    (continuation : (GlobalChainValueIndex → Digest) →
      ((OracleWorld.Range input × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) →
          ProbComp α) :
    𝒟[do
      let base ← $ᵗ (GlobalChainValueIndex → Digest)
      let table := globalCausalInstalledTable state base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalVerifierXmssRomImpl secretKey input).run state)).run
      continuation table result] =
    𝒟[do
      let result ← globalCausalLazyVerifierStep
        publicKey secretKey input state
      let base ← $ᵗ (GlobalChainValueIndex → Digest)
      continuation (globalCausalInstalledTable result.1.2 base) result] := by
  calc
    _ = 𝒟[do
        let base ← $ᵗ (GlobalChainValueIndex → Digest)
        let table := globalCausalInstalledTable state base
        let result ← (simulateQ
          (RevealProbeOracleSimulation.eagerTraceImpl table)
          ((globalCausalVerifierXmssRomImpl secretKey input).run state)).run
        continuation (globalCausalInstalledTable result.1.2 base) result] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro base
      simp only
      apply RevealProbeOracleSimulation.evalDist_bind_congr_of_support
      intro result hresult
      rw [simulate_eagerTrace_globalCausalVerifierXmssRomImpl_step_support_installedTable
        base publicKey secretKey input state result hresult]
    _ = _ := by
      unfold globalCausalLazyVerifierStep
      rw [← globalCausalMappedAdversaryAfterRealRomImpl_world_run
        publicKey secretKey input state]
      exact
        evalDist_installed_globalCausalMappedAdversaryAfterRealRomImpl_continuation_eq_lazy
          publicKey secretKey (.inl input) state continuation

def appendGlobalCausalVerifierResult
    {input : OracleWorld.Domain}
    (handled : ((OracleWorld.Range input × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
    (rest : ((α × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) :
    ((α × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :=
  ((rest.1.1, rest.1.2), handled.2 ++ rest.2)

noncomputable def globalCausalEagerVerifierRestContinuation
    (secretKey : SecretKey) {input : OracleWorld.Domain}
    (next : OracleWorld.Range input → OracleComp OracleWorld α)
    (continuation : (GlobalChainValueIndex → Digest) →
      ((α × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) →
          ProbComp β)
    (table : GlobalChainValueIndex → Digest)
    (handled : ((OracleWorld.Range input × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) :
    ProbComp β := do
  let rest ← (simulateQ
    (RevealProbeOracleSimulation.eagerTraceImpl table)
    ((simulateQ (globalCausalVerifierXmssRomImpl secretKey)
      (next handled.1.1)).run handled.1.2)).run
  continuation table (appendGlobalCausalVerifierResult handled rest)

set_option maxRecDepth 200000 in
theorem evalDist_installed_simulate_globalCausalVerifier_eq_lazy
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp OracleWorld α) (state : GlobalCausalHashState)
    (continuation : (GlobalChainValueIndex → Digest) →
      ((α × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) →
          ProbComp β) :
    𝒟[do
      let base ← $ᵗ (GlobalChainValueIndex → Digest)
      let table := globalCausalInstalledTable state base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((simulateQ (globalCausalVerifierXmssRomImpl secretKey)
          computation).run state)).run
      continuation table result] =
    𝒟[do
      let result ← ((simulateQ
        (globalCausalLazyVerifierImpl publicKey secretKey)
          computation).run state).run
      let base ← $ᵗ (GlobalChainValueIndex → Digest)
      continuation (globalCausalInstalledTable result.1.2 base) result] := by
  induction computation using OracleComp.inductionOn generalizing state continuation with
  | pure result =>
      simp [simulateQ_pure, WriterT.run_pure]
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, OracleQuery.input_query,
        WriterT.run_bind', StateT.run_bind]
      calc
        _ = 𝒟[do
            let handled ← globalCausalLazyVerifierStep
              publicKey secretKey input state
            let base ← $ᵗ (GlobalChainValueIndex → Digest)
            globalCausalEagerVerifierRestContinuation secretKey next continuation
              (globalCausalInstalledTable handled.1.2 base) handled] := by
          simpa [globalCausalEagerVerifierRestContinuation,
            appendGlobalCausalVerifierResult, map_eq_bind_pure_comp,
            bind_assoc, Function.comp_apply] using
            (evalDist_installed_globalCausalVerifierXmssRomImpl_step_fixedContinuation_eq_lazy
              publicKey secretKey input state
                (globalCausalEagerVerifierRestContinuation
                  secretKey next continuation))
        _ = 𝒟[do
            let handled ← globalCausalLazyVerifierStep
              publicKey secretKey input state
            let rest ← ((simulateQ
              (globalCausalLazyVerifierImpl publicKey secretKey)
                (next handled.1.1)).run handled.1.2).run
            let base ← $ᵗ (GlobalChainValueIndex → Digest)
            continuation (globalCausalInstalledTable rest.1.2 base)
              (appendGlobalCausalVerifierResult handled rest)] := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro handled
          exact ih handled.1.1 handled.1.2
            (fun table rest => continuation table
              (appendGlobalCausalVerifierResult handled rest))
        _ = _ := by
          simp [globalCausalLazyVerifierImpl_run,
            appendGlobalCausalVerifierResult, Prod.map,
            map_eq_bind_pure_comp, bind_assoc, Function.comp_apply]

end XmssSecurity.CappedChain
