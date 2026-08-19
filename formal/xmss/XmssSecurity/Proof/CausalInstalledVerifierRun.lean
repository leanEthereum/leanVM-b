import XmssSecurity.Proof.CausalInstalledAdversaryRun

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

noncomputable local instance causalInstalledVerifierRunSampleableChainTable :
    SampleableType (ChainValueIndex → Digest) :=
  SampleableType.ofFintype (ChainValueIndex → Digest)

theorem causalMappedAdversaryAfterRealRomImpl_world_run
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : OracleWorld.Domain) (state : CausalHashState) :
    (causalMappedAdversaryAfterRealRomImpl publicKey secretKey chain
      (.inl input)).run state =
        (causalVerifierXmssRomImpl secretKey chain input).run state := by
  cases input <;> rfl

noncomputable def causalLazyVerifierStep
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : OracleWorld.Domain) (state : CausalHashState) :
    ProbComp (((OracleWorld.Range input) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :=
  causalLazyMappedStep publicKey secretKey chain (.inl input) state

noncomputable def causalLazyVerifierImpl
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex) :
    QueryImpl OracleWorld
      (StateT CausalHashState
        (WriterT (RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
          ProbComp)) :=
  fun input state => WriterT.mk
    (causalLazyVerifierStep publicKey secretKey chain input state)

theorem causalLazyVerifierImpl_run
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : OracleWorld.Domain) (state : CausalHashState) :
    ((causalLazyVerifierImpl publicKey secretKey chain input).run state).run =
      causalLazyVerifierStep publicKey secretKey chain input state := rfl

theorem simulate_eagerTrace_causalVerifierXmssRomImpl_step_support_installedTable
    (base : ChainValueIndex → Digest)
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : OracleWorld.Domain) (state : CausalHashState)
    (result : ((OracleWorld.Range input × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl
        (causalInstalledTable state base))
        ((causalVerifierXmssRomImpl secretKey chain input).run state)).run)) :
    causalInstalledTable result.1.2 base =
      causalInstalledTable state base := by
  let table := causalInstalledTable state base
  have hinitial : CausalInstalledInvariant table state state :=
    ⟨causalRevealsAgree_causalInstalledTable state base,
      CausalRevealsLe.refl state⟩
  have hfinal :=
    eagerCausalVerifierInstalledImpl_preserves
      table state secretKey chain input state hinitial result.1
        (simulate_eagerTrace_projection_mem_support table _ result hresult)
  exact causalInstalledTable_eq_of_agrees_of_revealsLe
    table base state result.1.2 rfl hfinal.1 hfinal.2

set_option maxRecDepth 100000 in
theorem evalDist_installed_causalVerifierXmssRomImpl_step_fixedContinuation_eq_lazy
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : OracleWorld.Domain) (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      ((OracleWorld.Range input × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    𝒟[do
      let base ← $ᵗ (ChainValueIndex → Digest)
      let table := causalInstalledTable state base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((causalVerifierXmssRomImpl secretKey chain input).run state)).run
      continuation table result] =
    𝒟[do
      let result ← causalLazyVerifierStep
        publicKey secretKey chain input state
      let base ← $ᵗ (ChainValueIndex → Digest)
      continuation (causalInstalledTable result.1.2 base) result] := by
  calc
    _ = 𝒟[do
        let base ← $ᵗ (ChainValueIndex → Digest)
        let table := causalInstalledTable state base
        let result ← (simulateQ
          (RevealProbeOracleSimulation.eagerTraceImpl table)
          ((causalVerifierXmssRomImpl secretKey chain input).run state)).run
        continuation (causalInstalledTable result.1.2 base) result] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro base
      simp only
      apply RevealProbeOracleSimulation.evalDist_bind_congr_of_support
      intro result hresult
      rw [simulate_eagerTrace_causalVerifierXmssRomImpl_step_support_installedTable
        base publicKey secretKey chain input state result hresult]
    _ = _ := by
      unfold causalLazyVerifierStep
      rw [← causalMappedAdversaryAfterRealRomImpl_world_run
        publicKey secretKey chain input state]
      exact
        evalDist_installed_causalMappedAdversaryAfterRealRomImpl_continuation_eq_lazy
          publicKey secretKey chain (.inl input) state continuation

def appendCausalVerifierResult
    {input : OracleWorld.Domain}
    (handled : ((OracleWorld.Range input × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (rest : ((α × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) :
    ((α × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :=
  ((rest.1.1, rest.1.2), handled.2 ++ rest.2)

noncomputable def causalEagerVerifierRestContinuation
    (secretKey : SecretKey) (chain : ChainIndex)
    {input : OracleWorld.Domain}
    (next : OracleWorld.Range input → OracleComp OracleWorld α)
    (continuation : (ChainValueIndex → Digest) →
      ((α × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp β)
    (table : ChainValueIndex → Digest)
    (handled : ((OracleWorld.Range input × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) : ProbComp β := do
  let rest ← (simulateQ
    (RevealProbeOracleSimulation.eagerTraceImpl table)
    ((simulateQ (causalVerifierXmssRomImpl secretKey chain)
      (next handled.1.1)).run handled.1.2)).run
  continuation table (appendCausalVerifierResult handled rest)

set_option maxRecDepth 100000 in
theorem evalDist_installed_simulate_causalVerifier_eq_lazy
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (computation : OracleComp OracleWorld α) (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      ((α × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp β) :
    𝒟[do
      let base ← $ᵗ (ChainValueIndex → Digest)
      let table := causalInstalledTable state base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((simulateQ (causalVerifierXmssRomImpl secretKey chain)
          computation).run state)).run
      continuation table result] =
    𝒟[do
      let result ← ((simulateQ
        (causalLazyVerifierImpl publicKey secretKey chain)
          computation).run state).run
      let base ← $ᵗ (ChainValueIndex → Digest)
      continuation (causalInstalledTable result.1.2 base) result] := by
  induction computation using OracleComp.inductionOn generalizing state continuation with
  | pure result =>
      simp [simulateQ_pure, WriterT.run_pure]
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, OracleQuery.input_query,
        WriterT.run_bind', StateT.run_bind]
      calc
        _ = 𝒟[do
            let handled ← causalLazyVerifierStep
              publicKey secretKey chain input state
            let base ← $ᵗ (ChainValueIndex → Digest)
            causalEagerVerifierRestContinuation secretKey chain next continuation
              (causalInstalledTable handled.1.2 base) handled] := by
          simpa [causalEagerVerifierRestContinuation,
            appendCausalVerifierResult, map_eq_bind_pure_comp,
            bind_assoc, Function.comp_apply] using
            (evalDist_installed_causalVerifierXmssRomImpl_step_fixedContinuation_eq_lazy
              publicKey secretKey chain input state
                (causalEagerVerifierRestContinuation
                  secretKey chain next continuation))
        _ = 𝒟[do
            let handled ← causalLazyVerifierStep
              publicKey secretKey chain input state
            let rest ← ((simulateQ
              (causalLazyVerifierImpl publicKey secretKey chain)
                (next handled.1.1)).run handled.1.2).run
            let base ← $ᵗ (ChainValueIndex → Digest)
            continuation (causalInstalledTable rest.1.2 base)
              (appendCausalVerifierResult handled rest)] := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro handled
          exact ih handled.1.1 handled.1.2
            (fun table rest => continuation table
              (appendCausalVerifierResult handled rest))
        _ = _ := by
          simp [causalLazyVerifierImpl_run, appendCausalVerifierResult,
            Prod.map, map_eq_bind_pure_comp, bind_assoc,
            Function.comp_apply]

end XmssSecurity
