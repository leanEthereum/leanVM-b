import XmssSecurity.CausalInstalledResampling

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

noncomputable local instance causalInstalledAdversarySampleableChainTable :
    SampleableType (ChainValueIndex → Digest) :=
  SampleableType.ofFintype (ChainValueIndex → Digest)

def causalUniformOutput (n : Nat) (output : Fin (n + 1)) :
    (OracleWorld + SigningSpec).Range (.inl (.inl n)) :=
  output

noncomputable def causalLazyMappedStep
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState) :
    ProbComp ((((OracleWorld + SigningSpec).Range input) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :=
  match input with
  | .inl (.inl n) =>
      (fun output => ((output, state), [])) <$>
        (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))
  | .inl (.inr hashInput) =>
      causalLazyAttackerHashStep secretKey chain hashInput state
  | .inr request =>
      causalLazySigningQuery publicKey secretKey chain request state

theorem causalLazyMappedStep_uniform
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (n : Nat) (state : CausalHashState) :
    causalLazyMappedStep publicKey secretKey chain (.inl (.inl n)) state =
      (fun output => ((causalUniformOutput n output, state), [])) <$>
        (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) := rfl

theorem simulate_eagerTrace_causalUniformImpl
    (table : ChainValueIndex → Digest) (n : Nat)
    (state : CausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      ((causalUniformImpl n).run state)).run =
      (fun output => ((output, state),
        ([] : RevealProbeOracleSimulation.ActionTrace ChainValueIndex))) <$>
          (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) := by
  unfold causalUniformImpl
  rw [OracleComp.liftM_run_StateT, simulateQ_bind]
  simp [RevealProbeOracleSimulation.uniformQuery,
    RevealProbeOracleSimulation.eagerTraceImpl,
    RevealProbeOracleSimulation.eagerImpl,
    RevealProbeOracleSimulation.traceFragment,
    QueryImpl.withTraceAppend_apply, WriterT.run_tell,
    map_eq_bind_pure_comp]

theorem causalMappedAdversaryAfterRealRomImpl_uniform_run
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (n : Nat) (state : CausalHashState) :
    (causalMappedAdversaryAfterRealRomImpl publicKey secretKey chain
      (.inl (.inl n))).run state =
        (causalUniformImpl n).run state := rfl

theorem simulate_eagerTrace_causalMappedAdversaryAfterRealRomImpl_uniform
    (table : ChainValueIndex → Digest)
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (n : Nat) (state : CausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      ((causalMappedAdversaryAfterRealRomImpl publicKey secretKey chain
        (.inl (.inl n))).run state)).run =
      (fun output => ((causalUniformOutput n output, state),
        ([] : RevealProbeOracleSimulation.ActionTrace ChainValueIndex))) <$>
          (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) := by
  exact simulate_eagerTrace_causalUniformImpl table n state

set_option maxRecDepth 100000 in
theorem evalDist_installed_causalMappedAdversaryAfterRealRomImpl_continuation_eq_lazy
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      ((((OracleWorld + SigningSpec).Range input) × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    𝒟[do
      let base ← $ᵗ (ChainValueIndex → Digest)
      let table := causalInstalledTable state base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((causalMappedAdversaryAfterRealRomImpl
          publicKey secretKey chain input).run state)).run
      continuation (causalInstalledTable result.1.2 base) result] =
    𝒟[do
      let result ← causalLazyMappedStep
        publicKey secretKey chain input state
      let base ← $ᵗ (ChainValueIndex → Digest)
      continuation (causalInstalledTable result.1.2 base) result] := by
  rcases input with worldInput | request
  · rcases worldInput with n | hashInput
    · calc
        _ = 𝒟[do
            let base ← $ᵗ (ChainValueIndex → Digest)
            let output ← (liftM (unifSpec.query n) :
              ProbComp (Fin (n + 1)))
            continuation (causalInstalledTable state base)
              ((causalUniformOutput n output, state), [])] := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro base
          simp only
          rw [simulate_eagerTrace_causalMappedAdversaryAfterRealRomImpl_uniform]
          simp [map_eq_bind_pure_comp]
        _ = _ := by
          rw [OracleComp.DeferredSampling.evalDist_bind_comm]
          rw [causalLazyMappedStep_uniform]
          simp [map_eq_bind_pure_comp, bind_assoc]
    · exact
        evalDist_installed_causalAttackerHashQuery_continuation_eq_lazy
          secretKey chain hashInput state continuation
  · exact
      evalDist_installed_causalSigningQueryAfterRealRom_continuation_eq_lazy
        publicKey secretKey chain request state continuation

def attachLazyAttackerAction
    (input : (OracleWorld + SigningSpec).Domain)
    (result : ((((OracleWorld + SigningSpec).Range input) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) :
    ((((OracleWorld + SigningSpec).Range input × AttackerActionTrace) ×
      CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :=
  (((result.1.1, attackerActionFragment input result.1.1), result.1.2), result.2)

def causalAttachLazyAttackerContinuation
    (input : (OracleWorld + SigningSpec).Domain)
    (continuation : (ChainValueIndex → Digest) →
      ((((OracleWorld + SigningSpec).Range input × AttackerActionTrace) ×
        CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α)
    (table : ChainValueIndex → Digest)
    (result : ((((OracleWorld + SigningSpec).Range input) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) : ProbComp α :=
  continuation table (attachLazyAttackerAction input result)

set_option maxRecDepth 100000 in
theorem evalDist_installed_causalMappedAdversaryAfterRealRomImpl_attach_eq_lazy
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      ((((OracleWorld + SigningSpec).Range input × AttackerActionTrace) ×
        CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    𝒟[do
      let base ← $ᵗ (ChainValueIndex → Digest)
      let table := causalInstalledTable state base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((causalMappedAdversaryAfterRealRomImpl
          publicKey secretKey chain input).run state)).run
      causalAttachLazyAttackerContinuation input continuation
        (causalInstalledTable result.1.2 base) result] =
    𝒟[do
      let result ← causalLazyMappedStep
        publicKey secretKey chain input state
      let base ← $ᵗ (ChainValueIndex → Digest)
      causalAttachLazyAttackerContinuation input continuation
        (causalInstalledTable result.1.2 base) result] :=
  evalDist_installed_causalMappedAdversaryAfterRealRomImpl_continuation_eq_lazy
    publicKey secretKey chain input state
      (causalAttachLazyAttackerContinuation input continuation)

noncomputable def causalLazyActionTracedStep
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState) :
    ProbComp ((((OracleWorld + SigningSpec).Range input × AttackerActionTrace) ×
      CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :=
  attachLazyAttackerAction input <$>
    causalLazyMappedStep publicKey secretKey chain input state

set_option maxRecDepth 100000 in
theorem evalDist_installed_causalActionTracedMappedAdversaryAfterRealRomImpl_continuation_eq_lazy
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      ((((OracleWorld + SigningSpec).Range input × AttackerActionTrace) ×
        CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    𝒟[do
      let base ← $ᵗ (ChainValueIndex → Digest)
      let table := causalInstalledTable state base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        (((causalActionTracedMappedAdversaryAfterRealRomImpl
          publicKey secretKey chain input).run).run state)).run
      continuation (causalInstalledTable result.1.2 base) result] =
    𝒟[do
      let result ← causalLazyActionTracedStep
        publicKey secretKey chain input state
      let base ← $ᵗ (ChainValueIndex → Digest)
      continuation (causalInstalledTable result.1.2 base) result] := by
  calc
    _ = 𝒟[do
        let base ← $ᵗ (ChainValueIndex → Digest)
        let result ← causalEagerMappedAtTable
          (causalInstalledTable state base)
          publicKey secretKey chain input state
        causalAttachLazyAttackerContinuation input continuation
          (causalInstalledTable result.1.2 base) result] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro base
      simp only
      change 𝒟[causalEagerActionTracedAtTable
          (causalInstalledTable state base)
          publicKey secretKey chain input state >>= fun result =>
        continuation (causalInstalledTable result.1.2 base) result] = _
      rw [causalEagerActionTracedAtTable_eq_map_mappedAtTable]
      simp [causalAttachLazyAttackerContinuation,
        attachAttackerActionTrace, attachLazyAttackerAction,
        map_eq_bind_pure_comp, bind_assoc]
    _ = 𝒟[do
        let result ← causalLazyMappedStep
          publicKey secretKey chain input state
        let base ← $ᵗ (ChainValueIndex → Digest)
        causalAttachLazyAttackerContinuation input continuation
          (causalInstalledTable result.1.2 base) result] := by
      exact
        evalDist_installed_causalMappedAdversaryAfterRealRomImpl_attach_eq_lazy
          publicKey secretKey chain input state continuation
    _ = _ := by
      unfold causalLazyActionTracedStep
      simp [map_eq_bind_pure_comp, bind_assoc,
        causalAttachLazyAttackerContinuation, attachLazyAttackerAction]

theorem simulate_eagerTrace_causalActionTracedMappedAdversaryAfterRealRomImpl_step_support_installedTable
    (base : ChainValueIndex → Digest)
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState)
    (result : ((((OracleWorld + SigningSpec).Range input ×
      AttackerActionTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl
        (causalInstalledTable state base))
        (((causalActionTracedMappedAdversaryAfterRealRomImpl
          publicKey secretKey chain input).run).run state)).run)) :
    causalInstalledTable result.1.2 base =
      causalInstalledTable state base := by
  let table := causalInstalledTable state base
  have hinitial : CausalInstalledInvariant table state state :=
    ⟨causalRevealsAgree_causalInstalledTable state base,
      CausalRevealsLe.refl state⟩
  have hfinal :=
    simulate_eagerImpl_causalActionTracedMappedAdversaryAfterRealRomImpl_step_support_installedInvariant
      table state publicKey secretKey chain input state result.1 hinitial
        (simulate_eagerTrace_projection_mem_support table _ result hresult)
  exact causalInstalledTable_eq_of_agrees_of_revealsLe
    table base state result.1.2 rfl hfinal.1 hfinal.2

set_option maxRecDepth 100000 in
theorem evalDist_installed_causalActionTracedMappedAdversaryAfterRealRomImpl_fixedContinuation_eq_lazy
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      ((((OracleWorld + SigningSpec).Range input × AttackerActionTrace) ×
        CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    𝒟[do
      let base ← $ᵗ (ChainValueIndex → Digest)
      let table := causalInstalledTable state base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        (((causalActionTracedMappedAdversaryAfterRealRomImpl
          publicKey secretKey chain input).run).run state)).run
      continuation table result] =
    𝒟[do
      let result ← causalLazyActionTracedStep
        publicKey secretKey chain input state
      let base ← $ᵗ (ChainValueIndex → Digest)
      continuation (causalInstalledTable result.1.2 base) result] := by
  calc
    _ = 𝒟[do
        let base ← $ᵗ (ChainValueIndex → Digest)
        let table := causalInstalledTable state base
        let result ← (simulateQ
          (RevealProbeOracleSimulation.eagerTraceImpl table)
          (((causalActionTracedMappedAdversaryAfterRealRomImpl
            publicKey secretKey chain input).run).run state)).run
        continuation (causalInstalledTable result.1.2 base) result] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro base
      simp only
      apply RevealProbeOracleSimulation.evalDist_bind_congr_of_support
      intro result hresult
      rw [simulate_eagerTrace_causalActionTracedMappedAdversaryAfterRealRomImpl_step_support_installedTable
        base publicKey secretKey chain input state result hresult]
    _ = _ :=
      evalDist_installed_causalActionTracedMappedAdversaryAfterRealRomImpl_continuation_eq_lazy
        publicKey secretKey chain input state continuation

end XmssSecurity
