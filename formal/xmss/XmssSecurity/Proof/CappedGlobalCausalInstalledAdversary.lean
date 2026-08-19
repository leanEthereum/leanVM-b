import XmssSecurity.Proof.CappedGlobalCausalInstalledTableGame
import XmssSecurity.Proof.CappedGlobalCausalActionResampling

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

set_option maxRecDepth 2000000

noncomputable local instance globalCausalInstalledAdversarySampleableChainTable :
    SampleableType (GlobalChainValueIndex → Digest) :=
  SampleableType.ofFintype (GlobalChainValueIndex → Digest)

def globalCausalUniformOutput (n : Nat) (output : Fin (n + 1)) :
    (OracleWorld + SigningSpec).Range (.inl (.inl n)) :=
  output

noncomputable def globalCausalLazyMappedStep
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalCausalHashState) :
    ProbComp ((((OracleWorld + SigningSpec).Range input) ×
      GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :=
  match input with
  | .inl (.inl n) =>
      (fun output => ((output, state), [])) <$>
        (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))
  | .inl (.inr hashInput) =>
      globalCausalLazyAttackerHashStep secretKey hashInput state
  | .inr request =>
      globalCausalLazySigningQuery publicKey secretKey request state

theorem globalCausalLazyMappedStep_uniform
    (publicKey : PublicKey) (secretKey : SecretKey)
    (n : Nat) (state : GlobalCausalHashState) :
    globalCausalLazyMappedStep publicKey secretKey (.inl (.inl n)) state =
      (fun output => ((globalCausalUniformOutput n output, state), [])) <$>
        (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) :=
  rfl

theorem simulate_eagerTrace_globalCausalUniformImpl
    (table : GlobalChainValueIndex → Digest) (n : Nat)
    (state : GlobalCausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      ((globalCausalUniformImpl n).run state)).run =
      (fun output => ((output, state),
        ([] : RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))) <$>
          (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) := by
  unfold globalCausalUniformImpl
  rw [OracleComp.liftM_run_StateT, simulateQ_bind]
  simp [RevealProbeOracleSimulation.uniformQuery,
    RevealProbeOracleSimulation.eagerTraceImpl,
    RevealProbeOracleSimulation.eagerImpl,
    RevealProbeOracleSimulation.traceFragment,
    QueryImpl.withTraceAppend_apply, WriterT.run_tell,
    map_eq_bind_pure_comp]

theorem simulate_eagerTrace_globalCausalMappedAdversaryAfterRealRomImpl_uniform
    (table : GlobalChainValueIndex → Digest)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (n : Nat) (state : GlobalCausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      ((globalCausalMappedAdversaryAfterRealRomImpl publicKey secretKey
        (.inl (.inl n))).run state)).run =
      (fun output => ((globalCausalUniformOutput n output, state),
        ([] : RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))) <$>
          (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) :=
  simulate_eagerTrace_globalCausalUniformImpl table n state

set_option maxRecDepth 100000 in
theorem evalDist_installed_globalCausalMappedAdversaryAfterRealRomImpl_continuation_eq_lazy
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalCausalHashState)
    (continuation : (GlobalChainValueIndex → Digest) →
      ((((OracleWorld + SigningSpec).Range input) × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) → ProbComp α) :
    𝒟[do
      let base ← $ᵗ (GlobalChainValueIndex → Digest)
      let table := globalCausalInstalledTable state base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalMappedAdversaryAfterRealRomImpl
          publicKey secretKey input).run state)).run
      continuation (globalCausalInstalledTable result.1.2 base) result] =
    𝒟[do
      let result ← globalCausalLazyMappedStep
        publicKey secretKey input state
      let base ← $ᵗ (GlobalChainValueIndex → Digest)
      continuation (globalCausalInstalledTable result.1.2 base) result] := by
  rcases input with worldInput | request
  · rcases worldInput with n | hashInput
    · calc
        _ = 𝒟[do
            let base ← $ᵗ (GlobalChainValueIndex → Digest)
            let output ← (liftM (unifSpec.query n) :
              ProbComp (Fin (n + 1)))
            continuation (globalCausalInstalledTable state base)
              ((globalCausalUniformOutput n output, state), [])] := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro base
          simp only
          rw [simulate_eagerTrace_globalCausalMappedAdversaryAfterRealRomImpl_uniform]
          simp [map_eq_bind_pure_comp]
        _ = _ := by
          rw [OracleComp.DeferredSampling.evalDist_bind_comm]
          rw [globalCausalLazyMappedStep_uniform]
          simp [map_eq_bind_pure_comp, bind_assoc]
    · exact
        evalDist_installed_globalCausalAttackerHashQuery_continuation_eq_lazy
          secretKey hashInput state continuation
  · exact
      evalDist_installed_globalCausalSigningQueryAfterRealRom_continuation_eq_lazy
        publicKey secretKey request state continuation

def globalAttachLazyAttackerAction
    (input : (OracleWorld + SigningSpec).Domain)
    (result : ((((OracleWorld + SigningSpec).Range input) ×
      GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) :
    ((((OracleWorld + SigningSpec).Range input × AttackerActionTrace) ×
      GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :=
  (((result.1.1, attackerActionFragment input result.1.1), result.1.2), result.2)

def globalCausalAttachLazyAttackerContinuation
    (input : (OracleWorld + SigningSpec).Domain)
    (continuation : (GlobalChainValueIndex → Digest) →
      ((((OracleWorld + SigningSpec).Range input × AttackerActionTrace) ×
        GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) → ProbComp α)
    (table : GlobalChainValueIndex → Digest)
    (result : ((((OracleWorld + SigningSpec).Range input) ×
      GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) : ProbComp α :=
  continuation table (globalAttachLazyAttackerAction input result)

noncomputable def globalCausalLazyActionTracedStep
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalCausalHashState) :
    ProbComp ((((OracleWorld + SigningSpec).Range input × AttackerActionTrace) ×
      GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :=
  globalAttachLazyAttackerAction input <$>
    globalCausalLazyMappedStep publicKey secretKey input state

set_option maxRecDepth 200000 in
theorem evalDist_installed_globalCausalActionTracedMappedAdversaryAfterRealRomImpl_continuation_eq_lazy
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalCausalHashState)
    (continuation : (GlobalChainValueIndex → Digest) →
      ((((OracleWorld + SigningSpec).Range input × AttackerActionTrace) ×
        GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) → ProbComp α) :
    𝒟[do
      let base ← $ᵗ (GlobalChainValueIndex → Digest)
      let table := globalCausalInstalledTable state base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        (((globalCausalActionTracedMappedAdversaryAfterRealRomImpl
          publicKey secretKey input).run).run state)).run
      continuation (globalCausalInstalledTable result.1.2 base) result] =
    𝒟[do
      let result ← globalCausalLazyActionTracedStep
        publicKey secretKey input state
      let base ← $ᵗ (GlobalChainValueIndex → Digest)
      continuation (globalCausalInstalledTable result.1.2 base) result] := by
  calc
    _ = 𝒟[do
        let base ← $ᵗ (GlobalChainValueIndex → Digest)
        let result ← globalCausalEagerMappedAtTable
          (globalCausalInstalledTable state base)
          publicKey secretKey input state
        globalCausalAttachLazyAttackerContinuation input continuation
          (globalCausalInstalledTable result.1.2 base) result] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro base
      change 𝒟[globalCausalEagerActionTracedAtTable
          (globalCausalInstalledTable state base)
          publicKey secretKey input state >>= fun result =>
        continuation (globalCausalInstalledTable result.1.2 base) result] = _
      rw [globalCausalEagerActionTracedAtTable_eq_map_mappedAtTable]
      simp [globalCausalAttachLazyAttackerContinuation,
        globalAttachAttackerActionTrace, globalAttachLazyAttackerAction,
        map_eq_bind_pure_comp, bind_assoc]
    _ = 𝒟[do
        let result ← globalCausalLazyMappedStep
          publicKey secretKey input state
        let base ← $ᵗ (GlobalChainValueIndex → Digest)
        globalCausalAttachLazyAttackerContinuation input continuation
          (globalCausalInstalledTable result.1.2 base) result] :=
      evalDist_installed_globalCausalMappedAdversaryAfterRealRomImpl_continuation_eq_lazy
        publicKey secretKey input state
          (globalCausalAttachLazyAttackerContinuation input continuation)
    _ = _ := by
      unfold globalCausalLazyActionTracedStep
      simp [map_eq_bind_pure_comp, bind_assoc,
        globalCausalAttachLazyAttackerContinuation,
        globalAttachLazyAttackerAction]

theorem simulate_eagerTrace_globalCausalMappedAdversaryAfterRealRomImpl_support_installedTable
    (base : GlobalChainValueIndex → Digest)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalCausalHashState)
    (result : (((OracleWorld + SigningSpec).Range input ×
      GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
    (hresult : result ∈ support
      (globalCausalEagerMappedAtTable
        (globalCausalInstalledTable state base)
          publicKey secretKey input state)) :
    globalCausalInstalledTable result.1.2 base =
      globalCausalInstalledTable state base := by
  rcases input with worldInput | request
  · rcases worldInput with n | hashInput
    · unfold globalCausalEagerMappedAtTable at hresult
      rw [simulate_eagerTrace_globalCausalMappedAdversaryAfterRealRomImpl_uniform,
          support_map] at hresult
      obtain ⟨output, _houtput, rfl⟩ := hresult
      rfl
    · exact
        simulate_eagerTrace_globalCausalAttackerHashQuery_support_installedTable
          base secretKey hashInput state result hresult
  · exact
      simulate_eagerTrace_globalCausalSigningQueryAfterRealRom_support_installedTable
        base publicKey secretKey request state result hresult

theorem simulate_eagerTrace_globalCausalActionTracedMappedAdversaryAfterRealRomImpl_step_support_installedTable
    (base : GlobalChainValueIndex → Digest)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalCausalHashState)
    (result : ((((OracleWorld + SigningSpec).Range input ×
      AttackerActionTrace) × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
    (hresult : result ∈ support
      (globalCausalEagerActionTracedAtTable
        (globalCausalInstalledTable state base)
          publicKey secretKey input state)) :
    globalCausalInstalledTable result.1.2 base =
      globalCausalInstalledTable state base := by
  rw [globalCausalEagerActionTracedAtTable_eq_map_mappedAtTable,
    support_map] at hresult
  obtain ⟨mapped, hmapped, rfl⟩ := hresult
  exact
    simulate_eagerTrace_globalCausalMappedAdversaryAfterRealRomImpl_support_installedTable
      base publicKey secretKey input state mapped hmapped

set_option maxRecDepth 200000 in
theorem evalDist_installed_globalCausalActionTracedMappedAdversaryAfterRealRomImpl_fixedContinuation_eq_lazy
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalCausalHashState)
    (continuation : (GlobalChainValueIndex → Digest) →
      ((((OracleWorld + SigningSpec).Range input × AttackerActionTrace) ×
        GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) → ProbComp α) :
    𝒟[do
      let base ← $ᵗ (GlobalChainValueIndex → Digest)
      let table := globalCausalInstalledTable state base
      let result ← globalCausalEagerActionTracedAtTable
        table publicKey secretKey input state
      continuation table result] =
    𝒟[do
      let result ← globalCausalLazyActionTracedStep
        publicKey secretKey input state
      let base ← $ᵗ (GlobalChainValueIndex → Digest)
      continuation (globalCausalInstalledTable result.1.2 base) result] := by
  calc
    _ = 𝒟[do
        let base ← $ᵗ (GlobalChainValueIndex → Digest)
        let table := globalCausalInstalledTable state base
        let result ← globalCausalEagerActionTracedAtTable
          table publicKey secretKey input state
        continuation (globalCausalInstalledTable result.1.2 base) result] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro base
      apply RevealProbeOracleSimulation.evalDist_bind_congr_of_support
      intro result hresult
      rw [simulate_eagerTrace_globalCausalActionTracedMappedAdversaryAfterRealRomImpl_step_support_installedTable
        base publicKey secretKey input state result hresult]
    _ = _ :=
      evalDist_installed_globalCausalActionTracedMappedAdversaryAfterRealRomImpl_continuation_eq_lazy
        publicKey secretKey input state continuation

end XmssSecurity.CappedChain
