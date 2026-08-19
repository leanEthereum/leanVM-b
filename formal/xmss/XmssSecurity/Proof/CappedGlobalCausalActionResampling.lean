import XmssSecurity.Proof.CappedGlobalCausalAttackerHashResampling
import XmssSecurity.Proof.CappedGlobalCausalSigningResampling

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

noncomputable local instance globalCausalActionSampleableChainTable :
    SampleableType (GlobalChainValueIndex → Digest) :=
  SampleableType.ofFintype (GlobalChainValueIndex → Digest)

noncomputable def globalCausalEagerMappedAtTable
    (table : GlobalChainValueIndex → Digest)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalCausalHashState) :
    ProbComp ((((OracleWorld + SigningSpec).Range input) ×
      GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :=
  (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
    ((globalCausalMappedAdversaryAfterRealRomImpl
      publicKey secretKey input).run state)).run

noncomputable def globalCausalEagerMappedStep
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalCausalHashState) :
    ProbComp ((GlobalChainValueIndex → Digest) ×
      ((((OracleWorld + SigningSpec).Range input) ×
        GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) := do
  let table ← $ᵗ (GlobalChainValueIndex → Digest)
  let result ← globalCausalEagerMappedAtTable
    table publicKey secretKey input state
  pure (table, result)

noncomputable def globalCausalResampledMappedStep
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalCausalHashState) :
    ProbComp ((GlobalChainValueIndex → Digest) ×
      ((((OracleWorld + SigningSpec).Range input) ×
        GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) :=
  match input with
  | .inl (.inl n) =>
      globalCausalEagerMappedStep publicKey secretKey (.inl (.inl n)) state
  | .inl (.inr hashInput) =>
      globalCausalResampledAttackerHashStep secretKey hashInput state
  | .inr request =>
      globalCausalResampledSigningStep publicKey secretKey request state

theorem evalDist_globalCausalEagerMappedStep_eq_resampled
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalCausalHashState) :
    𝒟[globalCausalEagerMappedStep publicKey secretKey input state] =
    𝒟[globalCausalResampledMappedStep publicKey secretKey input state] := by
  rcases input with worldInput | request
  · rcases worldInput with n | hashInput
    · rfl
    · change 𝒟[globalCausalEagerAttackerHashStep
          secretKey hashInput state] =
        𝒟[globalCausalResampledAttackerHashStep
          secretKey hashInput state]
      exact
        evalDist_uniformGlobalTable_simulate_eagerTrace_globalCausalAttackerHashQuery_eq_resampled
          secretKey hashInput state
  · change 𝒟[globalCausalEagerSigningStep
        publicKey secretKey request state] =
      𝒟[globalCausalResampledSigningStep
        publicKey secretKey request state]
    exact evalDist_globalCausalEagerSigningStep_eq_resampled
      publicKey secretKey request state

theorem evalDist_globalCausalEagerMappedStep_continuation_eq_resampled
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalCausalHashState)
    (continuation : (GlobalChainValueIndex → Digest) →
      ((((OracleWorld + SigningSpec).Range input) × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) → ProbComp α) :
    𝒟[globalCausalEagerMappedStep publicKey secretKey input state >>=
      fun result => continuation result.1 result.2] =
    𝒟[globalCausalResampledMappedStep publicKey secretKey input state >>=
      fun result => continuation result.1 result.2] := by
  rw [evalDist_bind, evalDist_globalCausalEagerMappedStep_eq_resampled,
    ← evalDist_bind]

def globalAttachAttackerActionTrace
    (input : (OracleWorld + SigningSpec).Domain)
    (result : ((((OracleWorld + SigningSpec).Range input) ×
      GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) :
    ((((OracleWorld + SigningSpec).Range input × AttackerActionTrace) ×
      GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :=
  (((result.1.1, attackerActionFragment input result.1.1), result.1.2), result.2)

noncomputable def globalCausalEagerActionTracedAtTable
    (table : GlobalChainValueIndex → Digest)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalCausalHashState) :
    ProbComp ((((OracleWorld + SigningSpec).Range input × AttackerActionTrace) ×
      GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :=
  (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
    (((globalCausalActionTracedMappedAdversaryAfterRealRomImpl
      publicKey secretKey input).run).run state)).run

noncomputable def globalCausalEagerActionTracedStep
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalCausalHashState) :
    ProbComp ((GlobalChainValueIndex → Digest) ×
      ((((OracleWorld + SigningSpec).Range input × AttackerActionTrace) ×
        GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) := do
  let table ← $ᵗ (GlobalChainValueIndex → Digest)
  let result ← globalCausalEagerActionTracedAtTable
    table publicKey secretKey input state
  pure (table, result)

noncomputable def globalCausalResampledActionTracedStep
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalCausalHashState) :
    ProbComp ((GlobalChainValueIndex → Digest) ×
      ((((OracleWorld + SigningSpec).Range input × AttackerActionTrace) ×
        GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) :=
  (fun result =>
    (result.1, globalAttachAttackerActionTrace input result.2)) <$>
      globalCausalResampledMappedStep publicKey secretKey input state

theorem globalCausalActionTracedMappedAdversaryAfterRealRomImpl_run_eq_map
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalCausalHashState) :
    ((globalCausalActionTracedMappedAdversaryAfterRealRomImpl
        publicKey secretKey input).run).run state =
      (fun result =>
        ((result.1, attackerActionFragment input result.1), result.2)) <$>
        ((globalCausalMappedAdversaryAfterRealRomImpl
          publicKey secretKey input).run state) := by
  unfold globalCausalActionTracedMappedAdversaryAfterRealRomImpl
  rw [QueryImpl.withTraceAppend_apply, WriterT.run_bind',
    WriterT.run_monadLift', StateT.run_bind]
  simp [WriterT.run_tell, map_eq_bind_pure_comp]

theorem globalCausalEagerActionTracedAtTable_eq_map_mappedAtTable
    (table : GlobalChainValueIndex → Digest)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalCausalHashState) :
    globalCausalEagerActionTracedAtTable
        table publicKey secretKey input state =
      globalAttachAttackerActionTrace input <$>
        globalCausalEagerMappedAtTable
          table publicKey secretKey input state := by
  unfold globalCausalEagerActionTracedAtTable
    globalCausalEagerMappedAtTable
  rw [globalCausalActionTracedMappedAdversaryAfterRealRomImpl_run_eq_map,
    simulateQ_map, WriterT.run_map']
  congr 1

theorem globalCausalEagerActionTracedStep_eq_map_mappedStep
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalCausalHashState) :
    globalCausalEagerActionTracedStep publicKey secretKey input state =
      (fun result =>
        (result.1, globalAttachAttackerActionTrace input result.2)) <$>
        globalCausalEagerMappedStep publicKey secretKey input state := by
  unfold globalCausalEagerActionTracedStep globalCausalEagerMappedStep
  simp_rw [globalCausalEagerActionTracedAtTable_eq_map_mappedAtTable]
  simp [map_eq_bind_pure_comp, bind_assoc]

theorem evalDist_globalCausalEagerActionTracedStep_eq_resampled
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalCausalHashState) :
    𝒟[globalCausalEagerActionTracedStep
      publicKey secretKey input state] =
    𝒟[globalCausalResampledActionTracedStep
      publicKey secretKey input state] := by
  calc
    𝒟[globalCausalEagerActionTracedStep
        publicKey secretKey input state] =
        𝒟[(fun result =>
          (result.1, globalAttachAttackerActionTrace input result.2)) <$>
            globalCausalEagerMappedStep publicKey secretKey input state] := by
      rw [globalCausalEagerActionTracedStep_eq_map_mappedStep]
    _ = 𝒟[globalCausalResampledActionTracedStep
        publicKey secretKey input state] := by
      unfold globalCausalResampledActionTracedStep
      rw [evalDist_map, evalDist_globalCausalEagerMappedStep_eq_resampled,
        ← evalDist_map]

theorem evalDist_globalCausalEagerActionTracedStep_continuation_eq_resampled
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalCausalHashState)
    (continuation : (GlobalChainValueIndex → Digest) →
      ((((OracleWorld + SigningSpec).Range input × AttackerActionTrace) ×
        GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) → ProbComp α) :
    𝒟[globalCausalEagerActionTracedStep
        publicKey secretKey input state >>= fun result =>
      continuation result.1 result.2] =
    𝒟[globalCausalResampledActionTracedStep
        publicKey secretKey input state >>= fun result =>
      continuation result.1 result.2] := by
  rw [evalDist_bind,
    evalDist_globalCausalEagerActionTracedStep_eq_resampled,
    ← evalDist_bind]

end XmssSecurity.CappedChain
