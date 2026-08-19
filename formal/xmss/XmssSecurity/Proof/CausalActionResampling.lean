import XmssSecurity.Proof.CausalAttackerHashResampling

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

noncomputable local instance causalActionSampleableChainTable :
    SampleableType (ChainValueIndex → Digest) :=
  SampleableType.ofFintype (ChainValueIndex → Digest)

noncomputable def causalEagerMappedAtTable
    (table : ChainValueIndex → Digest)
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState) :
    ProbComp ((((OracleWorld + SigningSpec).Range input) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :=
  (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
    ((causalMappedAdversaryAfterRealRomImpl
      publicKey secretKey chain input).run state)).run

noncomputable def causalEagerMappedStep
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState) :
    ProbComp ((ChainValueIndex → Digest) ×
      ((((OracleWorld + SigningSpec).Range input) × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) := do
  let table ← $ᵗ (ChainValueIndex → Digest)
  let result ← causalEagerMappedAtTable
    table publicKey secretKey chain input state
  pure (table, result)

noncomputable def causalResampledMappedStep
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState) :
    ProbComp ((ChainValueIndex → Digest) ×
      ((((OracleWorld + SigningSpec).Range input) × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) :=
  match input with
  | .inl (.inl n) =>
      causalEagerMappedStep publicKey secretKey chain (.inl (.inl n)) state
  | .inl (.inr hashInput) =>
      causalResampledAttackerHashStep secretKey chain hashInput state
  | .inr request =>
      causalResampledSigningStep publicKey secretKey chain request state

theorem evalDist_causalEagerMappedStep_eq_resampled
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState) :
    𝒟[causalEagerMappedStep publicKey secretKey chain input state] =
    𝒟[causalResampledMappedStep publicKey secretKey chain input state] := by
  rcases input with worldInput | request
  · rcases worldInput with n | hashInput
    · rfl
    · change 𝒟[causalEagerAttackerHashStep
          secretKey chain hashInput state] =
        𝒟[causalResampledAttackerHashStep
          secretKey chain hashInput state]
      exact
        evalDist_uniformTable_simulate_eagerTrace_causalAttackerHashQuery_eq_resampled
          secretKey chain hashInput state
  · change 𝒟[causalEagerSigningStep
        publicKey secretKey chain request state] =
      𝒟[causalResampledSigningStep
        publicKey secretKey chain request state]
    exact evalDist_causalEagerSigningStep_eq_resampled
      publicKey secretKey chain request state

theorem evalDist_causalEagerMappedStep_continuation_eq_resampled
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      ((((OracleWorld + SigningSpec).Range input) × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    𝒟[causalEagerMappedStep publicKey secretKey chain input state >>=
      fun result => continuation result.1 result.2] =
    𝒟[causalResampledMappedStep publicKey secretKey chain input state >>=
      fun result => continuation result.1 result.2] := by
  rw [evalDist_bind, evalDist_causalEagerMappedStep_eq_resampled,
    ← evalDist_bind]

theorem mem_support_causalEagerMappedStep_iff_resampled
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState)
    (result : (ChainValueIndex → Digest) ×
      ((((OracleWorld + SigningSpec).Range input) × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) :
    result ∈ support
        (causalEagerMappedStep publicKey secretKey chain input state) ↔
      result ∈ support
        (causalResampledMappedStep publicKey secretKey chain input state) :=
  mem_support_iff_of_evalDist_eq
    (evalDist_causalEagerMappedStep_eq_resampled
      publicKey secretKey chain input state) result

def attachAttackerActionTrace
    (input : (OracleWorld + SigningSpec).Domain)
    (result : ((((OracleWorld + SigningSpec).Range input) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) :
    ((((OracleWorld + SigningSpec).Range input × AttackerActionTrace) ×
      CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :=
  (((result.1.1, attackerActionFragment input result.1.1), result.1.2), result.2)

noncomputable def causalEagerActionTracedAtTable
    (table : ChainValueIndex → Digest)
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState) :
    ProbComp ((((OracleWorld + SigningSpec).Range input × AttackerActionTrace) ×
      CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :=
  (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
    (((causalActionTracedMappedAdversaryAfterRealRomImpl
      publicKey secretKey chain input).run).run state)).run

noncomputable def causalEagerActionTracedStep
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState) :
    ProbComp ((ChainValueIndex → Digest) ×
      ((((OracleWorld + SigningSpec).Range input × AttackerActionTrace) ×
        CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) := do
  let table ← $ᵗ (ChainValueIndex → Digest)
  let result ← causalEagerActionTracedAtTable
    table publicKey secretKey chain input state
  pure (table, result)

noncomputable def causalResampledActionTracedStep
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState) :
    ProbComp ((ChainValueIndex → Digest) ×
      ((((OracleWorld + SigningSpec).Range input × AttackerActionTrace) ×
        CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) :=
  (fun result => (result.1, attachAttackerActionTrace input result.2)) <$>
    causalResampledMappedStep publicKey secretKey chain input state

theorem causalActionTracedMappedAdversaryAfterRealRomImpl_run_eq_map
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState) :
    ((causalActionTracedMappedAdversaryAfterRealRomImpl
        publicKey secretKey chain input).run).run state =
      (fun result =>
        ((result.1, attackerActionFragment input result.1), result.2)) <$>
        ((causalMappedAdversaryAfterRealRomImpl
          publicKey secretKey chain input).run state) := by
  unfold causalActionTracedMappedAdversaryAfterRealRomImpl
  rw [QueryImpl.withTraceAppend_apply, WriterT.run_bind',
    WriterT.run_monadLift', StateT.run_bind]
  simp [WriterT.run_tell, map_eq_bind_pure_comp]

theorem causalEagerActionTracedAtTable_eq_map_mappedAtTable
    (table : ChainValueIndex → Digest)
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState) :
    causalEagerActionTracedAtTable
        table publicKey secretKey chain input state =
      attachAttackerActionTrace input <$>
        causalEagerMappedAtTable
          table publicKey secretKey chain input state := by
  unfold causalEagerActionTracedAtTable causalEagerMappedAtTable
  rw [causalActionTracedMappedAdversaryAfterRealRomImpl_run_eq_map,
    simulateQ_map, WriterT.run_map']
  congr 1

theorem causalEagerActionTracedStep_eq_map_mappedStep
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState) :
    causalEagerActionTracedStep publicKey secretKey chain input state =
      (fun result => (result.1, attachAttackerActionTrace input result.2)) <$>
        causalEagerMappedStep publicKey secretKey chain input state := by
  unfold causalEagerActionTracedStep causalEagerMappedStep
  simp_rw [causalEagerActionTracedAtTable_eq_map_mappedAtTable]
  simp [map_eq_bind_pure_comp, bind_assoc]

theorem evalDist_causalEagerActionTracedStep_eq_resampled
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState) :
    𝒟[causalEagerActionTracedStep
      publicKey secretKey chain input state] =
    𝒟[causalResampledActionTracedStep
      publicKey secretKey chain input state] := by
  calc
    𝒟[causalEagerActionTracedStep
        publicKey secretKey chain input state] =
        𝒟[(fun result =>
          (result.1, attachAttackerActionTrace input result.2)) <$>
            causalEagerMappedStep publicKey secretKey chain input state] := by
      rw [causalEagerActionTracedStep_eq_map_mappedStep]
    _ = 𝒟[causalResampledActionTracedStep
        publicKey secretKey chain input state] := by
      unfold causalResampledActionTracedStep
      rw [evalDist_map, evalDist_causalEagerMappedStep_eq_resampled,
        ← evalDist_map]

theorem evalDist_causalEagerActionTracedStep_continuation_eq_resampled
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      ((((OracleWorld + SigningSpec).Range input × AttackerActionTrace) ×
        CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    𝒟[causalEagerActionTracedStep
        publicKey secretKey chain input state >>= fun result =>
      continuation result.1 result.2] =
    𝒟[causalResampledActionTracedStep
        publicKey secretKey chain input state >>= fun result =>
      continuation result.1 result.2] := by
  rw [evalDist_bind, evalDist_causalEagerActionTracedStep_eq_resampled,
    ← evalDist_bind]

end XmssSecurity
