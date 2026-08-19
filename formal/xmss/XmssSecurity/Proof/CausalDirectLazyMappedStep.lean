import XmssSecurity.Proof.CausalDirectLazySigning
import XmssSecurity.Proof.CausalInstalledAdversary

open OracleComp OracleSpec

namespace XmssSecurity

noncomputable local instance directLazyMappedStepSampleableChainTable :
    SampleableType (ChainValueIndex → Digest) :=
  SampleableType.ofFintype (ChainValueIndex → Digest)

def DirectActionOutput : (OracleWorld + SigningSpec).Domain → Type
  | .inl (.inl n) => Fin (n + 1)
  | .inl (.inr _) => HashOutput
  | .inr _ => Option Signature

theorem directActionOutput_eq_range
    (input : (OracleWorld + SigningSpec).Domain) :
    DirectActionOutput input = (OracleWorld + SigningSpec).Range input := by
  rcases input with (n | input) | request <;> rfl

def castDirectActionOutput
    (input : (OracleWorld + SigningSpec).Domain) :
    DirectActionOutput input → (OracleWorld + SigningSpec).Range input :=
  match input with
  | .inl (.inl _) => id
  | .inl (.inr _) => id
  | .inr _ => id

def castDirectActionResult
    (input : (OracleWorld + SigningSpec).Domain)
    (result : (DirectActionOutput input × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :
    (((OracleWorld + SigningSpec).Range input × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :=
  ((castDirectActionOutput input result.1.1, result.1.2), result.2)

@[simp]
theorem castDirectActionResult_uniform
    (n : Nat)
    (result : (Fin (n + 1) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :
    castDirectActionResult (Sum.inl (Sum.inl n)) result = result := rfl

@[simp]
theorem castDirectActionResult_hash
    (input : HashInput)
    (result : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :
    castDirectActionResult (Sum.inl (Sum.inr input)) result = result := rfl

@[simp]
theorem castDirectActionResult_signing
    (request : SignRequest)
    (result : (Option Signature × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :
    castDirectActionResult (Sum.inr request) result = result := rfl

theorem castDirectActionResult_uniform_eq_id (n : Nat) :
    castDirectActionResult (Sum.inl (Sum.inl n)) = id := by
  funext result
  exact castDirectActionResult_uniform n result

theorem castDirectActionResult_hash_eq_id (input : HashInput) :
    castDirectActionResult (Sum.inl (Sum.inr input)) = id := by
  funext result
  exact castDirectActionResult_hash input result

theorem castDirectActionResult_signing_eq_id (request : SignRequest) :
    castDirectActionResult (Sum.inr request) = id := by
  funext result
  exact castDirectActionResult_signing request result

noncomputable def filteredDirectEagerRawMappedStep
    (table : ChainValueIndex → Digest)
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState) :
    ProbComp ((DirectActionOutput input × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :=
  match input with
  | .inl (.inl n) =>
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((causalUniformImpl n).run state)).run
  | .inl (.inr hashInput) =>
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredProbingAttackerHashQueryAt keyView.secretKey selected hashInput
          state (chainInputProbe? keyView.secretKey.parameter selected
            hashInput))).run
  | .inr request =>
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredCausalSigningQuery keyView selected request state)).run

noncomputable def filteredDirectLazyRawMappedStep
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState) :
    ProbComp ((DirectActionOutput input × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :=
  match input with
  | .inl (.inl n) =>
      (fun output => ((output, state), [])) <$>
        (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))
  | .inl (.inr hashInput) =>
      filteredDirectLazyHashStep keyView.secretKey selected hashInput state
  | .inr request =>
      filteredDirectLazySigningQuery keyView selected request state

noncomputable def filteredDirectLazyMappedStep
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState) :
    ProbComp ((((OracleWorld + SigningSpec).Range input × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) :=
  castDirectActionResult input <$>
    filteredDirectLazyRawMappedStep keyView selected input state

set_option maxRecDepth 100000 in
theorem evalDist_installed_causalUniform_raw_fixedContinuation_eq_lazy
    (n : Nat) (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      ((Fin (n + 1) × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    𝒟[do
      let base ← $ᵗ (ChainValueIndex → Digest)
      let table := causalInstalledTable state base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((causalUniformImpl n).run state)).run
      continuation table result] =
    𝒟[do
      let result ← (fun output => ((output, state), [])) <$>
        (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))
      let base ← $ᵗ (ChainValueIndex → Digest)
      continuation (causalInstalledTable result.1.2 base) result] := by
  calc
    _ = 𝒟[do
        let base ← $ᵗ (ChainValueIndex → Digest)
        let output ← (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))
        continuation (causalInstalledTable state base) ((output, state), [])] := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro base
      simp_rw [simulate_eagerTrace_causalUniformImpl]
      simp [map_eq_bind_pure_comp]
    _ = _ := by
      rw [OracleComp.DeferredSampling.evalDist_bind_comm]
      simp [map_eq_bind_pure_comp, bind_assoc]

set_option maxHeartbeats 2000 in
set_option maxRecDepth 100000 in
theorem evalDist_installed_filteredDirectRawMappedStep_fixedContinuation_eq_lazy
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      ((DirectActionOutput input × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    𝒟[do
      let base ← $ᵗ (ChainValueIndex → Digest)
      let table := causalInstalledTable state base
      let result ← filteredDirectEagerRawMappedStep table keyView selected input state
      continuation table result] =
    𝒟[do
      let result ← filteredDirectLazyRawMappedStep keyView selected input state
      let base ← $ᵗ (ChainValueIndex → Digest)
      continuation (causalInstalledTable result.1.2 base) result] := by
  rcases input with (n | hashInput) | request
  · exact evalDist_installed_causalUniform_raw_fixedContinuation_eq_lazy
      n state continuation
  · exact
      evalDist_installed_filteredProbingAttackerHashQueryAt_fixedContinuation_eq_lazy
        keyView.secretKey selected hashInput state
          (chainInputProbe? keyView.secretKey.parameter selected hashInput)
            continuation
  · exact evalDist_installed_filteredCausalSigningQuery_fixedContinuation_eq_lazy
      keyView selected request state continuation

end XmssSecurity
