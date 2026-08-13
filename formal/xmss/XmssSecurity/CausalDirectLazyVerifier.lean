import XmssSecurity.CausalDirectStepCoupling
import XmssSecurity.CausalInstalledAdversary

open OracleComp OracleSpec

namespace XmssSecurity

noncomputable local instance directLazyVerifierSampleableChainTable :
    SampleableType (ChainValueIndex → Digest) :=
  SampleableType.ofFintype (ChainValueIndex → Digest)

noncomputable def filteredDirectLazyVerifierStep
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (input : OracleWorld.Domain) (state : CausalHashState) :
    ProbComp ((OracleWorld.Range input × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :=
  match input with
  | .inl n =>
      (fun output => ((output, state), [])) <$>
        (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))
  | .inr hashInput =>
      filteredDirectLazyHashStep keyView.secretKey selected hashInput state

noncomputable def filteredDirectLazyVerifierImpl
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex) :
    QueryImpl OracleWorld
      (StateT CausalHashState
        (WriterT (RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
          ProbComp)) :=
  fun input state => WriterT.mk
    (filteredDirectLazyVerifierStep keyView selected input state)

theorem filteredDirectLazyVerifierImpl_run
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (input : OracleWorld.Domain) (state : CausalHashState) :
    ((filteredDirectLazyVerifierImpl keyView selected input).run state).run =
      filteredDirectLazyVerifierStep keyView selected input state := rfl

def appendFilteredDirectVerifierResult
    {input : OracleWorld.Domain}
    (handled : ((OracleWorld.Range input × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (rest : ((α × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) :
    ((α × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :=
  ((rest.1.1, rest.1.2), handled.2 ++ rest.2)

set_option maxRecDepth 100000 in
theorem evalDist_installed_filteredDirectVerifier_uniform_fixedContinuation_eq_lazy
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

set_option maxRecDepth 100000 in
theorem evalDist_installed_filteredDirectVerifier_hash_fixedContinuation_eq_lazy
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (input : HashInput) (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      ((HashOutput × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    𝒟[do
      let base ← $ᵗ (ChainValueIndex → Digest)
      let table := causalInstalledTable state base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredProbingAttackerHashQueryAt keyView.secretKey selected input state
          (chainInputProbe? keyView.secretKey.parameter selected input))).run
      continuation table result] =
    𝒟[do
      let result ← filteredDirectLazyHashStep keyView.secretKey selected input state
      let base ← $ᵗ (ChainValueIndex → Digest)
      continuation (causalInstalledTable result.1.2 base) result] := by
  unfold filteredDirectLazyHashStep
  exact
    evalDist_installed_filteredProbingAttackerHashQueryAt_fixedContinuation_eq_lazy
      keyView.secretKey selected input state
        (chainInputProbe? keyView.secretKey.parameter selected input) continuation

noncomputable def filteredDirectEagerVerifierRestContinuation
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
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
    ((simulateQ (filteredDirectVerifierImpl keyView selected)
      (next handled.1.1)).run handled.1.2)).run
  continuation table (appendFilteredDirectVerifierResult handled rest)

set_option maxHeartbeats 20000 in
set_option maxRecDepth 100000 in
theorem evalDist_installed_filteredDirectVerifier_step_fixedContinuation_eq_lazy
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (input : OracleWorld.Domain)
    (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      ((OracleWorld.Range input × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp β) :
    𝒟[do
      let base ← $ᵗ (ChainValueIndex → Digest)
      let table := causalInstalledTable state base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((filteredDirectVerifierImpl keyView selected input).run state)).run
      continuation table result] =
    𝒟[do
      let result ← filteredDirectLazyVerifierStep
        keyView selected input state
      let base ← $ᵗ (ChainValueIndex → Digest)
      continuation (causalInstalledTable result.1.2 base) result] := by
  cases input with
  | inl n =>
      change
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
          continuation (causalInstalledTable result.1.2 base) result]
      exact evalDist_installed_filteredDirectVerifier_uniform_fixedContinuation_eq_lazy
        n state continuation
  | inr hashInput =>
      rw [filteredDirectVerifierImpl.eq_2,
        filteredDirectLazyVerifierStep.eq_2, StateT.run_mk]
      exact
        evalDist_installed_filteredDirectVerifier_hash_fixedContinuation_eq_lazy
          keyView selected hashInput state continuation

set_option maxRecDepth 100000 in
theorem evalDist_installed_simulate_filteredDirectVerifier_query_rest_eq_lazy
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld α)
    (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      ((α × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp β)
    (ih : ∀ (output : OracleWorld.Range input) (state : CausalHashState)
      (continuation : (ChainValueIndex → Digest) →
        ((α × CausalHashState) ×
          RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp β),
      𝒟[do
        let base ← $ᵗ (ChainValueIndex → Digest)
        let table := causalInstalledTable state base
        let result ← (simulateQ
          (RevealProbeOracleSimulation.eagerTraceImpl table)
          ((simulateQ (filteredDirectVerifierImpl keyView selected)
            (next output)).run state)).run
        continuation table result] =
      𝒟[do
        let result ← ((simulateQ
          (filteredDirectLazyVerifierImpl keyView selected)
            (next output)).run state).run
        let base ← $ᵗ (ChainValueIndex → Digest)
        continuation (causalInstalledTable result.1.2 base) result]) :
    𝒟[do
      let handled ← filteredDirectLazyVerifierStep
        keyView selected input state
      let base ← $ᵗ (ChainValueIndex → Digest)
      filteredDirectEagerVerifierRestContinuation keyView selected next
        continuation (causalInstalledTable handled.1.2 base) handled] =
    𝒟[do
      let handled ← filteredDirectLazyVerifierStep
        keyView selected input state
      let rest ← ((simulateQ
        (filteredDirectLazyVerifierImpl keyView selected)
          (next handled.1.1)).run handled.1.2).run
      let base ← $ᵗ (ChainValueIndex → Digest)
      continuation (causalInstalledTable rest.1.2 base)
        (appendFilteredDirectVerifierResult handled rest)] := by
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro handled
  exact ih handled.1.1 handled.1.2
    (fun table rest => continuation table
      (appendFilteredDirectVerifierResult handled rest))

set_option maxRecDepth 100000 in
theorem evalDist_filteredDirectLazyVerifier_query_bind
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld α)
    (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      ((α × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp β) :
    𝒟[do
      let handled ← filteredDirectLazyVerifierStep
        keyView selected input state
      let rest ← ((simulateQ
        (filteredDirectLazyVerifierImpl keyView selected)
          (next handled.1.1)).run handled.1.2).run
      let base ← $ᵗ (ChainValueIndex → Digest)
      continuation (causalInstalledTable rest.1.2 base)
        (appendFilteredDirectVerifierResult handled rest)] =
    𝒟[do
      let result ← ((simulateQ
        (filteredDirectLazyVerifierImpl keyView selected)
          (liftM (OracleSpec.query input) >>= next)).run state).run
      let base ← $ᵗ (ChainValueIndex → Digest)
      continuation (causalInstalledTable result.1.2 base) result] := by
  simp [filteredDirectLazyVerifierImpl_run,
    appendFilteredDirectVerifierResult,
    map_eq_bind_pure_comp, bind_assoc, Function.comp_apply]

set_option maxHeartbeats 20000 in
set_option maxRecDepth 100000 in
theorem evalDist_installed_simulate_filteredDirectVerifier_query_bind_eq_lazy
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld α)
    (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      ((α × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp β)
    (ih : ∀ (output : OracleWorld.Range input) (state : CausalHashState)
      (continuation : (ChainValueIndex → Digest) →
        ((α × CausalHashState) ×
          RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp β),
      𝒟[do
        let base ← $ᵗ (ChainValueIndex → Digest)
        let table := causalInstalledTable state base
        let result ← (simulateQ
          (RevealProbeOracleSimulation.eagerTraceImpl table)
          ((simulateQ (filteredDirectVerifierImpl keyView selected)
            (next output)).run state)).run
        continuation table result] =
      𝒟[do
        let result ← ((simulateQ
          (filteredDirectLazyVerifierImpl keyView selected)
            (next output)).run state).run
        let base ← $ᵗ (ChainValueIndex → Digest)
        continuation (causalInstalledTable result.1.2 base) result]) :
    𝒟[do
      let base ← $ᵗ (ChainValueIndex → Digest)
      let table := causalInstalledTable state base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((simulateQ (filteredDirectVerifierImpl keyView selected)
          (liftM (OracleSpec.query input) >>= next)).run state)).run
      continuation table result] =
    𝒟[do
      let result ← ((simulateQ
        (filteredDirectLazyVerifierImpl keyView selected)
          (liftM (OracleSpec.query input) >>= next)).run state).run
      let base ← $ᵗ (ChainValueIndex → Digest)
      continuation (causalInstalledTable result.1.2 base) result] := by
  calc
    _ = 𝒟[do
        let handled ← filteredDirectLazyVerifierStep
          keyView selected input state
        let base ← $ᵗ (ChainValueIndex → Digest)
        filteredDirectEagerVerifierRestContinuation keyView selected next
          continuation (causalInstalledTable handled.1.2 base) handled] :=
      by
        simpa [filteredDirectEagerVerifierRestContinuation,
          appendFilteredDirectVerifierResult, map_eq_bind_pure_comp,
          bind_assoc, Function.comp_apply] using
          (evalDist_installed_filteredDirectVerifier_step_fixedContinuation_eq_lazy
            keyView selected input state
              (filteredDirectEagerVerifierRestContinuation
                keyView selected next continuation))
    _ = 𝒟[do
        let handled ← filteredDirectLazyVerifierStep
          keyView selected input state
        let rest ← ((simulateQ
          (filteredDirectLazyVerifierImpl keyView selected)
            (next handled.1.1)).run handled.1.2).run
        let base ← $ᵗ (ChainValueIndex → Digest)
        continuation (causalInstalledTable rest.1.2 base)
          (appendFilteredDirectVerifierResult handled rest)] :=
      evalDist_installed_simulate_filteredDirectVerifier_query_rest_eq_lazy
        keyView selected input next state continuation ih
    _ = _ := evalDist_filteredDirectLazyVerifier_query_bind
      keyView selected input next state continuation

set_option maxRecDepth 100000 in
theorem evalDist_installed_simulate_filteredDirectVerifier_eq_lazy
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (computation : OracleComp OracleWorld α) (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      ((α × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp β) :
    𝒟[do
      let base ← $ᵗ (ChainValueIndex → Digest)
      let table := causalInstalledTable state base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((simulateQ (filteredDirectVerifierImpl keyView selected)
          computation).run state)).run
      continuation table result] =
    𝒟[do
      let result ← ((simulateQ
        (filteredDirectLazyVerifierImpl keyView selected)
          computation).run state).run
      let base ← $ᵗ (ChainValueIndex → Digest)
      continuation (causalInstalledTable result.1.2 base) result] := by
  induction computation using OracleComp.inductionOn generalizing state continuation with
  | pure result =>
      simp [simulateQ_pure, WriterT.run_pure]
  | query_bind input next ih =>
      exact evalDist_installed_simulate_filteredDirectVerifier_query_bind_eq_lazy
        keyView selected input next state continuation ih

end XmssSecurity
