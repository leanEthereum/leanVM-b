import XmssSecurity.CausalDirectStepCoupling

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
theorem evalDist_installed_filteredDirectVerifier_step_continuation_eq_lazy
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (input : OracleWorld.Domain) (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      ((OracleWorld.Range input × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    𝓓[do
      let base ← $ᵗ (ChainValueIndex → Digest)
      let table := causalInstalledTable state base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((filteredDirectVerifierImpl keyView selected input).run state)).run
      continuation (causalInstalledTable result.1.2 base) result] =
    𝓓[do
      let result ← filteredDirectLazyVerifierStep
        keyView selected input state
      let base ← $ᵗ (ChainValueIndex → Digest)
      continuation (causalInstalledTable result.1.2 base) result] := by
  rcases input with n | hashInput
  · calc
      _ = 𝓓[do
          let base ← $ᵗ (ChainValueIndex → Digest)
          let output ← (liftM (unifSpec.query n) :
            ProbComp (Fin (n + 1)))
          continuation (causalInstalledTable state base)
            ((output, state), [])] := by
        apply OracleComp.DeferredSampling.evalDist_bind_congr_left
        intro base
        simp only [filteredDirectVerifierImpl]
        rw [simulate_eagerTrace_causalUniformImpl]
        simp [map_eq_bind_pure_comp]
      _ = _ := by
        rw [OracleComp.DeferredSampling.evalDist_bind_comm]
        simp [filteredDirectLazyVerifierStep, map_eq_bind_pure_comp,
          bind_assoc]
  · exact
      evalDist_installed_filteredProbingAttackerHashQuery_continuation_eq_lazy
        keyView.secretKey selected hashInput state continuation

set_option maxRecDepth 100000 in
theorem evalDist_installed_simulate_filteredDirectVerifier_eq_lazy
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (computation : OracleComp OracleWorld α) (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      ((α × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp β) :
    𝓓[do
      let base ← $ᵗ (ChainValueIndex → Digest)
      let table := causalInstalledTable state base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((simulateQ (filteredDirectVerifierImpl keyView selected)
          computation).run state)).run
      continuation table result] =
    𝓓[do
      let result ← ((simulateQ
        (filteredDirectLazyVerifierImpl keyView selected)
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
        _ = 𝓓[do
            let handled ← filteredDirectLazyVerifierStep
              keyView selected input state
            let rest ← ((simulateQ
              (filteredDirectLazyVerifierImpl keyView selected)
                (next handled.1.1)).run handled.1.2).run
            let base ← $ᵗ (ChainValueIndex → Digest)
            continuation (causalInstalledTable rest.1.2 base)
              (appendFilteredDirectVerifierResult handled rest)] := by
          calc
            _ = 𝓓[do
                let handled ← filteredDirectLazyVerifierStep
                  keyView selected input state
                let base ← $ᵗ (ChainValueIndex → Digest)
                let table := causalInstalledTable handled.1.2 base
                let rest ← (simulateQ
                  (RevealProbeOracleSimulation.eagerTraceImpl table)
                  ((simulateQ (filteredDirectVerifierImpl keyView selected)
                    (next handled.1.1)).run handled.1.2)).run
                continuation table
                  (appendFilteredDirectVerifierResult handled rest)] := by
              simpa [appendFilteredDirectVerifierResult, bind_assoc] using
                (evalDist_installed_filteredDirectVerifier_step_continuation_eq_lazy
                  keyView selected input state
                    (fun table handled => do
                      let rest ← (simulateQ
                        (RevealProbeOracleSimulation.eagerTraceImpl table)
                        ((simulateQ
                          (filteredDirectVerifierImpl keyView selected)
                          (next handled.1.1)).run handled.1.2)).run
                      continuation table
                        (appendFilteredDirectVerifierResult handled rest)))
            _ = _ := by
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro handled
              exact ih handled.1.1 handled.1.2
                (fun table rest => continuation table
                  (appendFilteredDirectVerifierResult handled rest))
        _ = _ := by
          simp [filteredDirectLazyVerifierImpl,
            appendFilteredDirectVerifierResult, map_eq_bind_pure_comp,
            bind_assoc]

end XmssSecurity
