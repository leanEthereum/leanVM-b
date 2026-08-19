import XmssSecurity.Proof.CausalFilteredSimulator
import XmssSecurity.Proof.CausalInstalledResampling

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

noncomputable local instance filteredInstalledSampleableChainTable :
    SampleableType (ChainValueIndex → Digest) :=
  SampleableType.ofFintype (ChainValueIndex → Digest)

noncomputable def filteredCausalLazyAttackerHashStep
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) :
    ProbComp ((HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :=
  match filteredCausalAttackerHashPlan secretKey selected input state with
  | .cached output =>
      pure ((output, causalRecordedState secretKey selected input state), [])
  | .reveal index =>
      match state.revealed index with
      | some value => do
          let output ← Rom.sampleHashOutputWithDigest value
          pure ((output, causalRevealResultState secretKey selected input state
            index value output),
            [RevealProbeOracleSimulation.ObservedAction.reveal index value])
      | none => do
          let output ← $ᵗ HashOutput
          let value := truncateHash output
          pure ((output, causalRevealResultState secretKey selected input state
            index value output),
            [RevealProbeOracleSimulation.ObservedAction.reveal index value])
  | .conditioned digest => do
      let output ← Rom.sampleHashOutputWithDigest digest
      let recorded := causalRecordedState secretKey selected input state
      pure ((output,
        { recorded with cache := recorded.cache.cacheQuery input output }), [])
  | .fresh => do
      let recorded := causalRecordedState secretKey selected input state
      let hashResult ← (randomOracle input).run recorded.cache
      pure ((hashResult.1, { recorded with cache := hashResult.2 }), [])

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
theorem evalDist_installed_filteredCausalAttackerHashQuery_continuation_eq_lazy
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      ((HashOutput × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    𝒟[do
      let base ← $ᵗ (ChainValueIndex → Digest)
      let table := causalInstalledTable state base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((filteredCausalAttackerHashQuery
          secretKey selected input).run state)).run
      continuation (causalInstalledTable result.1.2 base) result] =
    𝒟[do
      let result ← filteredCausalLazyAttackerHashStep
        secretKey selected input state
      let base ← $ᵗ (ChainValueIndex → Digest)
      continuation (causalInstalledTable result.1.2 base) result] := by
  generalize hplan :
    filteredCausalAttackerHashPlan secretKey selected input state = plan
  cases plan with
  | cached output =>
      simp only [filteredCausalLazyAttackerHashStep, hplan, pure_bind]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro base
      simp_rw [filteredCausalAttackerHashQuery_run, hplan]
      simp
  | conditioned digest =>
      simp only [filteredCausalLazyAttackerHashStep, hplan, pure_bind]
      calc
        _ = 𝒟[do
            let base ← $ᵗ (ChainValueIndex → Digest)
            let output ← Rom.sampleHashOutputWithDigest digest
            let recorded := causalRecordedState secretKey selected input state
            let result := ((output,
              { recorded with cache := recorded.cache.cacheQuery input output }),
                ([] : RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
            continuation (causalInstalledTable result.1.2 base) result] := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro base
          simp_rw [filteredCausalAttackerHashQuery_run, hplan]
          rw [simulateQ_bind, WriterT.run_bind',
            RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp]
          simp [map_eq_bind_pure_comp, bind_assoc]
        _ = _ := by
          rw [OracleComp.DeferredSampling.evalDist_bind_comm]
          simp [bind_assoc]
  | fresh =>
      simp only [filteredCausalLazyAttackerHashStep, hplan, pure_bind]
      calc
        _ = 𝒟[do
            let base ← $ᵗ (ChainValueIndex → Digest)
            let recorded := causalRecordedState secretKey selected input state
            let hashResult ← (randomOracle input).run recorded.cache
            continuation
              (causalInstalledTable
                { recorded with cache := hashResult.2 } base)
              ((hashResult.1, { recorded with cache := hashResult.2 }), [])] := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro base
          simp_rw [filteredCausalAttackerHashQuery_run, hplan]
          rw [simulate_eagerTrace_causalHashQuery]
          simp [map_eq_bind_pure_comp]
        _ = _ := by
          rw [OracleComp.DeferredSampling.evalDist_bind_comm]
          simp [bind_assoc]
  | reveal index =>
      cases hrevealed : state.revealed index with
      | some value =>
          simp only [filteredCausalLazyAttackerHashStep, hplan, hrevealed,
            pure_bind]
          calc
            _ = 𝒟[do
                let base ← $ᵗ (ChainValueIndex → Digest)
                let output ← Rom.sampleHashOutputWithDigest value
                continuation
                  (causalInstalledTable
                    (causalRevealResultState secretKey selected input state
                      index value output) base)
                  ((output, causalRevealResultState secretKey selected input state
                    index value output),
                    [RevealProbeOracleSimulation.ObservedAction.reveal
                      index value])] := by
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro base
              simp_rw [filteredCausalAttackerHashQuery_run, hplan]
              unfold causalRevealHashQuery
              rw [RevealProbeOracleSimulation.simulate_eagerTrace_reveal_then_liftProbComp]
              simp [causalInstalledTable_of_revealed state base index value
                hrevealed, map_eq_bind_pure_comp]
            _ = _ := by
              rw [OracleComp.DeferredSampling.evalDist_bind_comm]
              simp [bind_assoc]
      | none =>
          simp only [filteredCausalLazyAttackerHashStep, hplan, hrevealed,
            pure_bind]
          calc
            _ = 𝒟[do
                let base ← $ᵗ (ChainValueIndex → Digest)
                let output ← Rom.sampleHashOutputWithDigest (base index)
                let value := base index
                causalInstalledRevealContinuation secretKey selected input state
                  index continuation base value output] := by
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro base
              simp_rw [filteredCausalAttackerHashQuery_run, hplan]
              unfold causalRevealHashQuery
              rw [RevealProbeOracleSimulation.simulate_eagerTrace_reveal_then_liftProbComp]
              simp [causalInstalledTable_of_not_revealed
                state base index hrevealed, causalInstalledRevealContinuation,
                map_eq_bind_pure_comp]
            _ = 𝒟[causalProgrammedRevealContinuation
                secretKey selected input state index continuation] := by
              unfold causalProgrammedRevealContinuation
              exact
                (RevealProbeOracleSimulation.evalDist_uniformTable_bind_programmedCoordinate_continuation
                  index (causalInstalledRevealContinuation
                    secretKey selected input state index continuation))
            _ = 𝒟[causalFreshBaseRevealContinuation
                secretKey selected input state index continuation] :=
              evalDist_causalProgrammedRevealContinuation_eq_freshBase
                secretKey selected input state index continuation
            _ = _ := by
              unfold causalFreshBaseRevealContinuation
              simp [causalInstalledRevealContinuation, bind_assoc]

end XmssSecurity
