import XmssSecurity.CappedGlobalCausalInstalledAdversary

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

noncomputable local instance globalCausalInstalledAdversaryRunSampleableTable :
    SampleableType (GlobalChainValueIndex → Digest) :=
  SampleableType.ofFintype (GlobalChainValueIndex → Digest)

noncomputable def globalCausalLazyActionTracedImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (WriterT AttackerActionTrace
        (StateT GlobalCausalHashState
          (WriterT
            (RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
            ProbComp))) :=
  fun input => WriterT.mk fun state => WriterT.mk
    (globalCausalLazyActionTracedStep publicKey secretKey input state)

theorem globalCausalLazyActionTracedImpl_run
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalCausalHashState) :
    (((globalCausalLazyActionTracedImpl publicKey secretKey input).run).run
      state).run =
        globalCausalLazyActionTracedStep publicKey secretKey input state := rfl

def appendGlobalCausalActionTracedResult
    {input : (OracleWorld + SigningSpec).Domain}
    (handled : ((((OracleWorld + SigningSpec).Range input ×
      AttackerActionTrace) × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
    (rest : (((α × AttackerActionTrace) × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) :
    (((α × AttackerActionTrace) × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :=
  (((rest.1.1.1, handled.1.1.2 ++ rest.1.1.2), rest.1.2),
    handled.2 ++ rest.2)

noncomputable def globalCausalEagerAdversaryRestContinuation
    (publicKey : PublicKey) (secretKey : SecretKey)
    {input : (OracleWorld + SigningSpec).Domain}
    (next : (OracleWorld + SigningSpec).Range input →
      OracleComp (OracleWorld + SigningSpec) α)
    (continuation : (GlobalChainValueIndex → Digest) →
      (((α × AttackerActionTrace) × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) →
          ProbComp β)
    (table : GlobalChainValueIndex → Digest)
    (handled : ((((OracleWorld + SigningSpec).Range input ×
      AttackerActionTrace) × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) :
    ProbComp β := do
  let rest ← (simulateQ
    (RevealProbeOracleSimulation.eagerTraceImpl table)
    (((simulateQ
      (globalCausalActionTracedMappedAdversaryAfterRealRomImpl
        publicKey secretKey) (next handled.1.1.1)).run).run
          handled.1.2)).run
  continuation table (appendGlobalCausalActionTracedResult handled rest)

set_option maxRecDepth 200000 in
theorem evalDist_installed_simulate_globalCausalActionTracedAdversary_eq_lazy
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : GlobalCausalHashState)
    (continuation : (GlobalChainValueIndex → Digest) →
      (((α × AttackerActionTrace) × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) →
          ProbComp β) :
    𝒟[do
      let base ← $ᵗ (GlobalChainValueIndex → Digest)
      let table := globalCausalInstalledTable state base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        (((simulateQ
          (globalCausalActionTracedMappedAdversaryAfterRealRomImpl
            publicKey secretKey) computation).run).run state)).run
      continuation table result] =
    𝒟[do
      let result ← (((simulateQ
        (globalCausalLazyActionTracedImpl publicKey secretKey)
          computation).run).run state).run
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
            let handled ← globalCausalLazyActionTracedStep
              publicKey secretKey input state
            let base ← $ᵗ (GlobalChainValueIndex → Digest)
            globalCausalEagerAdversaryRestContinuation publicKey secretKey
              next continuation
              (globalCausalInstalledTable handled.1.2 base) handled] := by
          simpa [globalCausalEagerAdversaryRestContinuation,
            appendGlobalCausalActionTracedResult,
            globalCausalEagerActionTracedAtTable, Prod.map,
            map_eq_bind_pure_comp, bind_assoc, Function.comp_apply] using
            (evalDist_installed_globalCausalActionTracedMappedAdversaryAfterRealRomImpl_fixedContinuation_eq_lazy
              publicKey secretKey input state
                (globalCausalEagerAdversaryRestContinuation
                  publicKey secretKey next continuation))
        _ = 𝒟[do
            let handled ← globalCausalLazyActionTracedStep
              publicKey secretKey input state
            let rest ← (((simulateQ
              (globalCausalLazyActionTracedImpl publicKey secretKey)
                (next handled.1.1.1)).run).run handled.1.2).run
            let base ← $ᵗ (GlobalChainValueIndex → Digest)
            continuation (globalCausalInstalledTable rest.1.2 base)
              (appendGlobalCausalActionTracedResult handled rest)] := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro handled
          exact ih handled.1.1.1 handled.1.2
            (fun table rest => continuation table
              (appendGlobalCausalActionTracedResult handled rest))
        _ = _ := by
          simp [globalCausalLazyActionTracedImpl_run,
            appendGlobalCausalActionTracedResult, Prod.map,
            map_eq_bind_pure_comp, bind_assoc, Function.comp_apply]

end XmssSecurity.CappedChain
