import XmssSecurity.CappedChain.CausalInstalledAdversary

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.CappedChain

noncomputable local instance causalInstalledAdversaryRunSampleableChainTable :
    SampleableType (ChainValueIndex → Digest) :=
  SampleableType.ofFintype (ChainValueIndex → Digest)

noncomputable def causalLazyActionTracedImpl
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex) :
    QueryImpl (OracleWorld + SigningSpec)
      (WriterT AttackerActionTrace
        (StateT CausalHashState
          (WriterT (RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
            ProbComp))) :=
  fun input => WriterT.mk fun state => WriterT.mk
    (causalLazyActionTracedStep publicKey secretKey chain input state)

theorem causalLazyActionTracedImpl_run
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState) :
    (((causalLazyActionTracedImpl publicKey secretKey chain input).run).run
      state).run =
        causalLazyActionTracedStep publicKey secretKey chain input state := rfl

def appendCausalActionTracedResult
    {input : (OracleWorld + SigningSpec).Domain}
    (handled : ((((OracleWorld + SigningSpec).Range input ×
      AttackerActionTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (rest : (((α × AttackerActionTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) :
    (((α × AttackerActionTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :=
  (((rest.1.1.1, handled.1.1.2 ++ rest.1.1.2), rest.1.2),
    handled.2 ++ rest.2)

noncomputable def causalEagerAdversaryRestContinuation
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    {input : (OracleWorld + SigningSpec).Domain}
    (next : (OracleWorld + SigningSpec).Range input →
      OracleComp (OracleWorld + SigningSpec) α)
    (continuation : (ChainValueIndex → Digest) →
      (((α × AttackerActionTrace) × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp β)
    (table : ChainValueIndex → Digest)
    (handled : ((((OracleWorld + SigningSpec).Range input ×
      AttackerActionTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) : ProbComp β := do
  let rest ← (simulateQ
    (RevealProbeOracleSimulation.eagerTraceImpl table)
    (((simulateQ (causalActionTracedMappedAdversaryAfterRealRomImpl
      publicKey secretKey chain) (next handled.1.1.1)).run).run
        handled.1.2)).run
  continuation table (appendCausalActionTracedResult handled rest)

set_option maxRecDepth 100000 in
theorem evalDist_installed_simulate_causalActionTracedAdversary_eq_lazy
    (publicKey : PublicKey) (secretKey : SecretKey) (chain : ChainIndex)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      (((α × AttackerActionTrace) × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp β) :
    𝒟[do
      let base ← $ᵗ (ChainValueIndex → Digest)
      let table := causalInstalledTable state base
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl table)
        (((simulateQ (causalActionTracedMappedAdversaryAfterRealRomImpl
          publicKey secretKey chain) computation).run).run state)).run
      continuation table result] =
    𝒟[do
      let result ← (((simulateQ
        (causalLazyActionTracedImpl publicKey secretKey chain)
          computation).run).run state).run
      let base ← $ᵗ (ChainValueIndex → Digest)
      continuation (causalInstalledTable result.1.2 base) result] := by
  induction computation using OracleComp.inductionOn generalizing state continuation with
  | pure result =>
      simp [simulateQ_pure, WriterT.run_pure]
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, simulateQ_query,
        OracleQuery.input_query, OracleQuery.cont_query, id_map,
        WriterT.run_bind', StateT.run_bind]
      calc
        _ = 𝒟[do
            let handled ← causalLazyActionTracedStep
              publicKey secretKey chain input state
            let base ← $ᵗ (ChainValueIndex → Digest)
            causalEagerAdversaryRestContinuation publicKey secretKey chain
              next continuation
              (causalInstalledTable handled.1.2 base) handled] := by
          simpa [causalEagerAdversaryRestContinuation,
            appendCausalActionTracedResult, causalEagerActionTracedAtTable,
            Prod.map, map_eq_bind_pure_comp, bind_assoc,
            Function.comp_apply] using
            (evalDist_installed_causalActionTracedMappedAdversaryAfterRealRomImpl_fixedContinuation_eq_lazy
              publicKey secretKey chain input state
                (causalEagerAdversaryRestContinuation
                  publicKey secretKey chain next continuation))
        _ = 𝒟[do
            let handled ← causalLazyActionTracedStep
              publicKey secretKey chain input state
            let rest ← (((simulateQ
              (causalLazyActionTracedImpl publicKey secretKey chain)
                (next handled.1.1.1)).run).run handled.1.2).run
            let base ← $ᵗ (ChainValueIndex → Digest)
            continuation (causalInstalledTable rest.1.2 base)
              (appendCausalActionTracedResult handled rest)] := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro handled
          exact ih handled.1.1.1 handled.1.2
            (fun table rest => continuation table
              (appendCausalActionTracedResult handled rest))
        _ = _ := by
          simp [causalLazyActionTracedImpl_run,
            appendCausalActionTracedResult, Prod.map, map_eq_bind_pure_comp,
            bind_assoc, Function.comp_apply]

end XmssSecurity.CappedChain
