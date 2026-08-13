import XmssSecurity.CausalDirectLazyMappedStep

open OracleComp OracleSpec

namespace XmssSecurity

noncomputable local instance directLazyRawRunSampleableChainTable :
    SampleableType (ChainValueIndex → Digest) :=
  SampleableType.ofFintype (ChainValueIndex → Digest)

def attachDirectRawActionTrace
    (input : (OracleWorld + SigningSpec).Domain)
    (result : (DirectActionOutput input × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :
    ((((OracleWorld + SigningSpec).Range input × AttackerActionTrace) ×
      CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :=
  let output := castDirectActionOutput input result.1.1
  (((output, attackerActionFragment input output), result.1.2), result.2)

@[simp]
theorem attachDirectRawActionTrace_state
    (input : (OracleWorld + SigningSpec).Domain)
    (result : (DirectActionOutput input × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :
    (attachDirectRawActionTrace input result).1.2 = result.1.2 := rfl

noncomputable def filteredDirectEagerRawActionTracedStep
    (table : ChainValueIndex → Digest)
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState) :
    ProbComp ((((OracleWorld + SigningSpec).Range input × AttackerActionTrace) ×
      CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :=
  attachDirectRawActionTrace input <$>
    filteredDirectEagerRawMappedStep table keyView selected input state

noncomputable def filteredDirectLazyRawActionTracedStep
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState) :
    ProbComp ((((OracleWorld + SigningSpec).Range input × AttackerActionTrace) ×
      CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :=
  attachDirectRawActionTrace input <$>
    filteredDirectLazyRawMappedStep keyView selected input state

noncomputable def filteredDirectEagerRawActionTracedImpl
    (table : ChainValueIndex → Digest)
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex) :
    QueryImpl (OracleWorld + SigningSpec)
      (WriterT AttackerActionTrace
        (StateT CausalHashState
          (WriterT (RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
            ProbComp))) :=
  fun input => WriterT.mk fun state => WriterT.mk
    (filteredDirectEagerRawActionTracedStep table keyView selected input state)

noncomputable def filteredDirectLazyRawActionTracedImpl
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex) :
    QueryImpl (OracleWorld + SigningSpec)
      (WriterT AttackerActionTrace
        (StateT CausalHashState
          (WriterT (RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
            ProbComp))) :=
  fun input => WriterT.mk fun state => WriterT.mk
    (filteredDirectLazyRawActionTracedStep keyView selected input state)

theorem filteredDirectEagerRawActionTracedImpl_run
    (table : ChainValueIndex → Digest)
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState) :
    (((filteredDirectEagerRawActionTracedImpl table keyView selected input).run).run
      state).run =
        filteredDirectEagerRawActionTracedStep table keyView selected input state := rfl

theorem filteredDirectLazyRawActionTracedImpl_run
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState) :
    (((filteredDirectLazyRawActionTracedImpl keyView selected input).run).run
      state).run =
        filteredDirectLazyRawActionTracedStep keyView selected input state := rfl

def appendDirectRawActionTracedResult
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

set_option maxRecDepth 100000 in
theorem evalDist_installed_filteredDirectRawActionTracedStep_eq_lazy
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      ((((OracleWorld + SigningSpec).Range input × AttackerActionTrace) ×
        CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp α) :
    𝒟[do
      let base ← $ᵗ (ChainValueIndex → Digest)
      let table := causalInstalledTable state base
      let result ← filteredDirectEagerRawActionTracedStep table keyView selected
        input state
      continuation table result] =
    𝒟[do
      let result ← filteredDirectLazyRawActionTracedStep keyView selected input state
      let base ← $ᵗ (ChainValueIndex → Digest)
      continuation (causalInstalledTable result.1.2 base) result] := by
  simpa [filteredDirectEagerRawActionTracedStep,
    filteredDirectLazyRawActionTracedStep, map_eq_bind_pure_comp,
    bind_assoc] using
    (evalDist_installed_filteredDirectRawMappedStep_fixedContinuation_eq_lazy
      keyView selected input state
        (fun table result => continuation table
          (attachDirectRawActionTrace input result)))

set_option maxRecDepth 100000 in
theorem evalDist_installed_simulate_filteredDirectRawActionTraced_eq_lazy
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CausalHashState)
    (continuation : (ChainValueIndex → Digest) →
      (((α × AttackerActionTrace) × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) → ProbComp β) :
    𝒟[do
      let base ← $ᵗ (ChainValueIndex → Digest)
      let table := causalInstalledTable state base
      let result ← (((simulateQ
        (filteredDirectEagerRawActionTracedImpl table keyView selected)
          computation).run).run state).run
      continuation table result] =
    𝒟[do
      let result ← (((simulateQ
        (filteredDirectLazyRawActionTracedImpl keyView selected)
          computation).run).run state).run
      let base ← $ᵗ (ChainValueIndex → Digest)
      continuation (causalInstalledTable result.1.2 base) result] := by
  induction computation using OracleComp.inductionOn generalizing state continuation with
  | pure result =>
      simp [simulateQ_pure, WriterT.run_pure]
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, OracleQuery.input_query,
        WriterT.run_bind', StateT.run_bind]
      calc
        _ = 𝒟[do
            let handled ← filteredDirectLazyRawActionTracedStep
              keyView selected input state
            let rest ← (((simulateQ
              (filteredDirectLazyRawActionTracedImpl keyView selected)
                (next handled.1.1.1)).run).run handled.1.2).run
            let base ← $ᵗ (ChainValueIndex → Digest)
            continuation (causalInstalledTable rest.1.2 base)
              (appendDirectRawActionTracedResult handled rest)] := by
          calc
            _ = 𝒟[do
                let handled ← filteredDirectLazyRawActionTracedStep
                  keyView selected input state
                let base ← $ᵗ (ChainValueIndex → Digest)
                let table := causalInstalledTable handled.1.2 base
                let rest ← (((simulateQ
                  (filteredDirectEagerRawActionTracedImpl table keyView selected)
                    (next handled.1.1.1)).run).run handled.1.2).run
                continuation table
                  (appendDirectRawActionTracedResult handled rest)] := by
              simpa [filteredDirectEagerRawActionTracedImpl_run,
                appendDirectRawActionTracedResult, Prod.map,
                map_eq_bind_pure_comp, bind_assoc, Function.comp_apply] using
                (evalDist_installed_filteredDirectRawActionTracedStep_eq_lazy
                  keyView selected input state
                    (fun table handled => do
                      let rest ← (((simulateQ
                        (filteredDirectEagerRawActionTracedImpl table keyView selected)
                          (next handled.1.1.1)).run).run handled.1.2).run
                      continuation table
                        (appendDirectRawActionTracedResult handled rest)))
            _ = _ := by
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro handled
              exact ih handled.1.1.1 handled.1.2
                (fun table rest => continuation table
                  (appendDirectRawActionTracedResult handled rest))
        _ = _ := by
          simp [filteredDirectLazyRawActionTracedImpl_run,
            appendDirectRawActionTracedResult, Prod.map,
            map_eq_bind_pure_comp, bind_assoc, Function.comp_apply]

end XmssSecurity
