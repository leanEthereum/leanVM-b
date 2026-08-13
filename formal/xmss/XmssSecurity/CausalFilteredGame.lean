import XmssSecurity.CausalFilteredSuffix

open OracleComp OracleSpec

namespace XmssSecurity

def IsDirectHashAction :
    (OracleWorld + SigningSpec).Domain → Prop
  | .inl (.inr _) => True
  | _ => False

instance : DecidablePred IsDirectHashAction := fun input => by
  cases input with
  | inl worldInput =>
      cases worldInput with
      | inl _ => exact isFalse (by simp [IsDirectHashAction])
      | inr _ => exact isTrue trivial
  | inr _ => exact isFalse (by simp [IsDirectHashAction])

noncomputable def filteredDirectMappedAdversaryImpl
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT CausalHashState
        (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex))) :=
  fun input =>
    match input with
    | .inl (.inl n) => causalUniformImpl n
    | .inl (.inr hashInput) => fun state =>
        filteredProbingAttackerHashQueryAt keyView.secretKey selected hashInput
          state (chainInputProbe? keyView.secretKey.parameter selected hashInput)
    | .inr request => fun state =>
        filteredDirectSigningQuery keyView selected request state

noncomputable def filteredDirectVerifierImpl
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex) :
    QueryImpl OracleWorld
      (StateT CausalHashState
        (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex))) :=
  fun input =>
    match input with
    | .inl n => causalUniformImpl n
    | .inr hashInput => fun state =>
        filteredProbingAttackerHashQueryAt keyView.secretKey selected hashInput
          state (chainInputProbe? keyView.secretKey.parameter selected hashInput)

theorem filteredDirectMappedAdversaryImpl_step_isProbeQueryBoundP
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState) :
    (filteredDirectMappedAdversaryImpl keyView selected input).run state
      |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery
        (if IsDirectHashAction input then 1 else 0) := by
  rcases input with worldInput | request
  · rcases worldInput with n | hashInput
    · change ((causalUniformImpl n).run state).IsQueryBoundP
        RevealProbeOracleSimulation.IsProbeQuery 0
      exact causalUniformImpl_run_isProbeQueryBoundP n state
    · simp only [filteredDirectMappedAdversaryImpl, IsDirectHashAction]
      generalize hprobe :
        chainInputProbe? keyView.secretKey.parameter selected hashInput = probe
      exact filteredProbingAttackerHashQueryAt_isProbeQueryBoundP
        keyView.secretKey selected hashInput state probe
  · change (filteredDirectSigningQuery keyView selected request state)
        |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0
    exact filteredDirectSigningQuery_isProbeQueryBoundP
      keyView selected request state

theorem simulate_filteredDirectMappedAdversaryImpl_isProbeQueryBoundP
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (queries : Nat) (hqueries : computation.IsQueryBoundP
      IsDirectHashAction queries) (state : CausalHashState) :
    (simulateQ (filteredDirectMappedAdversaryImpl keyView selected)
      computation).run state |>.IsQueryBoundP
        RevealProbeOracleSimulation.IsProbeQuery queries := by
  exact OracleComp.IsQueryBoundP.simulateQ_run_StateT_of_step hqueries
    (filteredDirectMappedAdversaryImpl_step_isProbeQueryBoundP keyView selected)
      state

theorem filteredDirectVerifierImpl_step_isProbeQueryBoundP
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (input : OracleWorld.Domain) (state : CausalHashState) :
    (filteredDirectVerifierImpl keyView selected input).run state
      |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery
        (if input matches .inr _ then 1 else 0) := by
  rcases input with n | hashInput
  · change ((causalUniformImpl n).run state).IsQueryBoundP
        RevealProbeOracleSimulation.IsProbeQuery 0
    exact causalUniformImpl_run_isProbeQueryBoundP n state
  · simp only [filteredDirectVerifierImpl]
    generalize hprobe :
      chainInputProbe? keyView.secretKey.parameter selected hashInput = probe
    exact filteredProbingAttackerHashQueryAt_isProbeQueryBoundP
      keyView.secretKey selected hashInput state probe

theorem simulate_filteredDirectVerifierImpl_isProbeQueryBoundP
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (computation : OracleComp OracleWorld α)
    (queries : Nat) (hqueries : computation.IsQueryBoundP
      (· matches .inr _) queries) (state : CausalHashState) :
    (simulateQ (filteredDirectVerifierImpl keyView selected)
      computation).run state |>.IsQueryBoundP
        RevealProbeOracleSimulation.IsProbeQuery queries := by
  exact OracleComp.IsQueryBoundP.simulateQ_run_StateT_of_step hqueries
    (filteredDirectVerifierImpl_step_isProbeQueryBoundP keyView selected) state

end XmssSecurity
