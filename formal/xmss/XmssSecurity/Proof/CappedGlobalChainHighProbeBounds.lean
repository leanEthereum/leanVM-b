import XmssSecurity.Proof.CappedGlobalChainHighSigningSimulator
import XmssSecurity.Proof.CappedGlobalChainHighAttackerHashPlan

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

theorem globalCausalRevealHashQueryFromHigh_isProbeQueryBoundP
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex) :
    (globalCausalRevealHashQueryFromHigh high secretKey input state index)
      |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0 := by
  unfold globalCausalRevealHashQueryFromHigh
  apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
    (RevealProbeOracleSimulation.revealQuery_isProbeQueryBoundP index 0)
  intro value _hvalue
  exact OracleComp.isQueryBoundP_pure
    (p := RevealProbeOracleSimulation.IsProbeQuery) _ 0

theorem globalCausalAttackerHashQueryFromHigh_isProbeQueryBoundP
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) :
    (globalCausalAttackerHashQueryFromHigh high secretKey input).run state
      |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 1 := by
  rw [globalCausalAttackerHashQueryFromHigh_run]
  generalize hplan :
    globalFilteredCausalAttackerHashPlan secretKey input state = plan
  cases plan with
  | cached output => simp
  | redirect output => simp
  | fresh =>
      exact (globalCausalHashQuery_run_isProbeQueryBoundP input
        (globalCausalRecordedState secretKey input state)).mono (by omega)
  | reveal index =>
      exact (globalCausalRevealHashQueryFromHigh_isProbeQueryBoundP high
        secretKey input state index).mono (by omega)
  | probeThenFresh index target =>
      apply OracleComp.isQueryBoundP_bind (n := 1) (m := 0)
        (RevealProbeOracleSimulation.probeQuery_isProbeQueryBoundP index target)
      intro _ _
      exact globalCausalHashQuery_run_isProbeQueryBoundP input
        (globalCausalRecordedState secretKey input state)

end XmssSecurity.CappedChain
