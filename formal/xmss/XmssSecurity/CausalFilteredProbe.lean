import XmssSecurity.CausalFilteredResampling

open OracleComp OracleSpec

namespace XmssSecurity

noncomputable def filteredProbingAttackerHashQuery
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput) :
    StateT CausalHashState
      (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex))
      HashOutput := fun state =>
  match chainInputProbe? secretKey.parameter selected input with
  | none => (filteredCausalAttackerHashQuery
      secretKey selected input).run state
  | some probe => do
      let _ ← RevealProbeOracleSimulation.probeQuery probe.1 probe.2
      (filteredCausalAttackerHashQuery secretKey selected input).run state

theorem filteredCausalAttackerHashQuery_run_isProbeQueryBoundP
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) :
    (filteredCausalAttackerHashQuery secretKey selected input).run state
        |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0 := by
  rw [filteredCausalAttackerHashQuery_run]
  generalize hplan :
    filteredCausalAttackerHashPlan secretKey selected input state = plan
  cases plan with
  | cached output => simp
  | conditioned digest =>
      apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
        (RevealProbeOracleSimulation.liftProbComp_isProbeQueryBoundP
          (Rom.sampleHashOutputWithDigest digest) 0)
      intro output _houtput
      exact OracleComp.isQueryBoundP_pure
        (p := RevealProbeOracleSimulation.IsProbeQuery) (output,
          { (causalRecordedState secretKey selected input state) with
            cache := (causalRecordedState secretKey selected input state).cache.cacheQuery
              input output }) 0
  | fresh =>
      exact causalHashQuery_run_isProbeQueryBoundP input
        (causalRecordedState secretKey selected input state)
  | reveal index =>
      apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
        (RevealProbeOracleSimulation.revealQuery_isProbeQueryBoundP index 0)
      intro value _hvalue
      apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
        (RevealProbeOracleSimulation.liftProbComp_isProbeQueryBoundP
          (Rom.sampleHashOutputWithDigest value) 0)
      intro output _houtput
      exact OracleComp.isQueryBoundP_pure
        (p := RevealProbeOracleSimulation.IsProbeQuery) (output,
          causalRevealResultState secretKey selected input state
            index value output) 0

theorem filteredProbingAttackerHashQuery_run_isProbeQueryBoundP
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) :
    (filteredProbingAttackerHashQuery secretKey selected input).run state
        |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 1 := by
  unfold filteredProbingAttackerHashQuery
  cases hprobe : chainInputProbe? secretKey.parameter selected input with
  | none =>
      exact (filteredCausalAttackerHashQuery_run_isProbeQueryBoundP
        secretKey selected input state).mono (by omega)
  | some probe =>
      apply OracleComp.isQueryBoundP_bind (n := 1) (m := 0)
        (RevealProbeOracleSimulation.probeQuery_isProbeQueryBoundP
          probe.1 probe.2)
      intro _ _hunit
      exact filteredCausalAttackerHashQuery_run_isProbeQueryBoundP
        secretKey selected input state

end XmssSecurity
