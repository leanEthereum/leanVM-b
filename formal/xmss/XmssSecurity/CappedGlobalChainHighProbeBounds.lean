import XmssSecurity.CappedGlobalChainHighSigningSimulator
import XmssSecurity.CappedGlobalChainHighAttackerHashPlan

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
      |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0 := by
  rw [globalCausalAttackerHashQueryFromHigh_run]
  generalize hplan :
    globalFilteredCausalAttackerHashPlan secretKey input state = plan
  cases plan with
  | cached output => simp
  | redirect output => simp
  | fresh =>
      exact globalCausalHashQuery_run_isProbeQueryBoundP input
        (globalCausalRecordedState secretKey input state)
  | reveal index =>
      exact globalCausalRevealHashQueryFromHigh_isProbeQueryBoundP high
        secretKey input state index

theorem globalFilteredCausalSigningAttempt_isProbeQueryBoundP
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState) :
    (globalFilteredCausalSigningAttempt keyView request state)
      |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0 := by
  unfold globalFilteredCausalSigningAttempt
  apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
    (RevealProbeOracleSimulation.liftProbComp_isProbeQueryBoundP
      Concrete.signingRandomness 0)
  intro randomness _hrandomness
  apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
    (RevealProbeOracleSimulation.liftProbComp_isProbeQueryBoundP
      ((simulateQ randomOracle
        (Concrete.encodingHash keyView.secretKey.parameter request.epoch
          request.message randomness)).run state.cache) 0)
  intro encoded _hencoded
  cases hdecode : TargetSum.decodeDigest encoded.1 with
  | none =>
    exact OracleComp.isQueryBoundP_pure
      (p := RevealProbeOracleSimulation.IsProbeQuery)
        (none, { state with cache := encoded.2 }) 0
  | some encoding =>
    apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
      (revealGlobalSignatureChains_run_isProbeQueryBoundP request encoding
        allChains (Concrete.CacheReplay.signWithEncoding keyView.cache
          keyView.secretKey request.epoch randomness encoding)
        { state with cache := encoded.2 })
    intro result _hresult
    exact OracleComp.isQueryBoundP_pure
      (p := RevealProbeOracleSimulation.IsProbeQuery) _ 0

theorem globalFilteredCausalSignBoundedAttempts_isProbeQueryBoundP
    (attempts : Nat) (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState) :
    (globalFilteredCausalSignBoundedAttempts attempts keyView request state)
      |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0 := by
  induction attempts generalizing state with
  | zero =>
      exact OracleComp.isQueryBoundP_pure
        (p := RevealProbeOracleSimulation.IsProbeQuery) (none, state) 0
  | succ attempts ih =>
      rw [globalFilteredCausalSignBoundedAttempts]
      apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
        (globalFilteredCausalSigningAttempt_isProbeQueryBoundP keyView request
          state)
      intro result _hresult
      cases result.1 with
      | none => exact ih result.2
      | some signature =>
          exact OracleComp.isQueryBoundP_pure
            (p := RevealProbeOracleSimulation.IsProbeQuery)
              (some signature, result.2) 0

theorem globalFilteredCausalSigningQuery_isProbeQueryBoundP
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState) :
    (globalFilteredCausalSigningQuery keyView request state)
      |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0 := by
  unfold globalFilteredCausalSigningQuery
  exact globalFilteredCausalSignBoundedAttempts_isProbeQueryBoundP
    signingAttemptLimit keyView request state

end XmssSecurity.CappedChain
