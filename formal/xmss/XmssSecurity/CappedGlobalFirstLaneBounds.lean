import XmssSecurity.CappedGlobalFirstLaneProgram

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000

theorem globalFirstLaneUniformQuery_hazardBound (n : Nat) :
    (FirstLaneOracleSimulation.uniformQuery
      (Index := GlobalChainValueIndex) n).IsQueryBoundP
        FirstLaneOracleSimulation.IsHazardQuery 0 := by
  rw [FirstLaneOracleSimulation.uniformQuery,
    OracleComp.isQueryBoundP_query_iff]
  simp [FirstLaneOracleSimulation.IsHazardQuery]

theorem globalFirstLaneEncodingQuery_hazardBound (epoch : Epoch) :
    (FirstLaneOracleSimulation.encodingQuery
      (Index := GlobalChainValueIndex) epoch).IsQueryBoundP
        FirstLaneOracleSimulation.IsHazardQuery 1 := by
  rw [FirstLaneOracleSimulation.encodingQuery,
    OracleComp.isQueryBoundP_query_iff]
  simp [FirstLaneOracleSimulation.IsHazardQuery]

theorem globalFirstLaneEncodingSignAttemptQuery_hazardBound (epoch : Epoch) :
    (FirstLaneOracleSimulation.encodingSignAttemptQuery
      (Index := GlobalChainValueIndex) epoch).IsQueryBoundP
        FirstLaneOracleSimulation.IsHazardQuery 0 := by
  rw [FirstLaneOracleSimulation.encodingSignAttemptQuery,
    OracleComp.isQueryBoundP_query_iff]
  simp [FirstLaneOracleSimulation.IsHazardQuery]

theorem globalFirstLaneProbeQuery_hazardBound
    (index : GlobalChainValueIndex) (target : Digest) :
    (FirstLaneOracleSimulation.probeQuery index target).IsQueryBoundP
      FirstLaneOracleSimulation.IsHazardQuery 1 := by
  rw [FirstLaneOracleSimulation.probeQuery,
    OracleComp.isQueryBoundP_query_iff]
  simp [FirstLaneOracleSimulation.IsHazardQuery]

theorem globalFirstLaneRevealQuery_hazardBound
    (index : GlobalChainValueIndex) :
    (FirstLaneOracleSimulation.revealQuery index).IsQueryBoundP
      FirstLaneOracleSimulation.IsHazardQuery 0 := by
  rw [FirstLaneOracleSimulation.revealQuery,
    OracleComp.isQueryBoundP_query_iff]
  simp [FirstLaneOracleSimulation.IsHazardQuery]

theorem globalFirstLaneLiftProbComp_hazardBound
    (computation : ProbComp α) :
    (FirstLaneOracleSimulation.liftProbComp
      (Index := GlobalChainValueIndex) computation).IsQueryBoundP
        FirstLaneOracleSimulation.IsHazardQuery 0 := by
  unfold FirstLaneOracleSimulation.liftProbComp
  apply OracleComp.IsQueryBoundP.simulateQ_of_step
    (p := fun _ : unifSpec.Domain => False)
    (q := FirstLaneOracleSimulation.IsHazardQuery)
    (OracleComp.isQueryBoundP_false computation 0)
  · intro input hfalse
    exact hfalse.elim
  · intro input _
    exact globalFirstLaneUniformQuery_hazardBound input

theorem globalFirstLaneLiftRevealProbe_hazardBound
    (computation : OracleComp
      (RevealProbeOracleSimulation.World GlobalChainValueIndex) α)
    (fuel : Nat)
    (hbound : computation.IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery fuel) :
    (globalFirstLaneLiftRevealProbe computation).IsQueryBoundP
      FirstLaneOracleSimulation.IsHazardQuery fuel := by
  unfold globalFirstLaneLiftRevealProbe
  apply OracleComp.IsQueryBoundP.simulateQ_of_step hbound
  · intro input hprobe
    cases input with
    | uniform n => simp [RevealProbeOracleSimulation.IsProbeQuery] at hprobe
    | probe index target => exact globalFirstLaneProbeQuery_hazardBound index target
    | reveal index => simp [RevealProbeOracleSimulation.IsProbeQuery] at hprobe
  · intro input hnotProbe
    cases input with
    | uniform n => exact globalFirstLaneUniformQuery_hazardBound n
    | probe index target =>
        simp [RevealProbeOracleSimulation.IsProbeQuery] at hnotProbe
    | reveal index => exact globalFirstLaneRevealQuery_hazardBound index

theorem globalFirstLaneFreshEncodingQuery_hazardBound
    (kind : EncodingSampleKind) (epoch : Epoch) (input : HashInput)
    (state : GlobalCausalHashState) :
    (globalFirstLaneFreshEncodingQuery kind epoch input state).IsQueryBoundP
      FirstLaneOracleSimulation.IsHazardQuery
        (if kind = .query then 1 else 0) := by
  unfold globalFirstLaneFreshEncodingQuery
  cases kind with
  | side =>
      apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
        (globalFirstLaneLiftProbComp_hazardBound uniformHashOutput)
      intro output _
      exact OracleComp.isQueryBoundP_pure
        (p := FirstLaneOracleSimulation.IsHazardQuery) _ 0
  | query =>
      apply OracleComp.isQueryBoundP_bind (n := 1) (m := 0)
        (globalFirstLaneEncodingQuery_hazardBound epoch)
      intro output _
      exact OracleComp.isQueryBoundP_pure
        (p := FirstLaneOracleSimulation.IsHazardQuery) _ 0
  | sign =>
      apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
        (globalFirstLaneEncodingSignAttemptQuery_hazardBound epoch)
      intro output _
      exact OracleComp.isQueryBoundP_pure
        (p := FirstLaneOracleSimulation.IsHazardQuery) _ 0

theorem globalFirstLaneAttackerHashQueryFromHigh_hazardBound
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) :
    (globalFirstLaneAttackerHashQueryFromHigh high secretKey input).run state
      |>.IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery 1 := by
  change (globalFirstLaneAttackerHashQueryFromHighRun high secretKey input state)
    |>.IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery 1
  unfold globalFirstLaneAttackerHashQueryFromHighRun
  cases hepoch : encodingInputEpoch? secretKey.parameter input with
  | none =>
      change (globalFirstLaneLiftRevealProbe
        ((globalCausalAttackerHashQueryFromHigh high secretKey input).run state)
        ).IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery 1
      exact globalFirstLaneLiftRevealProbe_hazardBound
        ((globalCausalAttackerHashQueryFromHigh high secretKey input).run state) 1
        (globalCausalAttackerHashQueryFromHigh_isProbeQueryBoundP high secretKey
          input state)
  | some epoch =>
      change (match state.cache input with
        | some output =>
            pure (output, globalCausalRecordedState secretKey input state)
        | none => globalFirstLaneFreshEncodingQuery .query epoch input
            (globalCausalRecordedState secretKey input state)
        ).IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery 1
      cases hcache : state.cache input with
      | none =>
          simp only [hcache]
          exact globalFirstLaneFreshEncodingQuery_hazardBound .query epoch
            input (globalCausalRecordedState secretKey input state)
      | some output =>
          simp only [hcache]
          exact (OracleComp.isQueryBoundP_pure
            (p := FirstLaneOracleSimulation.IsHazardQuery) _ 0).mono (by omega)

theorem globalFirstLaneEncodingHashQuery_hazardBound
    (secretKey : SecretKey) (epoch : Epoch) (message : Message)
    (randomness : Randomness) (state : GlobalCausalHashState) :
    (globalFirstLaneEncodingHashQuery secretKey epoch message randomness state)
      |>.IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery 0 := by
  unfold globalFirstLaneEncodingHashQuery
  let input := Concrete.CacheView.encodingInput secretKey.parameter epoch
    (message, randomness)
  change (match state.cache input with
    | some output => pure (output, state)
    | none => globalFirstLaneFreshEncodingQuery .sign epoch input state
    ).IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery 0
  cases hcache : state.cache input with
  | none =>
      exact globalFirstLaneFreshEncodingQuery_hazardBound .sign epoch input state
  | some output =>
      exact OracleComp.isQueryBoundP_pure
        (p := FirstLaneOracleSimulation.IsHazardQuery) _ 0

theorem globalFirstLaneSigningAttempt_hazardBound
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState) :
    (globalFirstLaneSigningAttempt keyView request state).IsQueryBoundP
      FirstLaneOracleSimulation.IsHazardQuery 0 := by
  unfold globalFirstLaneSigningAttempt
  apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
    (globalFirstLaneLiftProbComp_hazardBound Concrete.signingRandomness)
  intro randomness _
  apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
    (globalFirstLaneEncodingHashQuery_hazardBound keyView.secretKey
      request.epoch request.message randomness state)
  intro encoded _
  cases hdecode : TargetSum.decodeDigest (truncateHash encoded.1) with
  | none =>
      exact OracleComp.isQueryBoundP_pure
        (p := FirstLaneOracleSimulation.IsHazardQuery) _ 0
  | some encoding =>
      apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
      · apply globalFirstLaneLiftRevealProbe_hazardBound
        exact revealGlobalSignatureChains_run_isProbeQueryBoundP request encoding
          allChains (Concrete.CacheReplay.signWithEncoding keyView.cache
            keyView.secretKey request.epoch randomness encoding) encoded.2
      · intro result _
        exact OracleComp.isQueryBoundP_pure
          (p := FirstLaneOracleSimulation.IsHazardQuery) _ 0

theorem globalFirstLaneSignBoundedAttempts_hazardBound
    (attempts : Nat) (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState) :
    (globalFirstLaneSignBoundedAttempts attempts keyView request state)
      |>.IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery 0 := by
  induction attempts generalizing state with
  | zero =>
      exact OracleComp.isQueryBoundP_pure
        (p := FirstLaneOracleSimulation.IsHazardQuery) _ 0
  | succ attempts ih =>
      rw [globalFirstLaneSignBoundedAttempts]
      apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
        (globalFirstLaneSigningAttempt_hazardBound keyView request state)
      intro result _
      cases hsignature : result.1 with
      | none =>
          exact ih result.2
      | some signature =>
          exact OracleComp.isQueryBoundP_pure
            (p := FirstLaneOracleSimulation.IsHazardQuery) _ 0

theorem globalFirstLaneSigningQuery_hazardBound
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState) :
    (globalFirstLaneSigningQuery keyView request state).IsQueryBoundP
      FirstLaneOracleSimulation.IsHazardQuery 0 := by
  exact globalFirstLaneSignBoundedAttempts_hazardBound signingAttemptLimit
    keyView request state

end XmssSecurity.CappedChain
