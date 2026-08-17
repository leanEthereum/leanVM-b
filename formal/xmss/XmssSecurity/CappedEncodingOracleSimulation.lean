import XmssSecurity.CappedEncodingGameTrace

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

noncomputable def cappedSplitUnloggedMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT (QueryCache HashSpec) (OracleComp EncodingSamplingWorld)) := by
  intro input
  cases input with
  | inl worldInput =>
      exact splitXmssRomImpl secretKey.parameter .query worldInput
  | inr request =>
      exact simulateQ (splitXmssRomImpl secretKey.parameter .sign)
        (Concrete.scheme.sign publicKey secretKey request.epoch request.message)

theorem cappedSplitUnloggedMappedAdversaryImpl_query_bridge
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (cache : QueryCache HashSpec) :
    𝒟[simulateQ encodingSamplingWorldImpl
        ((cappedSplitUnloggedMappedAdversaryImpl publicKey secretKey input).run cache)] =
      𝒟[(cappedUnloggedMappedAdversaryImpl publicKey secretKey input).run cache] := by
  cases input with
  | inl worldInput =>
      cases worldInput with
      | inl index =>
          simp only [cappedSplitUnloggedMappedAdversaryImpl,
            cappedUnloggedMappedAdversaryImpl, splitXmssRomImpl,
            xmssRomImpl, QueryImpl.add_apply_inl]
          exact congrArg evalDist (splitUniformOracle_bridge index cache)
      | inr hashInput =>
          simp only [cappedSplitUnloggedMappedAdversaryImpl,
            cappedUnloggedMappedAdversaryImpl, splitXmssRomImpl,
            xmssRomImpl, QueryImpl.add_apply_inr]
          exact congrArg evalDist
            (splitRandomOracle_bridge secretKey.parameter .query hashInput cache)
  | inr request =>
      simp only [cappedSplitUnloggedMappedAdversaryImpl,
        cappedUnloggedMappedAdversaryImpl]
      exact splitXmssRom_evalDist_simulation secretKey.parameter .sign
        (Concrete.scheme.sign publicKey secretKey request.epoch request.message)
        cache

theorem cappedSplitUnloggedMappedAdversary_evalDist_simulation
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) :
    𝒟[simulateQ encodingSamplingWorldImpl
        ((simulateQ (cappedSplitUnloggedMappedAdversaryImpl publicKey secretKey)
          computation).run cache)] =
      𝒟[(simulateQ (cappedUnloggedMappedAdversaryImpl publicKey secretKey)
        computation).run cache] := by
  rw [QueryImpl.simulateQ_mapStateTBase_run]
  apply OracleComp.evalDist_simulateQ_run_congr
  intro input state
  exact cappedSplitUnloggedMappedAdversaryImpl_query_bridge
    publicKey secretKey input state

noncomputable def cappedSplitCacheTracedMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT (QueryCache HashSpec × SigningCacheTrace)
        (OracleComp EncodingSamplingWorld)) :=
  QueryImpl.extendState
    (cappedSplitUnloggedMappedAdversaryImpl publicKey secretKey)
    signingCacheTraceUpdate

noncomputable def cappedSplitEncodingTracedMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)
        (OracleComp EncodingSamplingWorld)) :=
  QueryImpl.extendState
    (cappedSplitCacheTracedMappedAdversaryImpl publicKey secretKey)
    (encodingActionTraceUpdate secretKey)

theorem cappedSplitCacheTracedMappedAdversaryImpl_query_bridge
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : QueryCache HashSpec × SigningCacheTrace) :
    𝒟[simulateQ encodingSamplingWorldImpl
        ((cappedSplitCacheTracedMappedAdversaryImpl publicKey secretKey input).run state)] =
      𝒟[(cappedCacheTracedMappedAdversaryImpl publicKey secretKey input).run state] := by
  unfold cappedSplitCacheTracedMappedAdversaryImpl
    cappedCacheTracedMappedAdversaryImpl
  rw [QueryImpl.extendState_apply, QueryImpl.extendState_apply]
  simp only [simulateQ_bind, simulateQ_pure, evalDist_bind]
  rw [cappedSplitUnloggedMappedAdversaryImpl_query_bridge]

theorem cappedSplitCacheTracedMappedAdversary_evalDist_simulation
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : QueryCache HashSpec × SigningCacheTrace) :
    𝒟[simulateQ encodingSamplingWorldImpl
        ((simulateQ (cappedSplitCacheTracedMappedAdversaryImpl publicKey secretKey)
          computation).run state)] =
      𝒟[(simulateQ (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
        computation).run state] := by
  rw [QueryImpl.simulateQ_mapStateTBase_run]
  apply OracleComp.evalDist_simulateQ_run_congr
  intro input currentState
  exact cappedSplitCacheTracedMappedAdversaryImpl_query_bridge
    publicKey secretKey input currentState

theorem cappedSplitEncodingTracedMappedAdversaryImpl_query_bridge
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : (QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) :
    𝒟[simulateQ encodingSamplingWorldImpl
        ((cappedSplitEncodingTracedMappedAdversaryImpl publicKey secretKey input).run
          state)] =
      𝒟[(cappedEncodingTracedMappedAdversaryImpl publicKey secretKey input).run state] := by
  unfold cappedSplitEncodingTracedMappedAdversaryImpl
    cappedEncodingTracedMappedAdversaryImpl
  rw [QueryImpl.extendState_apply, QueryImpl.extendState_apply]
  simp only [simulateQ_bind, simulateQ_pure, evalDist_bind]
  rw [cappedSplitCacheTracedMappedAdversaryImpl_query_bridge]

theorem cappedSplitEncodingTracedMappedAdversary_evalDist_simulation
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : (QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) :
    𝒟[simulateQ encodingSamplingWorldImpl
        ((simulateQ (cappedSplitEncodingTracedMappedAdversaryImpl publicKey secretKey)
          computation).run state)] =
      𝒟[(simulateQ (cappedEncodingTracedMappedAdversaryImpl publicKey secretKey)
        computation).run state] := by
  rw [QueryImpl.simulateQ_mapStateTBase_run]
  apply OracleComp.evalDist_simulateQ_run_congr
  intro input currentState
  exact cappedSplitEncodingTracedMappedAdversaryImpl_query_bridge
    publicKey secretKey input currentState

noncomputable def cappedSplitDetailedGameAfterKeygenWithEncodingTrace
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) :
    OracleComp EncodingSamplingWorld (GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) := do
  let (forgery, adversaryState) ←
    (simulateQ (cappedSplitEncodingTracedMappedAdversaryImpl publicKey secretKey)
      (adversary.main publicKey)).run ((initialCache, []), [])
  let (verified, finalCache) ←
    (simulateQ (splitXmssRomImpl secretKey.parameter .query)
      (Concrete.scheme.verify publicKey forgery.epoch forgery.message
        forgery.signature)).run adversaryState.1.1
  let finalEncodingTrace := appendVerificationEncodingObservation secretKey forgery
    adversaryState.1.1 finalCache adversaryState.2
  pure (⟨publicKey, secretKey, forgery, adversaryState.1.2.toSigningLog, verified⟩,
    ((finalCache, adversaryState.1.2), finalEncodingTrace))

theorem cappedSplitDetailedGameAfterKeygenWithEncodingTrace_evalDist_simulation
    (adversary : Adversary Concrete.scheme)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) :
    𝒟[simulateQ encodingSamplingWorldImpl
        (cappedSplitDetailedGameAfterKeygenWithEncodingTrace adversary publicKey
          secretKey initialCache)] =
      𝒟[cappedDetailedGameAfterKeygenWithEncodingTrace adversary publicKey secretKey
        initialCache] := by
  unfold cappedSplitDetailedGameAfterKeygenWithEncodingTrace
    cappedDetailedGameAfterKeygenWithEncodingTrace
  simp only [simulateQ_bind, simulateQ_pure, evalDist_bind]
  rw [cappedSplitEncodingTracedMappedAdversary_evalDist_simulation]
  simp_rw [splitXmssRom_evalDist_simulation]

noncomputable def cappedSplitDetailedGameWithEncodingTrace
    (adversary : Adversary Concrete.scheme) :
    ProbComp (GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) := do
  let keyResult ← (simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅
  simulateQ encodingSamplingWorldImpl
    (cappedSplitDetailedGameAfterKeygenWithEncodingTrace adversary keyResult.1.1
      keyResult.1.2 keyResult.2)

theorem cappedSplitDetailedGameWithEncodingTrace_evalDist_simulation
    (adversary : Adversary Concrete.scheme) :
    𝒟[cappedSplitDetailedGameWithEncodingTrace adversary] =
      𝒟[cappedDetailedGameWithEncodingTrace adversary] := by
  unfold cappedSplitDetailedGameWithEncodingTrace
    cappedDetailedGameWithEncodingTrace
  simp only [evalDist_bind]
  simp_rw [cappedSplitDetailedGameAfterKeygenWithEncodingTrace_evalDist_simulation]

noncomputable def cappedSampledDetailedGameWithEncodingTrace
    (adversary : Adversary Concrete.scheme) :
    ProbComp ((GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) ×
        EncodingActionTrace) := do
  let keyResult ← (simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅
  (simulateQ encodingSamplingTraceImpl
    (cappedSplitDetailedGameAfterKeygenWithEncodingTrace adversary keyResult.1.1
      keyResult.1.2 keyResult.2)).run

theorem cappedSampledDetailedGameWithEncodingTrace_projection
    (adversary : Adversary Concrete.scheme) :
    Prod.fst <$> cappedSampledDetailedGameWithEncodingTrace adversary =
      cappedSplitDetailedGameWithEncodingTrace adversary := by
  unfold cappedSampledDetailedGameWithEncodingTrace
    cappedSplitDetailedGameWithEncodingTrace
  rw [map_bind]
  apply bind_congr
  intro keyResult
  exact encodingSamplingTrace_projection
    (cappedSplitDetailedGameAfterKeygenWithEncodingTrace adversary keyResult.1.1
      keyResult.1.2 keyResult.2)

theorem cappedDetailedGameWithEncodingTrace_monitorHit_probability_eq_sampled
    (adversary : Adversary Concrete.scheme) :
    Pr[(fun execution : GameOutcome ×
        ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) =>
      CappedEncodingMonitor.runObserved EncodingMonitor.State.empty execution.2.2 = true) |
      cappedDetailedGameWithEncodingTrace adversary] =
    Pr[(fun execution : (GameOutcome ×
        ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) ×
          EncodingActionTrace =>
      CappedEncodingMonitor.runObserved EncodingMonitor.State.empty
        execution.1.2.2 = true) |
      cappedSampledDetailedGameWithEncodingTrace adversary] := by
  calc
    _ = Pr[(fun execution : GameOutcome ×
          ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) =>
        CappedEncodingMonitor.runObserved EncodingMonitor.State.empty
          execution.2.2 = true) |
        cappedSplitDetailedGameWithEncodingTrace adversary] := by
      rw [probEvent_def, probEvent_def,
        cappedSplitDetailedGameWithEncodingTrace_evalDist_simulation]
    _ = _ := by
      rw [← cappedSampledDetailedGameWithEncodingTrace_projection, probEvent_map]
      rfl

end XmssSecurity
