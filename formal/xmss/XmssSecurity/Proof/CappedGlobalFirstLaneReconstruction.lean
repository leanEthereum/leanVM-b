import XmssSecurity.Proof.CappedGlobalFirstLaneErasure
import XmssSecurity.Proof.CappedEncodingActionTrace

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

def appendAttackerActionTrace
    (input : (OracleWorld + SigningSpec).Domain)
    (_initialState : (QueryCache HashSpec × SigningCacheTrace) ×
      EncodingActionTrace)
    (output : (OracleWorld + SigningSpec).Range input)
    (_finalState : (QueryCache HashSpec × SigningCacheTrace) ×
      EncodingActionTrace)
    (trace : AttackerActionTrace) : AttackerActionTrace :=
  trace ++ attackerActionFragment input output

noncomputable def cappedBothTracedMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT ((((QueryCache HashSpec × SigningCacheTrace) ×
        EncodingActionTrace) × AttackerActionTrace)) ProbComp) :=
  QueryImpl.extendState
    (cappedEncodingTracedMappedAdversaryImpl publicKey secretKey)
      appendAttackerActionTrace

theorem cappedBothTracedMappedAdversaryImpl_projection
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : (QueryCache HashSpec × SigningCacheTrace) ×
      EncodingActionTrace)
    (initialTrace : AttackerActionTrace) :
    Prod.map id Prod.fst <$>
        (simulateQ (cappedBothTracedMappedAdversaryImpl publicKey secretKey)
          computation).run (initialState, initialTrace) =
      (simulateQ (cappedEncodingTracedMappedAdversaryImpl publicKey secretKey)
        computation).run initialState := by
  exact OracleComp.extendState_run_proj_eq
    (cappedEncodingTracedMappedAdversaryImpl publicKey secretKey)
    appendAttackerActionTrace computation initialState initialTrace

theorem cappedUnloggedMappedAdversaryImpl_eq_sourceDirectMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    cappedUnloggedMappedAdversaryImpl publicKey secretKey =
      sourceDirectMappedAdversaryImpl publicKey secretKey := by
  funext input
  cases input with
  | inl worldInput => rfl
  | inr request => rfl

theorem cappedEncodingTracedMappedAdversaryImpl_actionProjection
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : (QueryCache HashSpec × SigningCacheTrace) ×
      EncodingActionTrace) :
    Prod.map id (fun state => state.1.1) <$>
        (simulateQ (cappedEncodingTracedMappedAdversaryImpl publicKey secretKey)
          computation).run initialState =
      (simulateQ (sourceDirectMappedAdversaryImpl publicKey secretKey)
        computation).run initialState.1.1 := by
  calc
    _ = Prod.map id Prod.fst <$>
        (simulateQ (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
          computation).run initialState.1 := by
      rw [← cappedEncodingTracedMappedAdversaryImpl_projection publicKey
        secretKey computation initialState.1 initialState.2]
      simp only [Functor.map_map]
      rfl
    _ = (simulateQ (cappedUnloggedMappedAdversaryImpl publicKey secretKey)
          computation).run initialState.1.1 :=
      cappedCacheTracedMappedAdversaryImpl_cache_projection publicKey secretKey
        computation initialState.1.1 initialState.1.2
    _ = _ := by
      rw [cappedUnloggedMappedAdversaryImpl_eq_sourceDirectMappedAdversaryImpl]

theorem cappedBothTracedMappedAdversaryImpl_eq_actionTracedStateImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    cappedBothTracedMappedAdversaryImpl publicKey secretKey =
      actionTracedStateImpl
        (cappedEncodingTracedMappedAdversaryImpl publicKey secretKey)
        attackerActionFragment := by
  funext input
  unfold cappedBothTracedMappedAdversaryImpl appendAttackerActionTrace
    QueryImpl.extendState actionTracedStateImpl
  rfl

theorem cappedBothTracedMappedAdversaryImpl_query_logs_eq
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : ((QueryCache HashSpec × SigningCacheTrace) ×
      EncodingActionTrace) × AttackerActionTrace)
    (result : (OracleWorld + SigningSpec).Range input ×
      (((QueryCache HashSpec × SigningCacheTrace) ×
        EncodingActionTrace) × AttackerActionTrace))
    (hlogs : initialState.1.1.2.toSigningLog =
      initialState.2.toSigningLog)
    (hmem : result ∈ support
      ((cappedBothTracedMappedAdversaryImpl publicKey secretKey input).run
        initialState)) :
    result.2.1.1.2.toSigningLog = result.2.2.toSigningLog := by
  rw [cappedBothTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    mem_support_bind_iff] at hmem
  obtain ⟨⟨output, encodingState⟩, hencoding, hpure⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  rw [cappedEncodingTracedMappedAdversaryImpl,
    QueryImpl.extendState_apply, mem_support_bind_iff] at hencoding
  obtain ⟨⟨cacheOutput, finalState⟩, hbase, hencodingPure⟩ := hencoding
  simp only [support_pure, Set.mem_singleton_iff] at hencodingPure
  have houtput : output = cacheOutput := congrArg Prod.fst hencodingPure
  have hstate : encodingState =
      (finalState,
        encodingActionTraceUpdate secretKey input initialState.1.1 cacheOutput
          finalState initialState.1.2) :=
    congrArg Prod.snd hencodingPure
  subst output
  subst encodingState
  have htraceEq :=
    cappedCacheTracedMappedAdversaryImpl_query_signingTrace_eq
      publicKey secretKey input initialState.1.1 (cacheOutput, finalState) hbase
  have htraceEq' : finalState.2 = signingCacheTraceUpdate input
      initialState.1.1.1 cacheOutput finalState.1 initialState.1.1.2 := by
    simpa using htraceEq
  change finalState.2.toSigningLog =
    (initialState.2 ++ attackerActionFragment input cacheOutput).toSigningLog
  rw [htraceEq', signingCacheTraceUpdate_toSigningLog,
    signingLogUpdate, AttackerActionTrace.toSigningLog_append,
    attackerActionFragment_toSigningLog, hlogs]

theorem cappedBothTracedMappedAdversaryImpl_logs_eq
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : ((QueryCache HashSpec × SigningCacheTrace) ×
      EncodingActionTrace) × AttackerActionTrace)
    (result : α × (((QueryCache HashSpec × SigningCacheTrace) ×
      EncodingActionTrace) × AttackerActionTrace))
    (hlogs : initialState.1.1.2.toSigningLog =
      initialState.2.toSigningLog)
    (hmem : result ∈ support
      ((simulateQ (cappedBothTracedMappedAdversaryImpl publicKey secretKey)
        computation).run initialState)) :
    result.2.1.1.2.toSigningLog = result.2.2.toSigningLog := by
  exact OracleComp.simulateQ_run_preservesInv
    (cappedBothTracedMappedAdversaryImpl publicKey secretKey)
    (fun state => state.1.1.2.toSigningLog = state.2.toSigningLog)
    (by
      intro input state hstate result hresult
      exact cappedBothTracedMappedAdversaryImpl_query_logs_eq
        publicKey secretKey input state result hstate hresult)
    computation initialState hlogs result hmem

theorem cappedBothTracedMappedAdversaryImpl_actionProjection
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : (QueryCache HashSpec × SigningCacheTrace) ×
      EncodingActionTrace)
    (initialTrace : AttackerActionTrace) :
    Prod.map id (fun state => (state.1.1.1, state.2)) <$>
        (simulateQ (cappedBothTracedMappedAdversaryImpl publicKey secretKey)
          computation).run (initialState, initialTrace) =
      (simulateQ (sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (initialState.1.1, initialTrace) := by
  rw [cappedBothTracedMappedAdversaryImpl_eq_actionTracedStateImpl]
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (actionTracedStateImpl
      (cappedEncodingTracedMappedAdversaryImpl publicKey secretKey)
      attackerActionFragment)
    (sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
    (fun state => (state.1.1.1, state.2))
  intro input state
  have hbase := cappedEncodingTracedMappedAdversaryImpl_actionProjection
    publicKey secretKey
      (liftM (OracleSpec.query input) :
        OracleComp (OracleWorld + SigningSpec) _) state.1
  have hbase' :
      Prod.map id (fun state => state.1.1) <$>
          (cappedEncodingTracedMappedAdversaryImpl publicKey secretKey input).run
            state.1 =
        (sourceDirectMappedAdversaryImpl publicKey secretKey input).run
          state.1.1.1 := by
    simpa [simulateQ_query] using hbase
  unfold sourceDirectTracedMappedAdversaryImpl
  unfold actionTracedStateImpl
  simp only [StateT.run_mk, map_bind]
  rw [← hbase']
  simp only [bind_map_left, map_pure]
  rfl

abbrev CappedBothTraceExecution :=
  GameOutcome × (((QueryCache HashSpec × SigningCacheTrace) ×
    EncodingActionTrace) × AttackerActionTrace)

abbrev CappedEncodingTraceExecution :=
  GameOutcome × ((QueryCache HashSpec × SigningCacheTrace) ×
    EncodingActionTrace)

noncomputable def cappedDetailedGameAfterKeygenWithBothTraces
    (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) :
    ProbComp CappedBothTraceExecution := do
  let result ←
    (simulateQ (cappedBothTracedMappedAdversaryImpl publicKey secretKey)
      (adversary.main publicKey)).run ((((initialCache, []), []), []))
  let forgery := result.1
  let state := result.2
  let verified ← (simulateQ xmssRomImpl
    (Concrete.scheme.verify publicKey forgery.epoch forgery.message
      forgery.signature)).run state.1.1.1
  let finalEncodingTrace := appendVerificationEncodingObservation secretKey
    forgery state.1.1.1 verified.2 state.1.2
  pure (⟨publicKey, secretKey, forgery, state.1.1.2.toSigningLog,
      verified.1⟩,
    (((verified.2, state.1.1.2), finalEncodingTrace), state.2))

theorem cappedDetailedGameAfterKeygenWithBothTraces_logs_eq
    (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec)
    (result : CappedBothTraceExecution)
    (hresult : result ∈ support
      (cappedDetailedGameAfterKeygenWithBothTraces adversary publicKey
        secretKey initialCache)) :
    result.1.signingLog = result.2.2.toSigningLog := by
  unfold cappedDetailedGameAfterKeygenWithBothTraces at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨⟨forgery, adversaryState⟩, hadversary, hverifyRest⟩ := hresult
  rw [mem_support_bind_iff] at hverifyRest
  obtain ⟨⟨verified, finalCache⟩, _hverify, hfinal⟩ := hverifyRest
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  exact cappedBothTracedMappedAdversaryImpl_logs_eq publicKey secretKey
    (adversary.main publicKey) ((((initialCache, []), []), []))
      (forgery, adversaryState) rfl hadversary

theorem cappedDetailedGameAfterKeygenWithBothTraces_outcome_eq_actionTraceOutcome
    (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec)
    (result : CappedBothTraceExecution)
    (hresult : result ∈ support
      (cappedDetailedGameAfterKeygenWithBothTraces adversary publicKey
        secretKey initialCache)) :
    result.1 = actionTraceOutcome publicKey secretKey
      ((result.1.forgery, result.1.verified), result.2.2) := by
  have hlogs := cappedDetailedGameAfterKeygenWithBothTraces_logs_eq
    adversary publicKey secretKey initialCache result hresult
  unfold cappedDetailedGameAfterKeygenWithBothTraces at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨⟨forgery, adversaryState⟩, hadversary, hverifyRest⟩ := hresult
  rw [mem_support_bind_iff] at hverifyRest
  obtain ⟨⟨verified, finalCache⟩, hverify, hfinal⟩ := hverifyRest
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  simp only [actionTraceOutcome]
  have hlogs' : adversaryState.1.1.2.toSigningLog =
      adversaryState.2.toSigningLog := by
    simpa using hlogs
  rw [hlogs']

theorem cappedDetailedGameAfterKeygenWithBothTraces_encodingProjection
    (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) :
    (fun result : CappedBothTraceExecution => (result.1, result.2.1)) <$>
        cappedDetailedGameAfterKeygenWithBothTraces adversary publicKey
          secretKey initialCache =
      cappedDetailedGameAfterKeygenWithEncodingTrace adversary publicKey
        secretKey initialCache := by
  let finish : Forgery ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) →
      ProbComp CappedEncodingTraceExecution := fun result => do
    let verified ← (simulateQ xmssRomImpl
      (Concrete.scheme.verify publicKey result.1.epoch result.1.message
        result.1.signature)).run result.2.1.1
    let finalEncodingTrace := appendVerificationEncodingObservation secretKey
      result.1 result.2.1.1 verified.2 result.2.2
    pure (⟨publicKey, secretKey, result.1, result.2.1.2.toSigningLog,
      verified.1⟩, ((verified.2, result.2.1.2), finalEncodingTrace))
  have hprojection := cappedBothTracedMappedAdversaryImpl_projection
    publicKey secretKey (adversary.main publicKey) (((initialCache, []), [])) []
  have hbound := congrArg (fun computation => computation >>= finish) hprojection
  simpa [cappedDetailedGameAfterKeygenWithBothTraces,
    cappedDetailedGameAfterKeygenWithEncodingTrace, finish, map_bind,
    bind_map_left, bind_assoc, Prod.map] using hbound

abbrev CappedBothTraceGameResult :=
  ((PublicKey × SecretKey) × QueryCache HashSpec) ×
    CappedBothTraceExecution

abbrev CappedActionTraceGameResult :=
  ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
    (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace)

def cappedBothEncodingProjection
    (result : CappedBothTraceGameResult) : CappedEncodingTraceExecution :=
  (result.2.1, result.2.2.1)

def cappedBothActionProjection
    (result : CappedBothTraceGameResult) : CappedActionTraceGameResult :=
  ((result.1,
    (actionTraceOutcome result.1.1.1 result.1.1.2
      ((result.2.1.forgery, result.2.1.verified), result.2.2.2),
      result.2.2.1.1.1)), result.2.2.2)

noncomputable def cappedDetailedGameWithKeygenCacheAndBothTraces
    (adversary : Adversary) :
    ProbComp CappedBothTraceGameResult := do
  let keyResult ← (simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅
  let execution ← cappedDetailedGameAfterKeygenWithBothTraces adversary
    keyResult.1.1 keyResult.1.2 keyResult.2
  pure (keyResult, execution)

theorem cappedDetailedGameWithKeygenCacheAndBothTraces_support_execution
    (adversary : Adversary)
    (result : CappedBothTraceGameResult)
    (hresult : result ∈ support
      (cappedDetailedGameWithKeygenCacheAndBothTraces adversary)) :
    result.2 ∈ support
      (cappedDetailedGameAfterKeygenWithBothTraces adversary result.1.1.1
        result.1.1.2 result.1.2) := by
  unfold cappedDetailedGameWithKeygenCacheAndBothTraces at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨keyResult, _hkeyResult, hrest⟩ := hresult
  rw [mem_support_bind_iff] at hrest
  obtain ⟨execution, hexecution, hfinal⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  exact hexecution

theorem cappedDetailedGameWithKeygenCacheAndBothTraces_outcome_eq
    (adversary : Adversary)
    (result : CappedBothTraceGameResult)
    (hresult : result ∈ support
      (cappedDetailedGameWithKeygenCacheAndBothTraces adversary)) :
    result.2.1 = (cappedBothActionProjection result).1.2.1 := by
  exact cappedDetailedGameAfterKeygenWithBothTraces_outcome_eq_actionTraceOutcome
    adversary result.1.1.1 result.1.1.2 result.1.2 result.2
      (cappedDetailedGameWithKeygenCacheAndBothTraces_support_execution
        adversary result hresult)

theorem cappedDetailedGameWithKeygenCacheAndBothTraces_encodingProjection
    (adversary : Adversary) :
    (fun result : CappedBothTraceGameResult =>
        (result.2.1, result.2.2.1)) <$>
        cappedDetailedGameWithKeygenCacheAndBothTraces adversary =
      cappedDetailedGameWithEncodingTrace adversary := by
  unfold cappedDetailedGameWithKeygenCacheAndBothTraces
    cappedDetailedGameWithEncodingTrace
  simp only [map_bind]
  apply bind_congr
  intro keyResult
  rw [← cappedDetailedGameAfterKeygenWithBothTraces_encodingProjection
    adversary keyResult.1.1 keyResult.1.2 keyResult.2]
  simp

theorem cappedDetailedGameWithKeygenCacheAndBothTraces_encodingProjection_eq
    (adversary : Adversary) :
    cappedBothEncodingProjection <$>
        cappedDetailedGameWithKeygenCacheAndBothTraces adversary =
      cappedDetailedGameWithEncodingTrace adversary :=
  cappedDetailedGameWithKeygenCacheAndBothTraces_encodingProjection adversary

end XmssSecurity.CappedChain
