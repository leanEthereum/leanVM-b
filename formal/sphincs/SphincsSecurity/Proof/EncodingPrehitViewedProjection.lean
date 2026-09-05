import SphincsSecurity.Proof.EncodingPrehitViewedTrace

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec TightEncoding

noncomputable def encodingPrehitLoggedAdversaryImpl (accountingKey secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT ((QueryCache HashSpec × Bool) × QueryLog SigningSpec) ProbComp) :=
  fun input state => do
    let result ← (((encodingPrehitImpl accountingKey).writerTMapBase
      (forwardOracles + signingOracle scheme secretKey) input).run).run state.1
    pure (result.1.1, (result.2, state.2 ++ result.1.2))

theorem encodingPrehitLoggedAdversaryImpl_query (accountingKey secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (cache : QueryCache HashSpec) (hit : Bool) (log : QueryLog SigningSpec) :
    (encodingPrehitLoggedAdversaryImpl accountingKey secretKey input).run ((cache, hit), log) =
      (fun result => (result.1.1.1, ((result.1.2, result.2), log ++ result.1.1.2))) <$>
        runEncodingPrehitMonitor accountingKey
          (((forwardOracles + signingOracle scheme secretKey) input).run) cache hit := by
  change (((encodingPrehitImpl accountingKey).writerTMapBase
    (forwardOracles + signingOracle scheme secretKey) input).run).run (cache, hit) >>= _ = _
  rw [QueryImpl.writerTMapBase, WriterT.run_mk, simulateQ_encodingPrehitImpl_run]
  simp

theorem encodingPrehitLoggedAdversaryImpl_run (accountingKey secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) (hit : Bool) (log : QueryLog SigningSpec) :
    (simulateQ (encodingPrehitLoggedAdversaryImpl accountingKey secretKey) computation).run ((cache, hit), log) =
      (fun result => (result.1.1.1, ((result.1.2, result.2), log ++ result.1.1.2))) <$>
        runEncodingPrehitMonitor accountingKey
          ((simulateQ (forwardOracles + signingOracle scheme secretKey) computation).run) cache hit := by
  rw [runEncodingPrehitMonitor_eq_simulateQ, Functor.map_map,
    QueryImpl.simulateQ_writerTMapBase_run]
  induction computation using OracleComp.inductionOn generalizing cache hit log with
  | pure value => simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind',
        StateT.run_bind, StateT.run_map, map_bind, Functor.map_map]
      simp only [encodingPrehitLoggedAdversaryImpl, StateT.run, bind_assoc, pure_bind]
      apply bind_congr
      intro result
      simpa [List.append_assoc, StateT.run] using ih result.1.1 result.2.1 result.2.2 (log ++ result.1.2)

def encodingPrehitViewedLogState (state : ViewedFullTraceState × Bool) :
    (QueryCache HashSpec × Bool) × QueryLog SigningSpec :=
  ((state.1.cache, state.2), state.1.trace.signing.toSigningLog)

theorem encodingPrehitViewedAdversaryImpl_query_log_projection
    (accountingKey secretKey : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (state : ViewedFullTraceState × Bool) :
    Prod.map id encodingPrehitViewedLogState <$>
      (encodingPrehitViewedAdversaryImpl accountingKey secretKey input).run state =
      (encodingPrehitLoggedAdversaryImpl accountingKey secretKey input).run
        (encodingPrehitViewedLogState state) := by
  change _ = (encodingPrehitLoggedAdversaryImpl accountingKey secretKey input).run
    ((state.1.cache, state.2), state.1.trace.signing.toSigningLog)
  rw [encodingPrehitLoggedAdversaryImpl_query]
  cases input with
  | inl query =>
      have hquery : (((forwardOracles + signingOracle scheme secretKey) (.inl query)).run) =
          (fun output => (output, ([] : QueryLog SigningSpec))) <$>
            (liftM (OracleWorld.query query) : OracleComp OracleWorld _) := rfl
      rw [hquery]
      erw [runEncodingPrehitMonitor_map]
      cases query <;>
        simp [encodingPrehitViewedAdversaryImpl, encodingPrehitViewedLogState,
          fullAdversaryTraceUpdate, signingCacheTraceUpdate, StateT.run, Prod.map]
  | inr request =>
      have hquery : (((forwardOracles + signingOracle scheme secretKey) (.inr request)).run) =
          (fun output => (output, ([⟨request, output⟩] : QueryLog SigningSpec))) <$>
            sign secretKey request := by
        change (QueryImpl.withLogging (spec := SigningSpec) (fun request => scheme.sign secretKey request) request).run = _
        rw [QueryImpl.run_withLogging_apply]
        rfl
      have hsign := runEncodingPrehitMonitor_map accountingKey Prod.fst
        (signWithView secretKey request) state.1.cache state.2
      rw [signWithView_fst] at hsign
      rw [hquery]
      erw [runEncodingPrehitMonitor_map]
      rw [hsign]
      simp [encodingPrehitViewedAdversaryImpl, encodingPrehitViewedLogState,
        fullAdversaryTraceUpdate, signingCacheTraceUpdate, SigningCacheTrace.toSigningLog,
        StateT.run, Prod.map]

theorem encodingPrehitViewedAdversaryImpl_log_projection
    (accountingKey secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : ViewedFullTraceState × Bool) :
    Prod.map id encodingPrehitViewedLogState <$>
      (simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey) computation).run state =
      (fun result => (result.1.1.1,
        ((result.1.2, result.2), state.1.trace.signing.toSigningLog ++ result.1.1.2))) <$>
        runEncodingPrehitMonitor accountingKey
          ((simulateQ (forwardOracles + signingOracle scheme secretKey) computation).run) state.1.cache state.2 := by
  rw [← encodingPrehitLoggedAdversaryImpl_run]
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (encodingPrehitViewedAdversaryImpl accountingKey secretKey)
    (encodingPrehitLoggedAdversaryImpl accountingKey secretKey) encodingPrehitViewedLogState
  exact encodingPrehitViewedAdversaryImpl_query_log_projection accountingKey secretKey

theorem encodingPrehitViewedAdversaryImpl_support_monitor
    (accountingKey secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : ViewedFullTraceState × Bool)
    (result : α × (ViewedFullTraceState × Bool))
    (hresult : result ∈ support
      ((simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey) computation).run state)) :
    ∃ log : QueryLog SigningSpec,
      (((result.1, log), result.2.1.cache), result.2.2) ∈ support
        (runEncodingPrehitMonitor accountingKey
          ((simulateQ (forwardOracles + signingOracle scheme secretKey) computation).run) state.1.cache state.2) ∧
      state.1.trace.signing.toSigningLog ++ log = result.2.1.trace.signing.toSigningLog := by
  have hproject : Prod.map id encodingPrehitViewedLogState result ∈ support
      ((fun result => (result.1.1.1,
        ((result.1.2, result.2), state.1.trace.signing.toSigningLog ++ result.1.1.2))) <$>
        runEncodingPrehitMonitor accountingKey
          ((simulateQ (forwardOracles + signingOracle scheme secretKey) computation).run) state.1.cache state.2) := by
    rw [← encodingPrehitViewedAdversaryImpl_log_projection, support_map]
    exact ⟨result, hresult, rfl⟩
  rw [support_map] at hproject
  obtain ⟨⟨⟨⟨value, log⟩, cache⟩, hit⟩, hrun, heq⟩ := hproject
  simp only [Prod.map, id_eq, encodingPrehitViewedLogState, Prod.mk.injEq] at heq
  obtain ⟨rfl, ⟨rfl, rfl⟩, hlog⟩ := heq
  exact ⟨log, hrun, hlog⟩

theorem runEncodingPrehitMonitor_verifyWithView_fst (accountingKey : SecretKey)
    (publicKey : PublicKey) (message : Message) (signature : Signature)
    (cache : QueryCache HashSpec) (hit : Bool) :
    runEncodingPrehitMonitor accountingKey (scheme.verify publicKey message signature) cache hit =
      (fun result => ((result.1.1.1, result.1.2), result.2)) <$>
        runEncodingPrehitMonitor accountingKey
          (liftM (verifyWithView publicKey message signature) : OracleComp OracleWorld (Bool × FewTimeView))
          cache hit := by
  have heq : scheme.verify publicKey message signature =
      Prod.fst <$> (liftM (verifyWithView publicKey message signature) :
        OracleComp OracleWorld (Bool × FewTimeView)) := by
    rw [← liftM_map, verifyWithView_fst]
    rfl
  rw [heq, runEncodingPrehitMonitor_map]

theorem gameRestWithEncodingPrehitView_monitor_projection (adversary : Adversary)
    (accountingKey : SecretKey) (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) (hit : Bool) :
    (fun result => ((result.1.2, result.2.1.cache), result.2.2)) <$>
      gameRestWithEncodingPrehitView adversary accountingKey publicKey secretKey initialCache hit =
      runEncodingPrehitMonitor accountingKey (gameRest scheme adversary publicKey secretKey) initialCache hit := by
  let finish : Forgery × ((QueryCache HashSpec × Bool) × QueryLog SigningSpec) →
      ProbComp ((Bool × QueryCache HashSpec) × Bool) := fun result => do
    let verified ← runEncodingPrehitMonitor accountingKey
      (scheme.verify publicKey result.1.message result.1.signature) result.2.1.1 result.2.1.2
    pure ((decide (SigningTranscript.Valid result.2.2 ∧
      ¬ SigningTranscript.Contains result.2.2 result.1) && verified.1.1, verified.1.2), verified.2)
  let state : ViewedFullTraceState × Bool := (⟨initialCache, ⟨[], [], []⟩, [], none⟩, hit)
  calc
    _ = (Prod.map id encodingPrehitViewedLogState <$>
        (simulateQ (encodingPrehitViewedAdversaryImpl accountingKey secretKey)
          (adversary.main publicKey)).run state) >>= finish := by
      simp [gameRestWithEncodingPrehitView, state, finish, encodingPrehitViewedLogState,
        runEncodingPrehitMonitor_verifyWithView_fst, map_bind, bind_map_left, Prod.map]
      rfl
    _ = _ := by
      rw [encodingPrehitViewedAdversaryImpl_log_projection]
      rw [gameRest, runEncodingPrehitMonitor_bind]
      simp only [runEncodingPrehitMonitor_bind, runEncodingPrehitMonitor_pure]
      simp [finish, state, SigningCacheTrace.toSigningLog, bind_map_left]

theorem gameAfterSecretsWithEncodingPrehitView_monitor_projection (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    (fun result => ((result.1.2.2, result.2.1.cache), result.2.2)) <$>
      gameAfterSecretsWithEncodingPrehitView adversary parameter otsSecret ftsSecret =
      runEncodingPrehitMonitor (primitiveAccountingKey parameter otsSecret ftsSecret)
        (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅ false := by
  rw [gameAfterSecretsWithEncodingPrehitView, gameAfterSecrets, runEncodingPrehitMonitor_bind]
  simp only [map_bind]
  apply bind_congr
  intro result
  rw [← gameRestWithEncodingPrehitView_monitor_projection adversary
    (primitiveAccountingKey parameter otsSecret ftsSecret) ⟨result.1.1, parameter⟩
    ⟨parameter, result.1.1, otsSecret, ftsSecret⟩ result.1.2 result.2]
  simp

end SphincsSecurity.Concrete
