import SphincsSecurity.Proof.SettledCollisionViewedTrace

namespace SphincsSecurity.Concrete.SettledCollision

open OracleComp OracleSpec

noncomputable def loggedAdversaryImpl (accountingKey secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT ((QueryCache HashSpec × History) × QueryLog SigningSpec) ProbComp) :=
  fun input state => do
    let result ← (((monitorImpl accountingKey).writerTMapBase
      (forwardOracles + signingOracle scheme secretKey) input).run).run state.1
    pure (result.1.1, (result.2, state.2 ++ result.1.2))

theorem loggedAdversaryImpl_query (accountingKey secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (cache : QueryCache HashSpec) (history : History) (log : QueryLog SigningSpec) :
    (loggedAdversaryImpl accountingKey secretKey input).run ((cache, history), log) =
      (fun result => (result.1.1.1, ((result.1.2, result.2), log ++ result.1.1.2))) <$>
        runMonitor accountingKey
          (((forwardOracles + signingOracle scheme secretKey) input).run) cache history := by
  change (((monitorImpl accountingKey).writerTMapBase
    (forwardOracles + signingOracle scheme secretKey) input).run).run (cache, history) >>= _ = _
  rw [QueryImpl.writerTMapBase, WriterT.run_mk, simulateQ_monitorImpl_run]
  simp

theorem loggedAdversaryImpl_run (accountingKey secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) (history : History) (log : QueryLog SigningSpec) :
    (simulateQ (loggedAdversaryImpl accountingKey secretKey) computation).run ((cache, history), log) =
      (fun result => (result.1.1.1, ((result.1.2, result.2), log ++ result.1.1.2))) <$>
        runMonitor accountingKey
          ((simulateQ (forwardOracles + signingOracle scheme secretKey) computation).run) cache history := by
  rw [runMonitor_eq_simulateQ, Functor.map_map,
    QueryImpl.simulateQ_writerTMapBase_run]
  induction computation using OracleComp.inductionOn generalizing cache history log with
  | pure value => simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind',
        StateT.run_bind, StateT.run_map, map_bind, Functor.map_map]
      simp only [loggedAdversaryImpl, StateT.run, bind_assoc, pure_bind]
      apply bind_congr
      intro result
      simpa [List.append_assoc, StateT.run] using ih result.1.1 result.2.1 result.2.2 (log ++ result.1.2)

def viewedLogState (state : ViewedFullTraceState × History) :
    (QueryCache HashSpec × History) × QueryLog SigningSpec :=
  ((state.1.cache, state.2), state.1.trace.signing.toSigningLog)

theorem viewedAdversaryImpl_query_log_projection
    (accountingKey secretKey : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (state : ViewedFullTraceState × History) :
    Prod.map id viewedLogState <$>
      (viewedAdversaryImpl accountingKey secretKey input).run state =
      (loggedAdversaryImpl accountingKey secretKey input).run
        (viewedLogState state) := by
  change _ = (loggedAdversaryImpl accountingKey secretKey input).run
    ((state.1.cache, state.2), state.1.trace.signing.toSigningLog)
  rw [loggedAdversaryImpl_query]
  cases input with
  | inl query =>
      have hquery : (((forwardOracles + signingOracle scheme secretKey) (.inl query)).run) =
          (fun output => (output, ([] : QueryLog SigningSpec))) <$>
            (liftM (OracleWorld.query query) : OracleComp OracleWorld _) := rfl
      rw [hquery]
      erw [runMonitor_map]
      cases query <;>
        simp [viewedAdversaryImpl, viewedLogState,
          fullAdversaryTraceUpdate, signingCacheTraceUpdate, StateT.run, Prod.map]
  | inr request =>
      have hquery : (((forwardOracles + signingOracle scheme secretKey) (.inr request)).run) =
          (fun output => (output, ([⟨request, output⟩] : QueryLog SigningSpec))) <$>
            sign secretKey request := by
        change (QueryImpl.withLogging (spec := SigningSpec) (fun request => scheme.sign secretKey request) request).run = _
        rw [QueryImpl.run_withLogging_apply]
        rfl
      have hsign := runMonitor_map accountingKey Prod.fst
        (signWithView secretKey request) state.1.cache state.2
      rw [signWithView_fst] at hsign
      rw [hquery]
      erw [runMonitor_map]
      rw [hsign]
      simp [viewedAdversaryImpl, viewedLogState,
        fullAdversaryTraceUpdate, signingCacheTraceUpdate, SigningCacheTrace.toSigningLog,
        StateT.run, Prod.map]

theorem viewedAdversaryImpl_log_projection
    (accountingKey secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : ViewedFullTraceState × History) :
    Prod.map id viewedLogState <$>
      (simulateQ (viewedAdversaryImpl accountingKey secretKey) computation).run state =
      (fun result => (result.1.1.1,
        ((result.1.2, result.2), state.1.trace.signing.toSigningLog ++ result.1.1.2))) <$>
        runMonitor accountingKey
          ((simulateQ (forwardOracles + signingOracle scheme secretKey) computation).run) state.1.cache state.2 := by
  rw [← loggedAdversaryImpl_run]
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (viewedAdversaryImpl accountingKey secretKey)
    (loggedAdversaryImpl accountingKey secretKey) viewedLogState
  exact viewedAdversaryImpl_query_log_projection accountingKey secretKey

theorem viewedAdversaryImpl_support_monitor
    (accountingKey secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : ViewedFullTraceState × History)
    (result : α × (ViewedFullTraceState × History))
    (hresult : result ∈ support
      ((simulateQ (viewedAdversaryImpl accountingKey secretKey) computation).run state)) :
    ∃ log : QueryLog SigningSpec,
      (((result.1, log), result.2.1.cache), result.2.2) ∈ support
        (runMonitor accountingKey
          ((simulateQ (forwardOracles + signingOracle scheme secretKey) computation).run) state.1.cache state.2) ∧
      state.1.trace.signing.toSigningLog ++ log = result.2.1.trace.signing.toSigningLog := by
  have hproject : Prod.map id viewedLogState result ∈ support
      ((fun result => (result.1.1.1,
        ((result.1.2, result.2), state.1.trace.signing.toSigningLog ++ result.1.1.2))) <$>
        runMonitor accountingKey
          ((simulateQ (forwardOracles + signingOracle scheme secretKey) computation).run) state.1.cache state.2) := by
    rw [← viewedAdversaryImpl_log_projection, support_map]
    exact ⟨result, hresult, rfl⟩
  rw [support_map] at hproject
  obtain ⟨⟨⟨⟨value, log⟩, cache⟩, history⟩, hrun, heq⟩ := hproject
  simp only [Prod.map, id_eq, viewedLogState, Prod.mk.injEq] at heq
  obtain ⟨rfl, ⟨rfl, rfl⟩, hlog⟩ := heq
  exact ⟨log, hrun, hlog⟩

theorem runMonitor_verifyWithView_fst (accountingKey : SecretKey)
    (publicKey : PublicKey) (message : Message) (signature : Signature)
    (cache : QueryCache HashSpec) (history : History) :
    runMonitor accountingKey (scheme.verify publicKey message signature) cache history =
      (fun result => ((result.1.1.1, result.1.2), result.2)) <$>
        runMonitor accountingKey
          (liftM (verifyWithView publicKey message signature) : OracleComp OracleWorld (Bool × FewTimeView))
          cache history := by
  have heq : scheme.verify publicKey message signature =
      Prod.fst <$> (liftM (verifyWithView publicKey message signature) :
        OracleComp OracleWorld (Bool × FewTimeView)) := by
    rw [← liftM_map, verifyWithView_fst]
    rfl
  rw [heq, runMonitor_map]

theorem gameRestWithView_monitor_projection (adversary : Adversary)
    (accountingKey : SecretKey) (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) (history : History) :
    (fun result => ((result.1.2, result.2.1.cache), result.2.2)) <$>
      gameRestWithView adversary accountingKey publicKey secretKey initialCache history =
      runMonitor accountingKey (gameRest scheme adversary publicKey secretKey) initialCache history := by
  let finish : Forgery × ((QueryCache HashSpec × History) × QueryLog SigningSpec) →
      ProbComp ((Bool × QueryCache HashSpec) × History) := fun result => do
    let verified ← runMonitor accountingKey
      (scheme.verify publicKey result.1.message result.1.signature) result.2.1.1 result.2.1.2
    pure ((decide (SigningTranscript.Valid result.2.2 ∧
      ¬ SigningTranscript.Contains result.2.2 result.1) && verified.1.1, verified.1.2), verified.2)
  let state : ViewedFullTraceState × History := (⟨initialCache, ⟨[], [], []⟩, [], none⟩, history)
  calc
    _ = (Prod.map id viewedLogState <$>
        (simulateQ (viewedAdversaryImpl accountingKey secretKey)
          (adversary.main publicKey)).run state) >>= finish := by
      simp [gameRestWithView, state, finish, viewedLogState,
        runMonitor_verifyWithView_fst, map_bind, bind_map_left, Prod.map]
      rfl
    _ = _ := by
      rw [viewedAdversaryImpl_log_projection]
      rw [gameRest, runMonitor_bind]
      simp only [runMonitor_bind, runMonitor_pure]
      simp [finish, state, SigningCacheTrace.toSigningLog, bind_map_left]

theorem gameAfterSecretsWithView_monitor_projection (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    (fun result => ((result.1.2.2, result.2.1.cache), result.2.2)) <$>
      gameAfterSecretsWithView adversary parameter otsSecret ftsSecret =
      runMonitor (primitiveAccountingKey parameter otsSecret ftsSecret)
        (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅ initialHistory := by
  rw [gameAfterSecretsWithView, gameAfterSecrets, runMonitor_bind]
  simp only [map_bind]
  apply bind_congr
  intro result
  rw [← gameRestWithView_monitor_projection adversary
    (primitiveAccountingKey parameter otsSecret ftsSecret) ⟨result.1.1, parameter⟩
    ⟨parameter, result.1.1, otsSecret, ftsSecret⟩ result.1.2 result.2]
  simp

end SphincsSecurity.Concrete.SettledCollision
