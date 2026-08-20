import XmssSecurity.Proof.OnlineExactCoupling

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

def onlineMonitoredCausalStateOf
    (state : GlobalMonitoredCausalState) : OnlineMonitoredCausalState :=
  ⟨state.causal, state.monitor⟩

def onlineGlobalMonitoredTracedStateOf
    (state : GlobalMonitoredTracedState) : OnlineGlobalMonitoredTracedState :=
  (onlineMonitoredCausalStateOf state.1, state.2)

noncomputable def onlineGlobalHighExactStateOf
    (state : GlobalHighExactMonitoredState) : OnlineGlobalHighExactState :=
  ⟨onlineGlobalMonitoredTracedStateOf state.1,
    CappedEncodingMonitor.OnlineState.initial.observeAll state.2⟩

def onlineMonitoredCausalResultOf
    (result : α × GlobalMonitoredCausalState) :
    α × OnlineMonitoredCausalState :=
  (result.1, onlineMonitoredCausalStateOf result.2)

theorem onlineMonitoredCausalResultOf_globalMonitoredCausalResult
    (table : GlobalChainValueIndex → Digest)
    (initial : GlobalMonitoredCausalState)
    (result : (α × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :
    onlineMonitoredCausalResultOf
        (globalMonitoredCausalResult table initial result) =
      onlineMonitoredCausalResult table
        (onlineMonitoredCausalStateOf initial) result := by
  rfl

theorem monitorGlobalCausalTrace_projection
    (table : GlobalChainValueIndex → Digest)
    (computation : GlobalCausalHashState → ProbComp
      ((α × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
    (state : GlobalMonitoredCausalState) :
    onlineMonitoredCausalResultOf <$>
        (monitorGlobalCausalTrace table computation).run state =
      (monitorGlobalCausalOnline table computation).run
        (onlineMonitoredCausalStateOf state) := by
  rw [monitorGlobalCausalTrace_run]
  change onlineMonitoredCausalResultOf <$>
      (globalMonitoredCausalResult table state <$> computation state.causal) =
    onlineMonitoredCausalResult table (onlineMonitoredCausalStateOf state) <$>
      computation state.causal
  simp only [Functor.map_map]
  apply congrArg (fun f => f <$> computation state.causal)
  funext result
  exact onlineMonitoredCausalResultOf_globalMonitoredCausalResult
    table state result

theorem globalHighMonitoredBaseMappedAdversaryImpl_online_projection
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalMonitoredCausalState) :
    onlineMonitoredCausalResultOf <$>
        (globalHighMonitoredBaseMappedAdversaryImpl right input).run state =
      (onlineGlobalHighMonitoredBaseMappedAdversaryImpl right input).run
        (onlineMonitoredCausalStateOf state) := by
  unfold globalHighMonitoredBaseMappedAdversaryImpl
    onlineGlobalHighMonitoredBaseMappedAdversaryImpl
  rcases input with (worldInput | request)
  · rcases worldInput with n | hashInput
    · exact monitorGlobalCausalTrace_projection right.1.2 _ state
    · exact monitorGlobalCausalTrace_projection right.1.2 _ state
  · exact monitorGlobalCausalTrace_projection right.1.2 _ state

def onlineGlobalMonitoredTracedResultOf
    (result : α × GlobalMonitoredTracedState) :
    α × OnlineGlobalMonitoredTracedState :=
  (result.1, onlineGlobalMonitoredTracedStateOf result.2)

theorem globalHighMonitoredMappedAdversaryImpl_online_projection
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalMonitoredTracedState) :
    onlineGlobalMonitoredTracedResultOf <$>
        (globalHighMonitoredMappedAdversaryImpl right input).run state =
      (onlineGlobalHighMonitoredMappedAdversaryImpl right input).run
        (onlineGlobalMonitoredTracedStateOf state) := by
  let finish := fun result : (OracleWorld + SigningSpec).Range input ×
      OnlineMonitoredCausalState =>
    (result.1, (result.2,
      state.2 ++ attackerActionFragment input result.1))
  have hbase := globalHighMonitoredBaseMappedAdversaryImpl_online_projection
    right input state.1
  have hlifted := congrArg (fun computation => finish <$> computation) hbase
  unfold globalHighMonitoredMappedAdversaryImpl
    onlineGlobalHighMonitoredMappedAdversaryImpl actionTracedStateImpl
  simp only [StateT.run_mk, map_bind, map_pure]
  simpa [finish, Functor.map_map, onlineGlobalMonitoredTracedResultOf,
    onlineGlobalMonitoredTracedStateOf, onlineMonitoredCausalResultOf] using
      hlifted

theorem onlineGlobalHighExactStateOf_queryResult
    (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalHighExactMonitoredState)
    (result : (OracleWorld + SigningSpec).Range input ×
      GlobalMonitoredTracedState) :
    onlineGlobalHighExactStateOf
        (result.2, encodingActionTraceUpdate secretKey input
          (state.1.1.causal.cache, []) result.1
            (result.2.1.causal.cache, []) state.2) =
      (onlineGlobalHighExactQueryResult secretKey input
        (onlineGlobalHighExactStateOf state)
          (result.1, onlineGlobalMonitoredTracedStateOf result.2)).2 := by
  unfold onlineGlobalHighExactStateOf onlineGlobalHighExactQueryResult
    onlineGlobalMonitoredTracedStateOf onlineMonitoredCausalStateOf
  simp only
  rw [OnlineState.observe_encodingActionTraceUpdate]

noncomputable def onlineGlobalHighExactResultOf
    (result : α × GlobalHighExactMonitoredState) :
    α × OnlineGlobalHighExactState :=
  (result.1, onlineGlobalHighExactStateOf result.2)

theorem globalHighExactMonitoredMappedAdversaryImpl_online_projection
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalHighExactMonitoredState) :
    onlineGlobalHighExactResultOf <$>
        (globalHighExactMonitoredMappedAdversaryImpl right input).run state =
      (onlineGlobalHighExactMappedAdversaryImpl right input).run
        (onlineGlobalHighExactStateOf state) := by
  let finish := fun result : (OracleWorld + SigningSpec).Range input ×
      OnlineGlobalMonitoredTracedState =>
    onlineGlobalHighExactQueryResult right.1.1.secretKey input
      (onlineGlobalHighExactStateOf state) result
  let projectOld := fun result : (OracleWorld + SigningSpec).Range input ×
      GlobalMonitoredTracedState =>
    onlineGlobalHighExactResultOf
      (result.1, (result.2,
        encodingActionTraceUpdate right.1.1.secretKey input
          (state.1.1.causal.cache, []) result.1
            (result.2.1.causal.cache, []) state.2))
  have hfunctions : projectOld =
      fun result => finish (onlineGlobalMonitoredTracedResultOf result) := by
    funext result
    apply Prod.ext
    · rfl
    · exact onlineGlobalHighExactStateOf_queryResult
        right.1.1.secretKey input state result
  have hbase := globalHighMonitoredMappedAdversaryImpl_online_projection
    right input state.1
  have hlifted := congrArg (fun computation => finish <$> computation) hbase
  unfold globalHighExactMonitoredMappedAdversaryImpl
    onlineGlobalHighExactMappedAdversaryImpl
  simp only [StateT.run_mk, map_bind, map_pure]
  change projectOld <$>
      (globalHighMonitoredMappedAdversaryImpl right input).run state.1 = _
  rw [hfunctions]
  simpa [finish, onlineGlobalHighExactStateOf, Functor.map_map] using hlifted

theorem simulate_globalHighExactMonitoredMappedAdversaryImpl_online_projection
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : GlobalHighExactMonitoredState) :
    onlineGlobalHighExactResultOf <$>
        (simulateQ (globalHighExactMonitoredMappedAdversaryImpl right)
          computation).run state =
      (simulateQ (onlineGlobalHighExactMappedAdversaryImpl right)
        computation).run (onlineGlobalHighExactStateOf state) := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  intro input current
  exact globalHighExactMonitoredMappedAdversaryImpl_online_projection
    right input current

theorem globalHighMonitoredVerifierImpl_online_projection
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (input : OracleWorld.Domain)
    (state : GlobalMonitoredTracedState) :
    onlineGlobalMonitoredTracedResultOf <$>
        (globalHighMonitoredVerifierImpl right input).run state =
      (onlineGlobalHighMonitoredVerifierImpl right input).run
        (onlineGlobalMonitoredTracedStateOf state) := by
  let finish := fun result : OracleWorld.Range input ×
      OnlineMonitoredCausalState => (result.1, (result.2, state.2))
  have hbase := globalHighMonitoredBaseMappedAdversaryImpl_online_projection
    right (.inl input) state.1
  have hlifted := congrArg (fun computation => finish <$> computation) hbase
  unfold globalHighMonitoredVerifierImpl
    onlineGlobalHighMonitoredVerifierImpl
  simp only [StateT.run_mk]
  simpa [finish, Functor.map_map, onlineGlobalMonitoredTracedResultOf,
    onlineGlobalMonitoredTracedStateOf, onlineMonitoredCausalResultOf] using
      hlifted

theorem simulate_globalHighMonitoredVerifierImpl_online_projection
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (computation : OracleComp OracleWorld α)
    (state : GlobalMonitoredTracedState) :
    onlineGlobalMonitoredTracedResultOf <$>
        (simulateQ (globalHighMonitoredVerifierImpl right) computation).run
          state =
      (simulateQ (onlineGlobalHighMonitoredVerifierImpl right) computation).run
        (onlineGlobalMonitoredTracedStateOf state) := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  intro input current
  exact globalHighMonitoredVerifierImpl_online_projection right input current

theorem onlineGlobalHighExactVerifierImpl_run_eq
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (computation : OracleComp OracleWorld α)
    (state : OnlineGlobalHighExactState) :
    (simulateQ (onlineGlobalHighExactVerifierImpl right) computation).run
        state =
      (fun result : α × OnlineGlobalMonitoredTracedState =>
        (result.1, ⟨result.2, state.encoding⟩)) <$>
      (simulateQ (onlineGlobalHighMonitoredVerifierImpl right) computation).run
        state.high := by
  let lens : StateLens OnlineGlobalHighExactState
      OnlineGlobalMonitoredTracedState :=
    ⟨OnlineGlobalHighExactState.high,
      fun current nextHigh => ⟨nextHigh, current.encoding⟩,
      by intro current; cases current; rfl,
      by simp,
      by simp⟩
  apply lens.simulateQ_run_eq
  intro input current
  rfl

noncomputable def onlineGlobalHighExactVerifiedResultOf
    (state : GlobalHighExactMonitoredState)
    (result : α × GlobalMonitoredTracedState) :
    α × OnlineGlobalHighExactState :=
  (result.1, ⟨onlineGlobalMonitoredTracedStateOf result.2,
    CappedEncodingMonitor.OnlineState.initial.observeAll state.2⟩)

theorem simulate_globalHighExactVerifier_online_projection
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (computation : OracleComp OracleWorld α)
    (state : GlobalHighExactMonitoredState) :
    onlineGlobalHighExactVerifiedResultOf state <$>
        (simulateQ (globalHighMonitoredVerifierImpl right) computation).run
          state.1 =
      (simulateQ (onlineGlobalHighExactVerifierImpl right) computation).run
        (onlineGlobalHighExactStateOf state) := by
  let finish := fun result : α × OnlineGlobalMonitoredTracedState =>
    (result.1, (⟨result.2,
      CappedEncodingMonitor.OnlineState.initial.observeAll state.2⟩ :
        OnlineGlobalHighExactState))
  have hbase := simulate_globalHighMonitoredVerifierImpl_online_projection
    right computation state.1
  have hlifted := congrArg (fun candidate => finish <$> candidate) hbase
  have hproject : onlineGlobalHighExactVerifiedResultOf state =
      fun result => finish (onlineGlobalMonitoredTracedResultOf result) := by
    funext result
    rfl
  rw [onlineGlobalHighExactVerifierImpl_run_eq]
  rw [hproject]
  simpa [finish, onlineGlobalHighExactStateOf, Functor.map_map] using hlifted

theorem onlineGlobalHighExactStateOf_appendVerification
    (secretKey : SecretKey) (forgery : Forgery)
    (initialState : GlobalHighExactMonitoredState)
    (finalHigh : GlobalMonitoredTracedState) :
    onlineGlobalHighExactStateOf
        (finalHigh, appendVerificationEncodingObservation secretKey forgery
          initialState.1.1.causal.cache finalHigh.1.causal.cache
            initialState.2) =
      finishOnlineVerificationEncoding secretKey forgery
        initialState.1.1.causal.cache finalHigh.1.causal.cache
          (onlineGlobalHighExactVerifiedResultOf initialState
            (false, finalHigh)).2 := by
  unfold onlineGlobalHighExactStateOf
    onlineGlobalHighExactVerifiedResultOf
    finishOnlineVerificationEncoding observeVerificationEncoding
  simp only
  rw [appendVerificationEncodingObservation_eq_append_empty,
    CappedEncodingMonitor.OnlineState.observeAll_append]

noncomputable def onlineGlobalHighExactExecutionOf
    (result : (Forgery × Bool) × GlobalHighExactMonitoredState) :
    (Forgery × Bool) × OnlineGlobalHighExactState :=
  (result.1, onlineGlobalHighExactStateOf result.2)

theorem globalHighExactMonitoredDetailedExecution_online_projection
    (adversary : Adversary Concrete.scheme)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) :
    onlineGlobalHighExactExecutionOf <$>
        globalHighExactMonitoredDetailedExecution adversary right =
      onlineGlobalHighExactDetailedExecution adversary right := by
  let initial : GlobalHighExactMonitoredState :=
    ((⟨globalFilteredCausalKeygenState right.1.1,
      some AdaptiveRevealMonitor.State.empty, []⟩, []), [])
  let oldTail := fun handled : Forgery × GlobalHighExactMonitoredState => do
    let verified ← (simulateQ (globalHighMonitoredVerifierImpl right)
      (Concrete.scheme.verify right.1.1.publicKey handled.1.epoch
        handled.1.message handled.1.signature)).run handled.2.1
    let finalTrace := appendVerificationEncodingObservation
      right.1.1.secretKey handled.1 handled.2.1.1.causal.cache
        verified.2.1.causal.cache handled.2.2
    pure ((handled.1, verified.1), (verified.2, finalTrace))
  let newTail := fun handled : Forgery × OnlineGlobalHighExactState => do
    let verified ← (simulateQ (onlineGlobalHighExactVerifierImpl right)
      (Concrete.scheme.verify right.1.1.publicKey handled.1.epoch
        handled.1.message handled.1.signature)).run handled.2
    pure ((handled.1, verified.1),
      finishOnlineVerificationEncoding right.1.1.secretKey handled.1
        handled.2.high.1.causal.cache verified.2.high.1.causal.cache
          verified.2)
  have htail (handled : Forgery × GlobalHighExactMonitoredState) :
      onlineGlobalHighExactExecutionOf <$> oldTail handled =
        newTail (handled.1, onlineGlobalHighExactStateOf handled.2) := by
    let oldFinish := fun verified : Bool × GlobalMonitoredTracedState =>
      ((handled.1, verified.1), onlineGlobalHighExactStateOf
        (verified.2, appendVerificationEncodingObservation
          right.1.1.secretKey handled.1 handled.2.1.1.causal.cache
            verified.2.1.causal.cache handled.2.2))
    let newFinish := fun verified : Bool × OnlineGlobalHighExactState =>
      ((handled.1, verified.1),
        finishOnlineVerificationEncoding right.1.1.secretKey handled.1
          (onlineGlobalHighExactStateOf handled.2).high.1.causal.cache
            verified.2.high.1.causal.cache verified.2)
    let projectVerified : Bool × GlobalMonitoredTracedState →
        Bool × OnlineGlobalHighExactState :=
      onlineGlobalHighExactVerifiedResultOf handled.2
    have hfunctions : oldFinish = fun verified =>
        newFinish (projectVerified verified) := by
      funext verified
      apply Prod.ext
      · rfl
      · exact onlineGlobalHighExactStateOf_appendVerification
          right.1.1.secretKey handled.1 handled.2 verified.2
    have hvertifier := simulate_globalHighExactVerifier_online_projection
      right
        (Concrete.scheme.verify right.1.1.publicKey handled.1.epoch
          handled.1.message handled.1.signature) handled.2
    unfold oldTail newTail
    simp only [map_bind, map_pure]
    change oldFinish <$> (simulateQ (globalHighMonitoredVerifierImpl right)
        (Concrete.scheme.verify right.1.1.publicKey handled.1.epoch
          handled.1.message handled.1.signature)).run handled.2.1 =
      newFinish <$> (simulateQ (onlineGlobalHighExactVerifierImpl right)
        (Concrete.scheme.verify right.1.1.publicKey handled.1.epoch
          handled.1.message handled.1.signature)).run
            (onlineGlobalHighExactStateOf handled.2)
    rw [hfunctions, ← Functor.map_map, hvertifier]
  change onlineGlobalHighExactExecutionOf <$> (do
      let handled ← (simulateQ
        (globalHighExactMonitoredMappedAdversaryImpl right)
          (adversary.main right.1.1.publicKey)).run initial
      oldTail handled) = (do
      let handled ← (simulateQ
        (onlineGlobalHighExactMappedAdversaryImpl right)
          (adversary.main right.1.1.publicKey)).run
            (OnlineGlobalHighExactState.initial
              (globalFilteredCausalKeygenState right.1.1))
      newTail handled)
  rw [map_bind]
  simp_rw [htail]
  let projectHandled := fun handled : Forgery ×
      GlobalHighExactMonitoredState =>
    (handled.1, onlineGlobalHighExactStateOf handled.2)
  rw [← bind_map_left projectHandled]
  have hhandled :=
    simulate_globalHighExactMonitoredMappedAdversaryImpl_online_projection
      right (adversary.main right.1.1.publicKey) initial
  change projectHandled <$>
      (simulateQ (globalHighExactMonitoredMappedAdversaryImpl right)
        (adversary.main right.1.1.publicKey)).run initial = _ at hhandled
  rw [hhandled]
  have hinitial : onlineGlobalHighExactStateOf initial =
      OnlineGlobalHighExactState.initial
        (globalFilteredCausalKeygenState right.1.1) := by rfl
  rw [hinitial]

noncomputable def onlineGlobalHighExactProgramResultOf
    (result : GlobalHighExactMonitoredProgramResult) :
    OnlineGlobalHighExactProgramResult :=
  (result.1, onlineGlobalHighExactExecutionOf result.2)

theorem globalHighExactMonitoredProgram_online_projection
    (adversary : Adversary Concrete.scheme) :
    onlineGlobalHighExactProgramResultOf <$>
        globalHighExactMonitoredProgram adversary =
      onlineGlobalHighExactProgram adversary := by
  unfold globalHighExactMonitoredProgram onlineGlobalHighExactProgram
  simp only [map_bind, map_pure]
  apply bind_congr
  intro right
  rw [← globalHighExactMonitoredDetailedExecution_online_projection]
  simp [onlineGlobalHighExactProgramResultOf,
    onlineGlobalHighExactExecutionOf, Functor.map_map]

end XmssSecurity.CappedChain
