import XmssSecurity.Proof.OnlineGlobalHighGame
import XmssSecurity.Proof.OnlineEncodingMonitor
import XmssSecurity.Proof.CappedExactFirstLaneCoupling

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

def OnlineGlobalSigningMonitoredStateRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftState : SourceSigningTracedState)
    (rightState : OnlineGlobalMonitoredTracedState) : Prop :=
  OnlineGlobalMonitoredTracedStateRelation left right
    (sourceSigningTracedStateProjection leftState) rightState

theorem relTriple_programmed_onlineGlobalHighMonitored_signingAction
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftState : SourceSigningTracedState)
    (rightState : OnlineGlobalMonitoredTracedState)
    (hstate : OnlineGlobalSigningMonitoredStateRelation left right.1
      leftState rightState)
    (input : (OracleWorld + SigningSpec).Domain) :
    RelTriple
      ((sourceSigningTracedMappedAdversaryImpl left.publicKey
        (Concrete.materializePrecomputation left.cache left.secretKey)
          input).run leftState)
      ((onlineGlobalHighMonitoredMappedAdversaryImpl right input).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          OnlineGlobalSigningMonitoredStateRelation left right.1
            leftResult.2 rightResult.2) ∨ rightResult.2.1.bad) := by
  let enrich := sourceSigningTracedQueryResult input leftState
  let project := sourceSigningTracedStateProjection leftState
  have hbase := relTriple_programmed_onlineGlobalHighMonitored_action left right
    hrel hleftSupport hrightSupport project rightState hstate input
  have hlifted : RelTriple
      (enrich <$> (sourceDirectTracedMappedAdversaryImpl left.publicKey
        (Concrete.materializePrecomputation left.cache left.secretKey)
          input).run project)
      (id <$> (onlineGlobalHighMonitoredMappedAdversaryImpl right input).run
        rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          OnlineGlobalSigningMonitoredStateRelation left right.1
            leftResult.2 rightResult.2) ∨ rightResult.2.1.bad) := by
    apply relTriple_map
    apply relTriple_post_mono hbase
    intro leftResult rightResult hresult
    rcases hresult with hgood | hbad
    · exact Or.inl ⟨hgood.1, hgood.2⟩
    · exact Or.inr hbad
  rw [id_map] at hlifted
  rw [sourceSigningTracedMappedAdversaryImpl_query_eq_map]
  exact hlifted

structure OnlineGlobalHighExactState where
  high : OnlineGlobalMonitoredTracedState
  encoding : CappedEncodingMonitor.OnlineState

def OnlineGlobalHighExactState.bad
    (state : OnlineGlobalHighExactState) : Prop :=
  state.high.1.bad ∨ state.encoding.hit = true

def OnlineGlobalHighExactState.initial
    (causal : GlobalCausalHashState) : OnlineGlobalHighExactState :=
  ⟨(⟨causal, some AdaptiveRevealMonitor.State.empty⟩, []),
    CappedEncodingMonitor.OnlineState.initial⟩

def SourceOnlineGlobalHighExactStateRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftState : SourceExactTracedState)
    (rightState : OnlineGlobalHighExactState) : Prop :=
  OnlineGlobalSigningMonitoredStateRelation left right
      (sourceExactSigningProjection leftState) rightState.high ∧
    rightState.encoding =
      CappedEncodingMonitor.OnlineState.initial.observeAll leftState.1.2

noncomputable def onlineGlobalHighExactQueryResult
    (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : OnlineGlobalHighExactState)
    (result : (OracleWorld + SigningSpec).Range input ×
      OnlineGlobalMonitoredTracedState) :
    (OracleWorld + SigningSpec).Range input × OnlineGlobalHighExactState :=
  let observation := encodingObservation? secretKey input
    (initialState.high.1.causal.cache, []) result.1
      (result.2.1.causal.cache, [])
  let encoding := match observation with
    | none => initialState.encoding
    | some action => initialState.encoding.observe action
  (result.1, ⟨result.2, encoding⟩)

noncomputable def onlineGlobalHighExactMappedAdversaryImpl
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT OnlineGlobalHighExactState ProbComp) := fun input =>
  StateT.mk fun state =>
    onlineGlobalHighExactQueryResult right.1.1.secretKey input state <$>
      (onlineGlobalHighMonitoredMappedAdversaryImpl right input).run state.high

theorem onlineGlobalHighExactMappedAdversaryImpl_preserves_bad
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) :
    QueryImpl.PreservesInv
      (onlineGlobalHighExactMappedAdversaryImpl right)
      OnlineGlobalHighExactState.bad := by
  intro input state hbad result hresult
  unfold onlineGlobalHighExactMappedAdversaryImpl at hresult
  simp only [StateT.run_mk] at hresult
  rw [support_map] at hresult
  obtain ⟨baseResult, hbase, rfl⟩ := hresult
  rcases hbad with hchain | hencoding
  · apply Or.inl
    exact onlineGlobalHighMonitoredMappedAdversaryImpl_preserves_bad right
      input state.high hchain baseResult hbase
  · apply Or.inr
    unfold onlineGlobalHighExactQueryResult
    simp only
    cases encodingObservation? right.1.1.secretKey input
        (state.high.1.causal.cache, []) baseResult.1
        (baseResult.2.1.causal.cache, []) with
    | none => exact hencoding
    | some action =>
        simp [CappedEncodingMonitor.OnlineState.observe, hencoding]

theorem OnlineState.observe_encodingActionTraceUpdate
    (state : CappedEncodingMonitor.OnlineState)
    (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState finalState : QueryCache HashSpec × SigningCacheTrace)
    (output : (OracleWorld + SigningSpec).Range input)
    (trace : EncodingActionTrace) :
    state.observeAll (encodingActionTraceUpdate secretKey input initialState
      output finalState trace) =
      match encodingObservation? secretKey input initialState output finalState with
      | none => state.observeAll trace
      | some action => (state.observeAll trace).observe action := by
  unfold encodingActionTraceUpdate
  cases encodingObservation? secretKey input initialState output finalState with
  | none => rfl
  | some action =>
      rw [CappedEncodingMonitor.OnlineState.observeAll_append]
      rfl

theorem relTriple_programmed_onlineGlobalHighExact_action
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftState : SourceExactTracedState)
    (rightState : OnlineGlobalHighExactState)
    (hstate : SourceOnlineGlobalHighExactStateRelation left right.1
      leftState rightState)
    (input : (OracleWorld + SigningSpec).Domain) :
    RelTriple
      ((cappedBothTracedMappedAdversaryImpl left.publicKey
        (Concrete.materializePrecomputation left.cache left.secretKey)
          input).run leftState)
      ((onlineGlobalHighExactMappedAdversaryImpl right input).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          SourceOnlineGlobalHighExactStateRelation left right.1
            leftResult.2 rightResult.2) ∨ rightResult.2.bad) := by
  let leftSecret :=
    Concrete.materializePrecomputation left.cache left.secretKey
  have hbase :=
    relTriple_programmed_onlineGlobalHighMonitored_signingAction left right
      hrel hleftSupport hrightSupport
      (sourceExactSigningProjection leftState) rightState.high hstate.1 input
  have hlifted : RelTriple
      (sourceExactQueryResult leftSecret input leftState <$>
        (sourceSigningTracedMappedAdversaryImpl left.publicKey leftSecret
          input).run (sourceExactSigningProjection leftState))
      (onlineGlobalHighExactQueryResult right.1.1.secretKey input rightState <$>
        (onlineGlobalHighMonitoredMappedAdversaryImpl right input).run
          rightState.high)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          SourceOnlineGlobalHighExactStateRelation left right.1
            leftResult.2 rightResult.2) ∨ rightResult.2.bad) := by
    apply relTriple_map
    apply relTriple_post_mono hbase
    intro leftResult rightResult hresult
    rcases hresult with hgood | hbad
    · apply Or.inl
      refine ⟨hgood.1, hgood.2, ?_⟩
      obtain ⟨_monitorInitial, _hmonitorInitial, _hagreesInitial,
        _hrevealedInitial, hinitialCausal, _hretainedInitial⟩ := hstate.1.1
      obtain ⟨_monitorFinal, _hmonitorFinal, _hagreesFinal,
        _hrevealedFinal, hfinalCausal, _hretainedFinal⟩ := hgood.2.1
      have hcacheUpdate :=
        encodingActionTraceUpdate_eq_of_globalSigningCachesAgree
          leftSecret input leftState.1.1.1 rightState.high.1.causal.cache
          leftResult.2.1.1 rightResult.2.1.causal.cache
          (by simpa [leftSecret, Concrete.materializePrecomputation,
            Concrete.precomputedSecretKey, sourceSigningTracedStateProjection,
            sourceExactSigningProjection] using hinitialCausal.1)
          (by simpa [leftSecret, Concrete.materializePrecomputation,
            Concrete.precomputedSecretKey, sourceSigningTracedStateProjection,
            sourceExactSigningProjection] using hfinalCausal.1)
          leftResult.1 leftState.1.2
      have hparameter := programmedGlobal_secretKey_parameter_eq left right
        hrel hleftSupport hrightSupport
      have hsecretUpdate := encodingActionTraceUpdate_eq_of_parameter_eq
        leftSecret right.1.1.secretKey
        (by simpa [leftSecret, Concrete.materializePrecomputation,
          Concrete.precomputedSecretKey] using hparameter.symm)
        input rightState.high.1.causal.cache rightResult.2.1.causal.cache
        leftResult.1 leftState.1.2
      have htraceUpdate := hcacheUpdate.trans hsecretUpdate
      unfold onlineGlobalHighExactQueryResult sourceExactQueryResult
      simp only
      rw [hstate.2, hgood.1]
      rw [hgood.1] at htraceUpdate
      rw [← OnlineState.observe_encodingActionTraceUpdate]
      rw [← htraceUpdate]
    · exact Or.inr (Or.inl hbad)
  rw [cappedBothTracedMappedAdversaryImpl_query_eq_sourceExactMap]
  unfold onlineGlobalHighExactMappedAdversaryImpl
  simp only [StateT.run_mk]
  exact hlifted

theorem simulate_onlineGlobalHighExactMappedAdversaryImpl_preserves_bad
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : OnlineGlobalHighExactState)
    (hbad : state.bad)
    (result : α × OnlineGlobalHighExactState)
    (hresult : result ∈ support
      ((simulateQ (onlineGlobalHighExactMappedAdversaryImpl right)
        computation).run state)) :
    result.2.bad :=
  OracleComp.simulateQ_run_preservesInv
    (onlineGlobalHighExactMappedAdversaryImpl right)
    OnlineGlobalHighExactState.bad
    (onlineGlobalHighExactMappedAdversaryImpl_preserves_bad right)
    computation state hbad result hresult

theorem relTriple_programmed_onlineGlobalHighExact_adversary
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (leftState : SourceExactTracedState)
    (rightState : OnlineGlobalHighExactState)
    (hstate : SourceOnlineGlobalHighExactStateRelation left right.1
      leftState rightState) :
    RelTriple
      ((simulateQ
        (cappedBothTracedMappedAdversaryImpl left.publicKey
          (Concrete.materializePrecomputation left.cache left.secretKey))
          computation).run leftState)
      ((simulateQ (onlineGlobalHighExactMappedAdversaryImpl right)
          computation).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          SourceOnlineGlobalHighExactStateRelation left right.1
            leftResult.2 rightResult.2) ∨ rightResult.2.bad) := by
  induction computation using OracleComp.inductionOn generalizing leftState
      rightState with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure (Or.inl ⟨rfl, hstate⟩)
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, StateT.run_bind]
      apply relTriple_bind (relTriple_with_support
        (relTriple_programmed_onlineGlobalHighExact_action left right hrel
          hleftSupport hrightSupport leftState rightState hstate input))
      intro leftHead rightHead hhead
      rcases hhead.1 with hgood | hbad
      · rw [hgood.1]
        exact ih rightHead.1 leftHead.2 rightHead.2 hgood.2
      · apply relTriple_post_mono
          (relTriple_with_support
            (relTriple_prod (fun _ _ => True.intro) (fun _ _ => True.intro)))
        intro _leftResult rightResult hresult
        exact Or.inr
          (simulate_onlineGlobalHighExactMappedAdversaryImpl_preserves_bad
            right (next rightHead.1) rightHead.2 hbad rightResult hresult.2.2)

theorem relTriple_programmed_onlineGlobalHighMonitored_signingVerifierQuery
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftState : SourceSigningTracedState)
    (rightState : OnlineGlobalMonitoredTracedState)
    (hstate : OnlineGlobalSigningMonitoredStateRelation left right.1
      leftState rightState)
    (input : OracleWorld.Domain) :
    RelTriple
      ((sourceSigningTracedVerifierImpl input).run leftState)
      ((onlineGlobalHighMonitoredVerifierImpl right input).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          OnlineGlobalSigningMonitoredStateRelation left right.1
            leftResult.2 rightResult.2) ∨ rightResult.2.1.bad) := by
  let project := sourceSigningTracedStateProjection leftState
  let enrich := fun result : OracleWorld.Range input × SourceTracedState =>
    (result.1, ((result.2.1, leftState.1.2), result.2.2))
  have hbase :=
    relTriple_programmed_onlineGlobalHighMonitored_verifier_query left right
      hrel hleftSupport hrightSupport project rightState hstate input
  have hlifted : RelTriple
      (enrich <$> (sourceDirectTracedVerifierImpl input).run project)
      (id <$> (onlineGlobalHighMonitoredVerifierImpl right input).run
        rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          OnlineGlobalSigningMonitoredStateRelation left right.1
            leftResult.2 rightResult.2) ∨ rightResult.2.1.bad) := by
    apply relTriple_map
    apply relTriple_post_mono hbase
    intro leftResult rightResult hresult
    rcases hresult with hgood | hbad
    · exact Or.inl ⟨hgood.1, hgood.2⟩
    · exact Or.inr hbad
  rw [id_map] at hlifted
  have hleft : (sourceSigningTracedVerifierImpl input).run leftState =
      enrich <$> (sourceDirectTracedVerifierImpl input).run project := by
    rfl
  rw [hleft]
  exact hlifted

def onlineSourceExactVerifierResult
    (initialState : SourceExactTracedState)
    (result : OracleWorld.Range input × SourceSigningTracedState) :
    OracleWorld.Range input × SourceExactTracedState :=
  (result.1, ((result.2.1, initialState.1.2), result.2.2))

noncomputable def onlineSourceExactTracedVerifierImpl :
    QueryImpl OracleWorld (StateT SourceExactTracedState ProbComp) := fun input =>
  StateT.mk fun state => onlineSourceExactVerifierResult state <$>
    (sourceSigningTracedVerifierImpl input).run
      (sourceExactSigningProjection state)

theorem onlineSourceExactTracedVerifierImpl_run_eq
    (computation : OracleComp OracleWorld α)
    (initialState : SourceExactTracedState) :
    (simulateQ onlineSourceExactTracedVerifierImpl computation).run
        initialState =
      (fun result : α × SourceSigningTracedState =>
        (result.1, ((result.2.1, initialState.1.2), result.2.2))) <$>
      (simulateQ sourceSigningTracedVerifierImpl computation).run
        (sourceExactSigningProjection initialState) := by
  let lens : StateLens SourceExactTracedState SourceSigningTracedState :=
    ⟨sourceExactSigningProjection,
      fun state nextSigning => ((nextSigning.1, state.1.2), nextSigning.2),
      by
        intro state
        rcases state with ⟨⟨⟨cache, signingTrace⟩, encodingTrace⟩,
          actionTrace⟩
        rfl,
      by simp [sourceExactSigningProjection],
      by simp⟩
  apply lens.simulateQ_run_eq
  intro input state
  rfl

def onlineGlobalHighExactVerifierResult
    (initialState : OnlineGlobalHighExactState)
    (result : OracleWorld.Range input × OnlineGlobalMonitoredTracedState) :
    OracleWorld.Range input × OnlineGlobalHighExactState :=
  (result.1, ⟨result.2, initialState.encoding⟩)

noncomputable def onlineGlobalHighExactVerifierImpl
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) :
    QueryImpl OracleWorld
      (StateT OnlineGlobalHighExactState ProbComp) := fun input =>
  StateT.mk fun state => onlineGlobalHighExactVerifierResult state <$>
    (onlineGlobalHighMonitoredVerifierImpl right input).run state.high

theorem relTriple_programmed_onlineGlobalHighExact_verifier_action
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftState : SourceExactTracedState)
    (rightState : OnlineGlobalHighExactState)
    (hstate : SourceOnlineGlobalHighExactStateRelation left right.1
      leftState rightState)
    (input : OracleWorld.Domain) :
    RelTriple
      ((onlineSourceExactTracedVerifierImpl input).run leftState)
      ((onlineGlobalHighExactVerifierImpl right input).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          SourceOnlineGlobalHighExactStateRelation left right.1
            leftResult.2 rightResult.2) ∨ rightResult.2.bad) := by
  have hbase :=
    relTriple_programmed_onlineGlobalHighMonitored_signingVerifierQuery left
      right hrel hleftSupport hrightSupport
      (sourceExactSigningProjection leftState) rightState.high hstate.1 input
  unfold onlineSourceExactTracedVerifierImpl
    onlineGlobalHighExactVerifierImpl
  simp only [StateT.run_mk]
  apply relTriple_map
  apply relTriple_post_mono hbase
  intro leftResult rightResult hresult
  rcases hresult with hgood | hbad
  · exact Or.inl ⟨hgood.1, hgood.2, hstate.2⟩
  · exact Or.inr (Or.inl hbad)

theorem onlineGlobalHighExactVerifierImpl_preserves_bad
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) :
    QueryImpl.PreservesInv (onlineGlobalHighExactVerifierImpl right)
      OnlineGlobalHighExactState.bad := by
  intro input state hbad result hresult
  unfold onlineGlobalHighExactVerifierImpl at hresult
  simp only [StateT.run_mk] at hresult
  rw [support_map] at hresult
  obtain ⟨baseResult, hbase, rfl⟩ := hresult
  rcases hbad with hchain | hencoding
  · exact Or.inl
      (onlineGlobalHighMonitoredVerifierImpl_preserves_bad right input
        state.high hchain baseResult hbase)
  · exact Or.inr hencoding

theorem simulate_onlineGlobalHighExactVerifierImpl_preserves_bad
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (computation : OracleComp OracleWorld α)
    (state : OnlineGlobalHighExactState)
    (hbad : state.bad)
    (result : α × OnlineGlobalHighExactState)
    (hresult : result ∈ support
      ((simulateQ (onlineGlobalHighExactVerifierImpl right)
        computation).run state)) :
    result.2.bad :=
  OracleComp.simulateQ_run_preservesInv
    (onlineGlobalHighExactVerifierImpl right)
    OnlineGlobalHighExactState.bad
    (onlineGlobalHighExactVerifierImpl_preserves_bad right)
    computation state hbad result hresult

theorem relTriple_programmed_onlineGlobalHighExact_verifier
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (computation : OracleComp OracleWorld α)
    (leftState : SourceExactTracedState)
    (rightState : OnlineGlobalHighExactState)
    (hstate : SourceOnlineGlobalHighExactStateRelation left right.1
      leftState rightState) :
    RelTriple
      ((simulateQ onlineSourceExactTracedVerifierImpl computation).run
        leftState)
      ((simulateQ (onlineGlobalHighExactVerifierImpl right) computation).run
        rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          SourceOnlineGlobalHighExactStateRelation left right.1
            leftResult.2 rightResult.2) ∨ rightResult.2.bad) := by
  induction computation using OracleComp.inductionOn generalizing leftState
      rightState with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure (Or.inl ⟨rfl, hstate⟩)
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, StateT.run_bind]
      apply relTriple_bind (relTriple_with_support
        (relTriple_programmed_onlineGlobalHighExact_verifier_action left right
          hrel hleftSupport hrightSupport leftState rightState hstate input))
      intro leftHead rightHead hhead
      rcases hhead.1 with hgood | hbad
      · rw [hgood.1]
        exact ih rightHead.1 leftHead.2 rightHead.2 hgood.2
      · apply relTriple_post_mono
          (relTriple_with_support
            (relTriple_prod (fun _ _ => True.intro) (fun _ _ => True.intro)))
        intro _leftResult rightResult hresult
        exact Or.inr
          (simulate_onlineGlobalHighExactVerifierImpl_preserves_bad right
            (next rightHead.1) rightHead.2 hbad rightResult hresult.2.2)

theorem sourceOnlineGlobalHighExactStateRelation_initial
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen) :
    SourceOnlineGlobalHighExactStateRelation left right.1
      ((((left.cache, []), []), []))
      (OnlineGlobalHighExactState.initial
        (globalFilteredCausalKeygenState right.1.1)) := by
  constructor
  · constructor
    · exact onlineMonitoredFilteredStateRelation_initial left right.1
        left.cache (globalFilteredCausalKeygenState right.1.1)
        (programmedGlobal_filteredKeygen_stateRelation left right hrel
          hleftSupport hrightSupport)
        (globalFilteredCausalKeygenState_merkleRetained right.1.1)
        (fun index => by simp [globalFilteredCausalKeygenState])
    · rfl
  · rfl

theorem appendVerificationEncodingObservation_eq_append_empty
    (secretKey : SecretKey) (forgery : Forgery)
    (initialCache finalCache : QueryCache HashSpec)
    (trace : EncodingActionTrace) :
    appendVerificationEncodingObservation secretKey forgery initialCache
      finalCache trace =
    trace ++ appendVerificationEncodingObservation secretKey forgery
      initialCache finalCache [] := by
  let input := Concrete.CacheView.encodingInput secretKey.parameter forgery.epoch
    (forgery.message, forgery.signature.randomness)
  unfold appendVerificationEncodingObservation
  change (if initialCache input = none then
      match finalCache input with
      | none => trace
      | some output => trace ++ [.query forgery.epoch output]
    else trace) =
    trace ++ (if initialCache input = none then
      match finalCache input with
      | none => []
      | some output => [.query forgery.epoch output]
    else [])
  by_cases hinitial : initialCache input = none
  · rw [hinitial]
    cases hfinal : finalCache input with
    | none => simp
    | some output => simp
  · simp [hinitial]

noncomputable def observeVerificationEncoding
    (secretKey : SecretKey) (forgery : Forgery)
    (initialCache finalCache : QueryCache HashSpec)
    (state : CappedEncodingMonitor.OnlineState) :
    CappedEncodingMonitor.OnlineState :=
  state.observeAll (appendVerificationEncodingObservation secretKey forgery
    initialCache finalCache [])

noncomputable def finishOnlineVerificationEncoding
    (secretKey : SecretKey) (forgery : Forgery)
    (initialCache finalCache : QueryCache HashSpec)
    (state : OnlineGlobalHighExactState) : OnlineGlobalHighExactState :=
  { state with
    encoding := observeVerificationEncoding secretKey forgery initialCache
      finalCache state.encoding }

theorem finishOnlineVerificationEncoding_preserves_bad
    (secretKey : SecretKey) (forgery : Forgery)
    (initialCache finalCache : QueryCache HashSpec)
    (state : OnlineGlobalHighExactState)
    (hbad : state.bad) :
    (finishOnlineVerificationEncoding secretKey forgery initialCache
      finalCache state).bad := by
  rcases hbad with hchain | hencoding
  · exact Or.inl hchain
  · right
    rcases state with ⟨high, ⟨current, hit⟩⟩
    change hit = true at hencoding
    subst hit
    simp [finishOnlineVerificationEncoding, observeVerificationEncoding]

def finishSourceVerificationEncoding
    (secretKey : SecretKey) (forgery : Forgery)
    (initialState finalState : SourceExactTracedState) :
    SourceExactTracedState :=
  ((finalState.1.1,
    appendVerificationEncodingObservation secretKey forgery
      initialState.1.1.1 finalState.1.1.1 finalState.1.2), finalState.2)

theorem SourceOnlineGlobalHighExactStateRelation.finishVerificationEncoding
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (forgery : Forgery)
    (leftInitial leftFinal : SourceExactTracedState)
    (rightInitial rightFinal : OnlineGlobalHighExactState)
    (hinitial : SourceOnlineGlobalHighExactStateRelation left right.1
      leftInitial rightInitial)
    (hfinal : SourceOnlineGlobalHighExactStateRelation left right.1
      leftFinal rightFinal) :
    SourceOnlineGlobalHighExactStateRelation left right.1
      (finishSourceVerificationEncoding
        (Concrete.materializePrecomputation left.cache left.secretKey)
          forgery leftInitial leftFinal)
      (finishOnlineVerificationEncoding right.1.1.secretKey forgery
        rightInitial.high.1.causal.cache rightFinal.high.1.causal.cache
          rightFinal) := by
  let leftSecret :=
    Concrete.materializePrecomputation left.cache left.secretKey
  obtain ⟨_monitorInitial, _hmonitorInitial, _hagreesInitial,
    _hrevealedInitial, hinitialCausal, _hretainedInitial⟩ := hinitial.1.1
  obtain ⟨_monitorFinal, _hmonitorFinal, _hagreesFinal,
    _hrevealedFinal, hfinalCausal, _hretainedFinal⟩ := hfinal.1.1
  have hparameter := programmedGlobal_secretKey_parameter_eq left right hrel
    hleftSupport hrightSupport
  have hempty :=
    appendVerificationEncodingObservation_eq_of_globalSigningCachesAgree
      leftSecret right.1.1.secretKey
      (by simpa [leftSecret, Concrete.materializePrecomputation,
        Concrete.precomputedSecretKey] using hparameter.symm)
      forgery leftInitial.1.1.1 rightInitial.high.1.causal.cache
        leftFinal.1.1.1 rightFinal.high.1.causal.cache
      (by simpa [leftSecret, Concrete.materializePrecomputation,
        Concrete.precomputedSecretKey, sourceSigningTracedStateProjection,
        sourceExactSigningProjection] using hinitialCausal.1)
      (by simpa [leftSecret, Concrete.materializePrecomputation,
        Concrete.precomputedSecretKey, sourceSigningTracedStateProjection,
        sourceExactSigningProjection] using hfinalCausal.1)
      []
  have happend := appendVerificationEncodingObservation_eq_append_empty
    leftSecret forgery leftInitial.1.1.1 leftFinal.1.1.1 leftFinal.1.2
  constructor
  · simpa [finishSourceVerificationEncoding,
      finishOnlineVerificationEncoding, sourceExactSigningProjection] using
      hfinal.1
  · simp only [finishSourceVerificationEncoding,
      finishOnlineVerificationEncoding, observeVerificationEncoding]
    rw [hfinal.2, ← CappedEncodingMonitor.OnlineState.observeAll_append,
      ← hempty, ← happend]

noncomputable def onlineSourceGlobalExactDetailedExecution
    (adversary : Adversary Concrete.scheme)
    (keyView : ProgrammedGlobalChainKeygenView) :
    ProbComp ((Forgery × Bool) × SourceExactTracedState) := do
  let handled ← (simulateQ
    (cappedBothTracedMappedAdversaryImpl keyView.publicKey
      (Concrete.materializePrecomputation keyView.cache keyView.secretKey))
      (adversary.main keyView.publicKey)).run ((((keyView.cache, []), []), []))
  let verified ← (simulateQ onlineSourceExactTracedVerifierImpl
    (Concrete.scheme.verify keyView.publicKey handled.1.epoch
      handled.1.message handled.1.signature)).run handled.2
  pure ((handled.1, verified.1),
    finishSourceVerificationEncoding
      (Concrete.materializePrecomputation keyView.cache keyView.secretKey)
        handled.1 handled.2 verified.2)

noncomputable def onlineGlobalHighExactDetailedExecution
    (adversary : Adversary Concrete.scheme)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) :
    ProbComp ((Forgery × Bool) × OnlineGlobalHighExactState) := do
  let initial := OnlineGlobalHighExactState.initial
    (globalFilteredCausalKeygenState right.1.1)
  let handled ← (simulateQ (onlineGlobalHighExactMappedAdversaryImpl right)
    (adversary.main right.1.1.publicKey)).run initial
  let verified ← (simulateQ (onlineGlobalHighExactVerifierImpl right)
    (Concrete.scheme.verify right.1.1.publicKey handled.1.epoch
      handled.1.message handled.1.signature)).run handled.2
  let finalState := finishOnlineVerificationEncoding right.1.1.secretKey
    handled.1 handled.2.high.1.causal.cache verified.2.high.1.causal.cache
      verified.2
  pure ((handled.1, verified.1), finalState)

theorem onlineSourceGlobalExactDetailedExecution_eq
    (adversary : Adversary Concrete.scheme)
    (keyView : ProgrammedGlobalChainKeygenView) :
    onlineSourceGlobalExactDetailedExecution adversary keyView =
      sourceGlobalExactTracedDetailedExecution adversary keyView := by
  unfold onlineSourceGlobalExactDetailedExecution
    sourceGlobalExactTracedDetailedExecution
  simp only [onlineSourceExactTracedVerifierImpl_run_eq]
  simp [finishSourceVerificationEncoding, Functor.map_map]

theorem relTriple_onlineGlobalHighExact_detailedExecution
    (adversary : Adversary Concrete.scheme)
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen) :
    RelTriple
      (sourceGlobalExactTracedDetailedExecution adversary left)
      (onlineGlobalHighExactDetailedExecution adversary right)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          SourceOnlineGlobalHighExactStateRelation left right.1
            leftResult.2 rightResult.2) ∨ rightResult.2.bad) := by
  rw [← onlineSourceGlobalExactDetailedExecution_eq adversary left]
  unfold onlineSourceGlobalExactDetailedExecution
    onlineGlobalHighExactDetailedExecution
  let leftInitial : SourceExactTracedState := ((((left.cache, []), []), []))
  let rightInitial := OnlineGlobalHighExactState.initial
    (globalFilteredCausalKeygenState right.1.1)
  have hinitial : SourceOnlineGlobalHighExactStateRelation left right.1
      leftInitial rightInitial := by
    simpa [leftInitial, rightInitial] using
      sourceOnlineGlobalHighExactStateRelation_initial left right hrel
        hleftSupport hrightSupport
  have hhandled := relTriple_programmed_onlineGlobalHighExact_adversary left
    right hrel hleftSupport hrightSupport
      (adversary.main left.publicKey) leftInitial rightInitial hinitial
  have hpublicKey : left.publicKey = right.1.1.publicKey :=
    hrel.1.toStable.1.2.1
  simp only
  rw [← hpublicKey]
  apply relTriple_bind (relTriple_with_support hhandled)
  intro leftHandled rightHandled hresults
  rcases hresults.1 with hgood | hbad
  · have hforgery : leftHandled.1 = rightHandled.1 := hgood.1
    rw [← hforgery]
    have hvertifier := relTriple_programmed_onlineGlobalHighExact_verifier left
      right hrel hleftSupport hrightSupport
        (Concrete.scheme.verify left.publicKey leftHandled.1.epoch
          leftHandled.1.message leftHandled.1.signature)
        leftHandled.2 rightHandled.2 hgood.2
    let leftFinish := fun leftVerified : Bool × SourceExactTracedState =>
      ((leftHandled.1, leftVerified.1),
        finishSourceVerificationEncoding
          (Concrete.materializePrecomputation left.cache left.secretKey)
            leftHandled.1 leftHandled.2 leftVerified.2)
    let rightFinish := fun rightVerified : Bool × OnlineGlobalHighExactState =>
      ((leftHandled.1, rightVerified.1),
        finishOnlineVerificationEncoding right.1.1.secretKey leftHandled.1
          rightHandled.2.high.1.causal.cache
            rightVerified.2.high.1.causal.cache rightVerified.2)
    change RelTriple
      (leftFinish <$> (simulateQ onlineSourceExactTracedVerifierImpl
        (Concrete.scheme.verify left.publicKey leftHandled.1.epoch
          leftHandled.1.message leftHandled.1.signature)).run leftHandled.2)
      (rightFinish <$> (simulateQ (onlineGlobalHighExactVerifierImpl right)
        (Concrete.scheme.verify left.publicKey leftHandled.1.epoch
          leftHandled.1.message leftHandled.1.signature)).run rightHandled.2) _
    refine relTriple_map (f := leftFinish) (g := rightFinish) ?_
    apply relTriple_post_mono hvertifier
    intro leftVerified rightVerified hvertified
    rcases hvertified with hvertifiedGood | hvertifiedBad
    · apply Or.inl
      constructor
      · simp [leftFinish, rightFinish, hvertifiedGood.1]
      · exact hgood.2.finishVerificationEncoding left right hrel
          hleftSupport hrightSupport leftHandled.1 leftHandled.2
            leftVerified.2 rightHandled.2 rightVerified.2
              hvertifiedGood.2
    · exact Or.inr
        (finishOnlineVerificationEncoding_preserves_bad right.1.1.secretKey
          leftHandled.1 rightHandled.2.high.1.causal.cache
            rightVerified.2.high.1.causal.cache rightVerified.2
              hvertifiedBad)
  · let leftFinish := fun leftVerified : Bool × SourceExactTracedState =>
      ((leftHandled.1, leftVerified.1),
        finishSourceVerificationEncoding
          (Concrete.materializePrecomputation left.cache left.secretKey)
            leftHandled.1 leftHandled.2 leftVerified.2)
    let rightFinish := fun rightVerified : Bool × OnlineGlobalHighExactState =>
      ((rightHandled.1, rightVerified.1),
        finishOnlineVerificationEncoding right.1.1.secretKey rightHandled.1
          rightHandled.2.high.1.causal.cache
            rightVerified.2.high.1.causal.cache rightVerified.2)
    change RelTriple
      (leftFinish <$> (simulateQ onlineSourceExactTracedVerifierImpl
        (Concrete.scheme.verify left.publicKey leftHandled.1.epoch
          leftHandled.1.message leftHandled.1.signature)).run leftHandled.2)
      (rightFinish <$> (simulateQ (onlineGlobalHighExactVerifierImpl right)
        (Concrete.scheme.verify left.publicKey rightHandled.1.epoch
          rightHandled.1.message rightHandled.1.signature)).run rightHandled.2) _
    refine relTriple_map (f := leftFinish) (g := rightFinish) ?_
    apply relTriple_post_mono
      (relTriple_with_support
        (relTriple_prod (fun _ _ => True.intro) (fun _ _ => True.intro)))
    intro _leftVerified rightVerified hvertified
    apply Or.inr
    apply finishOnlineVerificationEncoding_preserves_bad
    exact simulate_onlineGlobalHighExactVerifierImpl_preserves_bad right
      (Concrete.scheme.verify left.publicKey rightHandled.1.epoch
        rightHandled.1.message rightHandled.1.signature)
      rightHandled.2 hbad rightVerified hvertified.2.2

abbrev OnlineGlobalHighExactProgramResult :=
  (((ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) ×
    ((Forgery × Bool) × OnlineGlobalHighExactState))

noncomputable def onlineGlobalHighExactProgram
    (adversary : Adversary Concrete.scheme) :
    ProbComp OnlineGlobalHighExactProgramResult := do
  let keyResult ← coupledGlobalChainKeygenWithBaseHighFull
  let execution ← onlineGlobalHighExactDetailedExecution adversary keyResult
  pure (keyResult, execution)

def SourceOnlineGlobalHighExactProgramRelation
    (left : SourceGlobalExactTracedProgramResult)
    (right : OnlineGlobalHighExactProgramResult) : Prop :=
  ProgrammedGlobalChainKeygenBaseHighStableRelation left.1 right.1 ∧
    ((left.2.1 = right.2.1 ∧
      SourceOnlineGlobalHighExactStateRelation left.1 right.1.1
        left.2.2 right.2.2) ∨ right.2.2.bad)

theorem relTriple_onlineGlobalHighExact_program
    (adversary : Adversary Concrete.scheme) :
    RelTriple (sourceGlobalExactTracedProgram adversary)
      (onlineGlobalHighExactProgram adversary)
      SourceOnlineGlobalHighExactProgramRelation := by
  unfold sourceGlobalExactTracedProgram onlineGlobalHighExactProgram
  apply relTriple_bind
    (relTriple_with_support
      relTriple_trajectoryProgrammedGlobalChainKeygen_withBaseHigh_stable)
  intro left right hkeygen
  obtain ⟨hrel, hleftSupport, hrightSupport⟩ := hkeygen
  have hrightViewSupport :=
    coupledGlobalChainKeygenWithBaseHighFull_support_keyView right
      hrightSupport
  apply relTriple_bind
    (relTriple_onlineGlobalHighExact_detailedExecution adversary left right
      hrel hleftSupport hrightViewSupport)
  intro leftExecution rightExecution hexecution
  exact relTriple_pure_pure ⟨hrel, hexecution⟩

end XmssSecurity.CappedChain
