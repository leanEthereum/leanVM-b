import XmssSecurity.Proof.CappedExactFirstLane
import XmssSecurity.Proof.CappedGlobalFirstLaneReconstruction

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

abbrev SourceSigningTracedState :=
  (QueryCache HashSpec × SigningCacheTrace) × AttackerActionTrace

def sourceSigningTracedStateProjection
    (state : SourceSigningTracedState) : SourceTracedState :=
  (state.1.1, state.2)

noncomputable def sourceSigningTracedMappedAdversaryImpl
    (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT SourceSigningTracedState ProbComp) :=
  actionTracedStateImpl
    (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
    attackerActionFragment

def sourceSigningTracedQueryResult
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : SourceSigningTracedState)
    (result : (OracleWorld + SigningSpec).Range input × SourceTracedState) :
    (OracleWorld + SigningSpec).Range input × SourceSigningTracedState :=
  (result.1,
    ((result.2.1,
      signingCacheTraceUpdate input initialState.1.1 result.1 result.2.1
        initialState.1.2), result.2.2))

theorem sourceSigningTracedMappedAdversaryImpl_query_eq_map
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : SourceSigningTracedState) :
    (sourceSigningTracedMappedAdversaryImpl publicKey secretKey input).run
        initialState =
      sourceSigningTracedQueryResult input initialState <$>
        (sourceDirectTracedMappedAdversaryImpl publicKey secretKey input).run
          (sourceSigningTracedStateProjection initialState) := by
  unfold sourceSigningTracedMappedAdversaryImpl actionTracedStateImpl
    sourceSigningTracedQueryResult sourceSigningTracedStateProjection
  unfold cappedCacheTracedMappedAdversaryImpl QueryImpl.extendState
  rw [cappedUnloggedMappedAdversaryImpl_eq_sourceDirectMappedAdversaryImpl]
  unfold sourceDirectTracedMappedAdversaryImpl actionTracedStateImpl
  simp only [StateT.run_mk, map_eq_bind_pure_comp, bind_assoc, pure_bind]
  apply bind_congr
  intro result
  rfl

theorem sourceSigningTracedMappedAdversaryImpl_query_projection
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : SourceSigningTracedState) :
    (fun result => (result.1,
        sourceSigningTracedStateProjection result.2)) <$>
        (sourceSigningTracedMappedAdversaryImpl publicKey secretKey input).run
          initialState =
      (sourceDirectTracedMappedAdversaryImpl publicKey secretKey input).run
        (sourceSigningTracedStateProjection initialState) := by
  rw [sourceSigningTracedMappedAdversaryImpl_query_eq_map]
  simp [Functor.map_map, sourceSigningTracedQueryResult,
    sourceSigningTracedStateProjection]

def GlobalSigningMonitoredTracedStateRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftState : SourceSigningTracedState)
    (rightState : GlobalMonitoredTracedState) : Prop :=
  GlobalMonitoredTracedStateRelation left right
    (sourceSigningTracedStateProjection leftState) rightState

theorem relTriple_programmed_globalHighMonitored_signingAction
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftState : SourceSigningTracedState)
    (rightState : GlobalMonitoredTracedState)
    (hstate : GlobalSigningMonitoredTracedStateRelation left right.1
      leftState rightState)
    (input : (OracleWorld + SigningSpec).Domain) :
    RelTriple
      ((sourceSigningTracedMappedAdversaryImpl left.publicKey
        (Concrete.materializePrecomputation left.cache left.secretKey)
          input).run leftState)
      ((globalHighMonitoredMappedAdversaryImpl right input).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalSigningMonitoredTracedStateRelation left right.1
            leftResult.2 rightResult.2) ∨ rightResult.2.1.bad) := by
  let enrich := sourceSigningTracedQueryResult input leftState
  let project := sourceSigningTracedStateProjection leftState
  have hbase := relTriple_programmed_globalHighMonitored_action left right hrel
    hleftSupport hrightSupport project rightState hstate input
  have hlifted : RelTriple
      (enrich <$> (sourceDirectTracedMappedAdversaryImpl left.publicKey
        (Concrete.materializePrecomputation left.cache left.secretKey)
          input).run project)
      (id <$> (globalHighMonitoredMappedAdversaryImpl right input).run
        rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalSigningMonitoredTracedStateRelation left right.1
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

noncomputable def sourceSigningTracedVerifierImpl :
    QueryImpl OracleWorld (StateT SourceSigningTracedState ProbComp) :=
  fun input => StateT.mk fun state =>
    (fun result => (result.1, ((result.2.1, state.1.2), result.2.2))) <$>
      (sourceDirectTracedVerifierImpl input).run
        (sourceSigningTracedStateProjection state)

theorem sourceSigningTracedVerifierImpl_query_run_eq
    (input : OracleWorld.Domain) (initialState : SourceSigningTracedState) :
    (sourceSigningTracedVerifierImpl input).run initialState =
      (fun result =>
        (result.1, ((result.2, initialState.1.2), initialState.2))) <$>
        (xmssRomImpl input).run initialState.1.1 := by
  unfold sourceSigningTracedVerifierImpl
  rw [StateT.run_mk, sourceDirectTracedVerifierImpl_query_run_eq]
  simp [Functor.map_map, sourceSigningTracedStateProjection]

theorem sourceSigningTracedVerifierImpl_run_eq
    (computation : OracleComp OracleWorld α)
    (initialState : SourceSigningTracedState) :
    (simulateQ sourceSigningTracedVerifierImpl computation).run initialState =
      (fun result =>
        (result.1, ((result.2, initialState.1.2), initialState.2))) <$>
        (simulateQ xmssRomImpl computation).run initialState.1.1 := by
  induction computation using OracleComp.inductionOn generalizing
      initialState with
  | pure value => simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, StateT.run_bind, map_bind]
      simp only [id_map]
      rw [sourceSigningTracedVerifierImpl_query_run_eq]
      simp only [bind_map_left]
      apply bind_congr
      intro head
      simpa using ih head.1 ((head.2, initialState.1.2), initialState.2)

theorem relTriple_programmed_globalHighMonitored_signingVerifierQuery
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftState : SourceSigningTracedState)
    (rightState : GlobalMonitoredTracedState)
    (hstate : GlobalSigningMonitoredTracedStateRelation left right.1
      leftState rightState)
    (input : OracleWorld.Domain) :
    RelTriple
      ((sourceSigningTracedVerifierImpl input).run leftState)
      ((globalHighMonitoredVerifierImpl right input).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalSigningMonitoredTracedStateRelation left right.1
            leftResult.2 rightResult.2) ∨ rightResult.2.1.bad) := by
  let project := sourceSigningTracedStateProjection leftState
  let enrich := fun result : OracleWorld.Range input × SourceTracedState =>
    (result.1, ((result.2.1, leftState.1.2), result.2.2))
  have hbase := relTriple_programmed_globalHighMonitored_verifier_query left
    right hrel hleftSupport hrightSupport project rightState hstate input
  have hlifted : RelTriple
      (enrich <$> (sourceDirectTracedVerifierImpl input).run project)
      (id <$> (globalHighMonitoredVerifierImpl right input).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalSigningMonitoredTracedStateRelation left right.1
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

theorem relTriple_programmed_globalHighMonitored_signingVerifier
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (computation : OracleComp OracleWorld α)
    (leftState : SourceSigningTracedState)
    (rightState : GlobalMonitoredTracedState)
    (hstate : GlobalSigningMonitoredTracedStateRelation left right.1
      leftState rightState) :
    RelTriple
      ((simulateQ sourceSigningTracedVerifierImpl computation).run leftState)
      ((simulateQ (globalHighMonitoredVerifierImpl right) computation).run
        rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalSigningMonitoredTracedStateRelation left right.1
            leftResult.2 rightResult.2) ∨ rightResult.2.1.bad) := by
  exact relTriple_simulateQ_run_until_bad_right
    sourceSigningTracedVerifierImpl
    (globalHighMonitoredVerifierImpl right)
    (GlobalSigningMonitoredTracedStateRelation left right.1)
    (fun state : GlobalMonitoredTracedState => state.1.bad)
    (fun input leftState rightState hstate =>
      relTriple_programmed_globalHighMonitored_signingVerifierQuery left right
        hrel hleftSupport hrightSupport leftState rightState hstate input)
    (fun input state hbad result hresult =>
      globalHighMonitoredVerifierImpl_preserves_bad right input state hbad
        result hresult)
    computation leftState rightState hstate

theorem globalSigningMonitoredTracedStateRelation_initial
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen) :
    GlobalSigningMonitoredTracedStateRelation left right.1
      ((left.cache, []), [])
      (⟨globalFilteredCausalKeygenState right.1.1,
        some AdaptiveRevealMonitor.State.empty, []⟩, []) := by
  exact globalMonitoredTracedStateRelation_initial left right hrel
    hleftSupport hrightSupport

theorem evalDist_materializedTrajectoryGlobalChainKeygen_eq_cappedKeygen :
    evalDist
        ((fun view : ProgrammedGlobalChainKeygenView =>
          Concrete.materializeCachedKeyResult view.keyResult) <$>
            trajectoryProgrammedGlobalChainKeygen) =
      evalDist ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅) := by
  calc
    _ = evalDist
        ((fun view : ProgrammedGlobalChainKeygenView =>
          Concrete.materializeCachedKeyResult view.keyResult) <$>
            actualGlobalChainKeygen) := by
      apply evalDist_map_congr_of_evalDist_eq
      exact evalDist_actualGlobalChainKeygen_eq_trajectoryProgrammed.symm
    _ = evalDist
        (Concrete.materializeCachedKeyResult <$>
          (simulateQ xmssRomImpl Concrete.keygen).run ∅) := by
      unfold actualGlobalChainKeygen
      simp [ProgrammedGlobalChainKeygenView.keyResult,
        map_eq_bind_pure_comp]
    _ = evalDist
        ((simulateQ xmssRomImpl Concrete.precomputedKeygen).run ∅) :=
      Concrete.evalDist_materialized_keygen_eq_precomputedKeygen
    _ = _ := by rfl

theorem probEvent_eq_of_evalDist_eq
    {computation₁ computation₂ : ProbComp α}
    (event : α → Prop)
    (heval : evalDist computation₁ = evalDist computation₂) :
    Pr[event | computation₁] = Pr[event | computation₂] := by
  simp only [probEvent_eq_tsum_indicator, probOutput_def]
  rw [heval]

end XmssSecurity.CappedChain
