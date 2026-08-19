import XmssSecurity.CappedExactFirstLane
import XmssSecurity.CappedGlobalFirstLaneReconstruction

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

theorem sourceSigningTracedMappedAdversaryImpl_query_baseProjection
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState : SourceSigningTracedState) :
    (fun result => (result.1, result.2.1)) <$>
        (sourceSigningTracedMappedAdversaryImpl publicKey secretKey input).run
          initialState =
      (cappedCacheTracedMappedAdversaryImpl publicKey secretKey input).run
        initialState.1 := by
  unfold sourceSigningTracedMappedAdversaryImpl actionTracedStateImpl
  simp [StateT.run_mk]

theorem sourceSigningTracedMappedAdversaryImpl_run_baseProjection
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : SourceSigningTracedState) :
    (fun result => (result.1, result.2.1)) <$>
        (simulateQ
          (sourceSigningTracedMappedAdversaryImpl publicKey secretKey)
          computation).run initialState =
      (simulateQ (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
        computation).run initialState.1 := by
  induction computation using OracleComp.inductionOn generalizing
      initialState with
  | pure value => simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, StateT.run_bind, map_bind]
      simp only [id_map]
      simp_rw [ih]
      calc
        _ = (do
            let head ← (fun result => (result.1, result.2.1)) <$>
              (sourceSigningTracedMappedAdversaryImpl publicKey secretKey
                input).run initialState
            (simulateQ
              (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
              (next head.1)).run head.2) := by
                rw [bind_map_left]
        _ = _ := by
          rw [sourceSigningTracedMappedAdversaryImpl_query_baseProjection]

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

theorem relTriple_programmed_globalHighMonitored_signingAdversary
    (adversary : Adversary Concrete.scheme)
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
      leftState rightState) :
    RelTriple
      ((simulateQ
        (sourceSigningTracedMappedAdversaryImpl left.publicKey
          (Concrete.materializePrecomputation left.cache left.secretKey))
          (adversary.main left.publicKey)).run leftState)
      ((simulateQ (globalHighMonitoredMappedAdversaryImpl right)
        (adversary.main left.publicKey)).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalSigningMonitoredTracedStateRelation left right.1
            leftResult.2 rightResult.2) ∨ rightResult.2.1.bad) := by
  exact relTriple_simulateQ_run_until_bad_right
    (sourceSigningTracedMappedAdversaryImpl left.publicKey
      (Concrete.materializePrecomputation left.cache left.secretKey))
    (globalHighMonitoredMappedAdversaryImpl right)
    (GlobalSigningMonitoredTracedStateRelation left right.1)
    (fun state : GlobalMonitoredTracedState => state.1.bad)
    (fun input leftState rightState hstate =>
      relTriple_programmed_globalHighMonitored_signingAction left right hrel
        hleftSupport hrightSupport leftState rightState hstate input)
    (fun input state hbad result hresult =>
      globalHighMonitoredMappedAdversaryImpl_preserves_bad right input state
        hbad result hresult)
    (adversary.main left.publicKey) leftState rightState hstate

noncomputable def sourceSigningTracedVerifierImpl :
    QueryImpl OracleWorld (StateT SourceSigningTracedState ProbComp) :=
  fun input => StateT.mk fun state =>
    (fun result => (result.1, ((result.2.1, state.1.2), result.2.2))) <$>
      (sourceDirectTracedVerifierImpl input).run
        (sourceSigningTracedStateProjection state)

theorem sourceSigningTracedVerifierImpl_query_projection
    (input : OracleWorld.Domain) (state : SourceSigningTracedState) :
    (fun result => (result.1,
      sourceSigningTracedStateProjection result.2)) <$>
        (sourceSigningTracedVerifierImpl input).run state =
      (sourceDirectTracedVerifierImpl input).run
        (sourceSigningTracedStateProjection state) := by
  unfold sourceSigningTracedVerifierImpl
  simp [StateT.run_mk, Functor.map_map,
    sourceSigningTracedStateProjection]

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

noncomputable def sourceGlobalSigningTracedDetailedExecution
    (adversary : Adversary Concrete.scheme)
    (keyView : ProgrammedGlobalChainKeygenView) :
    ProbComp ((Forgery × Bool) × SourceSigningTracedState) := do
  let handled ← (simulateQ
    (sourceSigningTracedMappedAdversaryImpl keyView.publicKey
      (Concrete.materializePrecomputation keyView.cache keyView.secretKey))
      (adversary.main keyView.publicKey)).run ((keyView.cache, []), [])
  let verified ← (simulateQ sourceSigningTracedVerifierImpl
    (Concrete.scheme.verify keyView.publicKey handled.1.epoch
      handled.1.message handled.1.signature)).run handled.2
  pure ((handled.1, verified.1), verified.2)

theorem relTriple_sourceGlobalSigning_globalHighMonitored_detailedExecution
    (adversary : Adversary Concrete.scheme)
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen) :
    RelTriple (sourceGlobalSigningTracedDetailedExecution adversary left)
      (globalHighMonitoredDetailedExecution adversary right)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalSigningMonitoredTracedStateRelation left right.1
            leftResult.2 rightResult.2) ∨ rightResult.2.1.bad) := by
  have hinitial := globalSigningMonitoredTracedStateRelation_initial left right
    hrel hleftSupport hrightSupport
  have hpublicKey : left.publicKey = right.1.1.publicKey :=
    hrel.1.toStable.1.2.1
  unfold sourceGlobalSigningTracedDetailedExecution
    globalHighMonitoredDetailedExecution
  rw [← hpublicKey]
  apply relTriple_bind
    (relTriple_programmed_globalHighMonitored_signingAdversary adversary left
      right hrel hleftSupport hrightSupport ((left.cache, []), [])
        (⟨globalFilteredCausalKeygenState right.1.1,
          some AdaptiveRevealMonitor.State.empty, []⟩, []) hinitial)
  intro leftHandled rightHandled hhandled
  rcases hhandled with hgood | hbad
  · obtain ⟨hforgery, hstates⟩ := hgood
    rw [← hforgery]
    apply relTriple_bind
      (relTriple_programmed_globalHighMonitored_signingVerifier left right hrel
        hleftSupport hrightSupport
        (Concrete.scheme.verify left.publicKey leftHandled.1.epoch
          leftHandled.1.message leftHandled.1.signature)
        leftHandled.2 rightHandled.2 hstates)
    intro leftVerified rightVerified hvertified
    apply relTriple_pure_pure
    rcases hvertified with hverifiedGood | hverifiedBad
    · exact Or.inl ⟨congrArg (Prod.mk leftHandled.1) hverifiedGood.1,
        hverifiedGood.2⟩
    · exact Or.inr hverifiedBad
  · apply relTriple_bind
      (relTriple_prod (fun _result _hresult => True.intro)
        (fun rightResult hrightResult =>
          OracleComp.simulateQ_run_preservesInv
            (globalHighMonitoredVerifierImpl right)
            (fun state : GlobalMonitoredTracedState => state.1.bad)
            (globalHighMonitoredVerifierImpl_preserves_bad right)
            (Concrete.scheme.verify left.publicKey rightHandled.1.epoch
              rightHandled.1.message rightHandled.1.signature)
            rightHandled.2 hbad rightResult hrightResult))
    intro leftVerified rightVerified hvertified
    apply relTriple_pure_pure
    exact Or.inr hvertified.2

abbrev SourceGlobalSigningTracedProgramResult :=
  ProgrammedGlobalChainKeygenView ×
    ((Forgery × Bool) × SourceSigningTracedState)

noncomputable def sourceGlobalSigningTracedProgram
    (adversary : Adversary Concrete.scheme) :
    ProbComp SourceGlobalSigningTracedProgramResult := do
  let keyView ← trajectoryProgrammedGlobalChainKeygen
  let execution ← sourceGlobalSigningTracedDetailedExecution adversary keyView
  pure (keyView, execution)

def sourceGlobalSigningExecutionResult
    (keyView : ProgrammedGlobalChainKeygenView)
    (execution : (Forgery × Bool) × SourceSigningTracedState) :
    GameOutcome × (QueryCache HashSpec × SigningCacheTrace) :=
  (⟨keyView.publicKey,
    Concrete.materializePrecomputation keyView.cache keyView.secretKey,
    execution.1.1, execution.2.1.2.toSigningLog, execution.1.2⟩,
    execution.2.1)

theorem sourceGlobalSigningTracedDetailedExecution_eq_signingTrace
    (adversary : Adversary Concrete.scheme)
    (keyView : ProgrammedGlobalChainKeygenView) :
    sourceGlobalSigningExecutionResult keyView <$>
        sourceGlobalSigningTracedDetailedExecution adversary keyView =
      cappedDetailedGameAfterKeygenWithSigningTrace adversary
        keyView.publicKey
        (Concrete.materializePrecomputation keyView.cache keyView.secretKey)
        keyView.cache := by
  unfold sourceGlobalSigningTracedDetailedExecution
    cappedDetailedGameAfterKeygenWithSigningTrace
  simp only [map_bind, map_pure]
  simp_rw [sourceSigningTracedVerifierImpl_run_eq]
  simp only [bind_map_left]
  let finish : Forgery × (QueryCache HashSpec × SigningCacheTrace) →
      ProbComp (GameOutcome × (QueryCache HashSpec × SigningCacheTrace)) :=
    fun handled => do
      let verified ← (simulateQ xmssRomImpl
        (Concrete.scheme.verify keyView.publicKey handled.1.epoch
          handled.1.message handled.1.signature)).run handled.2.1
      pure (⟨keyView.publicKey,
        Concrete.materializePrecomputation keyView.cache keyView.secretKey,
        handled.1, handled.2.2.toSigningLog, verified.1⟩,
        (verified.2, handled.2.2))
  change (do
      let handled ← (simulateQ
        (sourceSigningTracedMappedAdversaryImpl keyView.publicKey
          (Concrete.materializePrecomputation keyView.cache keyView.secretKey))
        (adversary.main keyView.publicKey)).run ((keyView.cache, []), [])
      finish (handled.1, handled.2.1)) =
    (do
      let handled ← (simulateQ
        (cappedCacheTracedMappedAdversaryImpl keyView.publicKey
          (Concrete.materializePrecomputation keyView.cache keyView.secretKey))
        (adversary.main keyView.publicKey)).run (keyView.cache, [])
      finish handled)
  rw [← bind_map_left,
    sourceSigningTracedMappedAdversaryImpl_run_baseProjection]

def sourceGlobalSigningProgramResult
    (result : SourceGlobalSigningTracedProgramResult) :
    GameOutcome × (QueryCache HashSpec × SigningCacheTrace) :=
  sourceGlobalSigningExecutionResult result.1 result.2

theorem sourceGlobalSigningTracedProgram_eq_trajectorySigningTrace
    (adversary : Adversary Concrete.scheme) :
    sourceGlobalSigningProgramResult <$>
        sourceGlobalSigningTracedProgram adversary = (do
      let keyView ← trajectoryProgrammedGlobalChainKeygen
      cappedDetailedGameAfterKeygenWithSigningTrace adversary
        keyView.publicKey
        (Concrete.materializePrecomputation keyView.cache keyView.secretKey)
        keyView.cache) := by
  unfold sourceGlobalSigningTracedProgram
  simp only [map_eq_bind_pure_comp, bind_assoc]
  apply bind_congr
  intro keyView
  rw [← sourceGlobalSigningTracedDetailedExecution_eq_signingTrace]
  simp [sourceGlobalSigningProgramResult, map_eq_bind_pure_comp]

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

theorem evalDist_sourceGlobalSigning_eq_cappedSigningTrace
    (adversary : Adversary Concrete.scheme) :
    evalDist (sourceGlobalSigningProgramResult <$>
        sourceGlobalSigningTracedProgram adversary) =
      evalDist (cappedDetailedGameWithSigningTrace adversary) := by
  rw [sourceGlobalSigningTracedProgram_eq_trajectorySigningTrace]
  unfold cappedDetailedGameWithSigningTrace
  rw [evalDist_bind, evalDist_bind]
  let project := fun view : ProgrammedGlobalChainKeygenView =>
    Concrete.materializeCachedKeyResult view.keyResult
  calc
    _ = evalDist (project <$> trajectoryProgrammedGlobalChainKeygen) >>=
        fun keyResult => evalDist
          (cappedDetailedGameAfterKeygenWithSigningTrace adversary
            keyResult.1.1 keyResult.1.2 keyResult.2) := by
      rw [evalDist_map, map_eq_bind_pure_comp, bind_assoc]
      apply bind_congr
      intro keyView
      simp [project, ProgrammedGlobalChainKeygenView.keyResult,
        Concrete.materializeCachedKeyResult]
    _ = evalDist ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅) >>=
        fun keyResult => evalDist
          (cappedDetailedGameAfterKeygenWithSigningTrace adversary
            keyResult.1.1 keyResult.1.2 keyResult.2) := by
      rw [evalDist_materializedTrajectoryGlobalChainKeygen_eq_cappedKeygen]
    _ = _ := rfl

def SigningTraceWinningExactFirstLaneBadEventOccurs
    (execution : GameOutcome ×
      (QueryCache HashSpec × SigningCacheTrace)) : Prop :=
  ((WinningOutcomeBadEventOccurs execution.2.1 execution.1 .encoding ∧
      ¬(WinningOutcomeBadEventOccurs execution.2.1 execution.1 .encoding ∧
        execution.2.2.HasEncodingInputPrehit execution.1.secretKey)) ∨
    GlobalWinningChainValueRevealed execution.2.1 execution.1)

def SourceWinningExactFirstLaneBadEventOccurs
    (result : SourceGlobalSigningTracedProgramResult) : Prop :=
  SigningTraceWinningExactFirstLaneBadEventOccurs
    (sourceGlobalSigningProgramResult result)

theorem cappedExactFirstLane_probability_eq_signingTrace
    (adversary : Adversary Concrete.scheme) :
    Pr[WinningExactFirstLaneBadEventOccurs |
        cappedDetailedGameWithEncodingTrace adversary] =
      Pr[SigningTraceWinningExactFirstLaneBadEventOccurs |
        cappedDetailedGameWithSigningTrace adversary] := by
  rw [← cappedDetailedGameWithEncodingTrace_projection, probEvent_map]
  rfl

theorem probEvent_eq_of_evalDist_eq
    {computation₁ computation₂ : ProbComp α}
    (event : α → Prop)
    (heval : evalDist computation₁ = evalDist computation₂) :
    Pr[event | computation₁] = Pr[event | computation₂] := by
  simp only [probEvent_eq_tsum_indicator, probOutput_def]
  rw [heval]

theorem cappedExactFirstLane_probability_eq_sourceGlobalSigning
    (adversary : Adversary Concrete.scheme) :
    Pr[WinningExactFirstLaneBadEventOccurs |
        cappedDetailedGameWithEncodingTrace adversary] =
      Pr[SourceWinningExactFirstLaneBadEventOccurs |
        sourceGlobalSigningTracedProgram adversary] := by
  rw [cappedExactFirstLane_probability_eq_signingTrace]
  calc
    _ = Pr[SigningTraceWinningExactFirstLaneBadEventOccurs |
        sourceGlobalSigningProgramResult <$>
          sourceGlobalSigningTracedProgram adversary] :=
      probEvent_eq_of_evalDist_eq _
        (evalDist_sourceGlobalSigning_eq_cappedSigningTrace adversary).symm
    _ = _ := by
      rw [probEvent_map]
      rfl

def SourceGlobalSigningHighMonitoredProgramRelation
    (left : SourceGlobalSigningTracedProgramResult)
    (right : GlobalHighMonitoredProgramResult) : Prop :=
  ProgrammedGlobalChainKeygenBaseHighStableRelation left.1 right.1 ∧
    ((left.2.1 = right.2.1 ∧
      GlobalSigningMonitoredTracedStateRelation left.1 right.1.1 left.2.2
        right.2.2) ∨ right.2.2.1.bad) ∧
    right.2.2.1.TraceConsistent right.1.1.2

theorem relTriple_sourceGlobalSigning_globalHighMonitored_program
    (adversary : Adversary Concrete.scheme) :
    RelTriple (sourceGlobalSigningTracedProgram adversary)
      (globalHighMonitoredProgram adversary)
      SourceGlobalSigningHighMonitoredProgramRelation := by
  unfold sourceGlobalSigningTracedProgram globalHighMonitoredProgram
  apply relTriple_bind
    (relTriple_with_support
      relTriple_trajectoryProgrammedGlobalChainKeygen_withBaseHigh_stable)
  intro left right hkeygen
  obtain ⟨hrel, hleftSupport, hrightSupport⟩ := hkeygen
  have hrightViewSupport :=
    coupledGlobalChainKeygenWithBaseHighFull_support_keyView right
      hrightSupport
  apply relTriple_bind
    (relTriple_with_support
      (relTriple_sourceGlobalSigning_globalHighMonitored_detailedExecution
        adversary left right hrel hleftSupport hrightViewSupport))
  intro leftExecution rightExecution hexecution
  apply relTriple_pure_pure
  exact ⟨hrel, hexecution.1,
    globalHighMonitoredDetailedExecution_traceConsistent adversary right
      rightExecution hexecution.2.2⟩

end XmssSecurity.CappedChain
