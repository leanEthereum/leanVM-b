import XmssSecurity.CappedGlobalFirstLaneTrace
import XmssSecurity.CappedGlobalChainHighDirectReduction
import XmssSecurity.CappedGlobalChainHighDirectDistribution

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

abbrev GlobalFirstLaneTracedState :=
  GlobalCausalHashState × AttackerActionTrace

noncomputable def globalFirstLaneTracedMappedAdversaryImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT GlobalFirstLaneTracedState
        (OracleComp GlobalFirstLaneWorld)) :=
  fun input => StateT.mk fun state => do
    let result ←
      (globalFirstLaneBaseMappedAdversaryImpl keyView edgeHigh input).run state.1
    pure (result.1,
      (result.2, state.2 ++ attackerActionFragment input result.1))

noncomputable def globalFirstLaneTracedVerifierImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    QueryImpl OracleWorld
      (StateT GlobalFirstLaneTracedState
        (OracleComp GlobalFirstLaneWorld)) :=
  fun input => StateT.mk fun state =>
    (fun result => (result.1, (result.2, state.2))) <$>
      (globalFirstLaneVerifierImpl keyView edgeHigh input).run state.1

noncomputable def globalFirstLaneTracedDetailedExecution
    (adversary : Adversary Concrete.scheme)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    StateT GlobalFirstLaneTracedState (OracleComp GlobalFirstLaneWorld)
      (Forgery × Bool) := do
  let handled ← simulateQ
    (globalFirstLaneTracedMappedAdversaryImpl keyView edgeHigh)
      (adversary.main keyView.publicKey)
  let verified ← simulateQ
    (globalFirstLaneTracedVerifierImpl keyView edgeHigh)
      (Concrete.scheme.verify keyView.publicKey handled.epoch
        handled.message handled.signature)
  pure (handled, verified)

abbrev GlobalFirstLaneTracedResult :=
  GlobalHighDirectKeyResult ×
    ((Forgery × Bool) × GlobalFirstLaneTracedState)

noncomputable def globalFirstLaneTracedProgram
    (adversary : Adversary Concrete.scheme) :
    OracleComp GlobalFirstLaneWorld GlobalFirstLaneTracedResult := do
  let keyResult ← FirstLaneOracleSimulation.liftProbComp
    globalHighDirectKeygen
  let execution ← (globalFirstLaneTracedDetailedExecution adversary keyResult.1
    keyResult.2).run (globalFilteredCausalKeygenState keyResult.1, [])
  pure (keyResult, execution)

def globalFirstLaneTracedBaseProjection
    (result : GlobalFirstLaneTracedResult) : GlobalFirstLaneResult :=
  (result.1, (result.2.1, result.2.2.1))

abbrev GlobalHighDirectTracedState :=
  GlobalCausalHashState × AttackerActionTrace

noncomputable def globalHighDirectTracedMappedAdversaryImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT GlobalHighDirectTracedState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  fun input => StateT.mk fun state => do
    let result ←
      (globalHighDirectBaseMappedAdversaryImpl keyView edgeHigh input).run state.1
    pure (result.1,
      (result.2, state.2 ++ attackerActionFragment input result.1))

noncomputable def globalHighDirectTracedVerifierImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    QueryImpl OracleWorld
      (StateT GlobalHighDirectTracedState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  fun input => StateT.mk fun state =>
    (fun result => (result.1, (result.2, state.2))) <$>
      (globalHighDirectVerifierImpl keyView edgeHigh input).run state.1

noncomputable def globalHighDirectTracedDetailedExecution
    (adversary : Adversary Concrete.scheme)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    StateT GlobalHighDirectTracedState
      (OracleComp
        (RevealProbeOracleSimulation.World GlobalChainValueIndex))
      (Forgery × Bool) := do
  let handled ← simulateQ
    (globalHighDirectTracedMappedAdversaryImpl keyView edgeHigh)
      (adversary.main keyView.publicKey)
  let verified ← simulateQ
    (globalHighDirectTracedVerifierImpl keyView edgeHigh)
      (Concrete.scheme.verify keyView.publicKey handled.epoch
        handled.message handled.signature)
  pure (handled, verified)

abbrev GlobalHighDirectTracedResult :=
  GlobalHighDirectKeyResult ×
    ((Forgery × Bool) × GlobalHighDirectTracedState)

noncomputable def globalHighDirectTracedProgram
    (adversary : Adversary Concrete.scheme) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      GlobalHighDirectTracedResult := do
  let keyResult ← RevealProbeOracleSimulation.liftProbComp
    globalHighDirectKeygen
  let execution ← (globalHighDirectTracedDetailedExecution adversary keyResult.1
    keyResult.2).run (globalFilteredCausalKeygenState keyResult.1, [])
  pure (keyResult, execution)

theorem globalFirstLaneTracedMappedAdversaryImpl_baseProjection
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : GlobalFirstLaneTracedState) :
    (fun result => (result.1, result.2.1)) <$>
        (simulateQ
          (globalFirstLaneTracedMappedAdversaryImpl keyView edgeHigh)
          computation).run initialState =
      (simulateQ (globalFirstLaneBaseMappedAdversaryImpl keyView edgeHigh)
        computation).run initialState.1 := by
  induction computation using OracleComp.inductionOn generalizing
      initialState with
  | pure value => simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, StateT.run_bind, map_bind]
      simp only [id_map]
      simp_rw [ih]
      unfold globalFirstLaneTracedMappedAdversaryImpl
      simp [StateT.run_mk]

theorem globalFirstLaneTracedVerifierImpl_baseProjection
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp OracleWorld α)
    (initialState : GlobalFirstLaneTracedState) :
    (fun result => (result.1, result.2.1)) <$>
        (simulateQ (globalFirstLaneTracedVerifierImpl keyView edgeHigh)
          computation).run initialState =
      (simulateQ (globalFirstLaneVerifierImpl keyView edgeHigh)
        computation).run initialState.1 := by
  induction computation using OracleComp.inductionOn generalizing
      initialState with
  | pure value => simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, StateT.run_bind, map_bind]
      simp only [id_map]
      simp_rw [ih]
      unfold globalFirstLaneTracedVerifierImpl
      simp [StateT.run_mk]

theorem globalFirstLaneTracedDetailedExecution_baseProjection
    (adversary : Adversary Concrete.scheme)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (initialState : GlobalFirstLaneTracedState) :
    (fun result => (result.1, result.2.1)) <$>
        (globalFirstLaneTracedDetailedExecution adversary keyView edgeHigh).run
          initialState =
      (globalFirstLaneDetailedExecution adversary keyView edgeHigh).run
        initialState.1 := by
  unfold globalFirstLaneTracedDetailedExecution
    globalFirstLaneDetailedExecution
  simp only [StateT.run_bind, StateT.run_pure, map_bind, map_pure]
  let project := fun handled : Forgery × GlobalFirstLaneTracedState =>
    (handled.1, handled.2.1)
  let tail := fun handled : Forgery × GlobalCausalHashState => do
    let verified ← (simulateQ
      (globalFirstLaneVerifierImpl keyView edgeHigh)
      (Concrete.scheme.verify keyView.publicKey handled.1.epoch
        handled.1.message handled.1.signature)).run handled.2
    pure ((handled.1, verified.1), verified.2)
  have htail (handled : Forgery × GlobalFirstLaneTracedState) :
      (do
        let verified ← (simulateQ
          (globalFirstLaneTracedVerifierImpl keyView edgeHigh)
          (Concrete.scheme.verify keyView.publicKey handled.1.epoch
            handled.1.message handled.1.signature)).run handled.2
        pure ((handled.1, verified.1), verified.2.1)) =
        tail (project handled) := by
    have hprojection := globalFirstLaneTracedVerifierImpl_baseProjection
      keyView edgeHigh
      (Concrete.scheme.verify keyView.publicKey handled.1.epoch
        handled.1.message handled.1.signature) handled.2
    simpa [tail, project, Functor.map_map, map_eq_bind_pure_comp] using
      congrArg (fun candidate =>
        (fun verified => ((handled.1, verified.1), verified.2)) <$> candidate)
        hprojection
  simp_rw [htail]
  change (do
    let handled ← (simulateQ
      (globalFirstLaneTracedMappedAdversaryImpl keyView edgeHigh)
      (adversary.main keyView.publicKey)).run initialState
    tail (project handled)) = _
  rw [← bind_map_left project,
    globalFirstLaneTracedMappedAdversaryImpl_baseProjection]

theorem globalFirstLaneTracedProgram_baseProjection
    (adversary : Adversary Concrete.scheme) :
    globalFirstLaneTracedBaseProjection <$>
        globalFirstLaneTracedProgram adversary =
      globalFirstLaneProgram adversary := by
  unfold globalFirstLaneTracedProgram globalFirstLaneProgram
  simp only [map_bind, map_pure]
  apply bind_congr
  intro keyResult
  have hprojection := globalFirstLaneTracedDetailedExecution_baseProjection
    adversary keyResult.1 keyResult.2
      (globalFilteredCausalKeygenState keyResult.1, [])
  simpa [globalFirstLaneTracedBaseProjection, Functor.map_map,
    map_eq_bind_pure_comp] using congrArg
      (fun candidate => (fun execution => (keyResult, execution)) <$> candidate)
      hprojection

theorem globalFirstLaneErase_tracedMappedAdversaryImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalFirstLaneTracedState) :
    GlobalFirstLaneErases
      ((globalFirstLaneTracedMappedAdversaryImpl keyView edgeHigh input).run
        state)
      ((globalHighDirectTracedMappedAdversaryImpl keyView edgeHigh input).run
        state) := by
  unfold globalFirstLaneTracedMappedAdversaryImpl
    globalHighDirectTracedMappedAdversaryImpl
  simp only [StateT.run_mk]
  apply ((globalFirstLaneBaseMappedErasure keyView edgeHigh).erase input
    state.1).bind
  intro result
  exact GlobalFirstLaneErases.pure _

theorem globalFirstLaneErase_tracedVerifierImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : OracleWorld.Domain)
    (state : GlobalFirstLaneTracedState) :
    GlobalFirstLaneErases
      ((globalFirstLaneTracedVerifierImpl keyView edgeHigh input).run state)
      ((globalHighDirectTracedVerifierImpl keyView edgeHigh input).run state) := by
  unfold globalFirstLaneTracedVerifierImpl
    globalHighDirectTracedVerifierImpl
  simp only [StateT.run_mk]
  apply ((globalFirstLaneOracleErasure keyView edgeHigh).erase input
    state.1).bind
  intro result
  exact GlobalFirstLaneErases.pure _

theorem globalFirstLaneErase_tracedDetailedExecution
    (adversary : Adversary Concrete.scheme)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (state : GlobalFirstLaneTracedState) :
    GlobalFirstLaneErases
      ((globalFirstLaneTracedDetailedExecution adversary keyView edgeHigh).run
        state)
      ((globalHighDirectTracedDetailedExecution adversary keyView edgeHigh).run
        state) := by
  unfold globalFirstLaneTracedDetailedExecution
    globalHighDirectTracedDetailedExecution
  apply (globalFirstLaneErases_simulateQ_run _ _
    (globalFirstLaneErase_tracedMappedAdversaryImpl keyView edgeHigh)
    (adversary.main keyView.publicKey) state).bind
  intro handled
  apply (globalFirstLaneErases_simulateQ_run _ _
    (globalFirstLaneErase_tracedVerifierImpl keyView edgeHigh)
    (Concrete.scheme.verify keyView.publicKey handled.1.epoch
      handled.1.message handled.1.signature) handled.2).bind
  intro verified
  exact GlobalFirstLaneErases.pure _

theorem globalFirstLaneErase_tracedProgram
    (adversary : Adversary Concrete.scheme) :
    GlobalFirstLaneErases
      (globalFirstLaneTracedProgram adversary)
      (globalHighDirectTracedProgram adversary) := by
  unfold globalFirstLaneTracedProgram globalHighDirectTracedProgram
  apply (globalFirstLaneErases_liftProbComp globalHighDirectKeygen).bind
  intro keyResult
  apply (globalFirstLaneErase_tracedDetailedExecution adversary keyResult.1
    keyResult.2 (globalFilteredCausalKeygenState keyResult.1, [])).bind
  intro execution
  exact GlobalFirstLaneErases.pure _

theorem map_globalFirstLaneTracedEagerExperiment_chainProjection
    (adversary : Adversary Concrete.scheme) :
    (fun result =>
        (result.1, (result.2.1, result.2.2.chainActions))) <$>
        FirstLaneOracleSimulation.eagerExperiment
          (globalFirstLaneTracedProgram adversary) =
      RevealProbeOracleSimulation.eagerExperiment
        (globalHighDirectTracedProgram adversary) := by
  rw [map_globalFirstLaneEagerExperiment_chainProjection]
  rw [(globalFirstLaneErase_tracedProgram adversary).eq]

theorem map_simulate_globalMonitoredTraced_full_projection_of_query
    {spec : OracleSpec ι}
    (table : GlobalChainValueIndex → Digest)
    (left : QueryImpl spec (StateT GlobalMonitoredTracedState ProbComp))
    (right : QueryImpl spec
      (StateT GlobalHighDirectTracedState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))))
    (hquery : ∀ (input : spec.Domain) (state : GlobalMonitoredCausalState)
      (attackerTrace : AttackerActionTrace),
      (fun result : spec.Range input × GlobalMonitoredTracedState =>
        ((result.1, (result.2.1.causal, result.2.2)), result.2.1.trace)) <$>
          (left input).run (state, attackerTrace) =
        (fun result : ((spec.Range input × GlobalHighDirectTracedState) ×
            RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
          (result.1, state.trace ++ result.2)) <$>
          (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
            ((right input).run (state.causal, attackerTrace))).run)
    (computation : OracleComp spec α)
    (state : GlobalMonitoredCausalState)
    (attackerTrace : AttackerActionTrace) :
    (fun result : α × GlobalMonitoredTracedState =>
      ((result.1, (result.2.1.causal, result.2.2)), result.2.1.trace)) <$>
        (simulateQ left computation).run (state, attackerTrace) =
      (fun result : ((α × GlobalHighDirectTracedState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          ((simulateQ right computation).run
            (state.causal, attackerTrace))).run := by
  induction computation using OracleComp.inductionOn generalizing state
      attackerTrace with
  | pure value => simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, StateT.run_bind, WriterT.run_bind', map_bind,
        simulateQ_spec_query]
      simp_rw [ih]
      let project :=
        fun result : spec.Range input × GlobalMonitoredTracedState =>
          ((result.1, (result.2.1.causal, result.2.2)), result.2.1.trace)
      let tail := fun head : ((spec.Range input ×
          GlobalHighDirectTracedState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (fun result => (result.1, head.2 ++ result.2)) <$>
          (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
            ((simulateQ right (next head.1.1)).run head.1.2)).run
      change (do
        let head ← (left input).run (state, attackerTrace)
        tail (project head)) = _
      rw [← bind_map_left project]
      have hhead := hquery input state attackerTrace
      change project <$> (left input).run (state, attackerTrace) = _ at hhead
      rw [hhead, bind_map_left]
      apply bind_congr
      intro head
      simp [tail, Functor.map_map, List.append_assoc]

theorem map_globalHighMonitored_adversary_full_query
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalMonitoredCausalState)
    (attackerTrace : AttackerActionTrace) :
    (fun result : (OracleWorld + SigningSpec).Range input ×
        GlobalMonitoredTracedState =>
      ((result.1, (result.2.1.causal, result.2.2)), result.2.1.trace)) <$>
        (globalHighMonitoredMappedAdversaryImpl
          ((keyView, base), edgeHigh) input).run (state, attackerTrace) =
      (fun result : (((OracleWorld + SigningSpec).Range input ×
          GlobalHighDirectTracedState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          ((globalHighDirectTracedMappedAdversaryImpl keyView edgeHigh input
            ).run (state.causal, attackerTrace))).run := by
  let addAttackerTrace := fun result :
      (((OracleWorld + SigningSpec).Range input × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
    ((result.1.1,
      (result.1.2, attackerTrace ++ attackerActionFragment input result.1.1)),
      result.2)
  have herased :
      (fun result : (OracleWorld + SigningSpec).Range input ×
          GlobalMonitoredTracedState =>
        ((result.1, result.2.1.causal), result.2.1.trace)) <$>
          (globalHighMonitoredMappedAdversaryImpl
            ((keyView, base), edgeHigh) input).run (state, attackerTrace) =
        (fun result : (((OracleWorld + SigningSpec).Range input ×
            GlobalCausalHashState) ×
            RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
          (result.1, state.trace ++ result.2)) <$>
          (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
            ((globalHighDirectBaseMappedAdversaryImpl keyView edgeHigh input
              ).run state.causal)).run := by
    rcases input with (uniformOrHash | request)
    · rcases uniformOrHash with n | hashInput
      · unfold globalHighDirectBaseMappedAdversaryImpl
          globalHighDirectOracleImpl globalHighDirectOracleExecution
          globalHighDirectUniformImpl
        exact map_globalHighMonitored_uniform_erased_projection keyView base
          edgeHigh n state attackerTrace
      · unfold globalHighDirectBaseMappedAdversaryImpl
          globalHighDirectOracleImpl globalHighDirectOracleExecution
        exact map_globalHighMonitored_hash_erased_projection keyView base
          edgeHigh hashInput state attackerTrace
    · unfold globalHighDirectBaseMappedAdversaryImpl
        globalHighDirectSigningImpl
      exact map_globalHighMonitored_sign_erased_projection keyView base
        edgeHigh request state attackerTrace
  have hlifted := congrArg (fun candidate => addAttackerTrace <$> candidate)
    herased
  simpa [addAttackerTrace, globalHighMonitoredMappedAdversaryImpl,
    actionTracedStateImpl, globalHighDirectTracedMappedAdversaryImpl,
    StateT.run_mk, Functor.map_map, Function.comp_def, simulateQ_bind,
    bind_map_left, List.append_assoc] using hlifted

theorem map_simulate_globalHighMonitored_adversary_full_projection
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : GlobalMonitoredCausalState)
    (attackerTrace : AttackerActionTrace) :
    (fun result : α × GlobalMonitoredTracedState =>
      ((result.1, (result.2.1.causal, result.2.2)), result.2.1.trace)) <$>
        (simulateQ (globalHighMonitoredMappedAdversaryImpl
          ((keyView, base), edgeHigh)) computation).run
            (state, attackerTrace) =
      (fun result : ((α × GlobalHighDirectTracedState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          ((simulateQ
            (globalHighDirectTracedMappedAdversaryImpl keyView edgeHigh)
            computation).run (state.causal, attackerTrace))).run := by
  apply map_simulate_globalMonitoredTraced_full_projection_of_query
  exact map_globalHighMonitored_adversary_full_query keyView base edgeHigh

theorem globalHighDirectTracedVerifierImpl_run_eq
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp OracleWorld α)
    (initialState : GlobalHighDirectTracedState) :
    (simulateQ (globalHighDirectTracedVerifierImpl keyView edgeHigh)
        computation).run initialState =
      (fun result => (result.1, (result.2, initialState.2))) <$>
        (simulateQ (globalHighDirectVerifierImpl keyView edgeHigh)
          computation).run initialState.1 := by
  induction computation using OracleComp.inductionOn generalizing
      initialState with
  | pure value => simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, StateT.run_bind, map_bind]
      simp only [id_map]
      unfold globalHighDirectTracedVerifierImpl
      rw [StateT.run_mk]
      simp only [bind_map_left]
      apply bind_congr
      intro head
      change (simulateQ
        (globalHighDirectTracedVerifierImpl keyView edgeHigh)
        (next head.1)).run (head.2, initialState.2) = _
      exact ih head.1 (head.2, initialState.2)

noncomputable def globalHighMonitoredVerifierBaseImpl
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) :
    QueryImpl OracleWorld (StateT GlobalMonitoredCausalState ProbComp) :=
  fun input => globalHighMonitoredBaseMappedAdversaryImpl right (.inl input)

theorem globalHighMonitoredVerifierImpl_run_eq
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (computation : OracleComp OracleWorld α)
    (initialState : GlobalMonitoredTracedState) :
    (simulateQ (globalHighMonitoredVerifierImpl right)
        computation).run initialState =
      (fun result => (result.1, (result.2, initialState.2))) <$>
        (simulateQ (globalHighMonitoredVerifierBaseImpl right)
          computation).run initialState.1 := by
  induction computation using OracleComp.inductionOn generalizing
      initialState with
  | pure value => simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, StateT.run_bind, map_bind]
      simp only [id_map]
      unfold globalHighMonitoredVerifierImpl
      rw [StateT.run_mk]
      simp only [bind_map_left]
      apply bind_congr
      intro head
      change (simulateQ (globalHighMonitoredVerifierImpl right)
        (next head.1)).run (head.2, initialState.2) = _
      exact ih head.1 (head.2, initialState.2)

theorem map_simulate_globalHighMonitored_verifier_full_projection
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp OracleWorld α)
    (state : GlobalMonitoredCausalState)
    (attackerTrace : AttackerActionTrace) :
    (fun result : α × GlobalMonitoredTracedState =>
      ((result.1, (result.2.1.causal, result.2.2)), result.2.1.trace)) <$>
        (simulateQ (globalHighMonitoredVerifierImpl
          ((keyView, base), edgeHigh)) computation).run
            (state, attackerTrace) =
      (fun result : ((α × GlobalHighDirectTracedState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          ((simulateQ
            (globalHighDirectTracedVerifierImpl keyView edgeHigh)
            computation).run (state.causal, attackerTrace))).run := by
  let addAttackerTrace := fun result :
      ((α × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
    ((result.1.1, (result.1.2, attackerTrace)), result.2)
  have herased := map_simulate_globalHighMonitored_verifier_erased_projection
    keyView base edgeHigh computation state attackerTrace
  have hlifted := congrArg (fun candidate => addAttackerTrace <$> candidate)
    herased
  rw [globalHighMonitoredVerifierImpl_run_eq] at hlifted
  rw [globalHighMonitoredVerifierImpl_run_eq]
  rw [globalHighDirectTracedVerifierImpl_run_eq]
  simpa [addAttackerTrace, Functor.map_map, Function.comp_def,
    simulateQ_map, bind_map_left] using hlifted

set_option maxHeartbeats 3000000 in
theorem map_globalHighMonitoredDetailedExecution_full_projection
    (adversary : Adversary Concrete.scheme)
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    (fun result : (Forgery × Bool) × GlobalMonitoredTracedState =>
      ((result.1, (result.2.1.causal, result.2.2)), result.2.1.trace)) <$>
        globalHighMonitoredDetailedExecution adversary
          ((keyView, base), edgeHigh) =
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
        ((globalHighDirectTracedDetailedExecution adversary keyView edgeHigh
          ).run (globalFilteredCausalKeygenState keyView, []))).run := by
  let initial : GlobalMonitoredTracedState :=
    (⟨globalFilteredCausalKeygenState keyView,
      some AdaptiveRevealMonitor.State.empty, []⟩, [])
  let project := fun result : Forgery × GlobalMonitoredTracedState =>
    ((result.1, (result.2.1.causal, result.2.2)), result.2.1.trace)
  let tail := fun head : ((Forgery × GlobalHighDirectTracedState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
    (fun result : ((Bool × GlobalHighDirectTracedState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
      (((head.1.1, result.1.1), result.1.2), head.2 ++ result.2)) <$>
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
        ((simulateQ (globalHighDirectTracedVerifierImpl keyView edgeHigh)
          (Concrete.scheme.verify keyView.publicKey head.1.1.epoch
            head.1.1.message head.1.1.signature)).run head.1.2)).run
  have htail (handled : Forgery × GlobalMonitoredTracedState) :
      (do
        let verified ← (simulateQ (globalHighMonitoredVerifierImpl
          ((keyView, base), edgeHigh))
          (Concrete.scheme.verify keyView.publicKey handled.1.epoch
            handled.1.message handled.1.signature)).run handled.2
        pure (((handled.1, verified.1),
          (verified.2.1.causal, verified.2.2)),
          verified.2.1.trace)) = tail (project handled) := by
    have hvertifier :=
      map_simulate_globalHighMonitored_verifier_full_projection keyView base
        edgeHigh
        (Concrete.scheme.verify keyView.publicKey handled.1.epoch
          handled.1.message handled.1.signature)
        handled.2.1 handled.2.2
    simpa [tail, project, Functor.map_map] using congrArg
      (fun candidate =>
        (fun result : ((Bool × GlobalHighDirectTracedState) ×
            RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
          (((handled.1, result.1.1), result.1.2), result.2)) <$> candidate)
      hvertifier
  unfold globalHighMonitoredDetailedExecution
    globalHighDirectTracedDetailedExecution
  simp only [map_bind, StateT.run_bind, StateT.run_pure, map_pure]
  rw [simulateQ_bind, WriterT.run_bind']
  simp_rw [htail]
  change (do
    let handled ← (simulateQ (globalHighMonitoredMappedAdversaryImpl
      ((keyView, base), edgeHigh))
        (adversary.main keyView.publicKey)).run initial
    tail (project handled)) = _
  rw [← bind_map_left project]
  have hhead := map_simulate_globalHighMonitored_adversary_full_projection
    keyView base edgeHigh (adversary.main keyView.publicKey) initial.1 initial.2
  change project <$> (simulateQ (globalHighMonitoredMappedAdversaryImpl
    ((keyView, base), edgeHigh))
      (adversary.main keyView.publicKey)).run initial = _ at hhead
  simp only [initial, List.nil_append] at hhead
  rw [hhead, bind_map_left]
  apply bind_congr
  intro head
  simp [tail, Functor.map_map]

def globalHighMonitoredFullProjection
    (result : GlobalHighMonitoredProgramResult) :
    (GlobalChainValueIndex → Digest) ×
      (GlobalHighDirectTracedResult ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :=
  (result.1.1.2,
    (((result.1.1.1, result.1.2),
      (result.2.1, (result.2.2.1.causal, result.2.2.2))),
      result.2.2.1.trace))

noncomputable def globalHighDirectTracedContinuation
    (adversary : Adversary Concrete.scheme)
    (parameter : PublicParameter)
    (base : GlobalChainValueIndex → Digest) :
    ProbComp ((GlobalChainValueIndex → Digest) ×
      (GlobalHighDirectTracedResult ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) := do
  let keyResult ← globalHighDirectKeygenAfterParameter parameter
  let execution ← (simulateQ
    (RevealProbeOracleSimulation.eagerTraceImpl base)
    ((globalHighDirectTracedDetailedExecution adversary keyResult.1 keyResult.2
      ).run (globalFilteredCausalKeygenState keyResult.1, []))).run
  pure (base, ((keyResult, execution.1), execution.2))

theorem globalHighMonitored_afterKey_full_projection
    (adversary : Adversary Concrete.scheme)
    (parameter : PublicParameter)
    (base : GlobalChainValueIndex → Digest) :
    (do
      let keyResult ← globalHighDirectKeygenAfterParameter parameter
      let execution ← globalHighMonitoredDetailedExecution adversary
        ((keyResult.1, base), keyResult.2)
      pure (globalHighMonitoredFullProjection
        (((keyResult.1, base), keyResult.2), execution))) =
      globalHighDirectTracedContinuation adversary parameter base := by
  unfold globalHighDirectTracedContinuation
  apply bind_congr
  intro keyResult
  have hdetail :=
    map_globalHighMonitoredDetailedExecution_full_projection adversary
      keyResult.1 base keyResult.2
  simpa [globalHighMonitoredFullProjection, Functor.map_map,
    map_eq_bind_pure_comp] using congrArg
      (fun candidate =>
        (fun execution : ((Forgery × Bool) × GlobalHighDirectTracedState) ×
            RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex =>
          (base, ((keyResult, execution.1), execution.2))) <$> candidate)
      hdetail

theorem globalHighMonitoredProgram_fullProjection_eq_parameterFirst
    (adversary : Adversary Concrete.scheme) :
    globalHighMonitoredFullProjection <$>
      globalHighMonitoredProgram adversary =
    (do
      let parameter ← Concrete.samplePublicParameter
      let base ← independentGlobalChainValueTable
      globalHighDirectTracedContinuation adversary parameter base) := by
  rw [globalHighMonitoredProgram_eq_directKeygen]
  simp only [map_eq_bind_pure_comp, bind_assoc]
  apply bind_congr
  intro parameter
  apply bind_congr
  intro base
  exact globalHighMonitored_afterKey_full_projection adversary parameter base

theorem globalHighDirectTracedContinuation_eq_eagerAfterBase
    (adversary : Adversary Concrete.scheme)
    (base : GlobalChainValueIndex → Digest) :
    (do
      let parameter ← Concrete.samplePublicParameter
      globalHighDirectTracedContinuation adversary parameter base) = (do
      let result ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl base)
        (globalHighDirectTracedProgram adversary)).run
      pure (base, result)) := by
  unfold globalHighDirectTracedContinuation globalHighDirectTracedProgram
    globalHighDirectKeygen
  simpa only [bind_assoc] using
    (eagerTrace_liftProbComp_then_bind base
      (do
        let parameter ← Concrete.samplePublicParameter
        globalHighDirectKeygenAfterParameter parameter)
      (fun keyResult =>
        (globalHighDirectTracedDetailedExecution adversary keyResult.1
          keyResult.2).run
          (globalFilteredCausalKeygenState keyResult.1, [])))

theorem evalDist_globalHighMonitoredFullProjection_eq_eagerExperiment
    (adversary : Adversary Concrete.scheme) :
    evalDist (globalHighMonitoredFullProjection <$>
      globalHighMonitoredProgram adversary) =
    evalDist (RevealProbeOracleSimulation.eagerExperiment
      (globalHighDirectTracedProgram adversary)) := by
  rw [globalHighMonitoredProgram_fullProjection_eq_parameterFirst]
  calc
    evalDist (do
        let parameter ← Concrete.samplePublicParameter
        let base ← independentGlobalChainValueTable
        globalHighDirectTracedContinuation adversary parameter base) =
      evalDist (do
        let base ← independentGlobalChainValueTable
        let parameter ← Concrete.samplePublicParameter
        globalHighDirectTracedContinuation adversary parameter base) := by
          exact OracleComp.DeferredSampling.evalDist_bind_comm
            Concrete.samplePublicParameter independentGlobalChainValueTable _
    _ = evalDist (do
        let base ← independentGlobalChainValueTable
        let result ← (simulateQ
          (RevealProbeOracleSimulation.eagerTraceImpl base)
          (globalHighDirectTracedProgram adversary)).run
        pure (base, result)) := by
          rw [evalDist_bind, evalDist_bind]
          apply bind_congr
          intro base
          exact congrArg evalDist
            (globalHighDirectTracedContinuation_eq_eagerAfterBase adversary
              base)
    _ = _ := by
      unfold RevealProbeOracleSimulation.eagerExperiment
      rw [evalDist_bind, evalDist_bind]
      unfold independentGlobalChainValueTable
        RevealProbeOracleSimulation.eagerTableSample
      rw [evalDist_uniformSample, evalDist_uniformSample]

theorem evalDist_globalHighMonitoredFullProjection_eq_firstLane
    (adversary : Adversary Concrete.scheme) :
    evalDist (globalHighMonitoredFullProjection <$>
      globalHighMonitoredProgram adversary) =
    evalDist ((fun result =>
      (result.1, (result.2.1, result.2.2.chainActions))) <$>
        FirstLaneOracleSimulation.eagerExperiment
          (globalFirstLaneTracedProgram adversary)) := by
  rw [evalDist_globalHighMonitoredFullProjection_eq_eagerExperiment]
  exact congrArg evalDist
    (map_globalFirstLaneTracedEagerExperiment_chainProjection adversary).symm

end XmssSecurity.CappedChain
