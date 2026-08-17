import XmssSecurity.CappedGlobalChainHighPublicHit
import XmssSecurity.CappedGlobalChainHighProbeBounds

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

noncomputable def globalHighDirectBaseMappedAdversaryImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT GlobalCausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  fun input =>
    match input with
    | .inl (.inl n) => globalCausalUniformImpl n
    | .inl (.inr hashInput) =>
        globalCausalAttackerHashQueryFromHigh
          (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey hashInput
    | .inr request => fun state =>
        globalFilteredCausalSigningQuery keyView request state

noncomputable def globalHighDirectMappedAdversaryImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    QueryImpl (OracleWorld + SigningSpec)
      (WriterT AttackerActionTrace
        (StateT GlobalCausalHashState
          (OracleComp
            (RevealProbeOracleSimulation.World GlobalChainValueIndex)))) :=
  (globalHighDirectBaseMappedAdversaryImpl keyView edgeHigh).withTraceAppend
    attackerActionFragment

noncomputable def globalHighDirectVerifierImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    QueryImpl OracleWorld
      (StateT GlobalCausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  fun input => globalHighDirectBaseMappedAdversaryImpl keyView edgeHigh (.inl input)

noncomputable def globalHighDirectDetailedExecution
    (adversary : Adversary Concrete.scheme)
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    StateT GlobalCausalHashState
      (OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex))
      (Forgery × Bool) := do
  let handled ← (simulateQ
    (globalHighDirectBaseMappedAdversaryImpl keyView edgeHigh)
      (adversary.main keyView.publicKey))
  let verified ← simulateQ (globalHighDirectVerifierImpl keyView edgeHigh)
    (Concrete.scheme.verify keyView.publicKey handled.epoch
      handled.message handled.signature)
  pure (handled, verified)

abbrev GlobalHighDirectKeyResult :=
  ProgrammedGlobalChainKeygenView × (GlobalChainEdgeIndex → Digest)

noncomputable def globalHighDirectKeygenAfterMaterial
    (parameter : PublicParameter) (material : GlobalChainTrajectoryMaterial)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    ProbComp GlobalHighDirectKeyResult := do
  let tree ← treeValues parameter material.1 allTreeValueIndices material.2.2
  let view : ProgrammedGlobalChainKeygenView :=
    (({
      secret := material.1
      table := globalChainTrajectoryMaterialTable material
      values := tree.1
      cache := tree.2
    } : CoupledGlobalChainKeygenView).toProgrammedView parameter)
  pure (view, edgeHigh)

noncomputable def globalHighDirectKeygenAfterParameter
    (parameter : PublicParameter) : ProbComp GlobalHighDirectKeyResult := do
  let material ← programmedGlobalChainTrajectoryMaterial parameter
  let edgeHigh ← independentGlobalChainHigh
  globalHighDirectKeygenAfterMaterial parameter material edgeHigh

noncomputable def globalHighDirectKeygen :
    ProbComp GlobalHighDirectKeyResult := do
  let parameter ← Concrete.samplePublicParameter
  globalHighDirectKeygenAfterParameter parameter

abbrev GlobalHighDirectResult :=
  GlobalHighDirectKeyResult ×
    ((Forgery × Bool) × GlobalCausalHashState)

noncomputable def globalHighDirectProgram
    (adversary : Adversary Concrete.scheme) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      GlobalHighDirectResult := do
  let keyResult ←
    RevealProbeOracleSimulation.liftProbComp globalHighDirectKeygen
  let execution ← (globalHighDirectDetailedExecution adversary keyResult.1
    keyResult.2).run (globalFilteredCausalKeygenState keyResult.1)
  pure (keyResult, execution)

attribute [local irreducible]
  treeValues
  programmedGlobalChainTrajectoryMaterial
  independentGlobalChainHigh
  globalChainTrajectoryMaterialTable
  CoupledGlobalChainKeygenView.toProgrammedView

theorem globalHighDirectKeygenAfterMaterial_with_base
    (parameter : PublicParameter) (material : GlobalChainTrajectoryMaterial)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (base : GlobalChainValueIndex → Digest) :
    (do
      let tree ← treeValues parameter material.1 allTreeValueIndices
        material.2.2
      let view : ProgrammedGlobalChainKeygenView :=
        (({
          secret := material.1
          table := globalChainTrajectoryMaterialTable material
          values := tree.1
          cache := tree.2
        } : CoupledGlobalChainKeygenView).toProgrammedView parameter)
      pure ((view, base), edgeHigh)) = (do
      let keyResult ←
        globalHighDirectKeygenAfterMaterial parameter material edgeHigh
      pure ((keyResult.1, base), keyResult.2)) := by
  unfold globalHighDirectKeygenAfterMaterial
  simp

theorem coupledGlobalChainKeygenWithBaseHighFull_eq_direct :
    coupledGlobalChainKeygenWithBaseHighFull = (do
      let parameter ← Concrete.samplePublicParameter
      let base ← independentGlobalChainValueTable
      let keyResult ← globalHighDirectKeygenAfterParameter parameter
      pure ((keyResult.1, base), keyResult.2)) := by
  unfold coupledGlobalChainKeygenWithBaseHighFull
    coupledGlobalChainKeygenWithBaseHigh
    programmedGlobalChainTrajectoryMaterialWithBaseHigh
    programmedGlobalChainTrajectoryMaterialWithBase
    globalHighDirectKeygenAfterParameter independentGlobalChainValueTable
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro parameter
  apply bind_congr
  intro base
  apply bind_congr
  intro material
  apply bind_congr
  intro edgeHigh
  exact globalHighDirectKeygenAfterMaterial_with_base parameter material
    edgeHigh base

theorem map_monitorGlobalCausalTrace_projection
    (table : GlobalChainValueIndex → Digest)
    (computation : GlobalCausalHashState → ProbComp
      ((α × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
    (state : GlobalMonitoredCausalState) :
    (fun result : α × GlobalMonitoredCausalState =>
      ((result.1, result.2.causal), result.2.trace)) <$>
        (monitorGlobalCausalTrace table computation).run state =
      (fun result : (α × GlobalCausalHashState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex =>
        (result.1, state.trace ++ result.2)) <$>
          computation state.causal := by
  rw [monitorGlobalCausalTrace_run, Functor.map_map]
  apply map_congr
  intro result
  simp [globalMonitoredCausalResult]

theorem map_simulate_globalMonitoredTraced_projection_of_query
    {spec : OracleSpec ι}
    (table : GlobalChainValueIndex → Digest)
    (left : QueryImpl spec (StateT GlobalMonitoredTracedState ProbComp))
    (right : QueryImpl spec
      (StateT GlobalCausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))))
    (hquery : ∀ (input : spec.Domain) (state : GlobalMonitoredCausalState)
      (attackerTrace : AttackerActionTrace),
      (fun result : spec.Range input × GlobalMonitoredTracedState =>
        ((result.1, result.2.1.causal), result.2.1.trace)) <$>
          (left input).run (state, attackerTrace) =
        (fun result : ((spec.Range input × GlobalCausalHashState) ×
            RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
          (result.1, state.trace ++ result.2)) <$>
          (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
            ((right input).run state.causal)).run)
    (computation : OracleComp spec α)
    (state : GlobalMonitoredCausalState)
    (attackerTrace : AttackerActionTrace) :
    (fun result : α × GlobalMonitoredTracedState =>
      ((result.1, result.2.1.causal), result.2.1.trace)) <$>
        (simulateQ left computation).run (state, attackerTrace) =
      (fun result : ((α × GlobalCausalHashState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          ((simulateQ right computation).run state.causal)).run := by
  induction computation using OracleComp.inductionOn generalizing state
      attackerTrace with
  | pure value => simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, StateT.run_bind, WriterT.run_bind', map_bind,
        simulateQ_spec_query]
      simp_rw [ih]
      let project := fun result : spec.Range input × GlobalMonitoredTracedState =>
        ((result.1, result.2.1.causal), result.2.1.trace)
      let tail := fun head : ((spec.Range input × GlobalCausalHashState) ×
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

theorem map_actionTracedStateImpl_globalMonitor_erased_step
    {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT GlobalMonitoredCausalState ProbComp))
    (fragment : (input : spec.Domain) → spec.Range input →
      AttackerActionTrace)
    (input : spec.Domain) (state : GlobalMonitoredCausalState)
    (attackerTrace : AttackerActionTrace) :
    (fun result : spec.Range input × GlobalMonitoredTracedState =>
      (result.1, result.2.1)) <$>
        (actionTracedStateImpl impl fragment input).run
          (state, attackerTrace) =
      (impl input).run state := by
  unfold actionTracedStateImpl
  simp [StateT.run_mk, map_eq_bind_pure_comp, bind_assoc]

theorem map_globalHighMonitored_uniform_erased_projection
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (n : Nat)
    (state : GlobalMonitoredCausalState)
    (attackerTrace : AttackerActionTrace) :
    (fun result : (OracleWorld + SigningSpec).Range (.inl (.inl n)) ×
        GlobalMonitoredTracedState =>
      ((result.1, result.2.1.causal), result.2.1.trace)) <$>
        (globalHighMonitoredMappedAdversaryImpl
          ((keyView, base), edgeHigh) (.inl (.inl n))).run
            (state, attackerTrace) =
      (fun result : (((OracleWorld + SigningSpec).Range (.inl (.inl n)) ×
          GlobalCausalHashState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          ((globalCausalUniformImpl n).run state.causal)).run := by
  calc
    _ = (fun result : (OracleWorld + SigningSpec).Range (.inl (.inl n)) ×
          GlobalMonitoredCausalState =>
          ((result.1, result.2.causal), result.2.trace)) <$>
        (globalHighMonitoredBaseMappedAdversaryImpl
          ((keyView, base), edgeHigh) (.inl (.inl n))).run state := by
      have herase := map_actionTracedStateImpl_globalMonitor_erased_step
        (globalHighMonitoredBaseMappedAdversaryImpl
          ((keyView, base), edgeHigh)) attackerActionFragment
        (.inl (.inl n)) state attackerTrace
      simpa [globalHighMonitoredMappedAdversaryImpl, Functor.map_map,
        Function.comp_def] using congrArg
          (fun candidate =>
            (fun result : (OracleWorld + SigningSpec).Range (.inl (.inl n)) ×
                GlobalMonitoredCausalState =>
              ((result.1, result.2.causal), result.2.trace)) <$> candidate)
          herase
    _ = _ := by
      unfold globalHighMonitoredBaseMappedAdversaryImpl
      exact map_monitorGlobalCausalTrace_projection base _ state

theorem map_globalHighMonitored_hash_erased_projection
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (input : HashInput)
    (state : GlobalMonitoredCausalState)
    (attackerTrace : AttackerActionTrace) :
    (fun result : (OracleWorld + SigningSpec).Range (.inl (.inr input)) ×
        GlobalMonitoredTracedState =>
      ((result.1, result.2.1.causal), result.2.1.trace)) <$>
        (globalHighMonitoredMappedAdversaryImpl
          ((keyView, base), edgeHigh) (.inl (.inr input))).run
            (state, attackerTrace) =
      (fun result : (((OracleWorld + SigningSpec).Range (.inl (.inr input)) ×
          GlobalCausalHashState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          ((globalCausalAttackerHashQueryFromHigh
            (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey input
              ).run state.causal)).run := by
  calc
    _ = (fun result : (OracleWorld + SigningSpec).Range (.inl (.inr input)) ×
          GlobalMonitoredCausalState =>
          ((result.1, result.2.causal), result.2.trace)) <$>
        (globalHighMonitoredBaseMappedAdversaryImpl
          ((keyView, base), edgeHigh) (.inl (.inr input))).run state := by
      have herase := map_actionTracedStateImpl_globalMonitor_erased_step
        (globalHighMonitoredBaseMappedAdversaryImpl
          ((keyView, base), edgeHigh)) attackerActionFragment
        (.inl (.inr input)) state attackerTrace
      simpa [globalHighMonitoredMappedAdversaryImpl, Functor.map_map,
        Function.comp_def] using congrArg
          (fun candidate =>
            (fun result : (OracleWorld + SigningSpec).Range
                (.inl (.inr input)) × GlobalMonitoredCausalState =>
              ((result.1, result.2.causal), result.2.trace)) <$> candidate)
          herase
    _ = _ := by
      unfold globalHighMonitoredBaseMappedAdversaryImpl
      exact map_monitorGlobalCausalTrace_projection base _ state

theorem map_globalHighMonitored_sign_erased_projection
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (request : SignRequest)
    (state : GlobalMonitoredCausalState)
    (attackerTrace : AttackerActionTrace) :
    (fun result : (OracleWorld + SigningSpec).Range (.inr request) ×
        GlobalMonitoredTracedState =>
      ((result.1, result.2.1.causal), result.2.1.trace)) <$>
        (globalHighMonitoredMappedAdversaryImpl
          ((keyView, base), edgeHigh) (.inr request)).run
            (state, attackerTrace) =
      (fun result : (((OracleWorld + SigningSpec).Range (.inr request) ×
          GlobalCausalHashState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          (globalFilteredCausalSigningQuery keyView request state.causal)).run := by
  calc
    _ = (fun result : (OracleWorld + SigningSpec).Range (.inr request) ×
          GlobalMonitoredCausalState =>
          ((result.1, result.2.causal), result.2.trace)) <$>
        (globalHighMonitoredBaseMappedAdversaryImpl
          ((keyView, base), edgeHigh) (.inr request)).run state := by
      have herase := map_actionTracedStateImpl_globalMonitor_erased_step
        (globalHighMonitoredBaseMappedAdversaryImpl
          ((keyView, base), edgeHigh)) attackerActionFragment
        (.inr request) state attackerTrace
      simpa [globalHighMonitoredMappedAdversaryImpl, Functor.map_map,
        Function.comp_def] using congrArg
          (fun candidate =>
            (fun result : (OracleWorld + SigningSpec).Range (.inr request) ×
                GlobalMonitoredCausalState =>
              ((result.1, result.2.causal), result.2.trace)) <$> candidate)
          herase
    _ = _ := by
      unfold globalHighMonitoredBaseMappedAdversaryImpl
      exact map_monitorGlobalCausalTrace_projection base _ state

theorem map_simulate_globalHighMonitored_adversary_erased_projection
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : GlobalMonitoredCausalState)
    (attackerTrace : AttackerActionTrace) :
    (fun result : α × GlobalMonitoredTracedState =>
      ((result.1, result.2.1.causal), result.2.1.trace)) <$>
        (simulateQ (globalHighMonitoredMappedAdversaryImpl
          ((keyView, base), edgeHigh)) computation).run
            (state, attackerTrace) =
      (fun result : ((α × GlobalCausalHashState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          ((simulateQ (globalHighDirectBaseMappedAdversaryImpl keyView edgeHigh)
            computation).run state.causal)).run := by
  apply map_simulate_globalMonitoredTraced_projection_of_query
  intro input current trace
  rcases input with (uniformOrHash | request)
  · rcases uniformOrHash with n | hashInput
    · exact map_globalHighMonitored_uniform_erased_projection keyView base
        edgeHigh n current trace
    · exact map_globalHighMonitored_hash_erased_projection keyView base
        edgeHigh hashInput current trace
  · exact map_globalHighMonitored_sign_erased_projection keyView base
      edgeHigh request current trace

theorem map_simulate_globalHighMonitored_verifier_erased_projection
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp OracleWorld α)
    (state : GlobalMonitoredCausalState)
    (attackerTrace : AttackerActionTrace) :
    (fun result : α × GlobalMonitoredTracedState =>
      ((result.1, result.2.1.causal), result.2.1.trace)) <$>
        (simulateQ (globalHighMonitoredVerifierImpl
          ((keyView, base), edgeHigh)) computation).run
            (state, attackerTrace) =
      (fun result : ((α × GlobalCausalHashState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          ((simulateQ (globalHighDirectVerifierImpl keyView edgeHigh)
            computation).run state.causal)).run := by
  apply map_simulate_globalMonitoredTraced_projection_of_query
  intro input current trace
  unfold globalHighMonitoredVerifierImpl globalHighDirectVerifierImpl
  simp only [StateT.run_mk, Functor.map_map]
  unfold globalHighMonitoredBaseMappedAdversaryImpl
    globalHighDirectBaseMappedAdversaryImpl
  rcases input with n | hashInput
  · exact map_monitorGlobalCausalTrace_projection base _ current
  · exact map_monitorGlobalCausalTrace_projection base _ current

set_option maxHeartbeats 3000000 in
theorem map_globalHighMonitoredDetailedExecution_erased_projection
    (adversary : Adversary Concrete.scheme)
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    (fun result : (Forgery × Bool) × GlobalMonitoredTracedState =>
      ((result.1, result.2.1.causal), result.2.1.trace)) <$>
        globalHighMonitoredDetailedExecution adversary
          ((keyView, base), edgeHigh) =
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
        ((globalHighDirectDetailedExecution adversary keyView edgeHigh).run
          (globalFilteredCausalKeygenState keyView))).run := by
  let initial : GlobalMonitoredTracedState :=
    (⟨globalFilteredCausalKeygenState keyView,
      some AdaptiveRevealMonitor.State.empty, []⟩, [])
  let project := fun result : Forgery × GlobalMonitoredTracedState =>
    ((result.1, result.2.1.causal), result.2.1.trace)
  let tail := fun head : ((Forgery × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
    (fun result : ((Bool × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
      (((head.1.1, result.1.1), result.1.2), head.2 ++ result.2)) <$>
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
        ((simulateQ (globalHighDirectVerifierImpl keyView edgeHigh)
          (Concrete.scheme.verify keyView.publicKey head.1.1.epoch
            head.1.1.message head.1.1.signature)).run head.1.2)).run
  have htail (handled : Forgery × GlobalMonitoredTracedState) :
      (do
        let verified ← (simulateQ (globalHighMonitoredVerifierImpl
          ((keyView, base), edgeHigh))
          (Concrete.scheme.verify keyView.publicKey handled.1.epoch
            handled.1.message handled.1.signature)).run handled.2
        pure (((handled.1, verified.1), verified.2.1.causal),
          verified.2.1.trace)) = tail (project handled) := by
    have hvertifier :=
      map_simulate_globalHighMonitored_verifier_erased_projection keyView base
        edgeHigh
        (Concrete.scheme.verify keyView.publicKey handled.1.epoch
          handled.1.message handled.1.signature)
        handled.2.1 handled.2.2
    simpa [tail, project, Functor.map_map] using congrArg
      (fun candidate =>
        (fun result : ((Bool × GlobalCausalHashState) ×
            RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
          (((handled.1, result.1.1), result.1.2), result.2)) <$> candidate)
      hvertifier
  unfold globalHighMonitoredDetailedExecution
    globalHighDirectDetailedExecution
  simp only [map_bind, StateT.run_bind, map_pure]
  rw [simulateQ_bind, WriterT.run_bind']
  simp_rw [htail]
  change (do
    let handled ← (simulateQ (globalHighMonitoredMappedAdversaryImpl
      ((keyView, base), edgeHigh))
        (adversary.main keyView.publicKey)).run initial
    tail (project handled)) = _
  rw [← bind_map_left project]
  have hhead := map_simulate_globalHighMonitored_adversary_erased_projection
    keyView base edgeHigh (adversary.main keyView.publicKey) initial.1 initial.2
  change project <$> (simulateQ (globalHighMonitoredMappedAdversaryImpl
    ((keyView, base), edgeHigh))
      (adversary.main keyView.publicKey)).run initial = _ at hhead
  simp only [initial, List.nil_append] at hhead
  rw [hhead, bind_map_left]
  apply bind_congr
  intro head
  simp [tail, Functor.map_map]

def globalHighMonitoredDirectProjection
    (result : GlobalHighMonitoredProgramResult) :
    (GlobalChainValueIndex → Digest) ×
      (GlobalHighDirectResult ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :=
  (result.1.1.2,
    (((result.1.1.1, result.1.2),
      (result.2.1, result.2.2.1.causal)), result.2.2.1.trace))

noncomputable def globalHighMonitoredContinuation
    (adversary : Adversary Concrete.scheme)
    (parameter : PublicParameter)
    (base : GlobalChainValueIndex → Digest) :
    ProbComp GlobalHighMonitoredProgramResult := do
  let keyResult ← globalHighDirectKeygenAfterParameter parameter
  let execution ← globalHighMonitoredDetailedExecution adversary
    ((keyResult.1, base), keyResult.2)
  pure (((keyResult.1, base), keyResult.2), execution)

noncomputable def globalHighDirectContinuation
    (adversary : Adversary Concrete.scheme)
    (parameter : PublicParameter)
    (base : GlobalChainValueIndex → Digest) :
    ProbComp ((GlobalChainValueIndex → Digest) ×
      (GlobalHighDirectResult ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) := do
  let keyResult ← globalHighDirectKeygenAfterParameter parameter
  let execution ← (simulateQ
    (RevealProbeOracleSimulation.eagerTraceImpl base)
    ((globalHighDirectDetailedExecution adversary keyResult.1 keyResult.2).run
      (globalFilteredCausalKeygenState keyResult.1))).run
  pure (base, ((keyResult, execution.1), execution.2))

attribute [local irreducible]
  globalHighMonitoredContinuation
  globalHighDirectContinuation

theorem globalHighMonitored_afterKey_projection
    (adversary : Adversary Concrete.scheme)
    (parameter : PublicParameter)
    (base : GlobalChainValueIndex → Digest) :
    (do
      let keyResult ← globalHighDirectKeygenAfterParameter parameter
      let execution ← globalHighMonitoredDetailedExecution adversary
        ((keyResult.1, base), keyResult.2)
      pure (globalHighMonitoredDirectProjection
        (((keyResult.1, base), keyResult.2), execution))) = (do
      let keyResult ← globalHighDirectKeygenAfterParameter parameter
      let execution ← (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl base)
        ((globalHighDirectDetailedExecution adversary keyResult.1 keyResult.2
          ).run (globalFilteredCausalKeygenState keyResult.1))).run
      pure (base, ((keyResult, execution.1), execution.2))) := by
  apply bind_congr
  intro keyResult
  have hdetail :=
    map_globalHighMonitoredDetailedExecution_erased_projection adversary
      keyResult.1 base keyResult.2
  simpa [globalHighMonitoredDirectProjection, Functor.map_map,
    map_eq_bind_pure_comp] using congrArg
      (fun candidate =>
        (fun execution : ((Forgery × Bool) × GlobalCausalHashState) ×
            RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex =>
          (base, ((keyResult, execution.1), execution.2))) <$> candidate)
      hdetail

attribute [local irreducible]
  globalHighDirectDetailedExecution
  globalHighDirectBaseMappedAdversaryImpl
  globalHighDirectVerifierImpl
  globalFilteredCausalSigningQuery
  globalHighMonitoredDetailedExecution
  globalHighDirectProgram
  globalHighMonitoredProgram

theorem globalHighMonitoredProgram_eq_directKeygen
    (adversary : Adversary Concrete.scheme) :
    globalHighMonitoredProgram adversary = (do
      let parameter ← Concrete.samplePublicParameter
      let base ← independentGlobalChainValueTable
      let keyResult ← globalHighDirectKeygenAfterParameter parameter
      let execution ← globalHighMonitoredDetailedExecution adversary
        ((keyResult.1, base), keyResult.2)
      pure (((keyResult.1, base), keyResult.2), execution)) := by
  rw [globalHighMonitoredProgram]
  rw [coupledGlobalChainKeygenWithBaseHighFull_eq_direct]
  simp only [bind_assoc, pure_bind]

end XmssSecurity.CappedChain
