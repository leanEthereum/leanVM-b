import XmssSecurity.Proof.CappedGlobalChainHighPublicHit
import XmssSecurity.Proof.CappedGlobalChainHighProbeBounds

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

noncomputable def globalHighDirectUniformImpl :
    QueryImpl unifSpec
      (StateT GlobalCausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  globalCausalUniformImpl

noncomputable abbrev globalHighDirectHashFromHighImpl
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) :
    QueryImpl HashSpec
      (StateT GlobalCausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  globalCausalAttackerHashQueryFromHigh high secretKey

noncomputable abbrev globalHighDirectHashImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    QueryImpl HashSpec
      (StateT GlobalCausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  globalHighDirectHashFromHighImpl
    (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey

noncomputable def globalHighDirectOracleExecution
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : OracleWorld.Domain) (state : GlobalCausalHashState) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (OracleWorld.Range input × GlobalCausalHashState) :=
  match input with
  | .inl n => (globalHighDirectUniformImpl n).run state
  | .inr hashInput =>
      (globalCausalAttackerHashQueryFromHigh
        (globalChainValueHighTableOfEdges edgeHigh) keyView.secretKey
          hashInput).run state

noncomputable def globalHighDirectOracleImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    QueryImpl OracleWorld
      (StateT GlobalCausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  fun input state => globalHighDirectOracleExecution keyView edgeHigh input state

noncomputable def globalHighDirectSigningImpl
    (keyView : ProgrammedGlobalChainKeygenView) :
    QueryImpl SigningSpec
      (StateT GlobalCausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  fun request state => globalFilteredCausalSigningQuery keyView request state

noncomputable def globalHighDirectBaseMappedAdversaryImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT GlobalCausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  globalHighDirectOracleImpl keyView edgeHigh +
    globalHighDirectSigningImpl keyView

noncomputable def globalHighDirectVerifierImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    QueryImpl OracleWorld
      (StateT GlobalCausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  globalHighDirectOracleImpl keyView edgeHigh

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
    (computation : GlobalCausalHashState → ProbComp
      ((α × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
    (state : GlobalMonitoredCausalState) :
    (fun result : α × GlobalMonitoredCausalState =>
      ((result.1, result.2.causal), result.2.trace)) <$>
        (monitorGlobalCausalTrace computation).run state =
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
      exact map_monitorGlobalCausalTrace_projection _ state

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
      exact map_monitorGlobalCausalTrace_projection _ state

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
      exact map_monitorGlobalCausalTrace_projection _ state

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
    globalHighDirectOracleImpl globalHighDirectOracleExecution
  rcases input with n | hashInput
  · exact map_monitorGlobalCausalTrace_projection _ current
  · exact map_monitorGlobalCausalTrace_projection _ current

def globalHighMonitoredDirectProjection
    (result : GlobalHighMonitoredProgramResult) :
    (GlobalChainValueIndex → Digest) ×
      (GlobalHighDirectResult ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :=
  (result.1.1.2,
    (((result.1.1.1, result.1.2),
      (result.2.1, result.2.2.1.causal)), result.2.2.1.trace))

end XmssSecurity.CappedChain
