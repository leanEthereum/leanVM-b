import XmssSecurity.CappedChain.CausalEagerHighReduction

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000

theorem map_simulate_actionTracedStateImpl_fst
    {ι : Type} {spec : OracleSpec ι} {σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (fragment : (input : spec.Domain) → spec.Range input →
      AttackerActionTrace)
    (computation : OracleComp spec α) (state : σ)
    (trace : AttackerActionTrace) :
    (fun result : α × (σ × AttackerActionTrace) =>
      (result.1, result.2.1)) <$>
        (simulateQ (actionTracedStateImpl impl fragment) computation).run
          (state, trace) =
      (simulateQ impl computation).run state := by
  induction computation using OracleComp.inductionOn generalizing state trace with
  | pure value => simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, StateT.run_bind, map_bind,
        simulateQ_spec_query]
      unfold actionTracedStateImpl
      simp only [StateT.run_mk, bind_assoc, pure_bind]
      apply bind_congr
      intro head
      exact ih head.1 head.2 (trace ++ fragment input head.1)

theorem map_simulate_monitoredTraced_projection_of_query
    {ι : Type} {spec : OracleSpec ι}
    (table : ChainValueIndex → Digest)
    (left : QueryImpl spec (StateT MonitoredTracedState ProbComp))
    (right : QueryImpl spec
      (StateT CausalHashState
        (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex))))
    (hquery : ∀ (input : spec.Domain) (state : MonitoredCausalState)
      (attackerTrace : AttackerActionTrace),
      (fun result : spec.Range input × MonitoredTracedState =>
        ((result.1, result.2.1.causal), result.2.1.trace)) <$>
          (left input).run (state, attackerTrace) =
        (fun result : ((spec.Range input × CausalHashState) ×
            RevealProbeOracleSimulation.ActionTrace ChainValueIndex) =>
          (result.1, state.trace ++ result.2)) <$>
          (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
            ((right input).run state.causal)).run)
    (computation : OracleComp spec α)
    (state : MonitoredCausalState) (attackerTrace : AttackerActionTrace) :
    (fun result : α × MonitoredTracedState =>
      ((result.1, result.2.1.causal), result.2.1.trace)) <$>
        (simulateQ left computation).run (state, attackerTrace) =
      (fun result : ((α × CausalHashState) ×
          RevealProbeOracleSimulation.ActionTrace ChainValueIndex) =>
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
      let project := fun result : spec.Range input × MonitoredTracedState =>
        ((result.1, result.2.1.causal), result.2.1.trace)
      let tail := fun head : ((spec.Range input × CausalHashState) ×
          RevealProbeOracleSimulation.ActionTrace ChainValueIndex) =>
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

theorem map_prefix_of_monitored_projection
    (headValue : β)
    (left : ProbComp (γ × MonitoredTracedState))
    (right : ProbComp ((γ × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hprojection :
      (fun result : γ × MonitoredTracedState =>
        ((result.1, result.2.1.causal), result.2.1.trace)) <$> left = right) :
    (do
      let result ← left
      pure (((headValue, result.1), result.2.1.causal), result.2.1.trace)) =
      (fun result : ((γ × CausalHashState) ×
          RevealProbeOracleSimulation.ActionTrace ChainValueIndex) =>
        (((headValue, result.1.1), result.1.2), result.2)) <$> right := by
  calc
    _ = (fun result : ((γ × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) =>
      (((headValue, result.1.1), result.1.2), result.2)) <$>
      ((fun result : γ × MonitoredTracedState =>
        ((result.1, result.2.1.causal), result.2.1.trace)) <$> left) := by
      rw [Functor.map_map]
      rfl
    _ = _ := congrArg
      (fun candidate =>
        (fun result : ((γ × CausalHashState) ×
            RevealProbeOracleSimulation.ActionTrace ChainValueIndex) =>
          (((headValue, result.1.1), result.1.2), result.2)) <$> candidate)
      hprojection

theorem map_simulate_filteredHighMonitoredBase_projection
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : MonitoredCausalState) :
    (fun result : α × MonitoredCausalState =>
      ((result.1, result.2.causal), result.2.trace)) <$>
        (simulateQ
          (filteredHighMonitoredBaseMappedAdversaryImpl keyHigh selected table)
            computation).run state =
    (fun result : ((α × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) =>
      (result.1, state.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          ((simulateQ (filteredHighMappedAdversaryImpl keyHigh selected)
            computation).run state.causal)).run := by
  unfold filteredHighMonitoredBaseMappedAdversaryImpl
    filteredHighMappedAdversaryImpl
  change (fun result : α × MonitoredCausalState =>
      ((result.1, result.2.causal), result.2.trace)) <$>
        (simulateQ
          (monitoredEagerRunImpl table
            (filteredHighMappedAdversaryRun keyHigh selected))
              computation).run state = _
  exact map_simulate_monitoredEagerRunImpl_projection table
    (filteredHighMappedAdversaryRun keyHigh selected) computation state

theorem map_simulate_filteredHighMonitoredMapped_projection
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : MonitoredCausalState) (attackerTrace : AttackerActionTrace) :
    (fun result : α × MonitoredTracedState =>
      ((result.1, result.2.1.causal), result.2.1.trace)) <$>
        (simulateQ
          (filteredHighMonitoredMappedAdversaryImpl keyHigh selected table)
            computation).run (state, attackerTrace) =
      (fun result : ((α × CausalHashState) ×
          RevealProbeOracleSimulation.ActionTrace ChainValueIndex) =>
        (result.1, state.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          ((simulateQ (filteredHighMappedAdversaryImpl keyHigh selected)
            computation).run state.causal)).run := by
  calc
    _ = (fun result : α × MonitoredCausalState =>
        ((result.1, result.2.causal), result.2.trace)) <$>
          (simulateQ
            (filteredHighMonitoredBaseMappedAdversaryImpl keyHigh selected table)
              computation).run state := by
      have herase := map_simulate_actionTracedStateImpl_fst
        (filteredHighMonitoredBaseMappedAdversaryImpl keyHigh selected table)
        attackerActionFragment computation state attackerTrace
      simpa [filteredHighMonitoredMappedAdversaryImpl, Functor.map_map,
        Function.comp_def] using congrArg
          (fun candidate =>
            (fun result : α × MonitoredCausalState =>
              ((result.1, result.2.causal), result.2.trace)) <$> candidate)
          herase
    _ = _ := map_simulate_filteredHighMonitoredBase_projection keyHigh selected
      table computation state

theorem filteredHighMonitoredVerifierImpl_hash_apply
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest)
    (hashInput : HashInput) :
    filteredHighMonitoredVerifierImpl keyHigh selected table (.inr hashInput) =
      filteredHighMonitoredHashVerifierImpl keyHigh selected table hashInput := by
  rfl

theorem filteredHighVerifierImpl_hash_apply
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (hashInput : HashInput) :
    filteredHighVerifierImpl keyHigh selected (.inr hashInput) =
      StateT.mk (filteredHighVerifierRun keyHigh selected (.inr hashInput)) := by
  rfl

theorem map_filteredHighMonitoredVerifierImpl_hash_projection
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest)
    (hashInput : HashInput) (state : MonitoredCausalState)
    (attackerTrace : AttackerActionTrace) :
    (fun result : HashOutput × MonitoredTracedState =>
      ((result.1, result.2.1.causal), result.2.1.trace)) <$>
        (filteredHighMonitoredHashVerifierImpl keyHigh selected table
          hashInput).run (state, attackerTrace) =
      (fun result : ((HashOutput × CausalHashState) ×
          RevealProbeOracleSimulation.ActionTrace ChainValueIndex) =>
        (result.1, state.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          (filteredHighVerifierRun keyHigh selected (.inr hashInput)
            state.causal)).run := by
  rw [filteredHighMonitoredHashVerifierImpl_run,
    filteredHighMonitoredHashVerifierRun_eq]
  unfold filteredHighVerifierRun monitoredTreeHashQuery
  simp only [Functor.map_map]
  exact map_monitorCausalTrace_projection table
    (fun causalState =>
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredTreeHashComputationAtFromHigh
          (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected
            hashInput causalState)).run) state

noncomputable def filteredHighMonitoredHashOnlyVerifierImpl
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest) :
    QueryImpl HashSpec (StateT MonitoredTracedState ProbComp) :=
  fun hashInput => filteredHighMonitoredHashVerifierImpl keyHigh selected table
    hashInput

noncomputable def filteredHighHashOnlyVerifierImpl
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) :
    QueryImpl HashSpec
      (StateT CausalHashState
        (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex))) :=
  fun hashInput => StateT.mk
    (filteredHighVerifierRun keyHigh selected (.inr hashInput))

theorem map_simulate_filteredHighMonitoredHashOnlyVerifier_projection
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest)
    (computation : OracleComp HashSpec α)
    (state : MonitoredCausalState) (attackerTrace : AttackerActionTrace) :
    (fun result : α × MonitoredTracedState =>
      ((result.1, result.2.1.causal), result.2.1.trace)) <$>
        (simulateQ
          (filteredHighMonitoredHashOnlyVerifierImpl keyHigh selected table)
            computation).run (state, attackerTrace) =
      (fun result : ((α × CausalHashState) ×
          RevealProbeOracleSimulation.ActionTrace ChainValueIndex) =>
        (result.1, state.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          ((simulateQ (filteredHighHashOnlyVerifierImpl keyHigh selected)
            computation).run state.causal)).run := by
  apply map_simulate_monitoredTraced_projection_of_query table
    (filteredHighMonitoredHashOnlyVerifierImpl keyHigh selected table)
    (filteredHighHashOnlyVerifierImpl keyHigh selected)
  intro hashInput queryState queryAttackerTrace
  unfold filteredHighMonitoredHashOnlyVerifierImpl
    filteredHighHashOnlyVerifierImpl
  rw [StateT.run_mk]
  exact map_filteredHighMonitoredVerifierImpl_hash_projection keyHigh selected
    table hashInput queryState queryAttackerTrace

theorem simulate_filteredHighMonitoredVerifier_liftM_eq_hashOnly
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest)
    (computation : OracleComp HashSpec α) :
    simulateQ (filteredHighMonitoredVerifierImpl keyHigh selected table)
        (liftM computation : OracleComp OracleWorld α) =
      simulateQ
        (filteredHighMonitoredHashOnlyVerifierImpl keyHigh selected table)
        computation := by
  rw [← OracleComp.liftComp_eq_liftM]
  apply QueryImpl.simulateQ_liftComp_right_eq_of_apply
  intro hashInput
  exact filteredHighMonitoredVerifierImpl_hash_apply keyHigh selected table
    hashInput

theorem simulate_filteredHighVerifier_liftM_eq_hashOnly
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (computation : OracleComp HashSpec α) :
    simulateQ (filteredHighVerifierImpl keyHigh selected)
        (liftM computation : OracleComp OracleWorld α) =
      simulateQ (filteredHighHashOnlyVerifierImpl keyHigh selected)
        computation := by
  rw [← OracleComp.liftComp_eq_liftM]
  apply QueryImpl.simulateQ_liftComp_right_eq_of_apply
  intro hashInput
  unfold filteredHighHashOnlyVerifierImpl
  exact filteredHighVerifierImpl_hash_apply keyHigh selected hashInput

theorem map_simulate_filteredHighMonitoredVerifier_liftM_projection
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest)
    (computation : OracleComp HashSpec α)
    (state : MonitoredCausalState) (attackerTrace : AttackerActionTrace) :
    (fun result : α × MonitoredTracedState =>
      ((result.1, result.2.1.causal), result.2.1.trace)) <$>
        (simulateQ
          (filteredHighMonitoredVerifierImpl keyHigh selected table)
          (liftM computation : OracleComp OracleWorld α)).run
            (state, attackerTrace) =
      (fun result : ((α × CausalHashState) ×
          RevealProbeOracleSimulation.ActionTrace ChainValueIndex) =>
        (result.1, state.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          ((simulateQ (filteredHighVerifierImpl keyHigh selected)
            (liftM computation : OracleComp OracleWorld α)).run
              state.causal)).run := by
  rw [simulate_filteredHighMonitoredVerifier_liftM_eq_hashOnly,
    simulate_filteredHighVerifier_liftM_eq_hashOnly]
  exact map_simulate_filteredHighMonitoredHashOnlyVerifier_projection keyHigh
    selected table computation state attackerTrace

theorem map_simulate_filteredHighMonitoredVerifier_verify_projection
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest)
    (publicKey : PublicKey) (forgery : Forgery)
    (state : MonitoredCausalState) (attackerTrace : AttackerActionTrace) :
    (fun result : Bool × MonitoredTracedState =>
      ((result.1, result.2.1.causal), result.2.1.trace)) <$>
        (simulateQ
          (filteredHighMonitoredVerifierImpl keyHigh selected table)
          (Concrete.scheme.verify publicKey forgery.epoch forgery.message
            forgery.signature)).run (state, attackerTrace) =
      (fun result : ((Bool × CausalHashState) ×
          RevealProbeOracleSimulation.ActionTrace ChainValueIndex) =>
        (result.1, state.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          ((simulateQ (filteredHighVerifierImpl keyHigh selected)
            (Concrete.scheme.verify publicKey forgery.epoch forgery.message
              forgery.signature)).run state.causal)).run := by
  unfold Concrete.scheme
  exact map_simulate_filteredHighMonitoredVerifier_liftM_projection keyHigh
    selected table
    (Concrete.verify publicKey forgery.epoch forgery.message forgery.signature)
    state attackerTrace

noncomputable def filteredHighUntracedDetailedExecution
    (adversary : Adversary Concrete.scheme)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) :
    StateT CausalHashState
      (OracleComp (RevealProbeOracleSimulation.World ChainValueIndex))
      (Forgery × Bool) := do
  let handled ← simulateQ (filteredHighMappedAdversaryImpl keyHigh selected)
    (adversary.main keyHigh.1.publicKey)
  (fun verified => (handled, verified)) <$>
    simulateQ (filteredHighVerifierImpl keyHigh selected)
      (Concrete.scheme.verify keyHigh.1.publicKey handled.epoch handled.message
        handled.signature)

set_option maxHeartbeats 1000000 in
theorem map_filteredHighMonitoredDetailedExecution_projection
    (adversary : Adversary Concrete.scheme)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest) :
    (fun result : (Forgery × Bool) × MonitoredTracedState =>
      ((result.1, result.2.1.causal), result.2.1.trace)) <$>
        filteredHighMonitoredDetailedExecution adversary keyHigh selected table =
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((filteredHighUntracedDetailedExecution adversary keyHigh selected).run
          (filteredCausalKeygenState selected keyHigh.1))).run := by
  unfold filteredHighMonitoredDetailedExecution
    filteredHighUntracedDetailedExecution
  simp only [map_bind, StateT.run_bind, StateT.run_map, map_pure]
  rw [simulateQ_bind, WriterT.run_bind']
  have heagerTail (handled : Forgery × CausalHashState) :
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((fun result : Bool × CausalHashState =>
          ((handled.1, result.1), result.2)) <$>
          (simulateQ (filteredHighVerifierImpl keyHigh selected)
            (Concrete.scheme.verify keyHigh.1.publicKey handled.1.epoch
              handled.1.message handled.1.signature)).run handled.2)).run =
        (fun result : ((Bool × CausalHashState) ×
            RevealProbeOracleSimulation.ActionTrace ChainValueIndex) =>
          (((handled.1, result.1.1), result.1.2), result.2)) <$>
          (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
            ((simulateQ (filteredHighVerifierImpl keyHigh selected)
              (Concrete.scheme.verify keyHigh.1.publicKey handled.1.epoch
                handled.1.message handled.1.signature)).run handled.2)).run := by
    rw [simulateQ_map, WriterT.run_map']
    rfl
  have htail (handled : Forgery × MonitoredTracedState) :
      (do
        let verified ← (simulateQ
          (filteredHighMonitoredVerifierImpl keyHigh selected table)
          (Concrete.scheme.verify keyHigh.1.publicKey handled.1.epoch
            handled.1.message handled.1.signature)).run handled.2
        pure (((handled.1, verified.1), verified.2.1.causal),
          verified.2.1.trace)) =
        (fun result : ((Bool × CausalHashState) ×
            RevealProbeOracleSimulation.ActionTrace ChainValueIndex) =>
          (((handled.1, result.1.1), result.1.2), result.2)) <$>
          ((fun result : ((Bool × CausalHashState) ×
              RevealProbeOracleSimulation.ActionTrace ChainValueIndex) =>
            (result.1, handled.2.1.trace ++ result.2)) <$>
            (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
              ((simulateQ (filteredHighVerifierImpl keyHigh selected)
                (Concrete.scheme.verify keyHigh.1.publicKey handled.1.epoch
                  handled.1.message handled.1.signature)).run
                    handled.2.1.causal)).run) := by
    have hverifier :=
      map_simulate_filteredHighMonitoredVerifier_verify_projection keyHigh
        selected table keyHigh.1.publicKey handled.1 handled.2.1 handled.2.2
    exact map_prefix_of_monitored_projection handled.1 _ _ hverifier
  simp_rw [htail]
  simp_rw [heagerTail]
  let initial : MonitoredCausalState :=
    ⟨filteredCausalKeygenState selected keyHigh.1,
      some AdaptiveRevealMonitor.State.empty, []⟩
  let project := fun result : Forgery × MonitoredTracedState =>
    ((result.1, result.2.1.causal), result.2.1.trace)
  let tail := fun head : ((Forgery × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) =>
    (fun result : ((Bool × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) =>
      (((head.1.1, result.1.1), result.1.2), result.2)) <$>
      ((fun result : ((Bool × CausalHashState) ×
          RevealProbeOracleSimulation.ActionTrace ChainValueIndex) =>
        (result.1, head.2 ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          ((simulateQ (filteredHighVerifierImpl keyHigh selected)
            (Concrete.scheme.verify keyHigh.1.publicKey head.1.1.epoch
              head.1.1.message head.1.1.signature)).run head.1.2)).run)
  change (do
    let head ← (simulateQ
      (filteredHighMonitoredMappedAdversaryImpl keyHigh selected table)
      (adversary.main keyHigh.1.publicKey)).run (initial, [])
    tail (project head)) = _
  rw [← bind_map_left project]
  have hhead := map_simulate_filteredHighMonitoredMapped_projection keyHigh
    selected table (adversary.main keyHigh.1.publicKey) initial []
  change project <$> (simulateQ
      (filteredHighMonitoredMappedAdversaryImpl keyHigh selected table)
      (adversary.main keyHigh.1.publicKey)).run (initial, []) = _ at hhead
  simp only [initial, List.nil_append] at hhead
  rw [hhead, bind_map_left]
  apply bind_congr
  intro head
  simp [tail, Functor.map_map]

abbrev FilteredHighUntracedDirectResult :=
  (ProgrammedFixedChainKeygenView × (ChainEdgeIndex → Digest)) ×
    ((Forgery × Bool) × CausalHashState)

noncomputable def filteredHighUntracedDirectProgram
    (adversary : Adversary Concrete.scheme) (selected : ChainIndex) :
    OracleComp (RevealProbeOracleSimulation.World ChainValueIndex)
      FilteredHighUntracedDirectResult := do
  let keyHigh ← RevealProbeOracleSimulation.liftProbComp
    (coupledWarmedFixedChainKeygenWithHigh selected)
  (fun execution => (keyHigh, execution)) <$>
    (filteredHighUntracedDetailedExecution adversary keyHigh selected).run
      (filteredCausalKeygenState selected keyHigh.1)

def filteredHighMonitoredUntracedProjection
    (result : FilteredHighMonitoredProgramResult) :
    (ChainValueIndex → Digest) ×
      (FilteredHighUntracedDirectResult ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :=
  (result.1.1.2,
    (((result.1.1.1, result.1.2),
      (result.2.1, result.2.2.1.causal)), result.2.2.1.trace))

set_option maxHeartbeats 1000000 in
theorem filteredHighMonitoredProgram_projection_eq_eagerExperiment
    (adversary : Adversary Concrete.scheme) (selected : ChainIndex) :
    filteredHighMonitoredUntracedProjection <$>
        filteredHighMonitoredProgram adversary selected =
      RevealProbeOracleSimulation.eagerExperiment
        (filteredHighUntracedDirectProgram adversary selected) := by
  unfold filteredHighMonitoredProgram filteredHighMonitoredUntracedProjection
    filteredHighUntracedDirectProgram
    uniformCoupledWarmedFixedChainKeygenWithHigh
    RevealProbeOracleSimulation.eagerExperiment
  simp only [map_bind, map_pure, pure_bind, bind_assoc]
  apply bind_congr
  intro table
  rw [simulateQ_bind, WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp]
  simp only [bind_map_left, List.nil_append, Prod.eta, bind_assoc]
  apply bind_congr
  intro keyHigh
  rw [simulateQ_map, WriterT.run_map']
  have hdetail := map_filteredHighMonitoredDetailedExecution_projection
    adversary keyHigh selected table
  simpa only [map_eq_bind_pure_comp, Functor.map_map,
    Function.comp_apply, Function.comp_def, Prod.map, Prod.map_apply, id_eq,
    bind_assoc, pure_bind,
    Prod.eta] using congrArg
      (fun candidate =>
        (fun result : ((Forgery × Bool) × CausalHashState) ×
            RevealProbeOracleSimulation.ActionTrace ChainValueIndex =>
          ((table, ((keyHigh, result.1), result.2)) :
            (ChainValueIndex → Digest) ×
              (FilteredHighUntracedDirectResult ×
                RevealProbeOracleSimulation.ActionTrace ChainValueIndex))) <$>
          candidate)
      hdetail

end XmssSecurity.CappedChain
