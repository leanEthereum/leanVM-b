import XmssSecurity.Proof.CappedExactFirstLaneBoundedProgram

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000
set_option linter.constructorNameAsVariable false

def liftGlobalChainTrace
    (trace : RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :
    FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex :=
  trace.map FirstLaneOracleSimulation.ObservedAction.chain

@[simp]
theorem liftGlobalChainTrace_chainActions
    (trace : RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :
    (liftGlobalChainTrace trace).chainActions = trace := by
  simp [liftGlobalChainTrace,
    FirstLaneOracleSimulation.ActionTrace.chainActions]

@[simp]
theorem liftGlobalChainTrace_hazardCount
    (trace : RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :
    FirstLaneOracleSimulation.hazardCount (liftGlobalChainTrace trace) =
      RevealProbeOracleSimulation.observedProbeCount trace := by
  induction trace with
  | nil => simp [liftGlobalChainTrace,
      FirstLaneOracleSimulation.hazardCount,
      RevealProbeOracleSimulation.observedProbeCount]
  | cons action trace ih =>
      cases action with
      | probe index target =>
          simp only [liftGlobalChainTrace, List.map_cons,
            FirstLaneOracleSimulation.hazardCount,
            RevealProbeOracleSimulation.observedProbeCount,
            Nat.succ.injEq]
          change FirstLaneOracleSimulation.hazardCount
              (liftGlobalChainTrace trace) =
            RevealProbeOracleSimulation.observedProbeCount trace
          exact ih
      | reveal index value =>
          simp only [liftGlobalChainTrace, List.map_cons,
            FirstLaneOracleSimulation.hazardCount,
            RevealProbeOracleSimulation.observedProbeCount]
          change FirstLaneOracleSimulation.hazardCount
              (liftGlobalChainTrace trace) =
            RevealProbeOracleSimulation.observedProbeCount trace
          exact ih

theorem simulate_eagerTrace_lift_emitObservedTrace
    (table : GlobalChainValueIndex → Digest)
    (trace : RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hagrees : RevealProbeOracleSimulation.TraceAgrees table trace) :
    (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      (globalFirstLaneLiftRevealProbe
        (RevealProbeOracleSimulation.emitObservedTrace trace))).run =
      pure ((), liftGlobalChainTrace trace) := by
  induction trace with
  | nil =>
      simp [RevealProbeOracleSimulation.emitObservedTrace,
        globalFirstLaneLiftRevealProbe, liftGlobalChainTrace]
  | cons action trace ih =>
      cases action with
      | probe index target =>
          simp only [RevealProbeOracleSimulation.TraceAgrees] at hagrees
          simp [RevealProbeOracleSimulation.emitObservedTrace,
            RevealProbeOracleSimulation.probeQuery,
            globalFirstLaneLiftRevealProbe, globalFirstLaneRevealProbeImpl,
            FirstLaneOracleSimulation.probeQuery, simulateQ_bind,
            FirstLaneOracleSimulation.eagerTraceImpl,
            FirstLaneOracleSimulation.eagerImpl,
            FirstLaneOracleSimulation.traceFragment,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell,
            liftGlobalChainTrace]
          change (fun x => (x.1,
              FirstLaneOracleSimulation.ObservedAction.chain
                (.probe index target) :: x.2)) <$>
              (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
                (globalFirstLaneLiftRevealProbe
                  (RevealProbeOracleSimulation.emitObservedTrace trace)
                )).run = _
          rw [ih hagrees]
          rfl
      | reveal index value =>
          obtain ⟨hvalue, hrest⟩ := hagrees
          simp [RevealProbeOracleSimulation.emitObservedTrace,
            RevealProbeOracleSimulation.revealQuery,
            globalFirstLaneLiftRevealProbe, globalFirstLaneRevealProbeImpl,
            FirstLaneOracleSimulation.revealQuery, simulateQ_bind,
            FirstLaneOracleSimulation.eagerTraceImpl,
            FirstLaneOracleSimulation.eagerImpl,
            FirstLaneOracleSimulation.traceFragment,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell, hvalue,
            liftGlobalChainTrace]
          change (fun x => (x.1,
              FirstLaneOracleSimulation.ObservedAction.chain
                (.reveal index value) :: x.2)) <$>
              (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
                (globalFirstLaneLiftRevealProbe
                  (RevealProbeOracleSimulation.emitObservedTrace trace)
                )).run = _
          rw [ih hrest]
          rfl

noncomputable def appendGlobalFirstLaneExactPublicTrace
    (result : GlobalFirstLaneExactPublicEagerResult) :
    GlobalFirstLaneExactPublicEagerResult :=
  (result.1, (result.2.1, result.2.2 ++ liftGlobalChainTrace
    (globalHighDirectExactForgeryPrimaryProbeTrace result.2.1)))

theorem simulate_eagerTrace_bind_lift_emitObservedTrace_keep
    (table : GlobalChainValueIndex → Digest)
    (computation : OracleComp GlobalFirstLaneWorld α)
    (suffix : α →
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hagrees : ∀ result, RevealProbeOracleSimulation.TraceAgrees table
      (suffix result)) :
    (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table) (do
      let result ← computation
      let _ ← globalFirstLaneLiftRevealProbe
        (RevealProbeOracleSimulation.emitObservedTrace (suffix result))
      pure result)).run =
    (fun result =>
      (result.1, result.2 ++ liftGlobalChainTrace (suffix result.1))) <$>
      (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        computation).run := by
  rw [simulateQ_bind, WriterT.run_bind']
  apply bind_congr
  intro result
  rcases result with ⟨result, trace⟩
  simp only [Function.comp_apply]
  rw [simulateQ_bind, WriterT.run_bind']
  rw [simulate_eagerTrace_lift_emitObservedTrace table (suffix result)
    (hagrees result)]
  simp only [simulateQ_pure, WriterT.run_pure', map_pure, pure_bind,
    Prod.map_apply, id_eq]
  change (pure (result,
      trace ++ (liftGlobalChainTrace (suffix result) ++ [])) : ProbComp _) =
    pure (result, trace ++ liftGlobalChainTrace (suffix result))
  rw [List.append_nil]

theorem eagerExperiment_globalFirstLaneExactTracedPublicProgram_eq_append
    (adversary : Adversary Concrete.scheme) :
    FirstLaneOracleSimulation.eagerExperiment
      (globalFirstLaneExactTracedPublicProgram adversary) =
    appendGlobalFirstLaneExactPublicTrace <$>
      FirstLaneOracleSimulation.eagerExperiment
        (globalFirstLaneExactTracedProgram adversary) := by
  unfold globalFirstLaneExactTracedPublicProgram
    FirstLaneOracleSimulation.eagerExperiment
  simp only [map_bind]
  apply bind_congr
  intro table
  rw [simulate_eagerTrace_bind_lift_emitObservedTrace_keep table
    (globalFirstLaneExactTracedProgram adversary)
    globalHighDirectExactForgeryPrimaryProbeTrace
    (globalHighDirectExactForgeryPrimaryProbeTrace_agrees table)]
  simp [appendGlobalFirstLaneExactPublicTrace, map_eq_bind_pure_comp,
    bind_assoc]

theorem globalHighExactMonitoredProgram_traceConsistent
    (adversary : Adversary Concrete.scheme)
    (result : GlobalHighExactMonitoredProgramResult)
    (hresult : result ∈ support
      (globalHighExactMonitoredProgram adversary)) :
    result.2.2.1.1.TraceConsistent result.1.1.2 := by
  unfold globalHighExactMonitoredProgram at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨right, _hright, htail⟩ := hresult
  rw [mem_support_bind_iff] at htail
  obtain ⟨execution, hexecution, hpure⟩ := htail
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  have hprojected : (execution.1, execution.2.1) ∈ support
      (globalHighMonitoredDetailedExecution adversary right) := by
    rw [← globalHighExactMonitoredDetailedExecution_projection,
      support_map]
    exact ⟨execution, hexecution, rfl⟩
  exact globalHighMonitoredDetailedExecution_traceConsistent adversary right
    (execution.1, execution.2.1) hprojected

theorem globalHighExactState_eq_of_projection_trace_consistent
    (table : GlobalChainValueIndex → Digest)
    (left right : GlobalHighExactMonitoredState)
    (hprojection : globalHighExactStateProjection left =
      globalHighExactStateProjection right)
    (htrace : left.1.1.trace = right.1.1.trace)
    (hleft : left.1.1.TraceConsistent table)
    (hright : right.1.1.TraceConsistent table) :
    left = right := by
  rcases left with ⟨⟨⟨leftCausal, leftMonitor, leftTrace⟩,
    leftAttacker⟩, leftEncoding⟩
  rcases right with ⟨⟨⟨rightCausal, rightMonitor, rightTrace⟩,
    rightAttacker⟩, rightEncoding⟩
  simp only [globalHighExactStateProjection, GlobalExactTracedState.mk.injEq]
    at hprojection
  change leftTrace = rightTrace at htrace
  simp only [GlobalMonitoredCausalState.TraceConsistent] at hleft hright
  obtain ⟨hcausal, hattacker, hencoding⟩ := hprojection
  subst rightCausal
  subst rightTrace
  subst rightAttacker
  subst rightEncoding
  rw [hleft, hright]

theorem globalFirstLaneExactCoupledProgram_support_info
    (adversary : Adversary Concrete.scheme)
    (result : GlobalFirstLaneExactCoupledProgramResult)
    (hresult : result ∈ support
      (globalFirstLaneExactCoupledProgram adversary)) :
    result.1 ∈ support coupledGlobalChainKeygenWithBaseHighFull ∧
    result.2 ∈ support
      ((simulateQ
        (FirstLaneOracleSimulation.eagerTraceImpl result.1.1.2)
        ((globalFirstLaneExactTracedDetailedExecution adversary result.1.1.1
          result.1.2).run (GlobalExactTracedState.initial
            (globalFilteredCausalKeygenState result.1.1.1)))).run) := by
  unfold globalFirstLaneExactCoupledProgram at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨right, hright, htail⟩ := hresult
  rw [mem_support_bind_iff] at htail
  obtain ⟨execution, hexecution, hpure⟩ := htail
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  exact ⟨hright, hexecution⟩

theorem coupledGlobalChainKeygenWithBaseHighFull_support_directKeyResult
    (result : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hresult : result ∈ support
      coupledGlobalChainKeygenWithBaseHighFull) :
    (result.1.1, result.2) ∈ support globalHighDirectKeygen := by
  rw [coupledGlobalChainKeygenWithBaseHighFull_eq_direct] at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨parameter, hparameter, hbaseTail⟩ := hresult
  rw [mem_support_bind_iff] at hbaseTail
  obtain ⟨base, _hbase, hkeyTail⟩ := hbaseTail
  rw [mem_support_bind_iff] at hkeyTail
  obtain ⟨keyResult, hkeyResult, hpure⟩ := hkeyTail
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  have hkeyGlobal : keyResult ∈ support globalHighDirectKeygen := by
    unfold globalHighDirectKeygen
    rw [mem_support_bind_iff]
    exact ⟨parameter, hparameter, hkeyResult⟩
  have hprojected : (result.1.1, result.2) = keyResult := by
    exact congrArg (fun candidate => (candidate.1.1, candidate.2)) hpure
  rw [hprojected]
  exact hkeyGlobal

theorem globalFirstLaneExactCoupled_run_mem_support
    (adversary : Adversary Concrete.scheme)
    (result : GlobalFirstLaneExactCoupledProgramResult)
    (hresult : result ∈ support
      (globalFirstLaneExactCoupledProgram adversary)) :
    (((result.1.1.1, result.1.2), result.2.1), result.2.2) ∈ support
      ((simulateQ
        (FirstLaneOracleSimulation.eagerTraceImpl result.1.1.2)
        (globalFirstLaneExactTracedProgram adversary)).run) := by
  obtain ⟨hkey, hexecution⟩ :=
    globalFirstLaneExactCoupledProgram_support_info adversary result hresult
  have hdirectKey :=
    coupledGlobalChainKeygenWithBaseHighFull_support_directKeyResult
      result.1 hkey
  unfold globalFirstLaneExactTracedProgram
  rw [simulateQ_bind, WriterT.run_bind', mem_support_bind_iff]
  refine ⟨((result.1.1.1, result.1.2), []), ?_, ?_⟩
  · rw [FirstLaneOracleSimulation.simulate_eagerTrace_liftProbComp,
      support_map]
    exact ⟨(result.1.1.1, result.1.2), hdirectKey, rfl⟩
  · simp only [List.nil_append]
    rw [show Prod.map id (fun x => x) =
      (id : GlobalExactTracedResult × FirstLaneOracleSimulation.ActionTrace
        GlobalChainValueIndex → _) from Prod.map_id,
      id_map, simulateQ_bind, WriterT.run_bind',
      mem_support_bind_iff]
    refine ⟨result.2, hexecution, ?_⟩
    simp

theorem exists_globalHighExactMonitored_of_coupled_support
    (adversary : Adversary Concrete.scheme)
    (result : GlobalFirstLaneExactCoupledProgramResult)
    (hresult : result ∈ support
      (globalFirstLaneExactCoupledProgram adversary)) :
    ∃ highResult ∈ support (globalHighExactMonitoredProgram adversary),
      globalHighExactMonitoredFullProjection highResult =
        (result.1.1.2,
          (((result.1.1.1, result.1.2), result.2.1),
            result.2.2.chainActions)) := by
  obtain ⟨hkey, hexecution⟩ :=
    globalFirstLaneExactCoupledProgram_support_info adversary result hresult
  have hmapped : (result.2.1, result.2.2.chainActions) ∈ support
      ((fun execution => (execution.1, execution.2.chainActions)) <$>
        (simulateQ
          (FirstLaneOracleSimulation.eagerTraceImpl result.1.1.2)
          ((globalFirstLaneExactTracedDetailedExecution adversary
            result.1.1.1 result.1.2).run (GlobalExactTracedState.initial
              (globalFilteredCausalKeygenState result.1.1.1)))).run) := by
    rw [support_map]
    exact ⟨result.2, hexecution, rfl⟩
  rw [simulate_globalFirstLaneEagerTrace_chainProjection] at hmapped
  rw [globalFirstLaneErase_exactTracedDetailedExecution adversary
    result.1.1.1 result.1.2 (GlobalExactTracedState.initial
      (globalFilteredCausalKeygenState result.1.1.1))] at hmapped
  rw [← map_globalHighExactMonitoredDetailedExecution_full_projection]
    at hmapped
  rw [support_map] at hmapped
  obtain ⟨highExecution, hhighExecution, hprojection⟩ := hmapped
  let highResult : GlobalHighExactMonitoredProgramResult :=
    (result.1, highExecution)
  have hhighResult : highResult ∈ support
      (globalHighExactMonitoredProgram adversary) := by
    unfold globalHighExactMonitoredProgram
    rw [mem_support_bind_iff]
    refine ⟨result.1, hkey, ?_⟩
    rw [mem_support_bind_iff]
    exact ⟨highExecution, hhighExecution, by simp [highResult]⟩
  refine ⟨highResult, hhighResult, ?_⟩
  simpa [highResult, globalHighExactMonitoredFullProjection] using
    congrArg (fun execution =>
      (result.1.1.2,
        (((result.1.1.1, result.1.2), execution.1), execution.2)))
      hprojection

theorem sourceFirstLaneExactGood_to_globalHighRelation
    (adversary : Adversary Concrete.scheme)
    (left : SourceGlobalExactTracedProgramResult)
    (right : GlobalFirstLaneExactCoupledProgramResult)
    (hrightSupport : right ∈ support
      (globalFirstLaneExactCoupledProgram adversary))
    (hkey : ProgrammedGlobalChainKeygenBaseHighStableRelation
      left.1 right.1)
    (hgood : left.2.1 = right.2.1.1 ∧
      SourceFirstLaneExactGoodStateRelation left.1 right.1.1 left.2.2
        right.2.1.2 right.2.2) :
    ∃ highResult ∈ support (globalHighExactMonitoredProgram adversary),
      SourceGlobalExactHighMonitoredProgramRelation left highResult ∧
      globalHighExactMonitoredFullProjection highResult =
        (right.1.1.2,
          (((right.1.1.1, right.1.2), right.2.1),
            right.2.2.chainActions)) := by
  obtain ⟨highResult, hhighSupport, hprojection⟩ :=
    exists_globalHighExactMonitored_of_coupled_support adversary right
      hrightSupport
  obtain ⟨witness, hwitnessRelation, hfirstState, hwitnessTrace,
    hwitnessConsistent⟩ := hgood.2
  have hhighConsistent :=
    globalHighExactMonitoredProgram_traceConsistent adversary highResult
      hhighSupport
  have hbase : highResult.1.1.2 = right.1.1.2 :=
    congrArg Prod.fst hprojection
  have hdirect :
      ((highResult.1.1.1, highResult.1.2),
        (highResult.2.1, globalHighExactStateProjection highResult.2.2)) =
      ((right.1.1.1, right.1.2),
        (right.2.1.1, right.2.1.2)) :=
    congrArg (fun projected => projected.2.1) hprojection
  have hchain : highResult.2.2.1.1.trace = right.2.2.chainActions :=
    congrArg (fun projected => projected.2.2) hprojection
  have hkeyView : highResult.1.1.1 = right.1.1.1 :=
    congrArg (fun direct => direct.1.1) hdirect
  have hedgeHigh : highResult.1.2 = right.1.2 :=
    congrArg (fun direct => direct.1.2) hdirect
  have houtcome : highResult.2.1 = right.2.1.1 :=
    congrArg (fun direct => direct.2.1) hdirect
  have hstateProjection :
      globalHighExactStateProjection highResult.2.2 = right.2.1.2 :=
    congrArg (fun direct => direct.2.2) hdirect
  have hfullKey : highResult.1 = right.1 := by
    apply Prod.ext
    · apply Prod.ext
      · exact hkeyView
      · exact hbase
    · exact hedgeHigh
  have hstate : highResult.2.2 = witness := by
    apply globalHighExactState_eq_of_projection_trace_consistent
      right.1.1.2
    · rw [hstateProjection, hfirstState]
    · rw [hchain, hwitnessTrace]
    · rw [← hbase]
      exact hhighConsistent
    · exact hwitnessConsistent
  refine ⟨highResult, hhighSupport, ?_, hprojection⟩
  refine ⟨?_, ?_, hhighConsistent⟩
  · rw [hfullKey]
    exact hkey
  · apply Or.inl
    constructor
    · rw [houtcome]
      exact hgood.1
    · rw [hfullKey, hstate]
      exact hwitnessRelation

theorem globalFirstLaneExactCoupledPublic_run_mem_support
    (adversary : Adversary Concrete.scheme)
    (result : GlobalFirstLaneExactCoupledProgramResult)
    (hresult : result ∈ support
      (globalFirstLaneExactCoupledProgram adversary)) :
    (appendGlobalFirstLaneExactPublicTrace
      (globalFirstLaneExactCoupledProjection result)).2 ∈ support
      ((simulateQ
        (FirstLaneOracleSimulation.eagerTraceImpl result.1.1.2)
        (globalFirstLaneExactTracedPublicProgram adversary)).run) := by
  have hrun := globalFirstLaneExactCoupled_run_mem_support adversary result
    hresult
  unfold globalFirstLaneExactTracedPublicProgram
  rw [simulate_eagerTrace_bind_lift_emitObservedTrace_keep
    result.1.1.2 (globalFirstLaneExactTracedProgram adversary)
    globalHighDirectExactForgeryPrimaryProbeTrace
    (globalHighDirectExactForgeryPrimaryProbeTrace_agrees result.1.1.2)]
  rw [support_map]
  exact ⟨(((result.1.1.1, result.1.2), result.2.1), result.2.2), hrun, by
    simp [appendGlobalFirstLaneExactPublicTrace,
      globalFirstLaneExactCoupledProjection]⟩

theorem sourceWinningExactFirstLane_good_implies_public_combinedHit
    (adversary : Adversary Concrete.scheme)
    (left : SourceGlobalExactTracedProgramResult)
    (right : GlobalFirstLaneExactCoupledProgramResult)
    (hleftSupport : left ∈ support
      (sourceGlobalExactTracedProgram adversary))
    (hrightSupport : right ∈ support
      (globalFirstLaneExactCoupledProgram adversary))
    (hkey : ProgrammedGlobalChainKeygenBaseHighStableRelation
      left.1 right.1)
    (hgood : left.2.1 = right.2.1.1 ∧
      SourceFirstLaneExactGoodStateRelation left.1 right.1.1 left.2.2
        right.2.1.2 right.2.2)
    (hevent : SourceWinningExactFirstLaneEvent left) :
    FirstLaneOracleSimulation.CombinedHit
      (appendGlobalFirstLaneExactPublicTrace
        (globalFirstLaneExactCoupledProjection right)).1
      (appendGlobalFirstLaneExactPublicTrace
        (globalFirstLaneExactCoupledProjection right)).2.2 := by
  obtain ⟨highResult, hhighSupport, hhighRelation, hprojection⟩ :=
    sourceFirstLaneExactGood_to_globalHighRelation adversary left right
      hrightSupport hkey hgood
  have hhighEvent := sourceWinningExactFirstLane_implies_globalHighExact
    adversary left highResult hleftSupport hhighSupport hhighRelation hevent
  have hprojected :=
    globalHighExactFirstLaneEvent_implies_projected highResult hhighEvent
  have htargetEvent : GlobalHighExactProjectedFirstLaneEvent
      ((appendGlobalFirstLaneExactPublicTrace
        (globalFirstLaneExactCoupledProjection right)).1,
       ((appendGlobalFirstLaneExactPublicTrace
        (globalFirstLaneExactCoupledProjection right)).2.1,
        (appendGlobalFirstLaneExactPublicTrace
          (globalFirstLaneExactCoupledProjection right)).2.2.chainActions)) := by
    rw [hprojection] at hprojected
    simpa [appendGlobalHighDirectExactPublicTrace,
      appendGlobalFirstLaneExactPublicTrace,
      globalFirstLaneExactCoupledProjection,
      FirstLaneOracleSimulation.ActionTrace.chainActions_append] using
        hprojected
  exact globalHighExactProjectedFirstLaneEvent_implies_combinedHit_of_run
    adversary
      (appendGlobalFirstLaneExactPublicTrace
        (globalFirstLaneExactCoupledProjection right)).1
      (appendGlobalFirstLaneExactPublicTrace
        (globalFirstLaneExactCoupledProjection right)).2
      (globalFirstLaneExactCoupledPublic_run_mem_support adversary right
        hrightSupport)
      htargetEvent

theorem observedProbeCount_exactForgeryPrimaryProbeTrace
    (result : GlobalExactTracedResult) :
    RevealProbeOracleSimulation.observedProbeCount
      (globalHighDirectExactForgeryPrimaryProbeTrace result) = numChains := by
  unfold globalHighDirectExactForgeryPrimaryProbeTrace
  exact observedProbeCount_globalHighDirectForgeryPrimaryProbeTrace _

theorem hazardCount_appendGlobalFirstLaneExactPublicTrace
    (result : GlobalFirstLaneExactPublicEagerResult) :
    FirstLaneOracleSimulation.hazardCount
      (appendGlobalFirstLaneExactPublicTrace result).2.2 =
    FirstLaneOracleSimulation.hazardCount result.2.2 + numChains := by
  simp [appendGlobalFirstLaneExactPublicTrace,
    FirstLaneOracleSimulation.hazardCount_append,
    observedProbeCount_exactForgeryPrimaryProbeTrace]

noncomputable def globalFirstLaneExactCoupledPublicProjection
    (result : GlobalFirstLaneExactCoupledProgramResult) :
    GlobalFirstLaneExactPublicEagerResult :=
  appendGlobalFirstLaneExactPublicTrace
    (globalFirstLaneExactCoupledProjection result)

def GlobalFirstLaneExactCoupledEnforcedHit
    (fuel : Nat) (result : GlobalFirstLaneExactCoupledProgramResult) : Prop :=
  FirstLaneOracleSimulation.CombinedHit
    (globalFirstLaneExactCoupledPublicProjection result).1
    (FirstLaneOracleSimulation.enforceHazardTrace fuel
      (globalFirstLaneExactCoupledPublicProjection result).2.2)

theorem sourceWinningExactFirstLane_good_implies_public_enforcedHit
    (countLimit fuel : Nat)
    (adversary : Adversary Concrete.scheme)
    (left : SourceGlobalExactTracedProgramResult)
    (right : GlobalFirstLaneExactCoupledProgramResult)
    (hleftSupport : left ∈ support
      (sourceGlobalExactTracedProgram adversary))
    (hrightSupport : right ∈ support
      (globalFirstLaneExactCoupledProgram adversary))
    (hkey : ProgrammedGlobalChainKeygenBaseHighStableRelation
      left.1 right.1)
    (hgood : left.2.1 = right.2.1.1 ∧
      SourceFirstLaneExactGoodStateRelation left.1 right.1.1 left.2.2
        right.2.1.2 right.2.2 ∧
      FirstLaneOracleSimulation.hazardCount right.2.2 ≤ countLimit)
    (hfuel : countLimit + numChains ≤ fuel)
    (hevent : SourceWinningExactFirstLaneEvent left) :
    GlobalFirstLaneExactCoupledEnforcedHit fuel right := by
  have hraw :=
    sourceWinningExactFirstLane_good_implies_public_combinedHit adversary
      left right hleftSupport hrightSupport hkey ⟨hgood.1, hgood.2.1⟩ hevent
  have hcount : FirstLaneOracleSimulation.hazardCount
      (globalFirstLaneExactCoupledPublicProjection right).2.2 ≤ fuel := by
    rw [globalFirstLaneExactCoupledPublicProjection,
      hazardCount_appendGlobalFirstLaneExactPublicTrace]
    dsimp only [globalFirstLaneExactCoupledProjection]
    omega
  unfold GlobalFirstLaneExactCoupledEnforcedHit
  rw [FirstLaneOracleSimulation.enforceHazardTrace_eq_self_of_count_le
    _ _ hcount]
  exact hraw

theorem sourceWinningExactFirstLane_hit_implies_public_enforcedHit
    (fuel : Nat)
    (right : GlobalFirstLaneExactCoupledProgramResult)
    (hhit : FirstLaneOracleSimulation.CombinedHit right.1.1.2
      (FirstLaneOracleSimulation.enforceHazardTrace fuel right.2.2)) :
    GlobalFirstLaneExactCoupledEnforcedHit fuel right := by
  unfold GlobalFirstLaneExactCoupledEnforcedHit
    globalFirstLaneExactCoupledPublicProjection
    appendGlobalFirstLaneExactPublicTrace
    globalFirstLaneExactCoupledProjection
  exact FirstLaneOracleSimulation.CombinedHit.enforce_append_of_prefix
    right.1.1.2 fuel right.2.2
      (liftGlobalChainTrace
        (globalHighDirectExactForgeryPrimaryProbeTrace
          ((right.1.1.1, right.1.2), right.2.1))) hhit

theorem sourceWinningExactFirstLane_implies_coupled_enforcedHit
    (countLimit fuel : Nat)
    (adversary : Adversary Concrete.scheme)
    (left : SourceGlobalExactTracedProgramResult)
    (right : GlobalFirstLaneExactCoupledProgramResult)
    (hleftSupport : left ∈ support
      (sourceGlobalExactTracedProgram adversary))
    (hrightSupport : right ∈ support
      (globalFirstLaneExactCoupledProgram adversary))
    (hrelation : SourceFirstLaneExactBoundedProgramRelation
      countLimit fuel left right)
    (hfuel : countLimit + numChains ≤ fuel)
    (hevent : SourceWinningExactFirstLaneEvent left) :
    GlobalFirstLaneExactCoupledEnforcedHit fuel right := by
  rcases hrelation with ⟨hkey, hgood | hhit⟩
  · exact sourceWinningExactFirstLane_good_implies_public_enforcedHit
      countLimit fuel adversary left right hleftSupport hrightSupport hkey
        hgood hfuel hevent
  · exact sourceWinningExactFirstLane_hit_implies_public_enforcedHit
      fuel right hhit

theorem evalDist_globalFirstLaneExactCoupledPublicProjection_eq_eager
    (adversary : Adversary Concrete.scheme) :
    evalDist (globalFirstLaneExactCoupledPublicProjection <$>
      globalFirstLaneExactCoupledProgram adversary) =
    evalDist (globalFirstLaneExactPublicEagerExperiment adversary) := by
  calc
    evalDist (globalFirstLaneExactCoupledPublicProjection <$>
        globalFirstLaneExactCoupledProgram adversary) =
      evalDist (appendGlobalFirstLaneExactPublicTrace <$>
        (globalFirstLaneExactCoupledProjection <$>
          globalFirstLaneExactCoupledProgram adversary)) := by
            apply congrArg evalDist
            rw [Functor.map_map]
            rfl
    _ = evalDist (appendGlobalFirstLaneExactPublicTrace <$>
        FirstLaneOracleSimulation.eagerExperiment
          (globalFirstLaneExactTracedProgram adversary)) := by
      exact evalDist_map_congr_of_evalDist_eq
        appendGlobalFirstLaneExactPublicTrace
        (globalFirstLaneExactCoupledProjection <$>
          globalFirstLaneExactCoupledProgram adversary)
        (FirstLaneOracleSimulation.eagerExperiment
          (globalFirstLaneExactTracedProgram adversary))
        (evalDist_globalFirstLaneExactCoupledProjection_eq_eagerExperiment
          adversary)
    _ = _ := by
      unfold globalFirstLaneExactPublicEagerExperiment
      rw [eagerExperiment_globalFirstLaneExactTracedPublicProgram_eq_append]

def GlobalFirstLaneExactPublicEnforcedHit
    (fuel : Nat) (result : GlobalFirstLaneExactPublicEagerResult) : Prop :=
  FirstLaneOracleSimulation.CombinedHit result.1
    (FirstLaneOracleSimulation.enforceHazardTrace fuel result.2.2)

theorem sourceWinningExactFirstLane_probability_le_coupled_enforcedHit
    (q fuel : Nat)
    (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (hfuel : q - treeHashQueryCount treeHeight + numChains ≤ fuel) :
    Pr[SourceWinningExactFirstLaneEvent |
        sourceGlobalExactTracedProgram adversary] ≤
      Pr[GlobalFirstLaneExactCoupledEnforcedHit fuel |
        globalFirstLaneExactCoupledProgram adversary] := by
  apply probEvent_le_of_relTriple
    (relTriple_with_support
      (relTriple_sourceGlobalExact_firstLane_program_boundedHit_sub_keygen
        q fuel adversary hbound (by omega)))
  intro left right hrelation hevent
  exact sourceWinningExactFirstLane_implies_coupled_enforcedHit
    (q - treeHashQueryCount treeHeight) fuel adversary left right
      hrelation.2.1 hrelation.2.2 hrelation.1 hfuel hevent

theorem coupled_enforcedHit_probability_eq_public_eager
    (fuel : Nat) (adversary : Adversary Concrete.scheme) :
    Pr[GlobalFirstLaneExactCoupledEnforcedHit fuel |
        globalFirstLaneExactCoupledProgram adversary] =
      Pr[GlobalFirstLaneExactPublicEnforcedHit fuel |
        globalFirstLaneExactPublicEagerExperiment adversary] := by
  calc
    _ = Pr[GlobalFirstLaneExactPublicEnforcedHit fuel |
        globalFirstLaneExactCoupledPublicProjection <$>
          globalFirstLaneExactCoupledProgram adversary] := by
      rw [probEvent_map]
      rfl
    _ = _ := probEvent_eq_of_evalDist_eq _
      (evalDist_globalFirstLaneExactCoupledPublicProjection_eq_eager
        adversary)

theorem public_eager_enforcedHit_probability_le
    (fuel : Nat) (adversary : Adversary Concrete.scheme) :
    Pr[GlobalFirstLaneExactPublicEnforcedHit fuel |
        globalFirstLaneExactPublicEagerExperiment adversary] ≤
      (fuel : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
  have hbound :=
    FirstLaneOracleSimulation.eagerExperiment_enforced_combinedHit_probability_le
      fuel (globalFirstLaneExactTracedPublicProgram adversary)
  rw [FirstLaneOracleSimulation.eagerExperiment_enforceHazardBound_eq_map,
    probEvent_map] at hbound
  exact hbound

theorem sourceWinningExactFirstLane_probability_le
    (q : Nat)
    (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    Pr[SourceWinningExactFirstLaneEvent |
        sourceGlobalExactTracedProgram adversary] ≤
      ((q - treeHashQueryCount treeHeight + numChains : Nat) : ENNReal) /
        ((2 ^ digestBits : Nat) : ENNReal) := by
  let fuel := q - treeHashQueryCount treeHeight + numChains
  calc
    _ ≤ Pr[GlobalFirstLaneExactCoupledEnforcedHit fuel |
        globalFirstLaneExactCoupledProgram adversary] :=
      sourceWinningExactFirstLane_probability_le_coupled_enforcedHit q fuel
        adversary hbound (by simp [fuel])
    _ = Pr[GlobalFirstLaneExactPublicEnforcedHit fuel |
        globalFirstLaneExactPublicEagerExperiment adversary] :=
      coupled_enforcedHit_probability_eq_public_eager fuel adversary
    _ ≤ _ := public_eager_enforcedHit_probability_le fuel adversary

theorem hasExactFirstLaneBound_of_hashQueryBound
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    HasExactFirstLaneBound q adversary := by
  unfold HasExactFirstLaneBound
  rw [cappedExactFirstLane_probability_eq_sourceGlobalExact]
  exact sourceWinningExactFirstLane_probability_le q adversary hbound

theorem hasExactFirstLaneBounds : HasExactFirstLaneBounds := by
  intro q adversary hbound
  exact hasExactFirstLaneBound_of_hashQueryBound q adversary hbound

end XmssSecurity.CappedChain
