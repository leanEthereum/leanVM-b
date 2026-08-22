import XmssSecurity.Proof.CappedExactFirstLaneBoundedProgram
import XmssSecurity.Proof.FirstLaneEagerBound
import XmssSecurity.Proof.FirstLaneHazardEnforcement

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
    (adversary : Adversary) :
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

theorem globalHighState_eq_of_projection_trace
    (left : GlobalMonitoredTracedState)
    (right : GlobalMonitoredTracedState)
    (hprojection : GlobalHighDirectTracedState.mk left.1.causal left.2 =
      GlobalHighDirectTracedState.mk right.1.causal right.2)
    (htrace : left.1.trace = right.1.trace) :
    left = right := by
  rcases left with ⟨⟨leftCausal, leftTrace⟩, leftAttacker⟩
  rcases right with ⟨⟨rightCausal, rightTrace⟩, rightAttacker⟩
  change (leftCausal, leftAttacker) = (rightCausal, rightAttacker)
    at hprojection
  simp only [Prod.mk.injEq] at hprojection
  change leftTrace = rightTrace at htrace
  obtain ⟨hcausal, hattacker⟩ := hprojection
  subst rightCausal
  subst rightTrace
  subst rightAttacker
  rfl

theorem globalFirstLaneExactCoupledProgram_support_info
    (adversary : Adversary)
    (result : GlobalFirstLaneExactCoupledProgramResult)
    (hresult : result ∈ support
      (globalFirstLaneExactCoupledProgram adversary)) :
    result.1 ∈ support coupledGlobalChainKeygenWithBaseHighFull ∧
    result.2 ∈ support
      ((simulateQ
        (FirstLaneOracleSimulation.eagerTraceImpl result.1.1.2)
        ((globalFirstLaneExactTracedDetailedExecution adversary result.1.1.1
          result.1.2).run (GlobalHighDirectTracedState.initial
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
    (adversary : Adversary)
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

theorem exists_globalHighMonitored_of_coupled_support
    (adversary : Adversary)
    (result : GlobalFirstLaneExactCoupledProgramResult)
    (hresult : result ∈ support
      (globalFirstLaneExactCoupledProgram adversary)) :
    ∃ highResult ∈ support (globalHighMonitoredProgram adversary),
      globalHighMonitoredFullProjection highResult =
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
            result.1.1.1 result.1.2).run (GlobalHighDirectTracedState.initial
              (globalFilteredCausalKeygenState result.1.1.1)))).run) := by
    rw [support_map]
    exact ⟨result.2, hexecution, rfl⟩
  rw [simulate_globalFirstLaneEagerTrace_chainProjection] at hmapped
  rw [globalFirstLaneErase_exactTracedDetailedExecution adversary
    result.1.1.1 result.1.2 (GlobalHighDirectTracedState.initial
      (globalFilteredCausalKeygenState result.1.1.1))] at hmapped
  rw [← map_globalHighMonitoredDetailedExecution_full_projection]
    at hmapped
  rw [support_map] at hmapped
  obtain ⟨highExecution, hhighExecution, hprojection⟩ := hmapped
  let highResult : GlobalHighMonitoredProgramResult :=
    (result.1, highExecution)
  have hhighResult : highResult ∈ support
      (globalHighMonitoredProgram adversary) := by
    unfold globalHighMonitoredProgram
    rw [mem_support_bind_iff]
    refine ⟨result.1, hkey, ?_⟩
    rw [mem_support_bind_iff]
    exact ⟨highExecution, hhighExecution, by simp [highResult]⟩
  refine ⟨highResult, hhighResult, ?_⟩
  simpa [highResult, globalHighMonitoredFullProjection] using
    congrArg (fun execution =>
      (result.1.1.2,
        (((result.1.1.1, result.1.2), execution.1), execution.2)))
      hprojection

theorem sourceFirstLaneExactGood_to_globalHighRelation
    (adversary : Adversary)
    (left : SourceGlobalExactTracedProgramResult)
    (right : GlobalFirstLaneExactCoupledProgramResult)
    (hrightSupport : right ∈ support
      (globalFirstLaneExactCoupledProgram adversary))
    (hkey : ProgrammedGlobalChainKeygenBaseHighStableRelation
      left.1 right.1)
    (hgood : left.2.1 = right.2.1.1 ∧
      SourceFirstLaneExactGoodStateRelation left.1 right.1.1 left.2.2
        right.2.1.2 right.2.2) :
    ∃ highResult ∈ support (globalHighMonitoredProgram adversary),
      SourceGlobalHighMonitoredProgramRelation
        (sourceGlobalExactErasedResult left)
        highResult ∧
      globalHighMonitoredFullProjection highResult =
        (right.1.1.2,
          (((right.1.1.1, right.1.2), right.2.1),
            right.2.2.chainActions)) ∧
      List.Sublist left.2.2.1.2 right.2.2.encodingActions ∧
      List.Sublist
        (CappedEncodingMonitor.validObservedSignEpochs
          right.2.2.encodingActions)
        (left.2.2.2.toSigningLog.map fun entry => entry.1.epoch) := by
  obtain ⟨highResult, hhighSupport, hprojection⟩ :=
    exists_globalHighMonitored_of_coupled_support adversary right
      hrightSupport
  obtain ⟨witness, hwitnessRelation, hfirstState, hwitnessTrace,
    hwitnessEncoding, hwitnessValidEpochs⟩ := hgood.2
  have hbase : highResult.1.1.2 = right.1.1.2 :=
    congrArg Prod.fst hprojection
  have hdirect :
      ((highResult.1.1.1, highResult.1.2),
        (highResult.2.1, GlobalHighDirectTracedState.mk
          highResult.2.2.1.causal highResult.2.2.2)) =
      ((right.1.1.1, right.1.2),
        (right.2.1.1, right.2.1.2)) :=
    congrArg (fun projected => projected.2.1) hprojection
  have hchain : highResult.2.2.1.trace = right.2.2.chainActions :=
    congrArg (fun projected => projected.2.2) hprojection
  have hkeyView : highResult.1.1.1 = right.1.1.1 :=
    congrArg (fun direct => direct.1.1) hdirect
  have hedgeHigh : highResult.1.2 = right.1.2 :=
    congrArg (fun direct => direct.1.2) hdirect
  have houtcome : highResult.2.1 = right.2.1.1 :=
    congrArg (fun direct => direct.2.1) hdirect
  have hstateProjection :
      GlobalHighDirectTracedState.mk highResult.2.2.1.causal highResult.2.2.2 =
        right.2.1.2 :=
    congrArg (fun direct => direct.2.2) hdirect
  have hfullKey : highResult.1 = right.1 := by
    apply Prod.ext
    · apply Prod.ext
      · exact hkeyView
      · exact hbase
    · exact hedgeHigh
  have hstate : highResult.2.2 = witness := by
    apply globalHighState_eq_of_projection_trace
    · rw [hstateProjection, hfirstState]
    · rw [hchain, hwitnessTrace]
  refine ⟨highResult, hhighSupport, ?_, hprojection, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · change ProgrammedGlobalChainKeygenBaseHighStableRelation left.1
        highResult.1
      rw [hfullKey]
      exact hkey
    · apply Or.inl
      constructor
      · change left.2.1 = highResult.2.1
        exact hgood.1.trans houtcome.symm
      · simpa [sourceGlobalExactErasedResult, sourceGlobalExactErasedExecution,
          GlobalSigningMonitoredTracedStateRelation,
          sourceExactSigningProjection, sourceSigningTracedStateProjection] using
            (show GlobalSigningMonitoredTracedStateRelation left.1
              highResult.1.1
              (sourceExactSigningProjection left.2.2) highResult.2.2 by
                rw [hfullKey, hstate]
                exact hwitnessRelation)
  · exact hwitnessEncoding
  · have hattacker : left.2.2.2 = witness.2 := by
      simpa [GlobalSigningMonitoredTracedStateRelation,
        sourceExactSigningProjection, sourceSigningTracedStateProjection] using
          hwitnessRelation.2
    rw [hattacker]
    exact hwitnessValidEpochs

theorem globalFirstLaneExactCoupledPublic_run_mem_support
    (adversary : Adversary)
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
    (adversary : Adversary)
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
  obtain ⟨highResult, hhighSupport, hhighRelation, hprojection,
    hencodingSub, hvalidSub⟩ :=
    sourceFirstLaneExactGood_to_globalHighRelation adversary left right
      hrightSupport hkey hgood
  let both := sourceGlobalExactProgramResult left
  have hbothMapped : both ∈ support
      (sourceGlobalExactProgramResult <$>
        sourceGlobalExactTracedProgram adversary) := by
    rw [support_map]
    exact ⟨left, hleftSupport, rfl⟩
  have hboth : both ∈ support
      (cappedDetailedGameWithKeygenCacheAndBothTraces adversary) :=
    (mem_support_iff_of_evalDist_eq
      (evalDist_sourceGlobalExact_eq_cappedBothTraces adversary) both).mp
        hbothMapped
  have hencodingSupport : cappedBothEncodingProjection both ∈ support
      (cappedDetailedGameWithEncodingTrace adversary) := by
    rw [← cappedDetailedGameWithKeygenCacheAndBothTraces_encodingProjection_eq,
      support_map]
    exact ⟨both, hboth, rfl⟩
  unfold SourceWinningExactFirstLaneEvent at hevent
  unfold WinningExactFirstLaneBadEventOccurs at hevent
  rcases hevent with hencoding | hchain
  · have hhit := cappedExactEncodingBranch_implies_monitorHit adversary
      (cappedBothEncodingProjection both) hencodingSupport hencoding
    have hbothExecution :=
      cappedDetailedGameWithKeygenCacheAndBothTraces_support_execution
        adversary both hboth
    have hlogs := cappedDetailedGameAfterKeygenWithBothTraces_logs_eq
      adversary both.1.1.1 both.1.1.2 both.1.2 both.2 hbothExecution
    have hvalidBoth : SigningTranscript.Valid
        both.2.2.2.toSigningLog := by
      rw [← hlogs]
      exact hencoding.1.signingTranscript_valid
    have hvalidLeft : SigningTranscript.Valid
        left.2.2.2.toSigningLog := by
      simpa [both, sourceGlobalExactProgramResult,
        sourceGlobalExactExecutionResult] using hvalidBoth
    apply globalHighExactEncodingEvent_implies_combinedHit
      (appendGlobalFirstLaneExactPublicTrace
        (globalFirstLaneExactCoupledProjection right)).1
      left.2.2.1.2 left.2.2.2
      (appendGlobalFirstLaneExactPublicTrace
        (globalFirstLaneExactCoupledProjection right)).2.2
    · simpa [appendGlobalFirstLaneExactPublicTrace,
        globalFirstLaneExactCoupledProjection, liftGlobalChainTrace,
        FirstLaneOracleSimulation.ActionTrace.encodingActions,
        FirstLaneOracleSimulation.ActionTrace.encodingActions_append] using
          hencodingSub
    · simpa [appendGlobalFirstLaneExactPublicTrace,
        globalFirstLaneExactCoupledProjection, liftGlobalChainTrace,
        FirstLaneOracleSimulation.ActionTrace.encodingActions,
        FirstLaneOracleSimulation.ActionTrace.encodingActions_append] using
          hvalidSub
    · exact hvalidLeft
    · simpa [both, cappedBothEncodingProjection,
        sourceGlobalExactProgramResult, sourceGlobalExactExecutionResult] using
          hhit
  · obtain ⟨chain, hwinning, hrevealed⟩ := hchain
    have hkeygen := cappedBothTraceGameResult_keyResult_mem_support
      adversary both hboth
    have hafter := cappedBothTraceGameResult_cacheExecution_mem_support
      adversary both hboth
    have horiginChain := chainValueRevealed_afterKeygen_has_origin adversary
      both.1 hkeygen (both.2.1, both.2.2.1.1.1) hafter chain hrevealed
    let leftOld := sourceGlobalExactErasedResult left
    let rightOld := highResult
    have hleftOld : leftOld ∈ support
        (sourceGlobalTracedProgram adversary) :=
      sourceGlobalExactErasedResult_mem_support adversary hleftSupport
    have hrightOld : rightOld ∈ support
        (globalHighMonitoredProgram adversary) :=
      hhighSupport
    have houtcome :=
      cappedDetailedGameWithKeygenCacheAndBothTraces_outcome_eq
        adversary both hboth
    have hwinningAction : WinningOutcomeBadEventOccurs
        (cappedBothActionProjection both).1.2.2
        (cappedBothActionProjection both).1.2.1 (.chain chain) := by
      rw [← houtcome]
      exact hwinning
    have horiginAction : OutcomeChainValueHasKeygenOrigin
        both.1.2 (cappedBothActionProjection both).1.2.2
        both.1.1.2 (cappedBothActionProjection both).1.2.1 chain := by
      rw [← houtcome]
      exact horiginChain
    have horiginOld : GlobalWinningOutcomeChainValueHasKeygenOrigin
        (eraseGlobalChainKeygenView (sourceGlobalProgramResult leftOld)).1.1.2
        (eraseGlobalChainKeygenView (sourceGlobalProgramResult leftOld)).1.2.2
        (eraseGlobalChainKeygenView (sourceGlobalProgramResult leftOld)).1.1.1.2
        (eraseGlobalChainKeygenView (sourceGlobalProgramResult leftOld)).1.2.1 := by
      refine ⟨chain, ?_, ?_⟩
      · simpa [leftOld, both, sourceGlobalExactErasedResult,
          sourceGlobalExactErasedExecution, sourceGlobalProgramResult,
          sourceGlobalExecutionResult, eraseGlobalChainKeygenView,
          cappedBothActionProjection, sourceGlobalExactProgramResult,
          sourceGlobalExactExecutionResult,
          ProgrammedGlobalChainKeygenView.keyResult,
          Concrete.materializeCachedKeyResult, Prod.eta] using hwinningAction
      · simpa [leftOld, both, sourceGlobalExactErasedResult,
          sourceGlobalExactErasedExecution, sourceGlobalProgramResult,
          sourceGlobalExecutionResult, eraseGlobalChainKeygenView,
          cappedBothActionProjection, sourceGlobalExactProgramResult,
          sourceGlobalExactExecutionResult,
          ProgrammedGlobalChainKeygenView.keyResult,
          Concrete.materializeCachedKeyResult, Prod.eta] using horiginAction
    have hobserved := sourceGlobal_origin_implies_right_publicObservedHit
      adversary leftOld rightOld hleftOld hrightOld hhighRelation horiginOld
    apply Or.inr
    unfold RevealProbeOracleSimulation.ObservedHit at hobserved
    have hpublic := globalHighMonitored_fullProjection_public_eq highResult
    rw [← hpublic, hprojection] at hobserved
    simpa [appendGlobalHighDirectExactPublicTrace,
      appendGlobalFirstLaneExactPublicTrace,
      globalFirstLaneExactCoupledProjection,
      FirstLaneOracleSimulation.ActionTrace.chainActions_append] using hobserved

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
    (adversary : Adversary)
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
    (adversary : Adversary)
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
    (adversary : Adversary) :
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
    (adversary : Adversary)
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
    (fuel : Nat) (adversary : Adversary) :
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
    (fuel : Nat) (adversary : Adversary) :
    Pr[GlobalFirstLaneExactPublicEnforcedHit fuel |
        globalFirstLaneExactPublicEagerExperiment adversary] ≤
      (fuel : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
  calc
    _ = Pr[FirstLaneOracleSimulation.ExperimentHit |
        FirstLaneOracleSimulation.enforceEagerResult fuel <$>
          FirstLaneOracleSimulation.eagerExperiment
            (globalFirstLaneExactTracedPublicProgram adversary)] := by
      unfold GlobalFirstLaneExactPublicEnforcedHit
        globalFirstLaneExactPublicEagerExperiment
      rw [probEvent_map]
      rfl
    _ = Pr[FirstLaneOracleSimulation.ExperimentHit |
        FirstLaneOracleSimulation.eagerExperiment
          (FirstLaneOracleSimulation.enforceHazardBound fuel
            (globalFirstLaneExactTracedPublicProgram adversary))] := by
      rw [FirstLaneOracleSimulation.eagerExperiment_enforceHazardBound_eq_map]
    _ = Pr[(fun hit : Bool => hit = true) |
        FirstLaneOracleSimulation.structuralExperiment
          (some EncodingMonitor.State.empty)
          AdaptiveRevealMonitor.State.empty fuel
          (FirstLaneOracleSimulation.enforceHazardBound fuel
            (globalFirstLaneExactTracedPublicProgram adversary))] := by
      exact FirstLaneOracleSimulation.combinedHit_probability_eq_structuralExperiment
        fuel (FirstLaneOracleSimulation.enforceHazardBound fuel
          (globalFirstLaneExactTracedPublicProgram adversary))
          (FirstLaneOracleSimulation.enforceHazardBound_isHazardQueryBoundP
            fuel (globalFirstLaneExactTracedPublicProgram adversary))
    _ ≤ _ := FirstLaneOracleSimulation.structuralExperiment_empty_true_probability_le
      fuel (FirstLaneOracleSimulation.enforceHazardBound fuel
        (globalFirstLaneExactTracedPublicProgram adversary))

theorem sourceWinningExactFirstLane_probability_le
    (q : Nat)
    (adversary : Adversary)
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
    (q : Nat) (adversary : Adversary)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    HasExactFirstLaneBound q adversary := by
  unfold HasExactFirstLaneBound
  rw [cappedExactFirstLane_probability_eq_sourceGlobalExact]
  exact sourceWinningExactFirstLane_probability_le q adversary hbound

theorem hasExactFirstLaneBounds : HasExactFirstLaneBounds := by
  intro q adversary hbound
  exact hasExactFirstLaneBound_of_hashQueryBound q adversary hbound

end XmssSecurity.CappedChain
