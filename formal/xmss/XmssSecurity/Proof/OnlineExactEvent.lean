import XmssSecurity.Proof.OnlineExactProjection
import XmssSecurity.Proof.FirstLaneEagerSimulation

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

def onlineGlobalHighDirectResult
    (result : OnlineGlobalHighExactProgramResult) : GlobalHighDirectResult :=
  ((result.1.1.1, result.1.2),
    (result.2.1, result.2.2.high.1.causal))

noncomputable def onlineForgeryPrimaryProbeTrace
    (result : OnlineGlobalHighExactProgramResult) :
    RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex :=
  globalHighDirectForgeryPrimaryProbeTrace
    (onlineGlobalHighDirectResult result)

def OnlineGlobalHighExactFirstLaneEvent
    (result : OnlineGlobalHighExactProgramResult) : Prop :=
  result.2.2.encoding.hit = true ∨
    (result.2.2.high.1.monitor.bind fun monitor =>
      RevealProbeOracleSimulation.advanceObserved result.1.1.2 monitor
        (onlineForgeryPrimaryProbeTrace result)) = none

noncomputable def oldOnlineFirstLaneTrace
    (result : GlobalHighExactMonitoredProgramResult) :
    FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex :=
  result.2.2.2.map (fun action =>
    FirstLaneOracleSimulation.ObservedAction.encoding
      (Index := GlobalChainValueIndex) action) ++
    (result.2.2.1.1.trace ++ globalHighDirectForgeryPrimaryProbeTrace
      ((result.1.1.1, result.1.2),
        (result.2.1, result.2.2.1.1.causal))).map
        FirstLaneOracleSimulation.ObservedAction.chain

@[simp] theorem encodingActions_map_encoding
    (trace : EncodingActionTrace) :
    FirstLaneOracleSimulation.ActionTrace.encodingActions
      (trace.map (fun action =>
        FirstLaneOracleSimulation.ObservedAction.encoding
          (Index := GlobalChainValueIndex) action)) = trace := by
  induction trace with
  | nil => rfl
  | cons action trace ih => simp [FirstLaneOracleSimulation.ActionTrace.encodingActions]

@[simp] theorem encodingActions_map_chain
    (trace : RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :
    FirstLaneOracleSimulation.ActionTrace.encodingActions
      (trace.map FirstLaneOracleSimulation.ObservedAction.chain) = [] := by
  induction trace with
  | nil => rfl
  | cons action trace ih => simp [FirstLaneOracleSimulation.ActionTrace.encodingActions]

@[simp] theorem chainActions_map_encoding
    (trace : EncodingActionTrace) :
    FirstLaneOracleSimulation.ActionTrace.chainActions
      (trace.map (fun action =>
        FirstLaneOracleSimulation.ObservedAction.encoding
          (Index := GlobalChainValueIndex) action)) = [] := by
  induction trace with
  | nil => rfl
  | cons action trace ih => simp [FirstLaneOracleSimulation.ActionTrace.chainActions]

@[simp] theorem chainActions_map_chain
    (trace : RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :
    FirstLaneOracleSimulation.ActionTrace.chainActions
      (trace.map FirstLaneOracleSimulation.ObservedAction.chain) = trace := by
  induction trace with
  | nil => rfl
  | cons action trace ih => simp [FirstLaneOracleSimulation.ActionTrace.chainActions]

@[simp] theorem oldOnlineFirstLaneTrace_encodingActions
    (result : GlobalHighExactMonitoredProgramResult) :
    (oldOnlineFirstLaneTrace result).encodingActions = result.2.2.2 := by
  simp [oldOnlineFirstLaneTrace,
    FirstLaneOracleSimulation.ActionTrace.encodingActions_append]

@[simp] theorem oldOnlineFirstLaneTrace_chainActions
    (result : GlobalHighExactMonitoredProgramResult) :
    (oldOnlineFirstLaneTrace result).chainActions =
      result.2.2.1.1.trace ++ globalHighDirectForgeryPrimaryProbeTrace
        ((result.1.1.1, result.1.2),
          (result.2.1, result.2.2.1.1.causal)) := by
  simp [oldOnlineFirstLaneTrace,
    FirstLaneOracleSimulation.ActionTrace.chainActions_append]

theorem onlineForgeryPrimaryProbeTrace_projection
    (result : GlobalHighExactMonitoredProgramResult) :
    onlineForgeryPrimaryProbeTrace
        (onlineGlobalHighExactProgramResultOf result) =
      globalHighDirectForgeryPrimaryProbeTrace
        ((result.1.1.1, result.1.2),
          (result.2.1, result.2.2.1.1.causal)) := by
  rfl

theorem onlineFirstLaneEvent_projection_iff
    (result : GlobalHighExactMonitoredProgramResult)
    (hconsistent : result.2.2.1.1.TraceConsistent result.1.1.2) :
    OnlineGlobalHighExactFirstLaneEvent
        (onlineGlobalHighExactProgramResultOf result) ↔
      FirstLaneOracleSimulation.CombinedHit result.1.1.2
        (oldOnlineFirstLaneTrace result) := by
  unfold OnlineGlobalHighExactFirstLaneEvent
    FirstLaneOracleSimulation.CombinedHit
  rw [oldOnlineFirstLaneTrace_encodingActions,
    oldOnlineFirstLaneTrace_chainActions]
  have hencoding :
      (onlineGlobalHighExactProgramResultOf result).2.2.encoding.hit =
        CappedEncodingMonitor.runObserved EncodingMonitor.State.empty
          result.2.2.2 := by
    exact CappedEncodingMonitor.OnlineState.observeAll_initial_hit result.2.2.2
  have hchain :
      ((onlineGlobalHighExactProgramResultOf result).2.2.high.1.monitor.bind
        fun monitor => RevealProbeOracleSimulation.advanceObserved
          result.1.1.2 monitor
            (onlineForgeryPrimaryProbeTrace
              (onlineGlobalHighExactProgramResultOf result))) = none ↔
      RevealProbeOracleSimulation.runObserved result.1.1.2
        AdaptiveRevealMonitor.State.empty
          (result.2.2.1.1.trace ++ globalHighDirectForgeryPrimaryProbeTrace
            ((result.1.1.1, result.1.2),
              (result.2.1, result.2.2.1.1.causal))) = true := by
    rw [onlineForgeryPrimaryProbeTrace_projection]
    change (result.2.2.1.1.monitor.bind fun monitor =>
      RevealProbeOracleSimulation.advanceObserved result.1.1.2 monitor _) =
        none ↔ _
    rw [hconsistent, ← RevealProbeOracleSimulation.advanceObserved_append,
      RevealProbeOracleSimulation.advanceObserved_eq_none_iff_runObserved_eq_true]
  rw [hencoding]
  simpa [onlineGlobalHighExactProgramResultOf] using
    (or_congr Iff.rfl hchain)

theorem globalHighExactMonitoredProgram_support_traceConsistent
    (adversary : Adversary Concrete.scheme)
    (result : GlobalHighExactMonitoredProgramResult)
    (hresult : result ∈ support
      (globalHighExactMonitoredProgram adversary)) :
    result.2.2.1.1.TraceConsistent result.1.1.2 := by
  have herased := globalHighExactErasedResult_mem_support adversary hresult
  obtain ⟨_hrightKey, hexecution⟩ :=
    globalHighMonitoredProgram_support_info adversary
      (globalHighExactErasedResult result) herased
  exact globalHighMonitoredDetailedExecution_traceConsistent adversary
    result.1 (result.2.1, result.2.2.1) hexecution

set_option maxRecDepth 1000000 in
theorem sourceWinningExactFirstLane_implies_onlineEvent
    (adversary : Adversary Concrete.scheme)
    (left : SourceGlobalExactTracedProgramResult)
    (right : OnlineGlobalHighExactProgramResult)
    (hleftSupport : left ∈ support
      (sourceGlobalExactTracedProgram adversary))
    (hrightSupport : right ∈ support
      (onlineGlobalHighExactProgram adversary))
    (hrel : SourceOnlineGlobalHighExactProgramRelation left right)
    (hevent : SourceWinningExactFirstLaneEvent left) :
    OnlineGlobalHighExactFirstLaneEvent right := by
  rw [← globalHighExactMonitoredProgram_online_projection,
    support_map] at hrightSupport
  obtain ⟨oldRight, holdRightSupport, rfl⟩ := hrightSupport
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
  have hconsistent := globalHighExactMonitoredProgram_support_traceConsistent
    adversary oldRight holdRightSupport
  unfold SourceWinningExactFirstLaneEvent at hevent
  unfold WinningExactFirstLaneBadEventOccurs at hevent
  rcases hevent with hencoding | hchain
  · have hhit := cappedExactEncodingBranch_implies_monitorHit adversary
      (cappedBothEncodingProjection both) hencodingSupport hencoding
    rcases hrel.2 with hgood | hbad
    · apply Or.inl
      rw [hgood.2.2]
      rw [CappedEncodingMonitor.OnlineState.observeAll_initial_hit]
      simpa [both, cappedBothEncodingProjection,
        sourceGlobalExactProgramResult, sourceGlobalExactExecutionResult]
        using hhit
    · rcases hbad with hchainBad | hencodingBad
      · apply Or.inr
        change (oldRight.2.2.1.1.monitor.bind fun monitor =>
          RevealProbeOracleSimulation.advanceObserved oldRight.1.1.2 monitor
            _) = none
        change oldRight.2.2.1.1.monitor = none at hchainBad
        rw [hchainBad]
        rfl
      · exact Or.inl hencodingBad
  · rcases hrel.2 with hgood | hbad
    · obtain ⟨chain, hwinning, hrevealed⟩ := hchain
      have hkeygen := cappedBothTraceGameResult_keyResult_mem_support
        adversary both hboth
      have hafter := cappedBothTraceGameResult_cacheExecution_mem_support
        adversary both hboth
      have horiginChain := chainValueRevealed_afterKeygen_has_origin adversary
        both.1 hkeygen (both.2.1, both.2.2.1.1.1) hafter chain hrevealed
      let leftOld := sourceGlobalExactErasedResult left
      let rightOld := globalHighExactErasedResult oldRight
      have hleftOld : leftOld ∈ support
          (sourceGlobalTracedProgram adversary) :=
        sourceGlobalExactErasedResult_mem_support adversary hleftSupport
      have hrightOld : rightOld ∈ support
          (globalHighMonitoredProgram adversary) :=
        globalHighExactErasedResult_mem_support adversary holdRightSupport
      have hrelOld : SourceGlobalHighMonitoredProgramRelation leftOld
          rightOld := by
        refine ⟨hrel.1, Or.inl ⟨hgood.1, ?_⟩, hconsistent⟩
        simpa [leftOld, rightOld, sourceGlobalExactErasedResult,
          sourceGlobalExactErasedExecution, globalHighExactErasedResult,
          GlobalMonitoredTracedStateRelation,
          OnlineGlobalSigningMonitoredStateRelation,
          OnlineGlobalMonitoredTracedStateRelation,
          GlobalMonitoredFilteredStateRelation,
          OnlineMonitoredFilteredStateRelation,
          sourceExactSigningProjection,
          sourceSigningTracedStateProjection,
          onlineGlobalHighExactProgramResultOf,
          onlineGlobalHighExactExecutionOf, onlineGlobalHighExactStateOf,
          onlineGlobalMonitoredTracedStateOf,
          onlineMonitoredCausalStateOf] using hgood.2.1
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
          (eraseGlobalChainKeygenView
            (sourceGlobalProgramResult leftOld)).1.1.2
          (eraseGlobalChainKeygenView
            (sourceGlobalProgramResult leftOld)).1.2.2
          (eraseGlobalChainKeygenView
            (sourceGlobalProgramResult leftOld)).1.1.1.2
          (eraseGlobalChainKeygenView
            (sourceGlobalProgramResult leftOld)).1.2.1 := by
        refine ⟨chain, ?_, ?_⟩
        · simpa [leftOld, both, sourceGlobalExactErasedResult,
            sourceGlobalExactErasedExecution, sourceGlobalProgramResult,
            sourceGlobalExecutionResult, eraseGlobalChainKeygenView,
            cappedBothActionProjection, sourceGlobalExactProgramResult,
            sourceGlobalExactExecutionResult,
            ProgrammedGlobalChainKeygenView.keyResult,
            Concrete.materializeCachedKeyResult, Prod.eta] using
              hwinningAction
        · simpa [leftOld, both, sourceGlobalExactErasedResult,
            sourceGlobalExactErasedExecution, sourceGlobalProgramResult,
            sourceGlobalExecutionResult, eraseGlobalChainKeygenView,
            cappedBothActionProjection, sourceGlobalExactProgramResult,
            sourceGlobalExactExecutionResult,
            ProgrammedGlobalChainKeygenView.keyResult,
            Concrete.materializeCachedKeyResult, Prod.eta] using
              horiginAction
      have hhit := sourceGlobal_origin_implies_right_publicObservedHit
        adversary leftOld rightOld hleftOld hrightOld hrelOld horiginOld
      apply (onlineFirstLaneEvent_projection_iff oldRight hconsistent).2
      apply Or.inr
      unfold RevealProbeOracleSimulation.ObservedHit at hhit
      dsimp only [globalHighMonitoredPublicProjection] at hhit
      simpa [oldOnlineFirstLaneTrace,
        globalHighMonitored_forgeryProbeTrace_eq_direct, rightOld,
        globalHighExactErasedResult, globalHighMonitoredDirectProjection]
        using hhit
    · rcases hbad with hchainBad | hencodingBad
      · apply Or.inr
        change (oldRight.2.2.1.1.monitor.bind fun monitor =>
          RevealProbeOracleSimulation.advanceObserved oldRight.1.1.2 monitor
            _) = none
        change oldRight.2.2.1.1.monitor = none at hchainBad
        rw [hchainBad]
        rfl
      · exact Or.inl hencodingBad

end XmssSecurity.CappedChain
