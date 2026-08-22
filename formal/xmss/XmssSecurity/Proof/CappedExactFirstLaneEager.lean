import XmssSecurity.Proof.CappedExactFirstLaneTransport
import XmssSecurity.Proof.CappedGlobalChainHighPublicProgram
import XmssSecurity.Proof.CappedGlobalChainHighActionTrace

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000
set_option linter.constructorNameAsVariable false

theorem map_globalHighMonitored_adversary_exact_query
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalMonitoredTracedState) :
    (fun result => ((result.1, GlobalHighDirectTracedState.mk
      result.2.1.causal result.2.2), result.2.1.trace)) <$>
        (globalHighMonitoredMappedAdversaryImpl
          ((keyView, base), edgeHigh) input).run state =
      (fun result : (((OracleWorld + SigningSpec).Range input ×
          GlobalHighDirectTracedState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.1.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          ((globalHighDirectTracedMappedAdversaryImpl keyView edgeHigh
            input).run (GlobalHighDirectTracedState.mk state.1.causal state.2))).run := by
  exact map_globalHighMonitored_adversary_full_query keyView base edgeHigh
    input state.1 state.2

theorem map_simulate_globalHighMonitored_exact_of_query
    {spec : OracleSpec ι}
    (table : GlobalChainValueIndex → Digest)
    (left : QueryImpl spec
      (StateT GlobalMonitoredTracedState ProbComp))
    (right : QueryImpl spec
      (StateT GlobalHighDirectTracedState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))))
    (hquery : ∀ (input : spec.Domain)
      (state : GlobalMonitoredTracedState),
      (fun result : spec.Range input × GlobalMonitoredTracedState =>
        ((result.1, GlobalHighDirectTracedState.mk result.2.1.causal result.2.2),
          result.2.1.trace)) <$>
          (left input).run state =
        (fun result : ((spec.Range input ×
            GlobalHighDirectTracedState) ×
            RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
          (result.1, state.1.trace ++ result.2)) <$>
          (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
            ((right input).run
              (GlobalHighDirectTracedState.mk state.1.causal state.2))).run)
    (computation : OracleComp spec α)
    (state : GlobalMonitoredTracedState) :
    (fun result : α × GlobalMonitoredTracedState =>
      ((result.1, GlobalHighDirectTracedState.mk result.2.1.causal result.2.2),
        result.2.1.trace)) <$>
        (simulateQ left computation).run state =
      (fun result : ((α × GlobalHighDirectTracedState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.1.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          ((simulateQ right computation).run
            (GlobalHighDirectTracedState.mk state.1.causal state.2))).run := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, StateT.run_bind, WriterT.run_bind', map_bind,
        simulateQ_spec_query]
      simp_rw [ih]
      let project := fun result :
          spec.Range input × GlobalMonitoredTracedState =>
        ((result.1, GlobalHighDirectTracedState.mk result.2.1.causal result.2.2),
          result.2.1.trace)
      let tail := fun head : ((spec.Range input ×
          GlobalHighDirectTracedState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (fun result => (result.1, head.2 ++ result.2)) <$>
          (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
            ((simulateQ right (next head.1.1)).run head.1.2)).run
      change (do
        let head ← (left input).run state
        tail (project head)) = _
      rw [← bind_map_left project]
      have hhead := hquery input state
      change project <$> (left input).run state = _ at hhead
      rw [hhead, bind_map_left]
      apply bind_congr
      intro head
      simp [tail, Functor.map_map, List.append_assoc]

theorem map_simulate_globalHighMonitored_adversary_exact
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : GlobalMonitoredTracedState) :
    (fun result : α × GlobalMonitoredTracedState =>
      ((result.1, GlobalHighDirectTracedState.mk result.2.1.causal result.2.2),
        result.2.1.trace)) <$>
        (simulateQ (globalHighMonitoredMappedAdversaryImpl
          ((keyView, base), edgeHigh)) computation).run state =
      (fun result : ((α × GlobalHighDirectTracedState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.1.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          ((simulateQ
            (globalHighDirectTracedMappedAdversaryImpl keyView edgeHigh)
            computation).run
              (GlobalHighDirectTracedState.mk state.1.causal state.2))).run := by
  apply map_simulate_globalHighMonitored_exact_of_query
  exact map_globalHighMonitored_adversary_exact_query keyView base edgeHigh

theorem map_simulate_globalHighMonitored_verifier_exact
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (computation : OracleComp OracleWorld α)
    (state : GlobalMonitoredTracedState) :
    (fun result : α × GlobalMonitoredTracedState =>
      ((result.1, GlobalHighDirectTracedState.mk result.2.1.causal result.2.2),
        result.2.1.trace)) <$>
        (simulateQ (globalHighMonitoredVerifierImpl
          ((keyView, base), edgeHigh)) computation).run state =
      (fun result : ((α × GlobalHighDirectTracedState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.1.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          ((simulateQ
            (globalHighDirectTracedVerifierImpl keyView edgeHigh)
            computation).run
              (GlobalHighDirectTracedState.mk state.1.causal state.2))).run := by
  exact map_simulate_globalHighMonitored_verifier_full_projection keyView
    base edgeHigh computation state.1 state.2

set_option maxHeartbeats 3000000 in
theorem map_globalHighMonitoredDetailedExecution_full_projection
    (adversary : Adversary)
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    (fun result : (Forgery × Bool) × GlobalMonitoredTracedState =>
      ((result.1, GlobalHighDirectTracedState.mk result.2.1.causal result.2.2),
        result.2.1.trace)) <$>
        globalHighMonitoredDetailedExecution adversary
          ((keyView, base), edgeHigh) =
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
        ((globalHighDirectTracedDetailedExecution adversary keyView
          edgeHigh).run (GlobalHighDirectTracedState.initial
            (globalFilteredCausalKeygenState keyView)))).run := by
  let initial : GlobalMonitoredTracedState :=
    (⟨globalFilteredCausalKeygenState keyView, []⟩, [])
  let project := fun result : Forgery × GlobalMonitoredTracedState =>
    ((result.1, GlobalHighDirectTracedState.mk result.2.1.causal result.2.2),
      result.2.1.trace)
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
          GlobalHighDirectTracedState.mk verified.2.1.causal verified.2.2),
            verified.2.1.trace)) = tail (project handled) := by
    have hvertifier :=
      map_simulate_globalHighMonitored_verifier_exact keyView
        base edgeHigh
        (Concrete.scheme.verify keyView.publicKey handled.1.epoch
          handled.1.message handled.1.signature) handled.2
    simpa [tail, project, Functor.map_map] using
      congrArg
      (fun candidate =>
        (fun result : ((Bool × GlobalHighDirectTracedState) ×
            RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
          (((handled.1, result.1.1), result.1.2), result.2)) <$>
          candidate)
        hvertifier
  unfold globalHighMonitoredDetailedExecution
    globalHighDirectTracedDetailedExecution
  simp only [map_bind, StateT.run_mk, simulateQ_bind, WriterT.run_bind',
    map_pure]
  simp_rw [htail]
  change (do
    let handled ← (simulateQ (globalHighMonitoredMappedAdversaryImpl
      ((keyView, base), edgeHigh))
        (adversary.main keyView.publicKey)).run initial
    tail (project handled)) = _
  rw [← bind_map_left project]
  have hhead :=
    map_simulate_globalHighMonitored_adversary_exact keyView
      base edgeHigh (adversary.main keyView.publicKey) initial
  change project <$>
    (simulateQ (globalHighMonitoredMappedAdversaryImpl
      ((keyView, base), edgeHigh))
        (adversary.main keyView.publicKey)).run initial = _ at hhead
  simp only [initial, List.nil_append] at hhead
  rw [hhead, bind_map_left]
  apply bind_congr
  intro head
  simp [tail]

def globalHighMonitoredFullProjection
    (result : GlobalHighMonitoredProgramResult) :
    (GlobalChainValueIndex → Digest) ×
      (GlobalExactTracedResult ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :=
  (result.1.1.2,
    (((result.1.1.1, result.1.2),
      (result.2.1, GlobalHighDirectTracedState.mk result.2.2.1.causal
        result.2.2.2)), result.2.2.1.trace))


def globalHighDirectExactTracedBaseProjection
    (result : GlobalExactTracedResult) : GlobalHighDirectResult :=
  (result.1, (result.2.1, result.2.2.causalState))

noncomputable def globalHighDirectExactForgeryPrimaryProbeTrace
    (result : GlobalExactTracedResult) :
    RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex :=
  globalHighDirectForgeryPrimaryProbeTrace
    (globalHighDirectExactTracedBaseProjection result)

noncomputable def appendGlobalHighDirectExactPublicTrace
    (result : (GlobalChainValueIndex → Digest) ×
      (GlobalExactTracedResult ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) :
    (GlobalChainValueIndex → Digest) ×
      (GlobalExactTracedResult ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :=
  (result.1, (result.2.1, result.2.2 ++
    globalHighDirectExactForgeryPrimaryProbeTrace result.2.1))


noncomputable def globalFirstLaneExactTracedPublicProgram
    (adversary : Adversary) :
    OracleComp GlobalFirstLaneWorld GlobalExactTracedResult := do
  let result ← globalFirstLaneExactTracedProgram adversary
  let _ ← globalFirstLaneLiftRevealProbe
    (RevealProbeOracleSimulation.emitObservedTrace
      (globalHighDirectExactForgeryPrimaryProbeTrace result))
  pure result


theorem globalHighDirectExactForgeryPrimaryProbeTrace_agrees
    (table : GlobalChainValueIndex → Digest)
    (result : GlobalExactTracedResult) :
    RevealProbeOracleSimulation.TraceAgrees table
      (globalHighDirectExactForgeryPrimaryProbeTrace result) := by
  unfold globalHighDirectExactForgeryPrimaryProbeTrace
  exact globalHighDirectForgeryPrimaryProbeTrace_agrees table _


theorem globalHighMonitored_fullProjection_public_eq
    (result : GlobalHighMonitoredProgramResult) :
    let projected := appendGlobalHighDirectExactPublicTrace
      (globalHighMonitoredFullProjection result)
    (projected.1, ((), projected.2.2)) =
      globalHighMonitoredPublicProjection result := by
  rw [globalHighMonitoredPublicProjection_eq_append_direct]
  rfl

theorem globalHighExactEncodingEvent_implies_combinedHit
    (table : GlobalChainValueIndex → Digest)
    (encodingTrace : EncodingActionTrace)
    (attackerTrace : AttackerActionTrace)
    (trace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hencodingSub : List.Sublist encodingTrace trace.encodingActions)
    (hvalidSub : List.Sublist
      (CappedEncodingMonitor.validObservedSignEpochs
        trace.encodingActions)
      (attackerTrace.toSigningLog.map
        fun entry => entry.1.epoch))
    (hvalid : SigningTranscript.Valid attackerTrace.toSigningLog)
    (hhit : CappedEncodingMonitor.runObserved EncodingMonitor.State.empty
      encodingTrace = true) :
    FirstLaneOracleSimulation.CombinedHit table trace := by
  apply Or.inl
  have hnodup :
      (CappedEncodingMonitor.validObservedSignEpochs
        trace.encodingActions).Nodup := by
    exact hvalidSub.nodup hvalid
  exact CappedEncodingMonitor.runObserved_empty_eq_true_mono_sublist
    hencodingSub hnodup hhit

abbrev GlobalFirstLaneExactPublicEagerResult :=
  (GlobalChainValueIndex → Digest) ×
    (GlobalExactTracedResult ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)


noncomputable def globalFirstLaneExactPublicEagerExperiment
    (adversary : Adversary) :
    ProbComp GlobalFirstLaneExactPublicEagerResult :=
  FirstLaneOracleSimulation.eagerExperiment
    (globalFirstLaneExactTracedPublicProgram adversary)


end XmssSecurity.CappedChain
