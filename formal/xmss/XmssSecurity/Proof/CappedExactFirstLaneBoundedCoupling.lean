import XmssSecurity.Proof.CappedExactFirstLaneAccounting
import XmssSecurity.Proof.CappedGlobalChainHighActionTrace
import XmssSecurity.Proof.CappedExactFirstLaneEager
import XmssSecurity.Proof.FirstLaneEagerBound
import XmssSecurity.Proof.MarginalCoupling
import XmssSecurity.Proof.StateLens
import XmssSecurity.Proof.BoundedFirstLaneCoupling
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000

theorem verifierHashQueryCost_eq_if (input : OracleWorld.Domain) :
    verifierHashQueryCost input =
      (if input matches .inr _ then 1 else 0) := by
  rcases input with n | hashInput <;> rfl

def globalFirstLaneExactFullProjection {α : Type}
    (chainPrefix : RevealProbeOracleSimulation.ActionTrace
      GlobalChainValueIndex)
    (result : (α × GlobalHighDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex) :
    (α × GlobalHighDirectTracedState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex :=
  (result.1, chainPrefix ++ result.2.chainActions)

theorem map_eagerTrace_erasure_eq {α : Type}
    (base : GlobalChainValueIndex → Digest)
    (chainPrefix : RevealProbeOracleSimulation.ActionTrace
      GlobalChainValueIndex)
    (firstLane : OracleComp GlobalFirstLaneWorld
      (α × GlobalHighDirectTracedState))
    (direct : OracleComp
      (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (α × GlobalHighDirectTracedState))
    (herase : GlobalFirstLaneErases firstLane direct) :
    (fun result => (result.1, chainPrefix ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          direct).run =
      globalFirstLaneExactFullProjection chainPrefix <$>
        (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base)
          firstLane).run := by
  have htarget :=
    simulate_globalFirstLaneEagerTrace_chainProjection base firstLane
  rw [herase] at htarget
  have htarget' := congrArg
    (fun computation =>
      (fun result => (result.1, chainPrefix ++ result.2)) <$> computation)
    htarget
  unfold globalFirstLaneExactFullProjection
  simpa [Functor.map_map, Function.comp_def] using htarget'.symm

theorem map_globalHighMonitored_action_eq_firstLane
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (highState : GlobalMonitoredTracedState) :
    (fun result => ((result.1, GlobalHighDirectTracedState.mk
      result.2.1.causal result.2.2), result.2.1.trace)) <$>
        (globalHighMonitoredMappedAdversaryImpl
          ((keyView, base), edgeHigh) input).run highState =
      globalFirstLaneExactFullProjection highState.1.trace <$>
        (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base)
          ((globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh
            input).run (GlobalHighDirectTracedState.mk highState.1.causal
              highState.2))).run := by
  have hhigh := map_globalHighMonitored_adversary_exact_query keyView base
    edgeHigh input highState
  have herase := globalFirstLaneErase_exactTracedMappedAdversaryImpl keyView
    edgeHigh input
      (GlobalHighDirectTracedState.mk highState.1.causal highState.2)
  rw [hhigh]
  exact map_eagerTrace_erasure_eq base highState.1.trace _ _ herase

theorem relTriple_globalHighMonitored_firstLane_action
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (highState : GlobalMonitoredTracedState) :
    RelTriple
      ((globalHighMonitoredMappedAdversaryImpl
        ((keyView, base), edgeHigh) input).run highState)
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base)
        ((globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh
          input).run (GlobalHighDirectTracedState.mk highState.1.causal
            highState.2))).run)
      (fun highResult firstLaneResult =>
        ((highResult.1, GlobalHighDirectTracedState.mk
            highResult.2.1.causal highResult.2.2),
            highResult.2.1.trace) =
          globalFirstLaneExactFullProjection highState.1.trace
            firstLaneResult ∧
        highResult ∈ support
          ((globalHighMonitoredMappedAdversaryImpl
            ((keyView, base), edgeHigh) input).run highState) ∧
        firstLaneResult ∈ support
          ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base)
            ((globalFirstLaneExactTracedMappedAdversaryImpl keyView edgeHigh
              input).run (GlobalHighDirectTracedState.mk highState.1.causal
                highState.2))).run)) := by
  classical
  letI : DecidableEq
      (((OracleWorld + SigningSpec).Range input ×
        GlobalHighDirectTracedState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :=
    Classical.decEq _
  apply relTriple_of_evalDist_map_eq_with_support_general
  exact congrArg evalDist
    (map_globalHighMonitored_action_eq_firstLane keyView base edgeHigh input
      highState)

def SourceFirstLaneExactGoodStateRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftState : SourceExactTracedState)
    (firstLaneState : GlobalHighDirectTracedState)
    (trace : FirstLaneOracleSimulation.ActionTrace
      GlobalChainValueIndex) : Prop :=
  ∃ highState : GlobalMonitoredTracedState,
    GlobalSigningMonitoredTracedStateRelation left right
      (sourceExactSigningProjection leftState) highState ∧
    firstLaneState = GlobalHighDirectTracedState.mk
      highState.1.causal highState.2 ∧
    trace.chainActions = highState.1.trace ∧
    highState.1.TraceConsistent right.2 ∧
    List.Sublist leftState.1.2 trace.encodingActions ∧
    List.Sublist
      (CappedEncodingMonitor.validObservedSignEpochs trace.encodingActions)
      (highState.2.toSigningLog.map fun entry => entry.1.epoch)

theorem SourceFirstLaneExactGoodStateRelation.validSignEpochs_sublist
    (hrelation : SourceFirstLaneExactGoodStateRelation left right leftState
      firstLaneState trace) :
    List.Sublist
      (CappedEncodingMonitor.validObservedSignEpochs trace.encodingActions)
      (firstLaneState.attackerTrace.toSigningLog.map
        fun entry => entry.1.epoch) := by
  rcases hrelation with ⟨highState, _hsource, hfirstLane, _hchain,
    _hconsistent, _hencoding, hvalidEpochs⟩
  rw [hfirstLane]
  exact hvalidEpochs

theorem cappedBothTracedMappedAdversaryImpl_support_unlogged_output
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : SourceExactTracedState)
    (result : (OracleWorld + SigningSpec).Range input ×
      SourceExactTracedState)
    (hresult : result ∈ support
      ((cappedBothTracedMappedAdversaryImpl publicKey secretKey input).run
        state)) :
    result.1 ∈ support
      (sourceUnloggedMappedAdversaryImpl publicKey secretKey input) := by
  rw [cappedBothTracedMappedAdversaryImpl_query_eq_sourceExactMap,
    support_map] at hresult
  obtain ⟨signingResult, hsigning, rfl⟩ := hresult
  have hdirect : (signingResult.1,
      sourceSigningTracedStateProjection signingResult.2) ∈ support
      ((sourceDirectTracedMappedAdversaryImpl publicKey secretKey input).run
        (sourceSigningTracedStateProjection
          (sourceExactSigningProjection state))) := by
    rw [← sourceSigningTracedMappedAdversaryImpl_query_projection,
      support_map]
    exact ⟨signingResult, hsigning, rfl⟩
  exact (sourceDirectTracedMappedAdversaryImpl_support_info publicKey
    secretKey input
      (sourceSigningTracedStateProjection
        (sourceExactSigningProjection state))
      (signingResult.1,
        sourceSigningTracedStateProjection signingResult.2) hdirect).1


theorem relTriple_sourceExact_firstLane_action
    (used : Nat)
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (input : (OracleWorld + SigningSpec).Domain)
    (leftState : SourceExactTracedState)
    (firstLaneState : GlobalHighDirectTracedState)
    (trace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hstate : SourceFirstLaneExactGoodStateRelation left right.1 leftState
      firstLaneState trace)
    (hcount : FirstLaneOracleSimulation.hazardCount trace ≤ used) :
    RelTriple
      ((cappedBothTracedMappedAdversaryImpl left.publicKey
        (Concrete.materializePrecomputation left.cache left.secretKey)
          input).run leftState)
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
        ((globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2
          input).run firstLaneState)).run)
      (fun leftResult firstLaneResult =>
        (leftResult.1 = firstLaneResult.1.1 ∧
          SourceFirstLaneExactGoodStateRelation left right.1 leftResult.2
            firstLaneResult.1.2 (trace ++ firstLaneResult.2) ∧
          FirstLaneOracleSimulation.hazardCount
              (trace ++ firstLaneResult.2) ≤
            used + directHashActionCost input ∧
          leftResult.2.2.hashInputs.length =
            leftState.2.hashInputs.length + directHashActionCost input) ∨
        (FirstLaneOracleSimulation.CombinedHit right.1.2
            (trace ++ firstLaneResult.2) ∧
          FirstLaneOracleSimulation.hazardCount
              (trace ++ firstLaneResult.2) ≤
            used + directHashActionCost input)) := by
  rcases hstate with ⟨highState, hsourceHigh, hfirstLaneState,
    hchainTrace, hconsistent, hencodingTrace, hvalidEpochs⟩
  subst firstLaneState
  have hsource :=
    relTriple_programmed_globalHighMonitored_sourceExact_action left right hrel
      hleftSupport hrightSupport leftState highState hsourceHigh input
  have hhigh := relTriple_globalHighMonitored_firstLane_action
    right.1.1 right.1.2 right.2 input highState
  apply relTriple_post_mono (relTriple_trans_exists hsource hhigh)
  intro leftResult firstLaneResult hglued
  obtain ⟨highResult, hsourceResult, hhighResult⟩ := hglued
  obtain ⟨hprojection, hhighSupport, hfirstLaneSupport⟩ := hhighResult
  have hfragmentCount : FirstLaneOracleSimulation.hazardCount
      firstLaneResult.2 ≤ directHashActionCost input :=
    FirstLaneOracleSimulation.simulate_eagerTrace_support_hazardCount_le
      right.1.2
      ((globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2
        input).run (GlobalHighDirectTracedState.mk highState.1.causal
          highState.2))
      (directHashActionCost input)
      (globalFirstLaneExactTracedMappedAdversaryImpl_hazardBound right.1.1
        right.2 input (GlobalHighDirectTracedState.mk highState.1.causal
          highState.2))
      firstLaneResult hfirstLaneSupport
  have htotalCount : FirstLaneOracleSimulation.hazardCount
      (trace ++ firstLaneResult.2) ≤
        used + directHashActionCost input := by
    rw [FirstLaneOracleSimulation.hazardCount_append]
    omega
  have hnextConsistent :=
    globalHighMonitoredMappedAdversaryImpl_preserves_traceConsistent
      right input highState hconsistent highResult hhighSupport
  have hhighActionTrace :=
    globalHighMonitoredMappedAdversaryImpl_support_actionTrace_eq right
      input highState highResult hhighSupport
  have hfirstLaneEncodingSub :=
    globalFirstLaneExactTracedMappedAdversaryImpl_query_trace_sublist
      right.1.2 right.1.1 right.2 input
        (GlobalHighDirectTracedState.mk highState.1.causal highState.2)
          leftState.1.2 firstLaneResult hfirstLaneSupport
  have houtputProjection : highResult.1 = firstLaneResult.1.1 :=
    congrArg (fun result => result.1.1) hprojection
  have hcausalProjection : highResult.2.1.causal =
      firstLaneResult.1.2.causalState := by
    exact congrArg (fun result => result.1.2.causalState) hprojection
  have hfragmentValid :=
    globalFirstLaneExactTracedMappedAdversary_validSignEpochs_sublist
      right.1.2 right.1.1 right.2 (liftM (OracleSpec.query input))
        (GlobalHighDirectTracedState.mk highState.1.causal highState.2)
          firstLaneResult
          (by simpa only [simulateQ_spec_query] using hfirstLaneSupport)
  have hattackerProjection : highResult.2.2 =
      firstLaneResult.1.2.attackerTrace := by
    exact congrArg (fun result => result.1.2.attackerTrace) hprojection
  have hnextValidEpochs : List.Sublist
      (CappedEncodingMonitor.validObservedSignEpochs
        (trace ++ firstLaneResult.2).encodingActions)
      (highResult.2.2.toSigningLog.map fun entry => entry.1.epoch) := by
    rw [FirstLaneOracleSimulation.ActionTrace.encodingActions_append,
      CappedEncodingMonitor.validObservedSignEpochs_append,
      hattackerProjection]
    exact (hvalidEpochs.append (List.Sublist.refl _)).trans hfragmentValid
  rcases hsourceResult with hgood | hbad
  · apply Or.inl
    refine ⟨hgood.1.trans ?_, ?_, htotalCount, ?_⟩
    · exact congrArg (fun result => result.1.1) hprojection
    · have hnextEncodingTrace : List.Sublist leftResult.2.1.2
          (trace ++ firstLaneResult.2).encodingActions := by
        rw [FirstLaneOracleSimulation.ActionTrace.encodingActions_append]
        rw [hgood.2.2, houtputProjection, hcausalProjection]
        exact hfirstLaneEncodingSub.trans
          (hencodingTrace.append (List.Sublist.refl _))
      refine ⟨highResult.2, hgood.2.1, ?_, ?_, hnextConsistent,
        hnextEncodingTrace, hnextValidEpochs⟩
      · exact congrArg (fun result => result.1.2) hprojection |>.symm
      · rw [FirstLaneOracleSimulation.ActionTrace.chainActions_append,
          hchainTrace]
        exact congrArg Prod.snd hprojection |>.symm
    · have hinitialTrace : leftState.2 = highState.2 := hsourceHigh.2
      have hfinalTrace : leftResult.2.2 = highResult.2.2 := hgood.2.1.2
      rw [hfinalTrace, hhighActionTrace, ← hinitialTrace,
        AttackerActionTrace.hashInputs_append, List.length_append,
        attackerActionFragment_hashInputs_length]
  · apply Or.inr
    have hchainProjection : highResult.2.1.trace =
        highState.1.trace ++ firstLaneResult.2.chainActions := by
      simpa [globalFirstLaneExactFullProjection] using
          congrArg Prod.snd hprojection
    have hchainHit : RevealProbeOracleSimulation.runObserved right.1.2
        AdaptiveRevealMonitor.State.empty
          (trace ++ firstLaneResult.2).chainActions = true := by
      rw [FirstLaneOracleSimulation.ActionTrace.chainActions_append,
        hchainTrace]
      rw [← hchainProjection]
      exact highResult.2.1.bad_implies_runObserved right.1.2
        hnextConsistent hbad
    have hhit : FirstLaneOracleSimulation.CombinedHit right.1.2
        (trace ++ firstLaneResult.2) := Or.inr hchainHit
    exact ⟨hhit, htotalCount⟩


def sourceExactVerifierResult
    (initialState : SourceExactTracedState)
    (result : OracleWorld.Range input × SourceSigningTracedState) :
    OracleWorld.Range input × SourceExactTracedState :=
  (result.1, ((result.2.1, initialState.1.2), result.2.2))

noncomputable def sourceExactTracedVerifierImpl : QueryImpl OracleWorld
    (StateT SourceExactTracedState ProbComp) := fun input =>
  StateT.mk fun state => sourceExactVerifierResult state <$>
    (sourceSigningTracedVerifierImpl input).run
      (sourceExactSigningProjection state)

theorem sourceExactTracedVerifierImpl_run_eq
    (computation : OracleComp OracleWorld α)
    (initialState : SourceExactTracedState) :
    (simulateQ sourceExactTracedVerifierImpl computation).run initialState =
      (fun result : α × SourceSigningTracedState =>
        (result.1, ((result.2.1, initialState.1.2), result.2.2))) <$>
        (simulateQ sourceSigningTracedVerifierImpl computation).run
          (sourceExactSigningProjection initialState) := by
  let lens : StateLens SourceExactTracedState SourceSigningTracedState :=
    ⟨sourceExactSigningProjection,
      fun state nextSigning => ((nextSigning.1, state.1.2), nextSigning.2),
      by
        intro state
        rcases state with ⟨⟨⟨cache, signingTrace⟩, encodingTrace⟩, actionTrace⟩
        rfl,
      by simp [sourceExactSigningProjection],
      by simp⟩
  apply lens.simulateQ_run_eq
  intro input state
  rfl

theorem relTriple_programmed_globalHighMonitored_sourceExact_verifier_action
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftState : SourceExactTracedState)
    (highState : GlobalMonitoredTracedState)
    (hstate : GlobalSigningMonitoredTracedStateRelation left right.1
      (sourceExactSigningProjection leftState) highState)
    (input : OracleWorld.Domain) :
    RelTriple
      ((sourceExactTracedVerifierImpl input).run leftState)
      ((globalHighMonitoredVerifierImpl right input).run highState)
      (fun leftResult highResult =>
        (leftResult.1 = highResult.1 ∧
          GlobalSigningMonitoredTracedStateRelation left right.1
            (sourceExactSigningProjection leftResult.2) highResult.2 ∧
          leftResult.2.1.2 = leftState.1.2) ∨
        highResult.2.1.bad) := by
  have hbase :=
    relTriple_programmed_globalHighMonitored_signingVerifierQuery left right
      hrel hleftSupport hrightSupport
        (sourceExactSigningProjection leftState) highState hstate input
  let enrich : OracleWorld.Range input × SourceSigningTracedState →
      OracleWorld.Range input × SourceExactTracedState :=
    sourceExactVerifierResult leftState
  have hlifted : RelTriple
      (enrich <$>
        (sourceSigningTracedVerifierImpl input).run
          (sourceExactSigningProjection leftState))
      (id <$> (globalHighMonitoredVerifierImpl right input).run highState)
      (fun leftResult highResult =>
        (leftResult.1 = highResult.1 ∧
          GlobalSigningMonitoredTracedStateRelation left right.1
            (sourceExactSigningProjection leftResult.2) highResult.2 ∧
          leftResult.2.1.2 = leftState.1.2) ∨
        highResult.2.1.bad) := by
    apply relTriple_map
    apply relTriple_post_mono hbase
    intro leftResult highResult hresult
    rcases hresult with hgood | hbad
    · exact Or.inl ⟨hgood.1, by
        simpa [enrich, sourceExactVerifierResult,
          sourceExactSigningProjection] using hgood.2, rfl⟩
    · exact Or.inr hbad
  rw [id_map] at hlifted
  have hleft : (sourceExactTracedVerifierImpl input).run leftState =
      enrich <$>
        (sourceSigningTracedVerifierImpl input).run
          (sourceExactSigningProjection leftState) := by rfl
  rw [hleft]
  exact hlifted

theorem map_globalHighMonitored_verifier_action_eq_firstLane
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : OracleWorld.Domain)
    (highState : GlobalMonitoredTracedState) :
    (fun result => ((result.1, GlobalHighDirectTracedState.mk
      result.2.1.causal result.2.2), result.2.1.trace)) <$>
        (globalHighMonitoredVerifierImpl
          ((keyView, base), edgeHigh) input).run highState =
      globalFirstLaneExactFullProjection highState.1.trace <$>
        (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base)
          ((globalFirstLaneExactTracedVerifierImpl keyView edgeHigh input).run
            (GlobalHighDirectTracedState.mk highState.1.causal
              highState.2))).run := by
  have hhigh := map_simulate_globalHighMonitored_verifier_exact keyView base
    edgeHigh (liftM (OracleWorld.query input)) highState
  simp only [simulateQ_spec_query] at hhigh
  have herase := globalFirstLaneErase_exactTracedVerifierImpl keyView edgeHigh
    input (GlobalHighDirectTracedState.mk highState.1.causal highState.2)
  rw [hhigh]
  exact map_eagerTrace_erasure_eq base highState.1.trace _ _ herase

theorem relTriple_globalHighMonitored_firstLane_verifier_action
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (input : OracleWorld.Domain)
    (highState : GlobalMonitoredTracedState) :
    RelTriple
      ((globalHighMonitoredVerifierImpl
        ((keyView, base), edgeHigh) input).run highState)
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base)
        ((globalFirstLaneExactTracedVerifierImpl keyView edgeHigh input).run
          (GlobalHighDirectTracedState.mk highState.1.causal
            highState.2))).run)
      (fun highResult firstLaneResult =>
        ((highResult.1, GlobalHighDirectTracedState.mk
            highResult.2.1.causal highResult.2.2),
            highResult.2.1.trace) =
          globalFirstLaneExactFullProjection highState.1.trace
            firstLaneResult ∧
        highResult ∈ support
          ((globalHighMonitoredVerifierImpl
            ((keyView, base), edgeHigh) input).run highState) ∧
        firstLaneResult ∈ support
          ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base)
            ((globalFirstLaneExactTracedVerifierImpl keyView edgeHigh input).run
              (GlobalHighDirectTracedState.mk highState.1.causal
                highState.2))).run)) := by
  classical
  letI : DecidableEq
      ((OracleWorld.Range input × GlobalHighDirectTracedState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :=
    Classical.decEq _
  apply relTriple_of_evalDist_map_eq_with_support_general
  exact congrArg evalDist
    (map_globalHighMonitored_verifier_action_eq_firstLane keyView base
      edgeHigh input highState)

theorem relTriple_sourceExact_firstLane_verifier_action
    (used : Nat)
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (input : OracleWorld.Domain)
    (leftState : SourceExactTracedState)
    (firstLaneState : GlobalHighDirectTracedState)
    (trace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hstate : SourceFirstLaneExactGoodStateRelation left right.1 leftState
      firstLaneState trace)
    (hcount : FirstLaneOracleSimulation.hazardCount trace ≤ used) :
    RelTriple
      ((sourceExactTracedVerifierImpl input).run leftState)
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
        ((globalFirstLaneExactTracedVerifierImpl right.1.1 right.2 input).run
          firstLaneState)).run)
      (fun leftResult firstLaneResult =>
        (leftResult.1 = firstLaneResult.1.1 ∧
          SourceFirstLaneExactGoodStateRelation left right.1 leftResult.2
            firstLaneResult.1.2 (trace ++ firstLaneResult.2) ∧
          FirstLaneOracleSimulation.hazardCount
              (trace ++ firstLaneResult.2) ≤
            used + verifierHashQueryCost input) ∨
        (FirstLaneOracleSimulation.CombinedHit right.1.2
            (trace ++ firstLaneResult.2) ∧
          FirstLaneOracleSimulation.hazardCount
              (trace ++ firstLaneResult.2) ≤
            used + verifierHashQueryCost input)) := by
  rcases hstate with ⟨highState, hsourceHigh, hfirstLaneState,
    hchainTrace, hconsistent, hencodingTrace, hvalidEpochs⟩
  subst firstLaneState
  have hsource :=
    relTriple_programmed_globalHighMonitored_sourceExact_verifier_action
      left right
      hrel hleftSupport hrightSupport leftState highState hsourceHigh input
  have hhigh :=
    relTriple_globalHighMonitored_firstLane_verifier_action right.1.1
      right.1.2 right.2 input highState
  apply relTriple_post_mono (relTriple_trans_exists hsource hhigh)
  intro leftResult firstLaneResult hglued
  obtain ⟨highResult, hsourceResult, hhighResult⟩ := hglued
  obtain ⟨hprojection, hhighSupport, hfirstLaneSupport⟩ := hhighResult
  have hfragmentCount : FirstLaneOracleSimulation.hazardCount
      firstLaneResult.2 ≤ verifierHashQueryCost input := by
    apply FirstLaneOracleSimulation.simulate_eagerTrace_support_hazardCount_le
      right.1.2
      ((globalFirstLaneExactTracedVerifierImpl right.1.1 right.2 input).run
        (GlobalHighDirectTracedState.mk highState.1.causal highState.2))
      (verifierHashQueryCost input) _ firstLaneResult hfirstLaneSupport
    change ((globalFirstLaneExactTracedVerifierImpl right.1.1 right.2 input
      ).run (GlobalHighDirectTracedState.mk highState.1.causal
        highState.2)).IsQueryBoundP
        FirstLaneOracleSimulation.IsHazardQuery (verifierHashQueryCost input)
    rw [verifierHashQueryCost_eq_if]
    exact globalFirstLaneExactTracedVerifierImpl_hazardBound right.1.1
      right.2 input
        (GlobalHighDirectTracedState.mk highState.1.causal highState.2)
  have htotalCount : FirstLaneOracleSimulation.hazardCount
      (trace ++ firstLaneResult.2) ≤
        used + verifierHashQueryCost input := by
    rw [FirstLaneOracleSimulation.hazardCount_append]
    omega
  have hnextConsistent :=
    globalHighMonitoredVerifierImpl_preserves_traceConsistent right input
      highState hconsistent highResult hhighSupport
  have hfragmentValid :=
    globalFirstLaneExactTracedVerifier_validSignEpochs_eq_nil right.1.2
      right.1.1 right.2 (liftM (OracleSpec.query input))
        (GlobalHighDirectTracedState.mk highState.1.causal highState.2)
          firstLaneResult
          (by simpa only [simulateQ_spec_query] using hfirstLaneSupport)
  have hattackerProjection : highResult.2.2 =
      firstLaneResult.1.2.attackerTrace := by
    exact congrArg (fun result => result.1.2.attackerTrace) hprojection
  have hfirstAttacker : firstLaneResult.1.2.attackerTrace =
      highState.2 := by
    obtain ⟨baseResult, _hbase, hresultEq⟩ :=
      globalFirstLaneExactTracedVerifier_eager_support_decompose right.1.2
        right.1.1 right.2 (liftM (OracleSpec.query input))
          (GlobalHighDirectTracedState.mk highState.1.causal highState.2)
            firstLaneResult
            (by simpa only [simulateQ_spec_query] using hfirstLaneSupport)
    rw [hresultEq]
    rfl
  have hnextValidEpochs : List.Sublist
      (CappedEncodingMonitor.validObservedSignEpochs
        (trace ++ firstLaneResult.2).encodingActions)
      (highResult.2.2.toSigningLog.map fun entry => entry.1.epoch) := by
    rw [FirstLaneOracleSimulation.ActionTrace.encodingActions_append,
      CappedEncodingMonitor.validObservedSignEpochs_append,
      hfragmentValid, List.append_nil, hattackerProjection]
    rw [hfirstAttacker]
    exact hvalidEpochs
  rcases hsourceResult with hgood | hbad
  · apply Or.inl
    refine ⟨hgood.1.trans ?_, ?_, htotalCount⟩
    · exact congrArg (fun result => result.1.1) hprojection
    · have hnextEncodingTrace : List.Sublist leftResult.2.1.2
          (trace ++ firstLaneResult.2).encodingActions := by
        rw [FirstLaneOracleSimulation.ActionTrace.encodingActions_append,
          hgood.2.2]
        exact hencodingTrace.trans (List.sublist_append_left _ _)
      refine ⟨highResult.2, hgood.2.1, ?_, ?_, hnextConsistent,
        hnextEncodingTrace, hnextValidEpochs⟩
      · exact congrArg (fun result => result.1.2) hprojection |>.symm
      · rw [FirstLaneOracleSimulation.ActionTrace.chainActions_append,
          hchainTrace]
        exact congrArg Prod.snd hprojection |>.symm
  · apply Or.inr
    have hchainProjection : highResult.2.1.trace =
        highState.1.trace ++ firstLaneResult.2.chainActions := by
      simpa [globalFirstLaneExactFullProjection] using
          congrArg Prod.snd hprojection
    have hchainHit : RevealProbeOracleSimulation.runObserved right.1.2
        AdaptiveRevealMonitor.State.empty
          (trace ++ firstLaneResult.2).chainActions = true := by
      rw [FirstLaneOracleSimulation.ActionTrace.chainActions_append,
        hchainTrace, ← hchainProjection]
      exact highResult.2.1.bad_implies_runObserved right.1.2
        hnextConsistent hbad
    exact ⟨Or.inr hchainHit, htotalCount⟩

theorem relTriple_sourceExact_firstLane_verifier_boundedHit
    (countLimit hitLimit used fuel : Nat)
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (computation : OracleComp OracleWorld α)
    (hbound : computation.IsQueryBoundP (· matches .inr _) fuel)
    (leftState : SourceExactTracedState)
    (firstLaneState : GlobalHighDirectTracedState)
    (trace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hstate : SourceFirstLaneExactGoodStateRelation left right.1 leftState
      firstLaneState trace)
    (hcount : FirstLaneOracleSimulation.hazardCount trace ≤ used)
    (htotal : used + fuel ≤ countLimit)
    (hlimits : countLimit ≤ hitLimit) :
    RelTriple
      ((simulateQ sourceExactTracedVerifierImpl computation).run leftState)
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
        ((simulateQ
          (globalFirstLaneExactTracedVerifierImpl right.1.1 right.2)
          computation).run firstLaneState)).run)
      (fun leftResult firstLaneResult =>
        (leftResult.1 = firstLaneResult.1.1 ∧
          SourceFirstLaneExactGoodStateRelation left right.1 leftResult.2
            firstLaneResult.1.2 (trace ++ firstLaneResult.2) ∧
          FirstLaneOracleSimulation.hazardCount
              (trace ++ firstLaneResult.2) ≤ countLimit) ∨
        FirstLaneOracleSimulation.CombinedHit right.1.2
          (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
            (trace ++ firstLaneResult.2))) := by
  let leftFinish := fun (value : α) (state : SourceExactTracedState) =>
    (pure (value, state) : ProbComp (α × SourceExactTracedState))
  let rightFinish := fun (value : α) (state : GlobalHighDirectTracedState) =>
    (pure (value, state) : OracleComp GlobalFirstLaneWorld
      (α × GlobalHighDirectTracedState))
  have hgeneric := relTriple_simulateQ_bind_bounded_firstLane right.1.2
    sourceExactTracedVerifierImpl
    (globalFirstLaneExactTracedVerifierImpl right.1.1 right.2)
    leftFinish rightFinish verifierHashQueryCost
    (SourceFirstLaneExactGoodStateRelation left right.1)
    (fun _state _spent => True)
    (fun rest remaining =>
      rest.IsQueryBoundP (· matches .inr _) remaining)
    (by
      intro input next remaining _state _result hrest _hresult
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hrest
      rcases input with uniformInput | hashInput
      · exact ⟨by simp [verifierHashQueryCost], by
          simpa [verifierHashQueryCost] using hrest.2 _result.1⟩
      · exact ⟨by
          simp only [verifierHashQueryCost]
          exact Nat.succ_le_iff.2 (hrest.1.resolve_left (by simp)), by
          simpa [verifierHashQueryCost] using hrest.2 _result.1⟩)
    (by
      intro spent input state firstState history hstates hprefix _haccounted
      apply relTriple_post_mono
        (relTriple_sourceExact_firstLane_verifier_action spent left right hrel
          hleftSupport hrightSupport input state firstState history hstates
            hprefix)
      intro leftResult firstResult hresult
      rcases hresult with hgood | hhit
      · exact Or.inl ⟨hgood.1, hgood.2.1, hgood.2.2, True.intro⟩
      · exact Or.inr hhit)
    countLimit hitLimit
    (by
      intro value spent remaining state firstState history _hremaining hstates
        hprefix _haccounted htotal
      simp only [leftFinish, rightFinish, simulateQ_pure, WriterT.run_pure']
      apply relTriple_pure_pure
      exact Or.inl ⟨rfl, by simpa using hstates, by
        simpa using hprefix.trans (by omega : spent ≤ countLimit)⟩)
    used fuel computation hbound leftState firstLaneState trace hstate hcount
      True.intro htotal hlimits
  simpa [leftFinish, rightFinish] using hgeneric

def sourceAppendVerificationState
    (secretKey : SecretKey) (forgery : Forgery)
    (initialState finalState : SourceExactTracedState) :
    SourceExactTracedState :=
  ((finalState.1.1,
    appendVerificationEncodingObservation secretKey forgery
      initialState.1.1.1 finalState.1.1.1 finalState.1.2), finalState.2)

def firstLaneAppendVerificationState
    (_secretKey : SecretKey) (_forgery : Forgery)
    (_initialState finalState : GlobalHighDirectTracedState) :
    GlobalHighDirectTracedState :=
  finalState

theorem SourceFirstLaneExactGoodStateRelation.appendVerification
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (forgery : Forgery)
    (leftInitial leftFinal : SourceExactTracedState)
    (firstLaneInitial firstLaneFinal : GlobalHighDirectTracedState)
    (initialTrace finalTrace :
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hinitial : SourceFirstLaneExactGoodStateRelation left right.1
      leftInitial firstLaneInitial initialTrace)
    (hfinal : SourceFirstLaneExactGoodStateRelation left right.1
      leftFinal firstLaneFinal finalTrace)
    (happendSub : List.Sublist
      (appendVerificationEncodingObservation right.1.1.secretKey forgery
        firstLaneInitial.causalState.cache
          firstLaneFinal.causalState.cache leftFinal.1.2)
      finalTrace.encodingActions) :
    SourceFirstLaneExactGoodStateRelation left right.1
      (sourceAppendVerificationState
        (Concrete.materializePrecomputation left.cache left.secretKey)
          forgery leftInitial leftFinal)
      (firstLaneAppendVerificationState right.1.1.secretKey forgery
        firstLaneInitial firstLaneFinal) finalTrace := by
  rcases hinitial with ⟨highInitial, hsourceInitial, hfirstInitial,
    _hchainInitial, _hconsistentInitial, _hencodingInitial,
    _hvalidInitial⟩
  rcases hfinal with ⟨highFinal, hsourceFinal, hfirstFinal,
    hchainFinal, hconsistentFinal, hencodingFinal, hvalidFinal⟩
  subst firstLaneInitial
  subst firstLaneFinal
  obtain ⟨_monitorInitial, _hmonitorInitial, _hagreesInitial,
    _hrevealedInitial, hinitialCausal, _hretainedInitial⟩ :=
      hsourceInitial.1
  obtain ⟨_monitorFinal, _hmonitorFinal, _hagreesFinal,
    _hrevealedFinal, hfinalCausal, _hretainedFinal⟩ :=
      hsourceFinal.1
  let leftSecret :=
    Concrete.materializePrecomputation left.cache left.secretKey
  have hparameter := programmedGlobal_secretKey_parameter_eq left right hrel
    hleftSupport hrightSupport
  have happend :=
    appendVerificationEncodingObservation_eq_of_globalSigningCachesAgree
      leftSecret right.1.1.secretKey
      (by simpa [leftSecret, Concrete.materializePrecomputation,
        Concrete.precomputedSecretKey] using hparameter.symm)
      forgery leftInitial.1.1.1 highInitial.1.causal.cache
        leftFinal.1.1.1 highFinal.1.causal.cache
      (by simpa [leftSecret, Concrete.materializePrecomputation,
        Concrete.precomputedSecretKey, sourceSigningTracedStateProjection,
        sourceExactSigningProjection] using hinitialCausal.1)
      (by simpa [leftSecret, Concrete.materializePrecomputation,
        Concrete.precomputedSecretKey, sourceSigningTracedStateProjection,
        sourceExactSigningProjection] using hfinalCausal.1)
      leftFinal.1.2
  let nextEncodingTrace := appendVerificationEncodingObservation leftSecret
    forgery leftInitial.1.1.1 leftFinal.1.1.1 leftFinal.1.2
  refine ⟨highFinal, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [sourceAppendVerificationState, sourceExactSigningProjection] using
      hsourceFinal
  · rfl
  · exact hchainFinal
  · exact hconsistentFinal
  · change List.Sublist nextEncodingTrace finalTrace.encodingActions
    unfold nextEncodingTrace
    rw [happend]
    simpa [firstLaneAppendVerificationState] using happendSub
  · exact hvalidFinal

theorem relTriple_sourceExact_firstLane_detailedExecution_boundedHit
    (countLimit hitLimit : Nat)
    (adversary : Adversary)
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (hsourceBound :
      (sourceUnloggedDetailedGameAfterKeygen adversary
        (Concrete.materializeCachedKeyResult left.keyResult).1.1
        (Concrete.materializeCachedKeyResult left.keyResult).1.2).IsQueryBoundP
          (· matches .inr _) countLimit)
    (hlimits : countLimit ≤ hitLimit) :
    RelTriple
      (sourceGlobalExactTracedDetailedExecution adversary left)
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
        ((globalFirstLaneExactTracedDetailedExecution adversary right.1.1
          right.2).run (GlobalHighDirectTracedState.initial
            (globalFilteredCausalKeygenState right.1.1)))).run)
      (fun leftResult firstLaneResult =>
        ((leftResult.1 = firstLaneResult.1.1 ∧
          SourceFirstLaneExactGoodStateRelation left right.1 leftResult.2
            firstLaneResult.1.2 firstLaneResult.2 ∧
          FirstLaneOracleSimulation.hazardCount firstLaneResult.2 ≤
            countLimit) ∨
        FirstLaneOracleSimulation.CombinedHit right.1.2
          (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
            firstLaneResult.2))) := by
  let secretKey :=
    Concrete.materializePrecomputation left.cache left.secretKey
  let sourceInitial : SourceExactTracedState := ((((left.cache, []), []), []))
  let highInitial : GlobalMonitoredTracedState :=
    (⟨globalFilteredCausalKeygenState right.1.1,
      some AdaptiveRevealMonitor.State.empty, []⟩, [])
  let firstLaneInitial : GlobalHighDirectTracedState :=
    GlobalHighDirectTracedState.initial
      (globalFilteredCausalKeygenState right.1.1)
  have hinitial : SourceFirstLaneExactGoodStateRelation left right.1
      sourceInitial firstLaneInitial [] := by
    refine ⟨highInitial, ?_, rfl, rfl, ?_, ?_, ?_⟩
    · simpa [sourceInitial, highInitial, sourceExactSigningProjection] using
        globalSigningMonitoredTracedStateRelation_initial left right hrel
          hleftSupport hrightSupport
    · simpa [highInitial] using
        globalMonitoredCausalState_initial_traceConsistent right.1.2
          (globalFilteredCausalKeygenState right.1.1)
    · simp [sourceInitial,
        FirstLaneOracleSimulation.ActionTrace.encodingActions]
    · simp [highInitial, CappedEncodingMonitor.validObservedSignEpochs,
        FirstLaneOracleSimulation.ActionTrace.encodingActions,
        CappedEncodingMonitor.validActions,
        EncodingMonitor.observedSignEpochs]
  let finish : Forgery → OracleComp OracleWorld (Forgery × Bool) :=
    fun forgery => Prod.mk forgery <$> Concrete.scheme.verify
      left.publicKey forgery.epoch forgery.message forgery.signature
  let Budget := fun
    (rest : OracleComp (OracleWorld + SigningSpec) Forgery)
    (remaining : Nat) =>
      (simulateQ
        (sourceUnloggedMappedAdversaryImpl left.publicKey secretKey) rest >>=
          finish).IsQueryBoundP (· matches .inr _) remaining
  let leftFinish := fun (forgery : Forgery)
    (initial : SourceExactTracedState) => do
      let verified ← (simulateQ sourceSigningTracedVerifierImpl
        (Concrete.scheme.verify left.publicKey forgery.epoch forgery.message
          forgery.signature)).run (sourceExactSigningProjection initial)
      pure ((forgery, verified.1),
        ((verified.2.1,
          appendVerificationEncodingObservation secretKey forgery
            initial.1.1.1 verified.2.1.1 initial.1.2), verified.2.2))
  let rightFinish := fun (forgery : Forgery)
    (initial : GlobalHighDirectTracedState) => do
      let verified ← (simulateQ
        (globalFirstLaneExactTracedVerifierImpl right.1.1 right.2)
        (Concrete.scheme.verify left.publicKey forgery.epoch forgery.message
          forgery.signature)).run initial
      pure ((forgery, verified.1),
        firstLaneAppendVerificationState right.1.1.secretKey forgery initial
          verified.2)
  have hfullBound : Budget (adversary.main left.publicKey) countLimit := by
    unfold Budget finish
    unfold sourceUnloggedDetailedGameAfterKeygen at hsourceBound
    exact hsourceBound
  have hcoupling := relTriple_simulateQ_bind_bounded_firstLane right.1.2
    (cappedBothTracedMappedAdversaryImpl left.publicKey secretKey)
    (globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2)
    leftFinish rightFinish directHashActionCost
    (SourceFirstLaneExactGoodStateRelation left right.1)
    (fun state spent => state.2.hashInputs.length = spent) Budget
    (by
      intro input next remaining state result hrest hresult
      unfold Budget at hrest ⊢
      rw [simulateQ_query_bind, bind_assoc] at hrest
      have houtput :=
        cappedBothTracedMappedAdversaryImpl_support_unlogged_output
          left.publicKey secretKey input state result hresult
      let continuation := fun response =>
        simulateQ
          (sourceUnloggedMappedAdversaryImpl left.publicKey secretKey)
          (next ((OracleSpec.query input).cont response)) >>= finish
      have hstep :
          (liftM (sourceUnloggedMappedAdversaryImpl left.publicKey secretKey
            input) >>= continuation).IsQueryBoundP
              (· matches .inr _) remaining := hrest
      have hnext :=
        sourceUnloggedMappedAdversaryImpl_continuation_hashQueryBound
          left.publicKey secretKey input continuation remaining hstep result.1
            houtput
      rwa [attackerActionFragment_hashInputs_length] at hnext)
    (by
      intro spent input state firstState history hstates hprefix hacct
      apply relTriple_post_mono
        (relTriple_sourceExact_firstLane_action spent left right hrel
          hleftSupport hrightSupport input state firstState history hstates
            hprefix)
      intro leftResult firstResult hresult
      rcases hresult with hgood | hhit
      · exact Or.inl ⟨hgood.1, hgood.2.1, hgood.2.2.1, by
          rw [hgood.2.2.2, hacct]⟩
      · exact Or.inr hhit)
    countLimit hitLimit
    (by
      intro forgery spent remaining state firstState history hremaining
        hstates hcount hacct htotal
      unfold Budget finish at hremaining
      simp only [simulateQ_pure, pure_bind] at hremaining
      have hverifyBound :
          (Concrete.scheme.verify left.publicKey forgery.epoch forgery.message
            forgery.signature).IsQueryBoundP (· matches .inr _) remaining :=
        (OracleComp.isQueryBoundP_map_iff _ _ _).mp hremaining
      have hverifier :=
        relTriple_sourceExact_firstLane_verifier_boundedHit countLimit hitLimit
          spent remaining left right hrel hleftSupport hrightSupport
            (Concrete.scheme.verify left.publicKey forgery.epoch
              forgery.message forgery.signature) hverifyBound state firstState
                history hstates hcount htotal hlimits
      let sourceFinish := fun verified : Bool × SourceExactTracedState =>
        ((forgery, verified.1),
          sourceAppendVerificationState secretKey forgery state verified.2)
      let firstFinish := fun verified :
          ((Bool × GlobalHighDirectTracedState) ×
            FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (((forgery, verified.1.1),
          firstLaneAppendVerificationState right.1.1.secretKey forgery
            firstState verified.1.2), verified.2)
      have hlifted : RelTriple
          (sourceFinish <$>
            (simulateQ sourceExactTracedVerifierImpl
              (Concrete.scheme.verify left.publicKey forgery.epoch
                forgery.message forgery.signature)).run state)
          (firstFinish <$>
            (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
              ((simulateQ
                (globalFirstLaneExactTracedVerifierImpl right.1.1 right.2)
                (Concrete.scheme.verify left.publicKey forgery.epoch
                  forgery.message forgery.signature)).run firstState)).run)
          (fun leftResult firstResult =>
            (leftResult.1 = firstResult.1.1 ∧
              SourceFirstLaneExactGoodStateRelation left right.1 leftResult.2
                firstResult.1.2 (history ++ firstResult.2) ∧
              FirstLaneOracleSimulation.hazardCount
                (history ++ firstResult.2) ≤ countLimit) ∨
            FirstLaneOracleSimulation.CombinedHit right.1.2
              (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
                (history ++ firstResult.2))) := by
        apply relTriple_map
        apply relTriple_post_mono (relTriple_with_support hverifier)
        intro leftVerified firstVerified hvertified
        obtain ⟨hverifiedRelation, hleftVerifiedSupport,
          hfirstVerifiedSupport⟩ := hvertified
        rcases hverifiedRelation with hgood | hhit
        · exact Or.inl ⟨congrArg (Prod.mk forgery) hgood.1,
            SourceFirstLaneExactGoodStateRelation.appendVerification left right
              hrel hleftSupport hrightSupport forgery state leftVerified.2
                firstState firstVerified.1.2 history
                  (history ++ firstVerified.2) hstates hgood.2.1 (by
                    rw [FirstLaneOracleSimulation.ActionTrace.encodingActions_append]
                    have hpublicKey : left.publicKey =
                        right.1.1.publicKey := hrel.1.toStable.1.2.1
                    rw [hpublicKey] at hfirstVerifiedSupport
                    have hlocal :=
                      globalFirstLaneExactTracedVerifier_append_trace_sublist
                        right.1.2 right.1.1 right.2 forgery firstState
                          leftVerified.2.1.2
                          (by
                            have hkeyResult :=
                              trajectoryProgrammedGlobalChainKeygen_support_keyResult
                                right.1.1 hrightSupport
                            exact keygen_parameter_eq right.1.1.keyResult
                              hkeyResult)
                          firstVerified hfirstVerifiedSupport
                    have hleftEncoding : leftVerified.2.1.2 = state.1.2 := by
                      rw [sourceExactTracedVerifierImpl_run_eq, support_map]
                        at hleftVerifiedSupport
                      obtain ⟨baseResult, _hbase, heq⟩ := hleftVerifiedSupport
                      subst leftVerified
                      rfl
                    rcases hstates with ⟨highInitial, hsourceInitial,
                      _hfirstInitial, _hchainInitial, _hconsistentInitial,
                      hencodingInitial, _hvalidInitial⟩
                    have hencodingFinal : List.Sublist leftVerified.2.1.2
                        history.encodingActions := by
                      rw [hleftEncoding]
                      exact hencodingInitial
                    exact hlocal.trans
                      (hencodingFinal.append (List.Sublist.refl _))),
            hgood.2.2⟩
        · exact Or.inr hhit
      have hsource : leftFinish forgery state = sourceFinish <$>
          (simulateQ sourceExactTracedVerifierImpl
            (Concrete.scheme.verify left.publicKey forgery.epoch
              forgery.message forgery.signature)).run state := by
        unfold leftFinish
        rw [sourceExactTracedVerifierImpl_run_eq]
        simp [sourceFinish, sourceAppendVerificationState, Functor.map_map]
      have hright :
          (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
            (rightFinish forgery firstState)).run =
          firstFinish <$>
            (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
              ((simulateQ
                (globalFirstLaneExactTracedVerifierImpl right.1.1 right.2)
                (Concrete.scheme.verify left.publicKey forgery.epoch
                  forgery.message forgery.signature)).run firstState)).run := by
        unfold rightFinish
        rw [simulateQ_bind, WriterT.run_bind']
        simp [firstFinish, firstLaneAppendVerificationState]
      rw [hsource, hright]
      exact hlifted)
    0 countLimit (adversary.main left.publicKey) hfullBound sourceInitial
      firstLaneInitial [] hinitial
      (by simp [FirstLaneOracleSimulation.hazardCount]) (by rfl) (by omega)
        hlimits
  have hpublicKey : left.publicKey = right.1.1.publicKey :=
    hrel.1.toStable.1.2.1
  unfold sourceGlobalExactTracedDetailedExecution
    globalFirstLaneExactTracedDetailedExecution
  simp only [StateT.run_mk]
  rw [← hpublicKey]
  exact hcoupling
end XmssSecurity.CappedChain
