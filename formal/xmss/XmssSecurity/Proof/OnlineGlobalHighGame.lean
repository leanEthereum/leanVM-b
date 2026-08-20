import XmssSecurity.Proof.OnlineRevealMonitor
import XmssSecurity.Proof.CappedGlobalChainHighHashReplay
import XmssSecurity.Proof.CappedGlobalChainHighSigningReplay
import XmssSecurity.Proof.CappedGlobalChainHighKeygenRelation
import XmssSecurity.Proof.CappedGlobalCausalUniformTrace
import XmssSecurity.Proof.CappedChain.SourceDirectTrace

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

theorem relTriple_programmed_onlineGlobalUniformQuery
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftCache : QueryCache HashSpec)
    (rightState : OnlineMonitoredCausalState)
    (hstate : OnlineMonitoredFilteredStateRelation left right leftCache
      rightState)
    (n : Nat) :
    RelTriple
      ((fun output : Fin (n + 1) => (output, leftCache)) <$>
        (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
      ((monitorGlobalCausalOnline right.2 fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.2)
          ((globalCausalUniformImpl n).run causalState)).run).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          OnlineMonitoredFilteredStateRelation left right leftResult.2
            rightResult.2) ∨ rightResult.2.bad) := by
  rcases hstate with
    ⟨monitor, hmonitor, hmonitorAgrees, hrevealed, hcausal, hretained⟩
  apply relTriple_monitorGlobalCausalOnline_of_filtered_until_hit left right
    _ _ rightState monitor hmonitor hmonitorAgrees hrevealed
  · rw [simulate_eagerTrace_globalCausalUniformImpl]
    have hmapped : RelTriple
        ((fun output : Fin (n + 1) => (output, leftCache)) <$>
          (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
        ((fun output : Fin (n + 1) =>
          ((output, rightState.causal),
            ([] : RevealProbeOracleSimulation.ActionTrace
              GlobalChainValueIndex))) <$>
          (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
        (fun leftResult rightResult =>
          leftResult.1 = rightResult.1.1 ∧
            GlobalFilteredCausalStateRelation left right leftResult.2
              rightResult.1.2) := by
      apply relTriple_map
      apply relTriple_post_mono
        (relTriple_refl
          (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
      intro leftOutput rightOutput houtput
      subst rightOutput
      exact ⟨rfl, hcausal⟩
    apply relTriple_post_mono hmapped
    intro leftOutput rightOutput houtput
    exact Or.inl houtput
  · intro result hresult
    rw [simulate_eagerTrace_globalCausalUniformImpl, support_map] at hresult
    obtain ⟨output, _houtput, rfl⟩ := hresult
    exact ⟨by trivial, ReplaysCausalReveals.nil rightState.causal.revealed⟩
  · intro result hresult
    rw [simulate_eagerTrace_globalCausalUniformImpl, support_map] at hresult
    obtain ⟨output, _houtput, rfl⟩ := hresult
    exact hretained

theorem relTriple_programmed_onlineGlobalAttackerHashQuery_until_hit
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftCache : QueryCache HashSpec)
    (rightState : OnlineMonitoredCausalState)
    (hstate : OnlineMonitoredFilteredStateRelation left right.1 leftCache
      rightState)
    (input : HashInput) :
    RelTriple
      ((randomOracle input).run leftCache)
      ((monitorGlobalCausalOnline right.1.2 fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
          ((globalCausalAttackerHashQueryFromHigh
            (globalChainValueHighTableOfEdges right.2)
              right.1.1.secretKey input).run causalState)).run).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          OnlineMonitoredFilteredStateRelation left right.1 leftResult.2
            rightResult.2) ∨ rightResult.2.bad) := by
  rcases hstate with
    ⟨monitor, hmonitor, hmonitorAgrees, hrevealed, hcausal, hretained⟩
  apply relTriple_monitorGlobalCausalOnline_of_filtered_until_hit left right.1
    _ _ rightState monitor hmonitor hmonitorAgrees hrevealed
  · exact relTriple_programmed_globalFilteredAttackerHashQuery_until_hit left
      right hrel hleftSupport hrightSupport leftCache rightState.causal
        hcausal hretained monitor hrevealed input
  · intro result hresult
    constructor
    · exact RevealProbeOracleSimulation.simulate_eagerTrace_support_traceAgrees
        right.1.2 _ result hresult
    · exact
        simulate_eagerTrace_globalCausalAttackerHashQueryFromHigh_support_replays
          right.1.2 (globalChainValueHighTableOfEdges right.2)
            right.1.1.secretKey input rightState.causal result hresult
  · intro result hresult
    exact simulate_eagerTrace_globalCausalAttackerHashQueryFromHigh_merkleRetained
      right.1.2 (globalChainValueHighTableOfEdges right.2)
        right.1.1.secretKey input rightState.causal hretained result hresult

theorem relTriple_programmed_onlineGlobalSigningQuery
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftCache : QueryCache HashSpec)
    (rightState : OnlineMonitoredCausalState)
    (hstate : OnlineMonitoredFilteredStateRelation left right.1 leftCache
      rightState)
    (request : SignRequest) :
    RelTriple
      ((simulateQ xmssRomImpl
        (Concrete.scheme.sign left.publicKey
          (Concrete.materializePrecomputation left.cache left.secretKey)
          request.epoch request.message)).run leftCache)
      ((monitorGlobalCausalOnline right.1.2 fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
          (globalFilteredCausalSigningQuery right.1.1 request
            causalState)).run).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          OnlineMonitoredFilteredStateRelation left right.1 leftResult.2
            rightResult.2) ∨ rightResult.2.bad) := by
  rcases hstate with
    ⟨monitor, hmonitor, hmonitorAgrees, hrevealed, hcausal, hretained⟩
  apply relTriple_monitorGlobalCausalOnline_of_filtered_until_hit left right.1
    _ _ rightState monitor hmonitor hmonitorAgrees hrevealed
  · apply relTriple_post_mono
      (relTriple_programmed_globalFilteredCausalSigningQuery left right hrel
        hleftSupport hrightSupport leftCache rightState.causal hcausal request)
    intro leftResult rightResult hresult
    exact Or.inl hresult
  · intro result hresult
    constructor
    · exact RevealProbeOracleSimulation.simulate_eagerTrace_support_traceAgrees
        right.1.2 _ result hresult
    · exact
        simulate_eagerTrace_globalFilteredCausalSigningQuery_support_replays
          right.1.2 right.1.1 request rightState.causal result hresult
  · intro result hresult
    exact simulate_eagerTrace_globalFilteredCausalSigningQuery_merkleRetained
      right.1.2 right.1.1 request rightState.causal hretained result hresult

abbrev OnlineGlobalMonitoredTracedState :=
  OnlineMonitoredCausalState × AttackerActionTrace

def OnlineGlobalMonitoredTracedStateRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftState : SourceTracedState)
    (rightState : OnlineGlobalMonitoredTracedState) : Prop :=
  OnlineMonitoredFilteredStateRelation left right leftState.1 rightState.1 ∧
    leftState.2 = rightState.2

noncomputable def onlineGlobalHighMonitoredBaseMappedAdversaryImpl
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT OnlineMonitoredCausalState ProbComp) := fun input =>
  match input with
  | .inl (.inl n) =>
      monitorGlobalCausalOnline right.1.2 fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
          ((globalCausalUniformImpl n).run causalState)).run
  | .inl (.inr hashInput) =>
      monitorGlobalCausalOnline right.1.2 fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
          ((globalCausalAttackerHashQueryFromHigh
            (globalChainValueHighTableOfEdges right.2)
              right.1.1.secretKey hashInput).run causalState)).run
  | .inr request =>
      monitorGlobalCausalOnline right.1.2 fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
          (globalFilteredCausalSigningQuery right.1.1 request
            causalState)).run

noncomputable def onlineGlobalHighMonitoredMappedAdversaryImpl
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT OnlineGlobalMonitoredTracedState ProbComp) :=
  actionTracedStateImpl (onlineGlobalHighMonitoredBaseMappedAdversaryImpl right)
    attackerActionFragment

theorem onlineGlobalHighMonitoredBaseMappedAdversaryImpl_preserves_bad
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) :
    QueryImpl.PreservesInv
      (onlineGlobalHighMonitoredBaseMappedAdversaryImpl right)
      OnlineMonitoredCausalState.bad := by
  intro input state hbad result hresult
  rcases input with (worldInput | request)
  · rcases worldInput with n | hashInput
    · exact monitorGlobalCausalOnline_preserves_bad right.1.2 _ state hbad
        result (by simpa [onlineGlobalHighMonitoredBaseMappedAdversaryImpl]
          using hresult)
    · exact monitorGlobalCausalOnline_preserves_bad right.1.2 _ state hbad
        result (by simpa [onlineGlobalHighMonitoredBaseMappedAdversaryImpl]
          using hresult)
  · exact monitorGlobalCausalOnline_preserves_bad right.1.2 _ state hbad
      result (by simpa [onlineGlobalHighMonitoredBaseMappedAdversaryImpl]
        using hresult)

theorem onlineGlobalHighMonitoredMappedAdversaryImpl_preserves_bad
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) :
    QueryImpl.PreservesInv
      (onlineGlobalHighMonitoredMappedAdversaryImpl right)
      (fun state : OnlineGlobalMonitoredTracedState => state.1.bad) := by
  intro input state hbad result hresult
  unfold onlineGlobalHighMonitoredMappedAdversaryImpl actionTracedStateImpl
    at hresult
  change result ∈ support (do
    let baseResult ←
      (onlineGlobalHighMonitoredBaseMappedAdversaryImpl right input).run state.1
    pure (baseResult.1,
      (baseResult.2, state.2 ++ attackerActionFragment input baseResult.1)))
      at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨baseResult, hbase, hfinal⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  exact onlineGlobalHighMonitoredBaseMappedAdversaryImpl_preserves_bad right
    input state.1 hbad baseResult hbase

theorem relTriple_onlineGlobalActionTracedState_until_bad
    (input : (OracleWorld + SigningSpec).Domain)
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftImpl : QueryImpl (OracleWorld + SigningSpec)
      (StateT (QueryCache HashSpec) ProbComp))
    (rightImpl : QueryImpl (OracleWorld + SigningSpec)
      (StateT OnlineMonitoredCausalState ProbComp))
    (leftState : SourceTracedState)
    (rightState : OnlineGlobalMonitoredTracedState)
    (htrace : leftState.2 = rightState.2)
    (hcouple : RelTriple
      ((leftImpl input).run leftState.1)
      ((rightImpl input).run rightState.1)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          OnlineMonitoredFilteredStateRelation left right leftResult.2
            rightResult.2) ∨ rightResult.2.bad)) :
    RelTriple
      ((actionTracedStateImpl leftImpl attackerActionFragment input).run
        leftState)
      ((actionTracedStateImpl rightImpl attackerActionFragment input).run
        rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          OnlineGlobalMonitoredTracedStateRelation left right leftResult.2
            rightResult.2) ∨ rightResult.2.1.bad) := by
  apply relTriple_map
  apply relTriple_post_mono hcouple
  intro leftResult rightResult hresult
  rcases hresult with hgood | hbad
  · apply Or.inl
    refine ⟨hgood.1, hgood.2, ?_⟩
    rw [← htrace, hgood.1]
  · exact Or.inr hbad

theorem relTriple_programmed_onlineGlobalHighMonitored_action
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftState : SourceTracedState)
    (rightState : OnlineGlobalMonitoredTracedState)
    (hstate : OnlineGlobalMonitoredTracedStateRelation left right.1 leftState
      rightState)
    (input : (OracleWorld + SigningSpec).Domain) :
    RelTriple
      ((sourceDirectTracedMappedAdversaryImpl left.publicKey
        (Concrete.materializePrecomputation left.cache left.secretKey)
          input).run leftState)
      ((onlineGlobalHighMonitoredMappedAdversaryImpl right input).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          OnlineGlobalMonitoredTracedStateRelation left right.1 leftResult.2
            rightResult.2) ∨ rightResult.2.1.bad) := by
  have liftBase := relTriple_onlineGlobalActionTracedState_until_bad input left
    right.1 (sourceDirectMappedAdversaryImpl left.publicKey
      (Concrete.materializePrecomputation left.cache left.secretKey))
      (onlineGlobalHighMonitoredBaseMappedAdversaryImpl right) leftState
        rightState hstate.2
  rcases input with (worldInput | request)
  · rcases worldInput with n | hashInput
    · apply liftBase
      simpa [sourceDirectMappedAdversaryImpl,
        unloggedMappedAdversaryImpl_apply_inl,
        onlineGlobalHighMonitoredBaseMappedAdversaryImpl, xmssRomImpl,
        unifFwdImpl, OracleComp.liftM_run_StateT] using
        (relTriple_programmed_onlineGlobalUniformQuery left right.1
          leftState.1 rightState.1 hstate.1 n)
    · apply liftBase
      simpa [sourceDirectMappedAdversaryImpl,
        unloggedMappedAdversaryImpl_apply_inl,
        onlineGlobalHighMonitoredBaseMappedAdversaryImpl, xmssRomImpl] using
        (relTriple_programmed_onlineGlobalAttackerHashQuery_until_hit left
          right hrel hleftSupport hrightSupport leftState.1 rightState.1
            hstate.1 hashInput)
  · apply liftBase
    simpa [sourceDirectMappedAdversaryImpl,
      unloggedMappedAdversaryImpl_apply_inr,
      onlineGlobalHighMonitoredBaseMappedAdversaryImpl] using
      (relTriple_programmed_onlineGlobalSigningQuery left right hrel
        hleftSupport hrightSupport leftState.1 rightState.1 hstate.1 request)

noncomputable def onlineGlobalHighMonitoredVerifierImpl
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) :
    QueryImpl OracleWorld
      (StateT OnlineGlobalMonitoredTracedState ProbComp) := fun input =>
  StateT.mk fun state =>
    (fun result => (result.1, (result.2, state.2))) <$>
      (onlineGlobalHighMonitoredBaseMappedAdversaryImpl right (.inl input)
        ).run state.1

theorem relTriple_keepOnlineGlobalAttackerTrace_until_bad
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftTrace rightTrace : AttackerActionTrace)
    (htrace : leftTrace = rightTrace)
    (leftComputation : ProbComp (α × QueryCache HashSpec))
    (rightComputation : ProbComp (α × OnlineMonitoredCausalState))
    (hcouple : RelTriple leftComputation rightComputation
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          OnlineMonitoredFilteredStateRelation left right leftResult.2
            rightResult.2) ∨ rightResult.2.bad)) :
    RelTriple
      ((fun result => (result.1, (result.2, leftTrace))) <$> leftComputation)
      ((fun result => (result.1, (result.2, rightTrace))) <$> rightComputation)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          OnlineGlobalMonitoredTracedStateRelation left right leftResult.2
            rightResult.2) ∨ rightResult.2.1.bad) := by
  apply relTriple_map
  apply relTriple_post_mono hcouple
  intro leftResult rightResult hresult
  rcases hresult with hgood | hbad
  · exact Or.inl ⟨hgood.1, hgood.2, htrace⟩
  · exact Or.inr hbad

theorem relTriple_programmed_onlineGlobalHighMonitored_verifier_query
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftState : SourceTracedState)
    (rightState : OnlineGlobalMonitoredTracedState)
    (hstate : OnlineGlobalMonitoredTracedStateRelation left right.1 leftState
      rightState)
    (input : OracleWorld.Domain) :
    RelTriple
      ((sourceDirectTracedVerifierImpl input).run leftState)
      ((onlineGlobalHighMonitoredVerifierImpl right input).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          OnlineGlobalMonitoredTracedStateRelation left right.1 leftResult.2
            rightResult.2) ∨ rightResult.2.1.bad) := by
  rw [sourceDirectTracedVerifierImpl_query_run_eq]
  unfold onlineGlobalHighMonitoredVerifierImpl
  rw [StateT.run_mk]
  apply relTriple_keepOnlineGlobalAttackerTrace_until_bad left right.1
    leftState.2 rightState.2 hstate.2
  rcases input with n | hashInput
  · simpa [sourceDirectTracedVerifierImpl,
      onlineGlobalHighMonitoredBaseMappedAdversaryImpl, xmssRomImpl,
      unifFwdImpl, OracleComp.liftM_run_StateT] using
      (relTriple_programmed_onlineGlobalUniformQuery left right.1
        leftState.1 rightState.1 hstate.1 n)
  · simpa [sourceDirectTracedVerifierImpl,
      onlineGlobalHighMonitoredBaseMappedAdversaryImpl, xmssRomImpl] using
      (relTriple_programmed_onlineGlobalAttackerHashQuery_until_hit left
        right hrel hleftSupport hrightSupport leftState.1 rightState.1 hstate.1
          hashInput)

theorem onlineGlobalHighMonitoredVerifierImpl_preserves_bad
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) :
    QueryImpl.PreservesInv (onlineGlobalHighMonitoredVerifierImpl right)
      (fun state : OnlineGlobalMonitoredTracedState => state.1.bad) := by
  intro input state hbad result hresult
  unfold onlineGlobalHighMonitoredVerifierImpl at hresult
  simp only [StateT.run_mk] at hresult
  rw [support_map] at hresult
  obtain ⟨baseResult, hbase, rfl⟩ := hresult
  exact onlineGlobalHighMonitoredBaseMappedAdversaryImpl_preserves_bad right
    (.inl input) state.1 hbad baseResult hbase

end XmssSecurity.CappedChain
