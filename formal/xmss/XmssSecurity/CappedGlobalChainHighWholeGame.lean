import XmssSecurity.CappedGlobalChainHighSigningReplay
import XmssSecurity.CappedGlobalChainHighKeygenRelation
import XmssSecurity.CappedGlobalCausalInstalledAdversary
import XmssSecurity.CappedChain.CausalEagerHighReduction

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

theorem relTriple_programmed_monitoredGlobalUniformQuery
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftCache : QueryCache HashSpec)
    (rightState : GlobalMonitoredCausalState)
    (hstate : GlobalMonitoredFilteredStateRelation left right leftCache
      rightState)
    (n : Nat) :
    RelTriple
      ((fun output : Fin (n + 1) => (output, leftCache)) <$>
        (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
      ((monitorGlobalCausalTrace right.2 fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.2)
          ((globalCausalUniformImpl n).run causalState)).run).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredFilteredStateRelation left right leftResult.2
            rightResult.2) ∨ rightResult.2.bad) := by
  rcases hstate with
    ⟨monitor, hmonitor, hmonitorAgrees, hrevealed, hcausal, hretained⟩
  apply relTriple_monitorGlobalCausalTrace_of_filtered_until_hit left right
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
    intro leftResult rightResult hresult
    exact Or.inl hresult
  · intro result hresult
    rw [simulate_eagerTrace_globalCausalUniformImpl, support_map] at hresult
    obtain ⟨output, _houtput, rfl⟩ := hresult
    exact ⟨by trivial, ReplaysCausalReveals.nil rightState.causal.revealed⟩
  · intro result hresult
    rw [simulate_eagerTrace_globalCausalUniformImpl, support_map] at hresult
    obtain ⟨output, _houtput, rfl⟩ := hresult
    exact hretained

abbrev GlobalMonitoredTracedState :=
  GlobalMonitoredCausalState × AttackerActionTrace

def GlobalMonitoredTracedStateRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftState : SourceTracedState)
    (rightState : GlobalMonitoredTracedState) : Prop :=
  GlobalMonitoredFilteredStateRelation left right leftState.1 rightState.1 ∧
    leftState.2 = rightState.2

noncomputable def globalHighMonitoredBaseMappedAdversaryImpl
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT GlobalMonitoredCausalState ProbComp) := fun input =>
  match input with
  | .inl (.inl n) =>
      monitorGlobalCausalTrace right.1.2 fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
          ((globalCausalUniformImpl n).run causalState)).run
  | .inl (.inr hashInput) =>
      monitorGlobalCausalTrace right.1.2 fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
          ((globalCausalAttackerHashQueryFromHigh
            (globalChainValueHighTableOfEdges right.2)
              right.1.1.secretKey hashInput).run causalState)).run
  | .inr request =>
      monitorGlobalCausalTrace right.1.2 fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
          (globalFilteredCausalSigningQuery right.1.1 request
            causalState)).run

noncomputable def globalHighMonitoredMappedAdversaryImpl
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT GlobalMonitoredTracedState ProbComp) :=
  actionTracedStateImpl (globalHighMonitoredBaseMappedAdversaryImpl right)
    attackerActionFragment

theorem relTriple_globalActionTracedState_until_bad
    (input : (OracleWorld + SigningSpec).Domain)
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftImpl : QueryImpl (OracleWorld + SigningSpec)
      (StateT (QueryCache HashSpec) ProbComp))
    (rightImpl : QueryImpl (OracleWorld + SigningSpec)
      (StateT GlobalMonitoredCausalState ProbComp))
    (leftState : SourceTracedState)
    (rightState : GlobalMonitoredTracedState)
    (htrace : leftState.2 = rightState.2)
    (hcouple : RelTriple
      ((leftImpl input).run leftState.1)
      ((rightImpl input).run rightState.1)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredFilteredStateRelation left right leftResult.2
            rightResult.2) ∨ rightResult.2.bad)) :
    RelTriple
      ((actionTracedStateImpl leftImpl attackerActionFragment input).run
        leftState)
      ((actionTracedStateImpl rightImpl attackerActionFragment input).run
        rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredTracedStateRelation left right leftResult.2
            rightResult.2) ∨ rightResult.2.1.bad) := by
  let wrapLeft := fun result : (OracleWorld + SigningSpec).Range input ×
      QueryCache HashSpec => (result.1,
    (result.2, leftState.2 ++ attackerActionFragment input result.1))
  let wrapRight := fun result : (OracleWorld + SigningSpec).Range input ×
      GlobalMonitoredCausalState => (result.1,
    (result.2, rightState.2 ++ attackerActionFragment input result.1))
  let post := fun leftResult : (OracleWorld + SigningSpec).Range input ×
      SourceTracedState => fun rightResult :
      (OracleWorld + SigningSpec).Range input × GlobalMonitoredTracedState =>
    (leftResult.1 = rightResult.1 ∧
      GlobalMonitoredTracedStateRelation left right leftResult.2
        rightResult.2) ∨ rightResult.2.1.bad
  have hprepared : RelTriple
      ((leftImpl input).run leftState.1)
      ((rightImpl input).run rightState.1)
      (fun leftResult rightResult =>
        post (wrapLeft leftResult) (wrapRight rightResult)) := by
    apply relTriple_post_mono hcouple
    intro leftResult rightResult hresult
    rcases hresult with hgood | hbad
    · refine Or.inl ⟨hgood.1, hgood.2, ?_⟩
      change leftState.2 ++ attackerActionFragment input leftResult.1 =
        rightState.2 ++ attackerActionFragment input rightResult.1
      rw [htrace, hgood.1]
    · exact Or.inr hbad
  unfold actionTracedStateImpl
  simpa [wrapLeft, wrapRight, post, map_eq_bind_pure_comp] using
    (relTriple_map (R := post) (f := wrapLeft) (g := wrapRight) hprepared)

theorem relTriple_programmed_globalHighMonitored_action
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftState : SourceTracedState)
    (rightState : GlobalMonitoredTracedState)
    (hstate : GlobalMonitoredTracedStateRelation left right.1 leftState
      rightState)
    (input : (OracleWorld + SigningSpec).Domain) :
    RelTriple
      ((sourceDirectTracedMappedAdversaryImpl left.publicKey
        (Concrete.materializePrecomputation left.cache left.secretKey)
          input).run leftState)
      ((globalHighMonitoredMappedAdversaryImpl right input).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredTracedStateRelation left right.1 leftResult.2
            rightResult.2) ∨ rightResult.2.1.bad) := by
  have liftBase := relTriple_globalActionTracedState_until_bad input left
    right.1 (sourceDirectMappedAdversaryImpl left.publicKey
      (Concrete.materializePrecomputation left.cache left.secretKey))
      (globalHighMonitoredBaseMappedAdversaryImpl right) leftState rightState
        hstate.2
  rcases input with (worldInput | request)
  · rcases worldInput with n | hashInput
    · apply liftBase
      simpa [sourceDirectMappedAdversaryImpl,
        unloggedMappedAdversaryImpl_apply_inl,
        globalHighMonitoredBaseMappedAdversaryImpl, xmssRomImpl, unifFwdImpl,
        OracleComp.liftM_run_StateT] using
        (relTriple_programmed_monitoredGlobalUniformQuery left right.1
          leftState.1 rightState.1 hstate.1 n)
    · apply liftBase
      simpa [sourceDirectMappedAdversaryImpl,
        unloggedMappedAdversaryImpl_apply_inl,
        globalHighMonitoredBaseMappedAdversaryImpl, xmssRomImpl] using
        (relTriple_programmed_monitoredGlobalAttackerHashQuery_until_hit left
          right hrel hleftSupport hrightSupport leftState.1 rightState.1
            hstate.1 hashInput)
  · apply liftBase
    simpa [sourceDirectMappedAdversaryImpl,
      unloggedMappedAdversaryImpl_apply_inr,
      globalHighMonitoredBaseMappedAdversaryImpl] using
      (relTriple_programmed_monitoredGlobalSigningQuery left right hrel
        hleftSupport hrightSupport leftState.1 rightState.1 hstate.1 request)

theorem globalHighMonitoredBaseMappedAdversaryImpl_preserves_bad
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalMonitoredCausalState) (hbad : state.bad)
    (result : (OracleWorld + SigningSpec).Range input ×
      GlobalMonitoredCausalState)
    (hresult : result ∈ support
      ((globalHighMonitoredBaseMappedAdversaryImpl right input).run state)) :
    result.2.bad := by
  rcases input with (worldInput | request)
  · rcases worldInput with n | hashInput
    · exact monitorGlobalCausalTrace_preserves_bad right.1.2 _ state hbad
        result (by simpa [globalHighMonitoredBaseMappedAdversaryImpl] using
          hresult)
    · exact monitorGlobalCausalTrace_preserves_bad right.1.2 _ state hbad
        result (by simpa [globalHighMonitoredBaseMappedAdversaryImpl] using
          hresult)
  · exact monitorGlobalCausalTrace_preserves_bad right.1.2 _ state hbad
      result (by simpa [globalHighMonitoredBaseMappedAdversaryImpl] using
        hresult)

theorem globalHighMonitoredMappedAdversaryImpl_preserves_bad
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalMonitoredTracedState) (hbad : state.1.bad)
    (result : (OracleWorld + SigningSpec).Range input ×
      GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((globalHighMonitoredMappedAdversaryImpl right input).run state)) :
    result.2.1.bad := by
  unfold globalHighMonitoredMappedAdversaryImpl actionTracedStateImpl at hresult
  change result ∈ support (do
    let baseResult ←
      (globalHighMonitoredBaseMappedAdversaryImpl right input).run state.1
    pure (baseResult.1,
      (baseResult.2, state.2 ++ attackerActionFragment input baseResult.1)))
      at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨baseResult, hbaseResult, hfinal⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  exact globalHighMonitoredBaseMappedAdversaryImpl_preserves_bad right input
    state.1 hbad baseResult hbaseResult

theorem globalHighMonitoredBaseMappedAdversaryImpl_preserves_traceConsistent
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalMonitoredCausalState)
    (hconsistent : state.TraceConsistent right.1.2)
    (result : (OracleWorld + SigningSpec).Range input ×
      GlobalMonitoredCausalState)
    (hresult : result ∈ support
      ((globalHighMonitoredBaseMappedAdversaryImpl right input).run state)) :
    result.2.TraceConsistent right.1.2 := by
  rcases input with (worldInput | request)
  · rcases worldInput with n | hashInput
    · exact monitorGlobalCausalTrace_preserves_traceConsistent right.1.2 _
        state hconsistent result
          (by simpa [globalHighMonitoredBaseMappedAdversaryImpl] using hresult)
    · exact monitorGlobalCausalTrace_preserves_traceConsistent right.1.2 _
        state hconsistent result
          (by simpa [globalHighMonitoredBaseMappedAdversaryImpl] using hresult)
  · exact monitorGlobalCausalTrace_preserves_traceConsistent right.1.2 _ state
      hconsistent result
        (by simpa [globalHighMonitoredBaseMappedAdversaryImpl] using hresult)

theorem globalHighMonitoredMappedAdversaryImpl_preserves_traceConsistent
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) :
    QueryImpl.PreservesInv (globalHighMonitoredMappedAdversaryImpl right)
      (fun state : GlobalMonitoredTracedState =>
        state.1.TraceConsistent right.1.2) := by
  intro input state hconsistent result hresult
  unfold globalHighMonitoredMappedAdversaryImpl actionTracedStateImpl at hresult
  change result ∈ support (do
    let baseResult ←
      (globalHighMonitoredBaseMappedAdversaryImpl right input).run state.1
    pure (baseResult.1,
      (baseResult.2, state.2 ++ attackerActionFragment input baseResult.1)))
      at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨baseResult, hbaseResult, hfinal⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  exact globalHighMonitoredBaseMappedAdversaryImpl_preserves_traceConsistent
    right input state.1 hconsistent baseResult hbaseResult

theorem relTriple_programmed_globalHighMonitored_adversary
    (adversary : Adversary Concrete.scheme)
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftState : SourceTracedState)
    (rightState : GlobalMonitoredTracedState)
    (hstate : GlobalMonitoredTracedStateRelation left right.1 leftState
      rightState) :
    RelTriple
      ((simulateQ
        (sourceDirectTracedMappedAdversaryImpl left.publicKey
          (Concrete.materializePrecomputation left.cache left.secretKey))
          (adversary.main left.publicKey)).run leftState)
      ((simulateQ (globalHighMonitoredMappedAdversaryImpl right)
        (adversary.main left.publicKey)).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredTracedStateRelation left right.1 leftResult.2
            rightResult.2) ∨ rightResult.2.1.bad) := by
  exact relTriple_simulateQ_run_until_bad_right
    (sourceDirectTracedMappedAdversaryImpl left.publicKey
      (Concrete.materializePrecomputation left.cache left.secretKey))
    (globalHighMonitoredMappedAdversaryImpl right)
    (GlobalMonitoredTracedStateRelation left right.1)
    (fun state : GlobalMonitoredTracedState => state.1.bad)
    (fun input leftState rightState hstate =>
      relTriple_programmed_globalHighMonitored_action left right hrel
        hleftSupport hrightSupport leftState rightState hstate input)
    (fun input state hbad result hresult =>
      globalHighMonitoredMappedAdversaryImpl_preserves_bad right input state
        hbad result hresult)
    (adversary.main left.publicKey) leftState rightState hstate

noncomputable def globalHighMonitoredVerifierImpl
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) :
    QueryImpl OracleWorld (StateT GlobalMonitoredTracedState ProbComp) :=
  fun input => StateT.mk fun state =>
    (fun result => (result.1, (result.2, state.2))) <$>
      ((globalHighMonitoredBaseMappedAdversaryImpl right (.inl input)).run
        state.1)

theorem relTriple_keepGlobalAttackerTrace_until_bad
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftTrace rightTrace : AttackerActionTrace)
    (htrace : leftTrace = rightTrace)
    (leftComputation : ProbComp (α × QueryCache HashSpec))
    (rightComputation : ProbComp (α × GlobalMonitoredCausalState))
    (hcouple : RelTriple leftComputation rightComputation
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredFilteredStateRelation left right leftResult.2
            rightResult.2) ∨ rightResult.2.bad)) :
    RelTriple
      ((fun result => (result.1, (result.2, leftTrace))) <$> leftComputation)
      ((fun result => (result.1, (result.2, rightTrace))) <$> rightComputation)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredTracedStateRelation left right leftResult.2
            rightResult.2) ∨ rightResult.2.1.bad) := by
  let wrapLeft := fun result : α × QueryCache HashSpec =>
    (result.1, (result.2, leftTrace))
  let wrapRight := fun result : α × GlobalMonitoredCausalState =>
    (result.1, (result.2, rightTrace))
  let post := fun leftResult : α × SourceTracedState =>
    fun rightResult : α × GlobalMonitoredTracedState =>
      (leftResult.1 = rightResult.1 ∧
        GlobalMonitoredTracedStateRelation left right leftResult.2
          rightResult.2) ∨ rightResult.2.1.bad
  have hprepared : RelTriple leftComputation rightComputation
      (fun leftResult rightResult =>
        post (wrapLeft leftResult) (wrapRight rightResult)) := by
    apply relTriple_post_mono hcouple
    intro leftResult rightResult hresult
    rcases hresult with hgood | hbad
    · exact Or.inl ⟨hgood.1, hgood.2, htrace⟩
    · exact Or.inr hbad
  simpa [wrapLeft, wrapRight, post] using
    (relTriple_map (R := post) (f := wrapLeft) (g := wrapRight) hprepared)

theorem relTriple_programmed_globalHighMonitored_verifier_query
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftState : SourceTracedState)
    (rightState : GlobalMonitoredTracedState)
    (hstate : GlobalMonitoredTracedStateRelation left right.1 leftState
      rightState)
    (input : OracleWorld.Domain) :
    RelTriple
      ((sourceDirectTracedVerifierImpl input).run leftState)
      ((globalHighMonitoredVerifierImpl right input).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredTracedStateRelation left right.1 leftResult.2
            rightResult.2) ∨ rightResult.2.1.bad) := by
  rw [sourceDirectTracedVerifierImpl_query_run_eq]
  unfold globalHighMonitoredVerifierImpl
  rw [StateT.run_mk]
  apply relTriple_keepGlobalAttackerTrace_until_bad left right.1 leftState.2
    rightState.2 hstate.2
  rcases input with n | hashInput
  · simpa [sourceDirectTracedVerifierImpl,
      globalHighMonitoredVerifierImpl,
      globalHighMonitoredBaseMappedAdversaryImpl, xmssRomImpl, unifFwdImpl,
      OracleComp.liftM_run_StateT] using
      (relTriple_programmed_monitoredGlobalUniformQuery left right.1
        leftState.1 rightState.1 hstate.1 n)
  · simpa [sourceDirectTracedVerifierImpl,
      globalHighMonitoredVerifierImpl,
      globalHighMonitoredBaseMappedAdversaryImpl, xmssRomImpl] using
      (relTriple_programmed_monitoredGlobalAttackerHashQuery_until_hit left
        right hrel hleftSupport hrightSupport leftState.1 rightState.1 hstate.1
          hashInput)

theorem globalHighMonitoredVerifierImpl_preserves_bad
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) :
    QueryImpl.PreservesInv (globalHighMonitoredVerifierImpl right)
      (fun state : GlobalMonitoredTracedState => state.1.bad) := by
  intro input state hbad result hresult
  unfold globalHighMonitoredVerifierImpl at hresult
  simp only [StateT.run_mk] at hresult
  rw [support_map] at hresult
  obtain ⟨baseResult, hbaseResult, rfl⟩ := hresult
  exact globalHighMonitoredBaseMappedAdversaryImpl_preserves_bad right
    (.inl input) state.1 hbad baseResult hbaseResult

theorem globalHighMonitoredVerifierImpl_preserves_traceConsistent
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) :
    QueryImpl.PreservesInv (globalHighMonitoredVerifierImpl right)
      (fun state : GlobalMonitoredTracedState =>
        state.1.TraceConsistent right.1.2) := by
  intro input state hconsistent result hresult
  unfold globalHighMonitoredVerifierImpl at hresult
  simp only [StateT.run_mk] at hresult
  rw [support_map] at hresult
  obtain ⟨baseResult, hbaseResult, rfl⟩ := hresult
  exact globalHighMonitoredBaseMappedAdversaryImpl_preserves_traceConsistent
    right (.inl input) state.1 hconsistent baseResult hbaseResult

theorem relTriple_programmed_globalHighMonitored_verifier
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (computation : OracleComp OracleWorld α)
    (leftState : SourceTracedState)
    (rightState : GlobalMonitoredTracedState)
    (hstate : GlobalMonitoredTracedStateRelation left right.1 leftState
      rightState) :
    RelTriple
      ((simulateQ sourceDirectTracedVerifierImpl computation).run leftState)
      ((simulateQ (globalHighMonitoredVerifierImpl right) computation).run
        rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredTracedStateRelation left right.1 leftResult.2
            rightResult.2) ∨ rightResult.2.1.bad) := by
  exact relTriple_simulateQ_run_until_bad_right sourceDirectTracedVerifierImpl
    (globalHighMonitoredVerifierImpl right)
    (GlobalMonitoredTracedStateRelation left right.1)
    (fun state : GlobalMonitoredTracedState => state.1.bad)
    (fun input leftState rightState hstate =>
      relTriple_programmed_globalHighMonitored_verifier_query left right hrel
        hleftSupport hrightSupport leftState rightState hstate input)
    (fun input state hbad result hresult =>
      globalHighMonitoredVerifierImpl_preserves_bad right input state hbad
        result hresult)
    computation leftState rightState hstate

theorem globalMonitoredTracedStateRelation_initial
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen) :
    GlobalMonitoredTracedStateRelation left right.1 (left.cache, [])
      (⟨globalFilteredCausalKeygenState right.1.1,
        some AdaptiveRevealMonitor.State.empty, []⟩, []) := by
  refine ⟨globalMonitoredFilteredStateRelation_initial left right.1 left.cache
    (globalFilteredCausalKeygenState right.1.1) ?_ ?_ ?_, rfl⟩
  · exact programmedGlobal_filteredKeygen_stateRelation left right hrel
      hleftSupport hrightSupport
  · exact globalFilteredCausalKeygenState_merkleRetained right.1.1
  · intro index
    simp [globalFilteredCausalKeygenState]

noncomputable def sourceGlobalTracedDetailedExecution
    (adversary : Adversary Concrete.scheme)
    (keyView : ProgrammedGlobalChainKeygenView) :
    ProbComp ((Forgery × Bool) × SourceTracedState) := do
  let handled ← (simulateQ
    (sourceDirectTracedMappedAdversaryImpl keyView.publicKey
      (Concrete.materializePrecomputation keyView.cache keyView.secretKey))
      (adversary.main keyView.publicKey)).run (keyView.cache, [])
  let verified ← (simulateQ sourceDirectTracedVerifierImpl
    (Concrete.scheme.verify keyView.publicKey handled.1.epoch
      handled.1.message handled.1.signature)).run handled.2
  pure ((handled.1, verified.1), verified.2)

noncomputable def globalHighMonitoredDetailedExecution
    (adversary : Adversary Concrete.scheme)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) :
    ProbComp ((Forgery × Bool) × GlobalMonitoredTracedState) := do
  let initial : GlobalMonitoredTracedState :=
    (⟨globalFilteredCausalKeygenState right.1.1,
      some AdaptiveRevealMonitor.State.empty, []⟩, [])
  let handled ← (simulateQ (globalHighMonitoredMappedAdversaryImpl right)
    (adversary.main right.1.1.publicKey)).run initial
  let verified ← (simulateQ (globalHighMonitoredVerifierImpl right)
    (Concrete.scheme.verify right.1.1.publicKey handled.1.epoch
      handled.1.message handled.1.signature)).run handled.2
  pure ((handled.1, verified.1), verified.2)

theorem relTriple_sourceGlobal_globalHighMonitored_detailedExecution
    (adversary : Adversary Concrete.scheme)
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen) :
    RelTriple (sourceGlobalTracedDetailedExecution adversary left)
      (globalHighMonitoredDetailedExecution adversary right)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredTracedStateRelation left right.1 leftResult.2
            rightResult.2) ∨ rightResult.2.1.bad) := by
  have hinitial := globalMonitoredTracedStateRelation_initial left right hrel
    hleftSupport hrightSupport
  have hpublicKey : left.publicKey = right.1.1.publicKey :=
    hrel.1.toStable.1.2.1
  unfold sourceGlobalTracedDetailedExecution
    globalHighMonitoredDetailedExecution
  rw [← hpublicKey]
  apply relTriple_bind
    (relTriple_programmed_globalHighMonitored_adversary adversary left right
      hrel hleftSupport hrightSupport (left.cache, [])
        (⟨globalFilteredCausalKeygenState right.1.1,
          some AdaptiveRevealMonitor.State.empty, []⟩, []) hinitial)
  intro leftHandled rightHandled hhandled
  rcases hhandled with hgood | hbad
  · obtain ⟨hforgery, hstates⟩ := hgood
    rw [← hforgery]
    apply relTriple_bind
      (relTriple_programmed_globalHighMonitored_verifier left right hrel
        hleftSupport hrightSupport
        (Concrete.scheme.verify left.publicKey leftHandled.1.epoch
          leftHandled.1.message leftHandled.1.signature)
        leftHandled.2 rightHandled.2 hstates)
    intro leftVerified rightVerified hvertified
    apply relTriple_pure_pure
    rcases hvertified with hverifiedGood | hverifiedBad
    · exact Or.inl ⟨congrArg (Prod.mk leftHandled.1) hverifiedGood.1,
        hverifiedGood.2⟩
    · exact Or.inr hverifiedBad
  · apply relTriple_bind
      (relTriple_prod (fun _result _hresult => True.intro)
        (fun rightResult hrightResult =>
          OracleComp.simulateQ_run_preservesInv
            (globalHighMonitoredVerifierImpl right)
            (fun state : GlobalMonitoredTracedState => state.1.bad)
            (globalHighMonitoredVerifierImpl_preserves_bad right)
            (Concrete.scheme.verify left.publicKey rightHandled.1.epoch
              rightHandled.1.message rightHandled.1.signature)
            rightHandled.2 hbad rightResult hrightResult))
    intro leftVerified rightVerified _hverified
    apply relTriple_pure_pure
    exact Or.inr _hverified.2

theorem globalHighMonitoredDetailedExecution_traceConsistent
    (adversary : Adversary Concrete.scheme)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (result : (Forgery × Bool) × GlobalMonitoredTracedState)
    (hresult : result ∈ support
      (globalHighMonitoredDetailedExecution adversary right)) :
    result.2.1.TraceConsistent right.1.2 := by
  unfold globalHighMonitoredDetailedExecution at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨handled, hhandled, hresult⟩ := hresult
  have hhandledConsistent := OracleComp.simulateQ_run_preservesInv
    (globalHighMonitoredMappedAdversaryImpl right)
    (fun state : GlobalMonitoredTracedState =>
      state.1.TraceConsistent right.1.2)
    (globalHighMonitoredMappedAdversaryImpl_preserves_traceConsistent right)
    (adversary.main right.1.1.publicKey)
    (⟨globalFilteredCausalKeygenState right.1.1,
      some AdaptiveRevealMonitor.State.empty, []⟩, [])
    (globalMonitoredCausalState_initial_traceConsistent right.1.2
      (globalFilteredCausalKeygenState right.1.1)) handled hhandled
  rw [mem_support_bind_iff] at hresult
  obtain ⟨verified, hvertified, hresult⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hresult
  subst result
  exact OracleComp.simulateQ_run_preservesInv
    (globalHighMonitoredVerifierImpl right)
    (fun state : GlobalMonitoredTracedState =>
      state.1.TraceConsistent right.1.2)
    (globalHighMonitoredVerifierImpl_preserves_traceConsistent right)
    (Concrete.scheme.verify right.1.1.publicKey handled.1.epoch
      handled.1.message handled.1.signature)
    handled.2 hhandledConsistent verified hvertified

def sourceGlobalExecutionResult
    (keyView : ProgrammedGlobalChainKeygenView)
    (execution : (Forgery × Bool) × SourceTracedState) :
    (GameOutcome × QueryCache HashSpec) × AttackerActionTrace :=
  ((actionTraceOutcome keyView.publicKey
    (Concrete.materializePrecomputation keyView.cache keyView.secretKey)
    (execution.1, execution.2.2), execution.2.1), execution.2.2)

theorem sourceGlobalTracedDetailedExecution_eq_actionTraced
    (adversary : Adversary Concrete.scheme)
    (keyView : ProgrammedGlobalChainKeygenView) :
    sourceGlobalExecutionResult keyView <$>
        sourceGlobalTracedDetailedExecution adversary keyView =
      detailedGameAfterKeygenWithActionTrace adversary keyView.publicKey
        (Concrete.materializePrecomputation keyView.cache keyView.secretKey)
          keyView.cache := by
  unfold sourceGlobalTracedDetailedExecution
    detailedGameAfterKeygenWithActionTrace
    sourceActionTracedDetailedGameAfterKeygen
  rw [sourceDirectTracedMappedAdversaryImpl_run_eq]
  simp only [List.nil_append, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    simulateQ_bind, StateT.run_bind]
  apply bind_congr
  intro handled
  simp only [Function.comp_apply, pure_bind]
  rw [sourceDirectTracedVerifierImpl_run_eq]
  simp [sourceGlobalExecutionResult, map_eq_bind_pure_comp]

abbrev SourceGlobalTracedProgramResult :=
  ProgrammedGlobalChainKeygenView ×
    ((Forgery × Bool) × SourceTracedState)

abbrev GlobalHighMonitoredProgramResult :=
  ((ProgrammedGlobalChainKeygenView ×
    (GlobalChainValueIndex → Digest)) ×
    (GlobalChainEdgeIndex → Digest)) ×
      ((Forgery × Bool) × GlobalMonitoredTracedState)

noncomputable def sourceGlobalTracedProgram
    (adversary : Adversary Concrete.scheme) :
    ProbComp SourceGlobalTracedProgramResult := do
  let keyView ← trajectoryProgrammedGlobalChainKeygen
  let execution ← sourceGlobalTracedDetailedExecution adversary keyView
  pure (keyView, execution)

def sourceGlobalProgramResult
    (result : SourceGlobalTracedProgramResult) :
    GlobalChainActionTracedResult :=
  let execution := sourceGlobalExecutionResult result.1 result.2
  ((result.1, execution.1), execution.2)

theorem sourceGlobalTracedProgram_eq_trajectoryProgrammedDetailedGame
    (adversary : Adversary Concrete.scheme) :
    sourceGlobalProgramResult <$> sourceGlobalTracedProgram adversary =
      trajectoryProgrammedGlobalChainDetailedGame adversary := by
  unfold sourceGlobalTracedProgram
    trajectoryProgrammedGlobalChainDetailedGame
  simp only [map_eq_bind_pure_comp, bind_assoc]
  apply bind_congr
  intro keyView
  rw [← sourceGlobalTracedDetailedExecution_eq_actionTraced]
  simp [sourceGlobalProgramResult, map_eq_bind_pure_comp]

noncomputable def globalHighMonitoredProgram
    (adversary : Adversary Concrete.scheme) :
    ProbComp GlobalHighMonitoredProgramResult := do
  let right ← coupledGlobalChainKeygenWithBaseHighFull
  let execution ← globalHighMonitoredDetailedExecution adversary right
  pure (right, execution)

def SourceGlobalHighMonitoredProgramRelation
    (left : SourceGlobalTracedProgramResult)
    (right : GlobalHighMonitoredProgramResult) : Prop :=
  ProgrammedGlobalChainKeygenBaseHighStableRelation left.1 right.1 ∧
    ((left.2.1 = right.2.1 ∧
      GlobalMonitoredTracedStateRelation left.1 right.1.1 left.2.2
        right.2.2) ∨ right.2.2.1.bad) ∧
    right.2.2.1.TraceConsistent right.1.1.2

theorem relTriple_sourceGlobal_globalHighMonitored_program
    (adversary : Adversary Concrete.scheme) :
    RelTriple (sourceGlobalTracedProgram adversary)
      (globalHighMonitoredProgram adversary)
      SourceGlobalHighMonitoredProgramRelation := by
  unfold sourceGlobalTracedProgram globalHighMonitoredProgram
  apply relTriple_bind
    (relTriple_with_support
      relTriple_trajectoryProgrammedGlobalChainKeygen_withBaseHigh_stable)
  intro left right hkeygen
  obtain ⟨hrel, hleftSupport, hrightSupport⟩ := hkeygen
  have hrightViewSupport :=
    coupledGlobalChainKeygenWithBaseHighFull_support_keyView right
      hrightSupport
  apply relTriple_bind
    (relTriple_with_support
      (relTriple_sourceGlobal_globalHighMonitored_detailedExecution adversary
        left right hrel hleftSupport hrightViewSupport))
  intro leftExecution rightExecution hexecution
  apply relTriple_pure_pure
  exact ⟨hrel, hexecution.1,
    globalHighMonitoredDetailedExecution_traceConsistent adversary right
      rightExecution hexecution.2.2⟩

end XmssSecurity.CappedChain
