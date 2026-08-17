import XmssSecurity.CappedGlobalChainHighWholeGame
import XmssSecurity.CappedGlobalChainHighProbeBounds
import XmssSecurity.CappedChain.CausalEagerHighDirectReduction

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

set_option maxHeartbeats 2000000
set_option maxRecDepth 2000000

theorem globalMonitoredCausalResult_support_probeCount_growth
    (table : GlobalChainValueIndex → Digest)
    (initial : GlobalMonitoredCausalState)
    (computation : OracleComp
      (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (α × GlobalCausalHashState))
    (fuel : Nat)
    (hbound : computation.IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery fuel)
    (rawResult : (α × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hrawResult : rawResult ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        computation).run)) :
    RevealProbeOracleSimulation.observedProbeCount
        (globalMonitoredCausalResult table initial rawResult).2.trace ≤
      RevealProbeOracleSimulation.observedProbeCount initial.trace + fuel := by
  have hrawCount :=
    RevealProbeOracleSimulation.simulate_eagerTrace_support_observedProbeCount_le
      (Index := GlobalChainValueIndex) table computation fuel hbound rawResult
        hrawResult
  simp only [globalMonitoredCausalResult]
  rw [RevealProbeOracleSimulation.observedProbeCount_append]
  omega

theorem globalHighMonitoredMappedAdversaryImpl_support_probeCount_growth
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalMonitoredTracedState)
    (result : (OracleWorld + SigningSpec).Range input ×
      GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((globalHighMonitoredMappedAdversaryImpl right input).run state)) :
    RevealProbeOracleSimulation.observedProbeCount result.2.1.trace ≤
      RevealProbeOracleSimulation.observedProbeCount state.1.trace +
        directHashActionCost input := by
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
  rcases input with (worldInput | request)
  · rcases worldInput with n | hashInput
    · simp only [globalHighMonitoredBaseMappedAdversaryImpl] at hbaseResult
      rw [monitorGlobalCausalTrace_run, support_map] at hbaseResult
      obtain ⟨rawResult, hrawResult, rfl⟩ := hbaseResult
      exact globalMonitoredCausalResult_support_probeCount_growth right.1.2
        state.1 ((globalCausalUniformImpl n).run state.1.causal) 0
          (globalCausalUniformImpl_run_isProbeQueryBoundP n state.1.causal)
            rawResult hrawResult
    · simp only [globalHighMonitoredBaseMappedAdversaryImpl] at hbaseResult
      rw [monitorGlobalCausalTrace_run, support_map] at hbaseResult
      obtain ⟨rawResult, hrawResult, rfl⟩ := hbaseResult
      exact globalMonitoredCausalResult_support_probeCount_growth right.1.2
        state.1
          ((globalCausalAttackerHashQueryFromHigh
            (globalChainValueHighTableOfEdges right.2)
              right.1.1.secretKey hashInput).run state.1.causal) 1
          (globalCausalAttackerHashQueryFromHigh_isProbeQueryBoundP
            (globalChainValueHighTableOfEdges right.2) right.1.1.secretKey
              hashInput state.1.causal) rawResult hrawResult
  · simp only [globalHighMonitoredBaseMappedAdversaryImpl] at hbaseResult
    rw [monitorGlobalCausalTrace_run, support_map] at hbaseResult
    obtain ⟨rawResult, hrawResult, rfl⟩ := hbaseResult
    exact globalMonitoredCausalResult_support_probeCount_growth right.1.2
      state.1 (globalFilteredCausalSigningQuery right.1.1 request
        state.1.causal) 0
      (globalFilteredCausalSigningQuery_isProbeQueryBoundP right.1.1 request
        state.1.causal) rawResult hrawResult

theorem globalHighMonitoredMappedAdversaryImpl_support_actionTrace_eq
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalMonitoredTracedState)
    (result : (OracleWorld + SigningSpec).Range input ×
      GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((globalHighMonitoredMappedAdversaryImpl right input).run state)) :
    result.2.2 = state.2 ++ attackerActionFragment input result.1 := by
  unfold globalHighMonitoredMappedAdversaryImpl actionTracedStateImpl at hresult
  change result ∈ support (do
    let baseResult ←
      (globalHighMonitoredBaseMappedAdversaryImpl right input).run state.1
    pure (baseResult.1,
      (baseResult.2, state.2 ++ attackerActionFragment input baseResult.1)))
      at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨baseResult, _hbaseResult, hfinal⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  rfl

def GlobalMonitoredProbeCountCoveredByAttackerTrace
    (state : GlobalMonitoredTracedState) : Prop :=
  RevealProbeOracleSimulation.observedProbeCount state.1.trace ≤
    state.2.hashInputs.length

theorem globalHighMonitoredMappedAdversaryImpl_preserves_probeCountCovered
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalMonitoredTracedState)
    (hcovered : GlobalMonitoredProbeCountCoveredByAttackerTrace state)
    (result : (OracleWorld + SigningSpec).Range input ×
      GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((globalHighMonitoredMappedAdversaryImpl right input).run state)) :
    GlobalMonitoredProbeCountCoveredByAttackerTrace result.2 := by
  have hcount :=
    globalHighMonitoredMappedAdversaryImpl_support_probeCount_growth right input
      state result hresult
  have htrace :=
    globalHighMonitoredMappedAdversaryImpl_support_actionTrace_eq right input
      state result hresult
  unfold GlobalMonitoredProbeCountCoveredByAttackerTrace at hcovered ⊢
  rw [htrace, AttackerActionTrace.hashInputs_append, List.length_append,
    attackerActionFragment_hashInputs_length]
  omega

theorem globalHighMonitoredAdversary_simulation_probeCountCovered
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : GlobalMonitoredTracedState)
    (hcovered : GlobalMonitoredProbeCountCoveredByAttackerTrace state)
    (result : α × GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((simulateQ (globalHighMonitoredMappedAdversaryImpl right)
        computation).run state)) :
    GlobalMonitoredProbeCountCoveredByAttackerTrace result.2 := by
  exact OracleComp.simulateQ_run_preservesInv
    (globalHighMonitoredMappedAdversaryImpl right)
    GlobalMonitoredProbeCountCoveredByAttackerTrace
    (fun input current hcurrent output houtput =>
      globalHighMonitoredMappedAdversaryImpl_preserves_probeCountCovered right
        input current hcurrent output houtput)
    computation state hcovered result hresult

theorem globalHighMonitoredVerifierImpl_support_probeCount_growth
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (input : OracleWorld.Domain)
    (state : GlobalMonitoredTracedState)
    (result : OracleWorld.Range input × GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((globalHighMonitoredVerifierImpl right input).run state)) :
    RevealProbeOracleSimulation.observedProbeCount result.2.1.trace ≤
      RevealProbeOracleSimulation.observedProbeCount state.1.trace +
        verifierHashQueryCost input := by
  unfold globalHighMonitoredVerifierImpl at hresult
  simp only [StateT.run_mk] at hresult
  rw [support_map] at hresult
  obtain ⟨baseResult, hbaseResult, rfl⟩ := hresult
  rcases input with n | hashInput
  · simp only [globalHighMonitoredBaseMappedAdversaryImpl] at hbaseResult
    rw [monitorGlobalCausalTrace_run, support_map] at hbaseResult
    obtain ⟨rawResult, hrawResult, rfl⟩ := hbaseResult
    exact globalMonitoredCausalResult_support_probeCount_growth right.1.2
      state.1 ((globalCausalUniformImpl n).run state.1.causal) 0
        (globalCausalUniformImpl_run_isProbeQueryBoundP n state.1.causal)
          rawResult hrawResult
  · simp only [globalHighMonitoredBaseMappedAdversaryImpl] at hbaseResult
    rw [monitorGlobalCausalTrace_run, support_map] at hbaseResult
    obtain ⟨rawResult, hrawResult, rfl⟩ := hbaseResult
    exact globalMonitoredCausalResult_support_probeCount_growth right.1.2
      state.1
        ((globalCausalAttackerHashQueryFromHigh
          (globalChainValueHighTableOfEdges right.2)
            right.1.1.secretKey hashInput).run state.1.causal) 1
        (globalCausalAttackerHashQueryFromHigh_isProbeQueryBoundP
          (globalChainValueHighTableOfEdges right.2) right.1.1.secretKey
            hashInput state.1.causal) rawResult hrawResult

def GlobalMonitoredBoundedObservedHit
    (queries : Nat) (table : GlobalChainValueIndex → Digest)
    (state : GlobalMonitoredCausalState) : Prop :=
  RevealProbeOracleSimulation.runObserved table
    AdaptiveRevealMonitor.State.empty
    (RevealProbeOracleSimulation.enforceProbeTrace queries state.trace) = true

theorem globalMonitoredBoundedObservedHit_of_bad_of_count_le
    (queries : Nat) (table : GlobalChainValueIndex → Digest)
    (state : GlobalMonitoredCausalState)
    (hconsistent : state.TraceConsistent table) (hbad : state.bad)
    (hcount : RevealProbeOracleSimulation.observedProbeCount state.trace ≤
      queries) :
    GlobalMonitoredBoundedObservedHit queries table state := by
  unfold GlobalMonitoredBoundedObservedHit
  rw [RevealProbeOracleSimulation.enforceProbeTrace_eq_self_of_count_le
    state.trace queries hcount]
  exact state.bad_implies_runObserved table hconsistent hbad

theorem globalMonitoredCausalResult_preserves_boundedObservedHit
    (queries : Nat) (table : GlobalChainValueIndex → Digest)
    (initial : GlobalMonitoredCausalState)
    (result : (α × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hhit : GlobalMonitoredBoundedObservedHit queries table initial) :
    GlobalMonitoredBoundedObservedHit queries table
      (globalMonitoredCausalResult table initial result).2 := by
  unfold GlobalMonitoredBoundedObservedHit at hhit ⊢
  simp only [globalMonitoredCausalResult]
  exact
    RevealProbeOracleSimulation.runObserved_enforceProbeTrace_append_eq_true_of_prefix
      table AdaptiveRevealMonitor.State.empty initial.trace result.2 queries
        hhit

theorem globalHighMonitoredMappedAdversaryImpl_preserves_boundedObservedHit
    (queries : Nat)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalMonitoredTracedState)
    (hhit : GlobalMonitoredBoundedObservedHit queries right.1.2 state.1)
    (result : (OracleWorld + SigningSpec).Range input ×
      GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((globalHighMonitoredMappedAdversaryImpl right input).run state)) :
    GlobalMonitoredBoundedObservedHit queries right.1.2 result.2.1 := by
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
  rcases input with (worldInput | request)
  · rcases worldInput with n | hashInput
    · simp only [globalHighMonitoredBaseMappedAdversaryImpl] at hbaseResult
      rw [monitorGlobalCausalTrace_run, support_map] at hbaseResult
      obtain ⟨rawResult, _hrawResult, rfl⟩ := hbaseResult
      exact globalMonitoredCausalResult_preserves_boundedObservedHit queries
        right.1.2 state.1 rawResult hhit
    · simp only [globalHighMonitoredBaseMappedAdversaryImpl] at hbaseResult
      rw [monitorGlobalCausalTrace_run, support_map] at hbaseResult
      obtain ⟨rawResult, _hrawResult, rfl⟩ := hbaseResult
      exact globalMonitoredCausalResult_preserves_boundedObservedHit queries
        right.1.2 state.1 rawResult hhit
  · simp only [globalHighMonitoredBaseMappedAdversaryImpl] at hbaseResult
    rw [monitorGlobalCausalTrace_run, support_map] at hbaseResult
    obtain ⟨rawResult, _hrawResult, rfl⟩ := hbaseResult
    exact globalMonitoredCausalResult_preserves_boundedObservedHit queries
      right.1.2 state.1 rawResult hhit

theorem globalHighMonitoredAdversary_simulation_preserves_boundedObservedHit
    (queries : Nat)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : GlobalMonitoredTracedState)
    (hhit : GlobalMonitoredBoundedObservedHit queries right.1.2 state.1)
    (result : α × GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((simulateQ (globalHighMonitoredMappedAdversaryImpl right)
        computation).run state)) :
    GlobalMonitoredBoundedObservedHit queries right.1.2 result.2.1 := by
  exact OracleComp.simulateQ_run_preservesInv
    (globalHighMonitoredMappedAdversaryImpl right)
    (fun candidate : GlobalMonitoredTracedState =>
      GlobalMonitoredBoundedObservedHit queries right.1.2 candidate.1)
    (fun input current hcurrent output houtput =>
      globalHighMonitoredMappedAdversaryImpl_preserves_boundedObservedHit
        queries right input current hcurrent output houtput)
    computation state hhit result hresult

theorem globalHighMonitoredVerifierImpl_preserves_boundedObservedHit
    (queries : Nat)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (input : OracleWorld.Domain)
    (state : GlobalMonitoredTracedState)
    (hhit : GlobalMonitoredBoundedObservedHit queries right.1.2 state.1)
    (result : OracleWorld.Range input × GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((globalHighMonitoredVerifierImpl right input).run state)) :
    GlobalMonitoredBoundedObservedHit queries right.1.2 result.2.1 := by
  unfold globalHighMonitoredVerifierImpl at hresult
  simp only [StateT.run_mk] at hresult
  rw [support_map] at hresult
  obtain ⟨baseResult, hbaseResult, rfl⟩ := hresult
  rcases input with n | hashInput
  · simp only [globalHighMonitoredBaseMappedAdversaryImpl] at hbaseResult
    rw [monitorGlobalCausalTrace_run, support_map] at hbaseResult
    obtain ⟨rawResult, _hrawResult, rfl⟩ := hbaseResult
    exact globalMonitoredCausalResult_preserves_boundedObservedHit queries
      right.1.2 state.1 rawResult hhit
  · simp only [globalHighMonitoredBaseMappedAdversaryImpl] at hbaseResult
    rw [monitorGlobalCausalTrace_run, support_map] at hbaseResult
    obtain ⟨rawResult, _hrawResult, rfl⟩ := hbaseResult
    exact globalMonitoredCausalResult_preserves_boundedObservedHit queries
      right.1.2 state.1 rawResult hhit

theorem globalHighMonitoredVerifier_simulation_preserves_boundedObservedHit
    (queries : Nat)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (computation : OracleComp OracleWorld α)
    (state : GlobalMonitoredTracedState)
    (hhit : GlobalMonitoredBoundedObservedHit queries right.1.2 state.1)
    (result : α × GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((simulateQ (globalHighMonitoredVerifierImpl right)
        computation).run state)) :
    GlobalMonitoredBoundedObservedHit queries right.1.2 result.2.1 := by
  exact OracleComp.simulateQ_run_preservesInv
    (globalHighMonitoredVerifierImpl right)
    (fun candidate : GlobalMonitoredTracedState =>
      GlobalMonitoredBoundedObservedHit queries right.1.2 candidate.1)
    (fun input current hcurrent output houtput =>
      globalHighMonitoredVerifierImpl_preserves_boundedObservedHit queries
        right input current hcurrent output houtput)
    computation state hhit result hresult

theorem relTriple_sourceGlobal_globalHighMonitored_adversary_boundedHit
    (countLimit hitLimit used fuel : Nat)
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (finish : α → OracleComp OracleWorld β)
    (hbound : (simulateQ
      (sourceUnloggedMappedAdversaryImpl left.publicKey
        (Concrete.materializePrecomputation left.cache left.secretKey))
        computation >>= finish).IsQueryBoundP (· matches .inr _) fuel)
    (leftState : SourceTracedState)
    (rightState : GlobalMonitoredTracedState)
    (hstate : GlobalMonitoredTracedStateRelation left right.1 leftState
      rightState)
    (hconsistent : rightState.1.TraceConsistent right.1.2)
    (hcount : RevealProbeOracleSimulation.observedProbeCount
      rightState.1.trace ≤ used)
    (htotal : used + fuel ≤ countLimit)
    (hlimits : countLimit ≤ hitLimit) :
    RelTriple
      ((simulateQ
        (sourceDirectTracedMappedAdversaryImpl left.publicKey
          (Concrete.materializePrecomputation left.cache left.secretKey))
          computation).run leftState)
      ((simulateQ (globalHighMonitoredMappedAdversaryImpl right)
        computation).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredTracedStateRelation left right.1 leftResult.2
            rightResult.2 ∧
          RevealProbeOracleSimulation.observedProbeCount
              rightResult.2.1.trace ≤ countLimit) ∨
        GlobalMonitoredBoundedObservedHit hitLimit right.1.2
          rightResult.2.1) := by
  induction computation using OracleComp.inductionOn generalizing leftState
      rightState used fuel finish with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure]
      apply relTriple_pure_pure
      exact Or.inl ⟨rfl, hstate, hcount.trans (by omega)⟩
  | query_bind input next ih =>
      rw [simulateQ_query_bind, bind_assoc] at hbound
      simp only [simulateQ_query_bind, StateT.run_bind]
      apply relTriple_bind (relTriple_with_support
        (relTriple_programmed_globalHighMonitored_action left right hrel
          hleftSupport hrightSupport leftState rightState hstate input))
      intro headLeft headRight hhead
      have hleftInfo := sourceDirectTracedMappedAdversaryImpl_support_info
        left.publicKey
          (Concrete.materializePrecomputation left.cache left.secretKey)
            input leftState headLeft hhead.2.1
      let continuation := fun response =>
        simulateQ
          (sourceUnloggedMappedAdversaryImpl left.publicKey
            (Concrete.materializePrecomputation left.cache left.secretKey))
            (next ((OracleSpec.query input).cont response)) >>= finish
      have hstepBound :
          (liftM (sourceUnloggedMappedAdversaryImpl left.publicKey
            (Concrete.materializePrecomputation left.cache left.secretKey)
              input) >>= continuation).IsQueryBoundP
              (· matches .inr _) fuel := by
        exact hbound
      have hrestBound :=
        sourceUnloggedMappedAdversaryImpl_continuation_hashQueryBound
          left.publicKey
            (Concrete.materializePrecomputation left.cache left.secretKey)
              input continuation fuel hstepBound headLeft.1 hleftInfo.1
      rw [attackerActionFragment_hashInputs_length] at hrestBound
      have hnextCount :=
        globalHighMonitoredMappedAdversaryImpl_support_probeCount_growth right
          input rightState headRight hhead.2.2
      have hnextConsistent :=
        globalHighMonitoredMappedAdversaryImpl_preserves_traceConsistent right
          input rightState hconsistent headRight hhead.2.2
      rcases hhead.1 with hgood | hbad
      · obtain ⟨hvalue, hstates⟩ := hgood
        rw [← hvalue]
        apply ih headLeft.1 (used + directHashActionCost input)
          (fuel - directHashActionCost input) finish hrestBound.2 headLeft.2
            headRight.2 hstates hnextConsistent (hnextCount.trans (by omega))
        omega
      · have hbounded : GlobalMonitoredBoundedObservedHit hitLimit right.1.2
            headRight.2.1 :=
          globalMonitoredBoundedObservedHit_of_bad_of_count_le hitLimit
            right.1.2 headRight.2.1 hnextConsistent hbad
              (hnextCount.trans (by omega))
        apply relTriple_post_mono
          (relTriple_prod
            (fun _result _hresult => True.intro)
            (globalHighMonitoredAdversary_simulation_preserves_boundedObservedHit
              hitLimit right
                (next ((OracleSpec.query input).cont headRight.1)) headRight.2
                  hbounded))
        intro _resultLeft _resultRight hresults
        exact Or.inr hresults.2

theorem relTriple_sourceGlobal_globalHighMonitored_verifier_boundedHit
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
    (leftState : SourceTracedState)
    (rightState : GlobalMonitoredTracedState)
    (hstate : GlobalMonitoredTracedStateRelation left right.1 leftState
      rightState)
    (hconsistent : rightState.1.TraceConsistent right.1.2)
    (hcount : RevealProbeOracleSimulation.observedProbeCount
      rightState.1.trace ≤ used)
    (htotal : used + fuel ≤ countLimit)
    (hlimits : countLimit ≤ hitLimit) :
    RelTriple
      ((simulateQ sourceDirectTracedVerifierImpl computation).run leftState)
      ((simulateQ (globalHighMonitoredVerifierImpl right) computation).run
        rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredTracedStateRelation left right.1 leftResult.2
            rightResult.2 ∧
          RevealProbeOracleSimulation.observedProbeCount
              rightResult.2.1.trace ≤ countLimit) ∨
        GlobalMonitoredBoundedObservedHit hitLimit right.1.2
          rightResult.2.1) := by
  induction computation using OracleComp.inductionOn generalizing leftState
      rightState used fuel with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure]
      apply relTriple_pure_pure
      exact Or.inl ⟨rfl, hstate, hcount.trans (by omega)⟩
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      simp only [simulateQ_query_bind, StateT.run_bind]
      rcases input with n | hashInput
      · apply relTriple_bind (relTriple_with_support
          (relTriple_programmed_globalHighMonitored_verifier_query left right
            hrel hleftSupport hrightSupport leftState rightState hstate
              (.inl n)))
        intro headLeft headRight hhead
        have hnextCount :=
          globalHighMonitoredVerifierImpl_support_probeCount_growth right
            (.inl n) rightState headRight hhead.2.2
        simp only [verifierHashQueryCost] at hnextCount
        have hnextConsistent :=
          globalHighMonitoredVerifierImpl_preserves_traceConsistent right
            (.inl n) rightState hconsistent headRight hhead.2.2
        rcases hhead.1 with hgood | hbad
        · obtain ⟨hvalue, hstates⟩ := hgood
          have hnextBound : (next headLeft.1).IsQueryBoundP
              (· matches .inr _) fuel := by
            rw [hvalue]
            simpa using hbound.2 headRight.1
          rw [← hvalue]
          exact ih headLeft.1 used fuel hnextBound headLeft.2 headRight.2
            hstates hnextConsistent (hnextCount.trans (by omega)) htotal
        · have hbounded : GlobalMonitoredBoundedObservedHit hitLimit right.1.2
              headRight.2.1 :=
            globalMonitoredBoundedObservedHit_of_bad_of_count_le hitLimit
              right.1.2 headRight.2.1 hnextConsistent hbad
                (hnextCount.trans (by omega))
          apply relTriple_post_mono
            (relTriple_prod
              (fun _result _hresult => True.intro)
              (globalHighMonitoredVerifier_simulation_preserves_boundedObservedHit
                hitLimit right (next headRight.1) headRight.2 hbounded))
          intro _resultLeft _resultRight hresults
          exact Or.inr hresults.2
      · have hfuel : 0 < fuel := hbound.1.resolve_left (by simp)
        apply relTriple_bind (relTriple_with_support
          (relTriple_programmed_globalHighMonitored_verifier_query left right
            hrel hleftSupport hrightSupport leftState rightState hstate
              (.inr hashInput)))
        intro headLeft headRight hhead
        have hnextCount :=
          globalHighMonitoredVerifierImpl_support_probeCount_growth right
            (.inr hashInput) rightState headRight hhead.2.2
        simp only [verifierHashQueryCost] at hnextCount
        have hnextConsistent :=
          globalHighMonitoredVerifierImpl_preserves_traceConsistent right
            (.inr hashInput) rightState hconsistent headRight hhead.2.2
        rcases hhead.1 with hgood | hbad
        · obtain ⟨hvalue, hstates⟩ := hgood
          have hnextBound : (next headLeft.1).IsQueryBoundP
              (· matches .inr _) (fuel - 1) := by
            rw [hvalue]
            simpa using hbound.2 headRight.1
          rw [← hvalue]
          apply ih headLeft.1 (used + 1) (fuel - 1) hnextBound headLeft.2
            headRight.2 hstates hnextConsistent (hnextCount.trans (by omega))
          omega
        · have hbounded : GlobalMonitoredBoundedObservedHit hitLimit right.1.2
              headRight.2.1 :=
            globalMonitoredBoundedObservedHit_of_bad_of_count_le hitLimit
              right.1.2 headRight.2.1 hnextConsistent hbad
                (hnextCount.trans (by omega))
          apply relTriple_post_mono
            (relTriple_prod
              (fun _result _hresult => True.intro)
              (globalHighMonitoredVerifier_simulation_preserves_boundedObservedHit
                hitLimit right (next headRight.1) headRight.2 hbounded))
          intro _resultLeft _resultRight hresults
          exact Or.inr hresults.2

theorem relTriple_sourceGlobal_globalHighMonitored_detailedExecution_boundedHit
    (countLimit hitLimit : Nat)
    (adversary : Adversary Concrete.scheme)
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (hbound : HasHashQueryBound Concrete.scheme adversary countLimit)
    (hlimits : countLimit ≤ hitLimit) :
    RelTriple
      (sourceGlobalTracedDetailedExecution adversary left)
      (globalHighMonitoredDetailedExecution adversary right)
      (fun leftResult rightResult =>
        ((leftResult.1 = rightResult.1 ∧
          GlobalMonitoredTracedStateRelation left right.1 leftResult.2
            rightResult.2) ∧
          RevealProbeOracleSimulation.observedProbeCount
            rightResult.2.1.trace ≤ countLimit) ∨
        GlobalMonitoredBoundedObservedHit hitLimit right.1.2
          rightResult.2.1) := by
  have hinitial := globalMonitoredTracedStateRelation_initial left right hrel
    hleftSupport hrightSupport
  have hinitialConsistent := globalMonitoredCausalState_initial_traceConsistent
    right.1.2 (globalFilteredCausalKeygenState right.1.1)
  have hleftKeyResult := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    left hleftSupport
  have hmaterializedKeyResult :
      Concrete.materializeCachedKeyResult left.keyResult ∈ support
        ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅) := by
    exact Concrete.oldKeygen_support_materializedPrecomputedKeygen
      left.keyResult hleftKeyResult
  have hsourceBound := sourceUnloggedDetailedGameAfterKeygen_hashQueryBound
    countLimit adversary hbound
      (Concrete.materializeCachedKeyResult left.keyResult)
        hmaterializedKeyResult
  let finish : Forgery → OracleComp OracleWorld (Forgery × Bool) :=
    fun forgery => Prod.mk forgery <$> Concrete.scheme.verify
      left.publicKey forgery.epoch forgery.message forgery.signature
  have hfullBound : (simulateQ
      (sourceUnloggedMappedAdversaryImpl left.publicKey
        (Concrete.materializePrecomputation left.cache left.secretKey))
        (adversary.main left.publicKey) >>= finish).IsQueryBoundP
          (· matches .inr _) countLimit := by
    unfold sourceUnloggedDetailedGameAfterKeygen at hsourceBound
    exact hsourceBound
  have hpublicKey : left.publicKey = right.1.1.publicKey :=
    hrel.1.toStable.1.2.1
  unfold sourceGlobalTracedDetailedExecution
    globalHighMonitoredDetailedExecution
  rw [← hpublicKey]
  apply relTriple_bind (relTriple_with_support
    (relTriple_sourceGlobal_globalHighMonitored_adversary_boundedHit
      countLimit hitLimit 0 countLimit left right hrel hleftSupport hrightSupport
        (adversary.main left.publicKey) finish hfullBound (left.cache, [])
          (⟨globalFilteredCausalKeygenState right.1.1,
            some AdaptiveRevealMonitor.State.empty, []⟩, []) hinitial
              hinitialConsistent (by simp
                [RevealProbeOracleSimulation.observedProbeCount]) (by omega)
                  hlimits))
  intro leftHandled rightHandled hhandled
  rcases hhandled.1 with hgood | hhit
  · obtain ⟨hforgery, hstates, _hcoarseCount⟩ := hgood
    have hrightCovered :=
      globalHighMonitoredAdversary_simulation_probeCountCovered right
        (adversary.main left.publicKey)
          (⟨globalFilteredCausalKeygenState right.1.1,
            some AdaptiveRevealMonitor.State.empty, []⟩, [])
          (by simp [GlobalMonitoredProbeCountCoveredByAttackerTrace,
            RevealProbeOracleSimulation.observedProbeCount,
            AttackerActionTrace.hashInputs]) rightHandled hhandled.2.2
    have hrightCount :
        RevealProbeOracleSimulation.observedProbeCount
            rightHandled.2.1.trace ≤
          leftHandled.2.2.hashInputs.length := by
      unfold GlobalMonitoredProbeCountCoveredByAttackerTrace at hrightCovered
      rw [← hstates.2] at hrightCovered
      exact hrightCovered
    have hresidual :=
      sourceDirectTracedMappedAdversary_residual_hashQueryBound
        left.publicKey
          (Concrete.materializePrecomputation left.cache left.secretKey)
            (adversary.main left.publicKey) finish countLimit hfullBound
              left.cache leftHandled hhandled.2.1
    have hverifyBound :
        (Concrete.scheme.verify left.publicKey leftHandled.1.epoch
          leftHandled.1.message leftHandled.1.signature).IsQueryBoundP
            (· matches .inr _)
              (countLimit - leftHandled.2.2.hashInputs.length) := by
      unfold finish at hresidual
      exact (OracleComp.isQueryBoundP_map_iff _ _ _).mp hresidual.2
    rw [← hforgery]
    apply relTriple_bind
      (relTriple_sourceGlobal_globalHighMonitored_verifier_boundedHit
        countLimit hitLimit leftHandled.2.2.hashInputs.length
          (countLimit - leftHandled.2.2.hashInputs.length) left right hrel
            hleftSupport hrightSupport
              (Concrete.scheme.verify left.publicKey leftHandled.1.epoch
                leftHandled.1.message leftHandled.1.signature)
              hverifyBound leftHandled.2 rightHandled.2 hstates
                (OracleComp.simulateQ_run_preservesInv
                  (globalHighMonitoredMappedAdversaryImpl right)
                  (fun state : GlobalMonitoredTracedState =>
                    state.1.TraceConsistent right.1.2)
                  (globalHighMonitoredMappedAdversaryImpl_preserves_traceConsistent
                    right)
                  (adversary.main left.publicKey)
                  (⟨globalFilteredCausalKeygenState right.1.1,
                    some AdaptiveRevealMonitor.State.empty, []⟩, [])
                  hinitialConsistent rightHandled hhandled.2.2)
                hrightCount (by omega) hlimits)
    intro leftVerified rightVerified hvertified
    apply relTriple_pure_pure
    rcases hvertified with hvertifiedGood | hvertifiedHit
    · exact Or.inl ⟨⟨congrArg (Prod.mk leftHandled.1) hvertifiedGood.1,
          hvertifiedGood.2.1⟩, hvertifiedGood.2.2⟩
    · exact Or.inr hvertifiedHit
  · apply relTriple_bind
      (relTriple_prod
        (fun _result _hresult => True.intro)
        (globalHighMonitoredVerifier_simulation_preserves_boundedObservedHit
          hitLimit right
            (Concrete.scheme.verify left.publicKey rightHandled.1.epoch
              rightHandled.1.message rightHandled.1.signature)
            rightHandled.2 hhit))
    intro leftVerified rightVerified hvertified
    apply relTriple_pure_pure
    exact Or.inr hvertified.2

def SourceGlobalHighBoundedProgramRelation
    (countLimit hitLimit : Nat)
    (left : SourceGlobalTracedProgramResult)
    (right : GlobalHighMonitoredProgramResult) : Prop :=
  ProgrammedGlobalChainKeygenBaseHighStableRelation left.1 right.1 ∧
    ((((left.2.1 = right.2.1 ∧
      GlobalMonitoredTracedStateRelation left.1 right.1.1 left.2.2
        right.2.2) ∧
      RevealProbeOracleSimulation.observedProbeCount right.2.2.1.trace ≤
        countLimit) ∨
      GlobalMonitoredBoundedObservedHit hitLimit right.1.1.2 right.2.2.1) ∧
    right.2.2.1.TraceConsistent right.1.1.2)

theorem relTriple_sourceGlobal_globalHighMonitored_program_boundedHit
    (countLimit hitLimit : Nat)
    (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary countLimit)
    (hlimits : countLimit ≤ hitLimit) :
    RelTriple (sourceGlobalTracedProgram adversary)
      (globalHighMonitoredProgram adversary)
      (SourceGlobalHighBoundedProgramRelation countLimit hitLimit) := by
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
      (relTriple_sourceGlobal_globalHighMonitored_detailedExecution_boundedHit
        countLimit hitLimit adversary left right hrel hleftSupport
          hrightViewSupport hbound hlimits))
  intro leftExecution rightExecution hexecution
  apply relTriple_pure_pure
  exact ⟨hrel, hexecution.1,
    globalHighMonitoredDetailedExecution_traceConsistent adversary right
      rightExecution hexecution.2.2⟩

end XmssSecurity.CappedChain
