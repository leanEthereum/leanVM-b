import XmssSecurity.CausalEagerHighHitTransfer
import XmssSecurity.CausalStrategyReduction

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity

set_option maxRecDepth 1000000
set_option linter.constructorNameAsVariable false

theorem causalRevealHashQueryFromHigh_isProbeQueryBoundP
    (high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (index : ChainValueIndex) :
    (causalRevealHashQueryFromHigh high secretKey selected input state index)
      |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0 := by
  unfold causalRevealHashQueryFromHigh
  apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
    (RevealProbeOracleSimulation.revealQuery_isProbeQueryBoundP index 0)
  intro value _hvalue
  exact OracleComp.isQueryBoundP_pure
    (p := RevealProbeOracleSimulation.IsProbeQuery) _ 0

theorem filteredCausalAttackerHashQueryFromHigh_isProbeQueryBoundP
    (high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) :
    (filteredCausalAttackerHashQueryFromHigh high secretKey selected input).run
      state |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0 := by
  rw [filteredCausalAttackerHashQueryFromHigh_run]
  generalize hplan :
    filteredCausalAttackerHashPlan secretKey selected input state = plan
  cases plan with
  | cached output => simp
  | reveal index =>
      exact causalRevealHashQueryFromHigh_isProbeQueryBoundP high secretKey
        selected input state index
  | conditioned digest =>
      apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
        (RevealProbeOracleSimulation.liftProbComp_isProbeQueryBoundP
          (Rom.sampleHashOutputWithDigest digest) 0)
      intro output _houtput
      exact OracleComp.isQueryBoundP_pure
        (p := RevealProbeOracleSimulation.IsProbeQuery) _ 0
  | fresh =>
      exact causalHashQuery_run_isProbeQueryBoundP input
        (causalRecordedState secretKey selected input state)

theorem filteredProbingAttackerHashQueryAtFromHigh_isProbeQueryBoundP
    (high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState)
    (probe : Option (ChainValueIndex × Digest)) :
    (filteredProbingAttackerHashQueryAtFromHigh high secretKey selected input
      state probe).IsQueryBoundP
        RevealProbeOracleSimulation.IsProbeQuery 1 := by
  cases probe with
  | none =>
      exact (filteredCausalAttackerHashQueryFromHigh_isProbeQueryBoundP high
        secretKey selected input state).mono (by omega)
  | some probe =>
      cases hrevealed : state.revealed probe.1 with
      | some value =>
          simpa [filteredProbingAttackerHashQueryAtFromHigh, hrevealed] using
            (filteredCausalAttackerHashQueryFromHigh_isProbeQueryBoundP high
              secretKey selected input state).mono (by omega)
      | none =>
          rw [filteredProbingAttackerHashQueryAtFromHigh, hrevealed]
          apply OracleComp.isQueryBoundP_bind (n := 1) (m := 0)
            (RevealProbeOracleSimulation.probeQuery_isProbeQueryBoundP
              probe.1 probe.2)
          intro _ _hunit
          exact filteredCausalAttackerHashQueryFromHigh_isProbeQueryBoundP high
            secretKey selected input state

theorem filteredTreeHashComputationAtFromHigh_isProbeQueryBoundP
    (high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) :
    (filteredTreeHashComputationAtFromHigh high secretKey selected input state)
      |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 1 := by
  unfold filteredTreeHashComputationAtFromHigh
  generalize hplan : filteredTreeProbingAttackerHashQueryAtFromHigh high
    secretKey selected input state = plan
  cases plan with
  | chain probe =>
      exact filteredProbingAttackerHashQueryAtFromHigh_isProbeQueryBoundP high
        secretKey selected input state (some probe)
  | currentCached =>
      unfold FilteredTreeHashProgram.computation
      cases hcache : state.cache input with
      | none =>
          exact (causalHashQuery_run_isProbeQueryBoundP input state).mono
            (by omega)
      | some output => simp [filteredTreePureHashComputation]
  | keygenCached =>
      unfold FilteredTreeHashProgram.computation
      cases hcache : state.keygenCache input with
      | none =>
          exact (causalHashQuery_run_isProbeQueryBoundP input state).mono
            (by omega)
      | some output => simp [filteredTreePureHashComputation]
  | leafCached =>
      unfold FilteredTreeHashProgram.computation
      cases hcache : filteredTreeKeygenLeafOutput secretKey input state with
      | none =>
          exact (causalHashQuery_run_isProbeQueryBoundP input state).mono
            (by omega)
      | some output => simp [filteredTreePureHashComputation]
  | fresh =>
      unfold FilteredTreeHashProgram.computation
      exact (causalHashQuery_run_isProbeQueryBoundP input state).mono (by omega)
  | leafProbe probe =>
      unfold FilteredTreeHashProgram.computation
        filteredTreeProbeThenFreshHashComputation
        filteredTreeFreshHashComputation
      apply OracleComp.isQueryBoundP_bind (n := 1) (m := 0)
        (RevealProbeOracleSimulation.probeQuery_isProbeQueryBoundP
          probe.1 probe.2)
      intro _ _hunit
      exact causalHashQuery_run_isProbeQueryBoundP input state

attribute [local irreducible]
  FilteredTreeHashProgram.computation
  filteredTreeHashComputationAtFromHigh
  filteredTreeChainHashComputation
  filteredTreePureHashComputation
  filteredTreeFreshHashComputation
  filteredTreeProbeThenFreshHashComputation

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem filteredTreeHashComputationAtFromHigh_support_probeCount_le_one
    (table high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState)
    (result : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredTreeHashComputationAtFromHigh high secretKey selected input
          state)).run)) :
    RevealProbeOracleSimulation.observedProbeCount result.2 ≤ 1 := by
  have hbound :
      (filteredTreeHashComputationAtFromHigh high secretKey selected input
        state).IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 1 :=
    filteredTreeHashComputationAtFromHigh_isProbeQueryBoundP high secretKey
      selected input state
  exact
    RevealProbeOracleSimulation.simulate_eagerTrace_support_observedProbeCount_le
      (Index := ChainValueIndex) (α := HashOutput × CausalHashState) table
        (filteredTreeHashComputationAtFromHigh high secretKey selected input
          state) 1 hbound result hresult

def directHashActionCost :
    (OracleWorld + SigningSpec).Domain → Nat
  | .inl (.inr _) => 1
  | _ => 0

@[simp]
theorem attackerActionFragment_hashInputs_length
    (input : (OracleWorld + SigningSpec).Domain)
    (output : (OracleWorld + SigningSpec).Range input) :
    (attackerActionFragment input output).hashInputs.length =
      directHashActionCost input := by
  rcases input with (uniformOrHash | request)
  · rcases uniformOrHash with n | hashInput <;> rfl
  · rfl

theorem monitoredCausalResult_support_probeCount_growth
    (table : ChainValueIndex → Digest) (initial : MonitoredCausalState)
    (computation : OracleComp
      (RevealProbeOracleSimulation.World ChainValueIndex)
      (α × CausalHashState))
    (fuel : Nat)
    (hbound : computation.IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery fuel)
    (rawResult : (α × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hrawResult : rawResult ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        computation).run)) :
    RevealProbeOracleSimulation.observedProbeCount
        (monitoredCausalResult table initial rawResult).2.trace ≤
      RevealProbeOracleSimulation.observedProbeCount initial.trace + fuel := by
  have hrawCount :=
    RevealProbeOracleSimulation.simulate_eagerTrace_support_observedProbeCount_le
      (Index := ChainValueIndex) table computation fuel hbound rawResult
        hrawResult
  simp only [monitoredCausalResult]
  rw [RevealProbeOracleSimulation.observedProbeCount_append]
  omega

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem filteredHighMonitoredMappedAdversaryImpl_support_probeCount_growth
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : MonitoredTracedState)
    (result : (OracleWorld + SigningSpec).Range input ×
      MonitoredTracedState)
    (hresult : result ∈ support
      ((filteredHighMonitoredMappedAdversaryImpl keyHigh selected table input
        ).run state)) :
    RevealProbeOracleSimulation.observedProbeCount result.2.1.trace ≤
      RevealProbeOracleSimulation.observedProbeCount state.1.trace +
        directHashActionCost input := by
  unfold filteredHighMonitoredMappedAdversaryImpl actionTracedStateImpl at hresult
  change result ∈ support (do
    let baseResult ←
      (filteredHighMonitoredBaseMappedAdversaryImpl keyHigh selected table
        input).run state.1
    pure (baseResult.1,
      (baseResult.2, state.2 ++ attackerActionFragment input baseResult.1)))
      at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨baseResult, hbaseResult, hfinal⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  unfold filteredHighMonitoredBaseMappedAdversaryImpl at hbaseResult
  rw [monitorCausalTrace_run, support_map] at hbaseResult
  obtain ⟨rawResult, hrawResult, rfl⟩ := hbaseResult
  rcases input with (uniformOrHash | request)
  · rcases uniformOrHash with n | hashInput
    · exact monitoredCausalResult_support_probeCount_growth table state.1
        ((causalUniformImpl n).run state.1.causal) 0
          (causalUniformImpl_run_isProbeQueryBoundP n state.1.causal)
            rawResult hrawResult
    · have hrawCount :
          RevealProbeOracleSimulation.observedProbeCount rawResult.2 ≤ 1 :=
        filteredTreeHashComputationAtFromHigh_support_probeCount_le_one table
          (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected
            hashInput state.1.causal rawResult hrawResult
      simp only [monitoredCausalResult]
      rw [RevealProbeOracleSimulation.observedProbeCount_append]
      simp only [directHashActionCost]
      omega
  · exact monitoredCausalResult_support_probeCount_growth table state.1
      (filteredCausalSigningQuery keyHigh.1 selected request state.1.causal) 0
      (filteredCausalSigningQuery_isProbeQueryBoundP keyHigh.1 selected request
          state.1.causal) rawResult hrawResult

theorem filteredHighMonitoredMappedAdversaryImpl_support_actionTrace_eq
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : MonitoredTracedState)
    (result : (OracleWorld + SigningSpec).Range input ×
      MonitoredTracedState)
    (hresult : result ∈ support
      ((filteredHighMonitoredMappedAdversaryImpl keyHigh selected table input
        ).run state)) :
    result.2.2 = state.2 ++ attackerActionFragment input result.1 := by
  unfold filteredHighMonitoredMappedAdversaryImpl actionTracedStateImpl at hresult
  change result ∈ support (do
    let baseResult ←
      (filteredHighMonitoredBaseMappedAdversaryImpl keyHigh selected table
        input).run state.1
    pure (baseResult.1,
      (baseResult.2, state.2 ++ attackerActionFragment input baseResult.1)))
      at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨baseResult, _hbaseResult, hfinal⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  rfl

def MonitoredProbeCountCoveredByAttackerTrace
    (state : MonitoredTracedState) : Prop :=
  RevealProbeOracleSimulation.observedProbeCount state.1.trace ≤
    state.2.hashInputs.length

theorem filteredHighMonitoredMappedAdversaryImpl_preserves_probeCountCovered
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (input : (OracleWorld + SigningSpec).Domain)
    (state : MonitoredTracedState)
    (hcovered : MonitoredProbeCountCoveredByAttackerTrace state)
    (result : (OracleWorld + SigningSpec).Range input ×
      MonitoredTracedState)
    (hresult : result ∈ support
      ((filteredHighMonitoredMappedAdversaryImpl keyHigh selected table input
        ).run state)) :
    MonitoredProbeCountCoveredByAttackerTrace result.2 := by
  have hcount :=
    filteredHighMonitoredMappedAdversaryImpl_support_probeCount_growth table
      keyHigh selected input state result hresult
  have htrace :=
    filteredHighMonitoredMappedAdversaryImpl_support_actionTrace_eq table
      keyHigh selected input state result hresult
  unfold MonitoredProbeCountCoveredByAttackerTrace at hcovered ⊢
  rw [htrace, AttackerActionTrace.hashInputs_append, List.length_append,
    attackerActionFragment_hashInputs_length]
  omega

theorem filteredHighMonitoredAdversary_simulation_probeCountCovered
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : MonitoredTracedState)
    (hcovered : MonitoredProbeCountCoveredByAttackerTrace state)
    (result : α × MonitoredTracedState)
    (hresult : result ∈ support
      ((simulateQ
        (filteredHighMonitoredMappedAdversaryImpl keyHigh selected table)
          computation).run state)) :
    MonitoredProbeCountCoveredByAttackerTrace result.2 := by
  exact OracleComp.simulateQ_run_preservesInv
    (filteredHighMonitoredMappedAdversaryImpl keyHigh selected table)
    MonitoredProbeCountCoveredByAttackerTrace
    (fun input current hcurrent output houtput =>
      filteredHighMonitoredMappedAdversaryImpl_preserves_probeCountCovered
        table keyHigh selected input current hcurrent output houtput)
    computation state hcovered result hresult

def verifierHashQueryCost : OracleWorld.Domain → Nat
  | .inl _ => 0
  | .inr _ => 1

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem filteredHighMonitoredVerifierImpl_support_probeCount_growth
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (input : OracleWorld.Domain)
    (state : MonitoredTracedState)
    (result : OracleWorld.Range input × MonitoredTracedState)
    (hresult : result ∈ support
      ((filteredHighMonitoredVerifierImpl keyHigh selected table input).run
        state)) :
    RevealProbeOracleSimulation.observedProbeCount result.2.1.trace ≤
      RevealProbeOracleSimulation.observedProbeCount state.1.trace +
        verifierHashQueryCost input := by
  rcases input with n | hashInput
  · change result ∈ support
      ((filteredHighMonitoredUniformVerifierImpl table n).run state) at hresult
    unfold filteredHighMonitoredUniformVerifierImpl at hresult
    simp only [StateT.run_mk] at hresult
    rw [support_map] at hresult
    obtain ⟨baseResult, hbaseResult, rfl⟩ := hresult
    rw [monitorCausalTrace_run, support_map] at hbaseResult
    obtain ⟨rawResult, hrawResult, rfl⟩ := hbaseResult
    exact monitoredCausalResult_support_probeCount_growth table state.1
      ((causalUniformImpl n).run state.1.causal) 0
        (causalUniformImpl_run_isProbeQueryBoundP n state.1.causal) rawResult
          hrawResult
  · change result ∈ support
      ((filteredHighMonitoredHashVerifierImpl keyHigh selected table hashInput
        ).run state) at hresult
    rw [filteredHighMonitoredHashVerifierImpl_run,
      filteredHighMonitoredHashVerifierRun_eq, support_map] at hresult
    obtain ⟨baseResult, hbaseResult, rfl⟩ := hresult
    unfold monitoredTreeHashQuery at hbaseResult
    rw [monitorCausalTrace_run, support_map] at hbaseResult
    obtain ⟨rawResult, hrawResult, rfl⟩ := hbaseResult
    have hrawCount :
        RevealProbeOracleSimulation.observedProbeCount rawResult.2 ≤ 1 :=
      filteredTreeHashComputationAtFromHigh_support_probeCount_le_one table
        (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected
          hashInput state.1.causal rawResult hrawResult
    simp only [monitoredCausalResult]
    rw [RevealProbeOracleSimulation.observedProbeCount_append]
    simp only [verifierHashQueryCost]
    omega

def MonitoredBoundedObservedHit
    (queries : Nat) (table : ChainValueIndex → Digest)
    (state : MonitoredCausalState) : Prop :=
  RevealProbeOracleSimulation.runObserved table
    AdaptiveRevealMonitor.State.empty
    (RevealProbeOracleSimulation.enforceProbeTrace queries state.trace) = true

theorem monitoredBoundedObservedHit_of_bad_of_count_le
    (queries : Nat) (table : ChainValueIndex → Digest)
    (state : MonitoredCausalState)
    (hconsistent : state.TraceConsistent table) (hbad : state.bad)
    (hcount : RevealProbeOracleSimulation.observedProbeCount state.trace ≤
      queries) :
    MonitoredBoundedObservedHit queries table state := by
  unfold MonitoredBoundedObservedHit
  rw [RevealProbeOracleSimulation.enforceProbeTrace_eq_self_of_count_le
    state.trace queries hcount]
  exact MonitoredCausalState.bad_implies_runObserved table state hconsistent
    hbad

theorem monitoredCausalResult_preserves_boundedObservedHit
    (queries : Nat) (table : ChainValueIndex → Digest)
    (initial : MonitoredCausalState)
    (result : (α × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hhit : MonitoredBoundedObservedHit queries table initial) :
    MonitoredBoundedObservedHit queries table
      (monitoredCausalResult table initial result).2 := by
  unfold MonitoredBoundedObservedHit at hhit ⊢
  simp only [monitoredCausalResult]
  exact
    RevealProbeOracleSimulation.runObserved_enforceProbeTrace_append_eq_true_of_prefix
      table AdaptiveRevealMonitor.State.empty initial.trace result.2 queries
        hhit

theorem filteredHighMonitoredMappedAdversaryImpl_preserves_boundedObservedHit
    (queries : Nat) (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (input : (OracleWorld + SigningSpec).Domain)
    (state : MonitoredTracedState)
    (hhit : MonitoredBoundedObservedHit queries table state.1)
    (result : (OracleWorld + SigningSpec).Range input ×
      MonitoredTracedState)
    (hresult : result ∈ support
      ((filteredHighMonitoredMappedAdversaryImpl keyHigh selected table input
        ).run state)) :
    MonitoredBoundedObservedHit queries table result.2.1 := by
  unfold filteredHighMonitoredMappedAdversaryImpl actionTracedStateImpl at hresult
  change result ∈ support (do
    let baseResult ←
      (filteredHighMonitoredBaseMappedAdversaryImpl keyHigh selected table
        input).run state.1
    pure (baseResult.1,
      (baseResult.2, state.2 ++ attackerActionFragment input baseResult.1)))
      at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨baseResult, hbaseResult, hfinal⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  unfold filteredHighMonitoredBaseMappedAdversaryImpl at hbaseResult
  rw [monitorCausalTrace_run, support_map] at hbaseResult
  obtain ⟨rawResult, _hrawResult, rfl⟩ := hbaseResult
  exact monitoredCausalResult_preserves_boundedObservedHit queries table state.1
    rawResult hhit

theorem filteredHighMonitoredAdversary_simulation_preserves_boundedObservedHit
    (queries : Nat) (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : MonitoredTracedState)
    (hhit : MonitoredBoundedObservedHit queries table state.1)
    (result : α × MonitoredTracedState)
    (hresult : result ∈ support
      ((simulateQ
        (filteredHighMonitoredMappedAdversaryImpl keyHigh selected table)
          computation).run state)) :
    MonitoredBoundedObservedHit queries table result.2.1 := by
  exact OracleComp.simulateQ_run_preservesInv
    (filteredHighMonitoredMappedAdversaryImpl keyHigh selected table)
    (fun candidate : MonitoredTracedState =>
      MonitoredBoundedObservedHit queries table candidate.1)
    (fun input current hcurrent output houtput =>
      filteredHighMonitoredMappedAdversaryImpl_preserves_boundedObservedHit
        queries table keyHigh selected input current hcurrent output houtput)
    computation state hhit result hresult

theorem sourceDirectTracedMappedAdversaryImpl_support_info
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : SourceTracedState)
    (result : (OracleWorld + SigningSpec).Range input × SourceTracedState)
    (hresult : result ∈ support
      ((sourceDirectTracedMappedAdversaryImpl publicKey secretKey input).run
        state)) :
    result.1 ∈ support
        (sourceUnloggedMappedAdversaryImpl publicKey secretKey input) ∧
      result.2.2 = state.2 ++ attackerActionFragment input result.1 := by
  unfold sourceDirectTracedMappedAdversaryImpl actionTracedStateImpl at hresult
  change result ∈ support (do
    let baseResult ←
      (sourceDirectMappedAdversaryImpl publicKey secretKey input).run state.1
    pure (baseResult.1,
      (baseResult.2, state.2 ++ attackerActionFragment input baseResult.1)))
      at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨baseResult, hbaseResult, hfinal⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  have hprojected : baseResult.1 ∈ support
      ((sourceDirectMappedAdversaryImpl publicKey secretKey input).run'
        state.1) := by
    rw [StateT.run'_eq, support_map]
    exact ⟨baseResult, hbaseResult, rfl⟩
  have hsource : baseResult.1 ∈ support
      (sourceUnloggedMappedAdversaryImpl publicKey secretKey input) := by
    rw [sourceDirectMappedAdversaryImpl_eq_compose] at hprojected
    exact OracleComp.support_simulateQ_run'_subset xmssRomImpl
      (sourceUnloggedMappedAdversaryImpl publicKey secretKey input) state.1
        hprojected
  exact ⟨hsource, rfl⟩

set_option maxRecDepth 1000000 in
theorem sourceDirectTracedMappedAdversary_residual_hashQueryBound
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (finish : α → OracleComp OracleWorld β) (queries : Nat)
    (hbound : (simulateQ
      (sourceUnloggedMappedAdversaryImpl publicKey secretKey) computation >>=
        finish).IsQueryBoundP (· matches .inr _) queries)
    (cache : QueryCache HashSpec)
    (result : α × SourceTracedState)
    (hresult : result ∈ support
      ((simulateQ
        (sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
          computation).run (cache, []))) :
    result.2.2.hashInputs.length ≤ queries ∧
      (finish result.1).IsQueryBoundP (· matches .inr _)
        (queries - result.2.2.hashInputs.length) := by
  rw [sourceDirectTracedMappedAdversaryImpl_run_eq] at hresult
  rw [support_map] at hresult
  obtain ⟨rawResult, hrawResult, heq⟩ := hresult
  have hprojected : rawResult.1 ∈ support
      ((simulateQ xmssRomImpl
        ((simulateQ
          (sourceActionTracedMappedAdversaryImpl publicKey secretKey)
            computation).run)).run' cache) := by
    rw [StateT.run'_eq, support_map]
    exact ⟨rawResult, hrawResult, rfl⟩
  have hsource : rawResult.1 ∈ support
      ((simulateQ
        (sourceActionTracedMappedAdversaryImpl publicKey secretKey)
          computation).run) :=
    OracleComp.support_simulateQ_run'_subset xmssRomImpl
      ((simulateQ
        (sourceActionTracedMappedAdversaryImpl publicKey secretKey)
          computation).run) cache hprojected
  have hresidual := sourceActionTracedMappedAdversary_residual_hashQueryBound
    publicKey secretKey computation finish queries hbound rawResult.1 hsource
  have hresultValue : result.1 = rawResult.1.1 := by
    simpa using congrArg Prod.fst heq.symm
  have hresultTrace : result.2.2 = rawResult.1.2 := by
    simpa using congrArg (fun candidate => candidate.2.2) heq.symm
  rw [hresultValue, hresultTrace]
  exact hresidual

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem relTriple_sourceDirect_filteredHighMonitored_adversary_boundedHit
    (queries used fuel : Nat) (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest))
    (hrel : ProgrammedActualKeygenTreeCacheHighRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1.1 ∈ support
      (actualFixedChainKeygen selected))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (finish : α → OracleComp OracleWorld β)
    (hbound : (simulateQ
      (sourceUnloggedMappedAdversaryImpl left.publicKey left.secretKey)
        computation >>= finish).IsQueryBoundP (· matches .inr _) fuel)
    (leftState : SourceTracedState) (rightState : MonitoredTracedState)
    (hstate : MonitoredTracedStateRelation left.secretKey.parameter selected
      left.cache right.1.1.cache right.1.2 leftState rightState)
    (hconsistent : rightState.1.TraceConsistent right.1.2)
    (hcount : RevealProbeOracleSimulation.observedProbeCount
      rightState.1.trace ≤ used)
    (htotal : used + fuel ≤ queries) :
    RelTriple
      ((simulateQ
        (sourceDirectTracedMappedAdversaryImpl left.publicKey left.secretKey)
          computation).run leftState)
      ((simulateQ
        (filteredHighMonitoredMappedAdversaryImpl (right.1.1, right.2)
          selected right.1.2) computation).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredTracedStateRelation left.secretKey.parameter selected
            left.cache right.1.1.cache right.1.2
              leftResult.2 rightResult.2 ∧
          RevealProbeOracleSimulation.observedProbeCount
              rightResult.2.1.trace ≤ queries) ∨
        MonitoredBoundedObservedHit queries right.1.2 rightResult.2.1) := by
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
        (relTriple_sourceDirect_filteredHighMonitored_action selected left right
          hrel hleftSupport hrightSupport leftState rightState hstate input))
      intro headLeft headRight hhead
      have hleftInfo := sourceDirectTracedMappedAdversaryImpl_support_info
        left.publicKey left.secretKey input leftState headLeft hhead.2.1
      let continuation := fun response =>
        simulateQ
          (sourceUnloggedMappedAdversaryImpl left.publicKey left.secretKey)
            (next ((OracleSpec.query input).cont response)) >>= finish
      have hstepBound :
          (liftM (sourceUnloggedMappedAdversaryImpl left.publicKey
            left.secretKey input) >>= continuation).IsQueryBoundP
              (· matches .inr _) fuel := by
        exact hbound
      have hrestBound :=
        sourceUnloggedMappedAdversaryImpl_continuation_hashQueryBound
          left.publicKey left.secretKey input continuation fuel hstepBound
            headLeft.1 hleftInfo.1
      rw [attackerActionFragment_hashInputs_length] at hrestBound
      have hnextCount :=
        filteredHighMonitoredMappedAdversaryImpl_support_probeCount_growth
          right.1.2 (right.1.1, right.2) selected input rightState headRight
            hhead.2.2
      have hnextConsistent :=
        filteredHighMonitoredMappedAdversaryImpl_preserves_traceConsistent
          (right.1.1, right.2) selected right.1.2 input rightState hconsistent
            headRight hhead.2.2
      rcases hhead.1 with hgood | hbad
      · obtain ⟨hvalue, hstates⟩ := hgood
        rw [← hvalue]
        apply ih headLeft.1 (used + directHashActionCost input)
          (fuel - directHashActionCost input) finish hrestBound.2 headLeft.2
            headRight.2 hstates hnextConsistent (hnextCount.trans (by omega))
        omega
      · have hbounded : MonitoredBoundedObservedHit queries right.1.2
            headRight.2.1 :=
          monitoredBoundedObservedHit_of_bad_of_count_le queries right.1.2
            headRight.2.1 hnextConsistent hbad
              (hnextCount.trans (by omega))
        apply relTriple_post_mono
          (relTriple_prod
            (fun _result _hresult => True.intro)
            (filteredHighMonitoredAdversary_simulation_preserves_boundedObservedHit
              queries right.1.2 (right.1.1, right.2) selected
                (next ((OracleSpec.query input).cont headRight.1)) headRight.2
                  hbounded))
        intro _resultLeft _resultRight hresults
        exact Or.inr hresults.2

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem filteredHighMonitoredVerifierImpl_preserves_boundedObservedHit
    (queries : Nat) (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (input : OracleWorld.Domain)
    (state : MonitoredTracedState)
    (hhit : MonitoredBoundedObservedHit queries table state.1)
    (result : OracleWorld.Range input × MonitoredTracedState)
    (hresult : result ∈ support
      ((filteredHighMonitoredVerifierImpl keyHigh selected table input).run
        state)) :
    MonitoredBoundedObservedHit queries table result.2.1 := by
  rcases input with n | hashInput
  · change result ∈ support
      ((filteredHighMonitoredUniformVerifierImpl table n).run state) at hresult
    unfold filteredHighMonitoredUniformVerifierImpl at hresult
    simp only [StateT.run_mk] at hresult
    rw [support_map] at hresult
    obtain ⟨baseResult, hbaseResult, rfl⟩ := hresult
    rw [monitorCausalTrace_run, support_map] at hbaseResult
    obtain ⟨rawResult, _hrawResult, rfl⟩ := hbaseResult
    exact monitoredCausalResult_preserves_boundedObservedHit queries table
      state.1 rawResult hhit
  · change result ∈ support
      ((filteredHighMonitoredHashVerifierImpl keyHigh selected table hashInput
        ).run state) at hresult
    rw [filteredHighMonitoredHashVerifierImpl_run,
      filteredHighMonitoredHashVerifierRun_eq, support_map] at hresult
    obtain ⟨baseResult, hbaseResult, rfl⟩ := hresult
    unfold monitoredTreeHashQuery at hbaseResult
    rw [monitorCausalTrace_run, support_map] at hbaseResult
    obtain ⟨rawResult, _hrawResult, rfl⟩ := hbaseResult
    exact monitoredCausalResult_preserves_boundedObservedHit queries table
      state.1 rawResult hhit

theorem filteredHighMonitoredVerifier_simulation_preserves_boundedObservedHit
    (queries : Nat) (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (computation : OracleComp OracleWorld α)
    (state : MonitoredTracedState)
    (hhit : MonitoredBoundedObservedHit queries table state.1)
    (result : α × MonitoredTracedState)
    (hresult : result ∈ support
      ((simulateQ (filteredHighMonitoredVerifierImpl keyHigh selected table)
        computation).run state)) :
    MonitoredBoundedObservedHit queries table result.2.1 := by
  exact OracleComp.simulateQ_run_preservesInv
    (filteredHighMonitoredVerifierImpl keyHigh selected table)
    (fun candidate : MonitoredTracedState =>
      MonitoredBoundedObservedHit queries table candidate.1)
    (fun input current hcurrent output houtput =>
      filteredHighMonitoredVerifierImpl_preserves_boundedObservedHit queries
        table keyHigh selected input current hcurrent output houtput)
    computation state hhit result hresult

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem relTriple_sourceDirect_filteredHighMonitored_verifier_boundedHit
    (queries used fuel : Nat) (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest))
    (hrel : ProgrammedActualKeygenTreeCacheHighRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1.1 ∈ support
      (actualFixedChainKeygen selected))
    (computation : OracleComp OracleWorld α)
    (hbound : computation.IsQueryBoundP (· matches .inr _) fuel)
    (leftState : SourceTracedState) (rightState : MonitoredTracedState)
    (hstate : MonitoredTracedStateRelation left.secretKey.parameter selected
      left.cache right.1.1.cache right.1.2 leftState rightState)
    (hconsistent : rightState.1.TraceConsistent right.1.2)
    (hcount : RevealProbeOracleSimulation.observedProbeCount
      rightState.1.trace ≤ used)
    (htotal : used + fuel ≤ queries) :
    RelTriple
      ((simulateQ sourceDirectTracedVerifierImpl computation).run leftState)
      ((simulateQ
        (filteredHighMonitoredVerifierImpl (right.1.1, right.2) selected
          right.1.2) computation).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          MonitoredTracedStateRelation left.secretKey.parameter selected
            left.cache right.1.1.cache right.1.2
              leftResult.2 rightResult.2 ∧
          RevealProbeOracleSimulation.observedProbeCount
              rightResult.2.1.trace ≤ queries) ∨
        MonitoredBoundedObservedHit queries right.1.2 rightResult.2.1) := by
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
          (relTriple_sourceDirect_filteredHighMonitored_verifier_uniform_query
            selected left right hrel hleftSupport hrightSupport leftState
              rightState hstate n))
        intro headLeft headRight hhead
        rcases hhead.1 with hgood | hbad
        · obtain ⟨hvalue, hstates⟩ := hgood
          have hnextBound : (next headLeft.1).IsQueryBoundP
              (· matches .inr _) fuel := by
            rw [hvalue]
            simpa using hbound.2 headRight.1
          have hnextCount :=
            filteredHighMonitoredVerifierImpl_support_probeCount_growth
              right.1.2 (right.1.1, right.2) selected (.inl n) rightState
                headRight hhead.2.2
          simp only [verifierHashQueryCost] at hnextCount
          have hnextConsistent :=
            filteredHighMonitoredVerifier_preserves_traceConsistent
              (right.1.1, right.2) selected right.1.2 (.inl n) rightState
                hconsistent headRight hhead.2.2
          rw [← hvalue]
          exact ih headLeft.1 used fuel hnextBound headLeft.2 headRight.2 hstates
            hnextConsistent (hnextCount.trans (by omega)) htotal
        · have hnextCount :=
            filteredHighMonitoredVerifierImpl_support_probeCount_growth
              right.1.2 (right.1.1, right.2) selected (.inl n) rightState
                headRight hhead.2.2
          simp only [verifierHashQueryCost] at hnextCount
          have hnextConsistent :=
            filteredHighMonitoredVerifier_preserves_traceConsistent
              (right.1.1, right.2) selected right.1.2 (.inl n) rightState
                hconsistent headRight hhead.2.2
          have hbounded : MonitoredBoundedObservedHit queries right.1.2
              headRight.2.1 :=
            monitoredBoundedObservedHit_of_bad_of_count_le queries right.1.2
              headRight.2.1 hnextConsistent hbad
                (hnextCount.trans (by omega))
          apply relTriple_post_mono
            (relTriple_prod
              (fun _result _hresult => True.intro)
              (filteredHighMonitoredVerifier_simulation_preserves_boundedObservedHit
                queries right.1.2 (right.1.1, right.2) selected
                  (next headRight.1) headRight.2 hbounded))
          intro _resultLeft _resultRight hresults
          exact Or.inr hresults.2
      · have hfuel : 0 < fuel := hbound.1.resolve_left (by simp)
        have hquery :=
          relTriple_sourceDirect_filteredHighMonitored_verifier_hash_query_impl
            selected left right hrel hleftSupport hrightSupport leftState
              rightState hstate hashInput
        apply relTriple_bind (relTriple_with_support hquery)
        intro headLeft headRight hhead
        rcases hhead.1 with hgood | hbad
        · obtain ⟨hvalue, hstates⟩ := hgood
          have hnextBound : (next headLeft.1).IsQueryBoundP
              (· matches .inr _) (fuel - 1) := by
            rw [hvalue]
            simpa using hbound.2 headRight.1
          have hnextCount :=
            filteredHighMonitoredVerifierImpl_support_probeCount_growth
              right.1.2 (right.1.1, right.2) selected (.inr hashInput)
                rightState headRight hhead.2.2
          simp only [verifierHashQueryCost] at hnextCount
          have hnextConsistent :=
            filteredHighMonitoredVerifier_preserves_traceConsistent
              (right.1.1, right.2) selected right.1.2 (.inr hashInput)
                rightState hconsistent headRight hhead.2.2
          rw [← hvalue]
          apply ih headLeft.1 (used + 1) (fuel - 1) hnextBound headLeft.2
            headRight.2 hstates hnextConsistent (hnextCount.trans (by omega))
          omega
        · have hnextCount :=
            filteredHighMonitoredVerifierImpl_support_probeCount_growth
              right.1.2 (right.1.1, right.2) selected (.inr hashInput)
                rightState headRight hhead.2.2
          simp only [verifierHashQueryCost] at hnextCount
          have hnextConsistent :=
            filteredHighMonitoredVerifier_preserves_traceConsistent
              (right.1.1, right.2) selected right.1.2 (.inr hashInput)
                rightState hconsistent headRight hhead.2.2
          have hbounded : MonitoredBoundedObservedHit queries right.1.2
              headRight.2.1 :=
            monitoredBoundedObservedHit_of_bad_of_count_le queries right.1.2
              headRight.2.1 hnextConsistent hbad
                (hnextCount.trans (by omega))
          apply relTriple_post_mono
            (relTriple_prod
              (fun _result _hresult => True.intro)
              (filteredHighMonitoredVerifier_simulation_preserves_boundedObservedHit
                queries right.1.2 (right.1.1, right.2) selected
                  (next headRight.1) headRight.2 hbounded))
          intro _resultLeft _resultRight hresults
          exact Or.inr hresults.2

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem relTriple_sourceDirect_filteredHighMonitored_detailedExecution_boundedHit
    (queries : Nat) (adversary : Adversary Concrete.singleAttemptScheme)
    (selected : ChainIndex)
    (left : ProgrammedFixedChainKeygenView)
    (right : (ProgrammedFixedChainKeygenView ×
      (ChainValueIndex → Digest)) × (ChainEdgeIndex → Digest))
    (hrel : ProgrammedActualKeygenTreeCacheHighRelation selected left right)
    (hleftSupport : left ∈ support
      (programmedWarmedFixedChainKeygen selected))
    (hrightSupport : right.1.1 ∈ support
      (actualFixedChainKeygen selected))
    (hbound : HasHashQueryBound Concrete.singleAttemptScheme adversary queries) :
    RelTriple
      (sourceDirectTracedDetailedExecution adversary left)
      (filteredHighMonitoredDetailedExecution adversary
        (right.1.1, right.2) selected right.1.2)
      (fun leftResult rightResult =>
        ((leftResult.1 = rightResult.1 ∧
          MonitoredTracedStateRelation left.secretKey.parameter selected
            left.cache right.1.1.cache right.1.2
              leftResult.2 rightResult.2) ∧
          RevealProbeOracleSimulation.observedProbeCount
            rightResult.2.1.trace ≤ queries) ∨
        MonitoredBoundedObservedHit queries right.1.2 rightResult.2.1) := by
  have hinitial := monitoredTracedStateRelation_initial selected left right.1
    (programmedActualKeygenCacheHighRelation_to_stable selected left right
      hrel.base hleftSupport hrightSupport)
    hleftSupport hrightSupport
  have hinitialConsistent := monitoredCausalState_initial_traceConsistent
    right.1.2 (filteredCausalKeygenState selected right.1.1)
  have hleftKeyResult := programmedWarmedFixedChainKeygen_support_keyResult
    selected left hleftSupport
  have hsourceBound := sourceUnloggedDetailedGameAfterKeygen_hashQueryBound
    queries adversary hbound left.keyResult hleftKeyResult
  let finish : Forgery → OracleComp OracleWorld (Forgery × Bool) :=
    fun forgery => Prod.mk forgery <$> Concrete.singleAttemptScheme.verify left.publicKey
      forgery.epoch forgery.message forgery.signature
  have hfullBound : (simulateQ
      (sourceUnloggedMappedAdversaryImpl left.publicKey left.secretKey)
        (adversary.main left.publicKey) >>= finish).IsQueryBoundP
          (· matches .inr _) queries := by
    unfold sourceUnloggedDetailedGameAfterKeygen at hsourceBound
    exact hsourceBound
  unfold sourceDirectTracedDetailedExecution
    filteredHighMonitoredDetailedExecution
  rw [← hrel.base.base.1.2.1]
  apply relTriple_bind (relTriple_with_support
    (relTriple_sourceDirect_filteredHighMonitored_adversary_boundedHit
      queries 0 queries selected left right hrel hleftSupport hrightSupport
        (adversary.main left.publicKey) finish hfullBound (left.cache, [])
          (⟨filteredCausalKeygenState selected right.1.1,
            some AdaptiveRevealMonitor.State.empty, []⟩, []) hinitial
              hinitialConsistent (by simp
                [RevealProbeOracleSimulation.observedProbeCount]) (by omega)))
  intro leftHandled rightHandled hhandled
  rcases hhandled.1 with hgood | hhit
  · obtain ⟨hforgery, hstates, _hcoarseCount⟩ := hgood
    have hrightCovered :=
      filteredHighMonitoredAdversary_simulation_probeCountCovered right.1.2
        (right.1.1, right.2) selected (adversary.main left.publicKey)
          (⟨filteredCausalKeygenState selected right.1.1,
            some AdaptiveRevealMonitor.State.empty, []⟩, [])
          (by simp [MonitoredProbeCountCoveredByAttackerTrace,
            RevealProbeOracleSimulation.observedProbeCount,
            AttackerActionTrace.hashInputs]) rightHandled hhandled.2.2
    have hrightCount :
        RevealProbeOracleSimulation.observedProbeCount
            rightHandled.2.1.trace ≤
          leftHandled.2.2.hashInputs.length := by
      unfold MonitoredProbeCountCoveredByAttackerTrace at hrightCovered
      rw [← hstates.2] at hrightCovered
      exact hrightCovered
    have hresidual :=
      sourceDirectTracedMappedAdversary_residual_hashQueryBound
        left.publicKey left.secretKey (adversary.main left.publicKey) finish
          queries hfullBound left.cache leftHandled hhandled.2.1
    have hverifyBound :
        (Concrete.singleAttemptScheme.verify left.publicKey leftHandled.1.epoch
          leftHandled.1.message leftHandled.1.signature).IsQueryBoundP
            (· matches .inr _)
              (queries - leftHandled.2.2.hashInputs.length) := by
      unfold finish at hresidual
      exact (OracleComp.isQueryBoundP_map_iff _ _ _).mp hresidual.2
    rw [← hforgery]
    apply relTriple_bind
      (relTriple_sourceDirect_filteredHighMonitored_verifier_boundedHit
        queries leftHandled.2.2.hashInputs.length
          (queries - leftHandled.2.2.hashInputs.length) selected left right hrel
            hleftSupport hrightSupport
              (Concrete.singleAttemptScheme.verify left.publicKey leftHandled.1.epoch
                leftHandled.1.message leftHandled.1.signature)
              hverifyBound leftHandled.2 rightHandled.2 hstates
                (filteredHighMonitoredAdversary_simulation_preserves_traceConsistent
                  (right.1.1, right.2) selected right.1.2
                    (adversary.main left.publicKey)
                    (⟨filteredCausalKeygenState selected right.1.1,
                      some AdaptiveRevealMonitor.State.empty, []⟩, [])
                    hinitialConsistent rightHandled hhandled.2.2)
                hrightCount (by omega))
    intro leftVerified rightVerified hverified
    apply relTriple_pure_pure
    rcases hverified with hverifiedGood | hverifiedHit
    · exact Or.inl ⟨⟨congrArg (Prod.mk leftHandled.1) hverifiedGood.1,
          hverifiedGood.2.1⟩, hverifiedGood.2.2⟩
    · exact Or.inr hverifiedHit
  · apply relTriple_bind
      (relTriple_prod
        (fun _result _hresult => True.intro)
        (filteredHighMonitoredVerifier_simulation_preserves_boundedObservedHit
          queries right.1.2 (right.1.1, right.2) selected
            (Concrete.singleAttemptScheme.verify left.publicKey rightHandled.1.epoch
              rightHandled.1.message rightHandled.1.signature)
            rightHandled.2 hhit))
    intro leftVerified rightVerified hverified
    apply relTriple_pure_pure
    exact Or.inr hverified.2

noncomputable def filteredHighMonitoredBaseVerifierImpl
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest) :
    QueryImpl OracleWorld (StateT MonitoredCausalState ProbComp) :=
  fun input =>
    match input with
    | .inl n => StateT.mk fun state =>
        (monitorCausalTrace table fun causalState =>
          (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
            ((causalUniformImpl n).run causalState)).run).run state
    | .inr hashInput => StateT.mk fun state =>
        monitoredTreeHashQuery keyHigh selected table hashInput state

theorem filteredHighMonitoredVerifierImpl_query_run_eq
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest)
    (input : OracleWorld.Domain) (state : MonitoredCausalState)
    (attackerTrace : AttackerActionTrace) :
    (filteredHighMonitoredVerifierImpl keyHigh selected table input).run
        (state, attackerTrace) =
      (fun result => (result.1, (result.2, attackerTrace))) <$>
        (filteredHighMonitoredBaseVerifierImpl keyHigh selected table input).run
          state := by
  rcases input with n | hashInput
  · rfl
  · change
      (filteredHighMonitoredHashVerifierImpl keyHigh selected table hashInput
        ).run (state, attackerTrace) =
        (fun result => (result.1, (result.2, attackerTrace))) <$>
          monitoredTreeHashQuery keyHigh selected table hashInput state
    rw [filteredHighMonitoredHashVerifierImpl_run,
      filteredHighMonitoredHashVerifierRun_eq]

theorem filteredHighMonitoredVerifierImpl_run_eq
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest)
    (computation : OracleComp OracleWorld α)
    (state : MonitoredCausalState) (attackerTrace : AttackerActionTrace) :
    (simulateQ (filteredHighMonitoredVerifierImpl keyHigh selected table)
        computation).run (state, attackerTrace) =
      (fun result => (result.1, (result.2, attackerTrace))) <$>
        (simulateQ
          (filteredHighMonitoredBaseVerifierImpl keyHigh selected table)
            computation).run state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind input next ih =>
      simp only [StateT.run_bind, simulateQ_bind, simulateQ_spec_query,
        map_bind]
      rw [filteredHighMonitoredVerifierImpl_query_run_eq]
      simp only [bind_map_left]
      apply bind_congr
      intro head
      exact ih head.1 head.2

theorem map_simulate_filteredHighMonitoredVerifier_action_projection
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest)
    (publicKey : PublicKey) (forgery : Forgery)
    (state : MonitoredCausalState) (attackerTrace : AttackerActionTrace) :
    (fun result : Bool × MonitoredTracedState =>
      (((result.1, result.2.2), result.2.1.causal), result.2.1.trace)) <$>
        (simulateQ
          (filteredHighMonitoredVerifierImpl keyHigh selected table)
          (Concrete.singleAttemptScheme.verify publicKey forgery.epoch forgery.message
            forgery.signature)).run (state, attackerTrace) =
      (fun result : ((Bool × CausalHashState) ×
          RevealProbeOracleSimulation.ActionTrace ChainValueIndex) =>
        (((result.1.1, attackerTrace), result.1.2),
          state.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          ((simulateQ (filteredHighVerifierImpl keyHigh selected)
            (Concrete.singleAttemptScheme.verify publicKey forgery.epoch forgery.message
              forgery.signature)).run state.causal)).run := by
  let project := fun result : Bool × MonitoredTracedState =>
    ((result.1, result.2.1.causal), result.2.1.trace)
  let augment := fun result : ((Bool × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) =>
    (((result.1.1, attackerTrace), result.1.2), result.2)
  calc
    _ = augment <$> (project <$>
        (simulateQ
          (filteredHighMonitoredVerifierImpl keyHigh selected table)
          (Concrete.singleAttemptScheme.verify publicKey forgery.epoch forgery.message
            forgery.signature)).run (state, attackerTrace)) := by
      rw [filteredHighMonitoredVerifierImpl_run_eq]
      simp [augment, project, Functor.map_map]
    _ = _ := by
      rw [map_simulate_filteredHighMonitoredVerifier_verify_projection
        keyHigh selected table publicKey forgery state attackerTrace]
      simp [augment, Functor.map_map]

set_option maxHeartbeats 1000000 in
theorem map_filteredHighMonitoredDetailedExecution_action_projection
    (adversary : Adversary Concrete.singleAttemptScheme)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (table : ChainValueIndex → Digest) :
    (fun result : (Forgery × Bool) × MonitoredTracedState =>
      ((((result.1, result.2.2), result.2.1.causal), result.2.1.trace))) <$>
        filteredHighMonitoredDetailedExecution adversary keyHigh selected table =
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((filteredHighDetailedGameAfterKeygen adversary keyHigh selected).run
          (filteredCausalKeygenState selected keyHigh.1))).run := by
  unfold filteredHighMonitoredDetailedExecution
    filteredHighDetailedGameAfterKeygen
  simp only [map_bind, StateT.run_bind, map_pure]
  rw [simulateQ_bind, WriterT.run_bind']
  have heagerTail
      (handled : (Forgery × AttackerActionTrace) × CausalHashState) :
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (do
          let verified ←
            (simulateQ (filteredHighVerifierImpl keyHigh selected)
              (Concrete.singleAttemptScheme.verify keyHigh.1.publicKey
                handled.1.1.epoch handled.1.1.message
                  handled.1.1.signature)).run handled.2
          pure (((handled.1.1, verified.1), handled.1.2), verified.2))).run =
        (fun result : ((Bool × CausalHashState) ×
            RevealProbeOracleSimulation.ActionTrace ChainValueIndex) =>
          ((((handled.1.1, result.1.1), handled.1.2), result.1.2),
            result.2)) <$>
          (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
            ((simulateQ (filteredHighVerifierImpl keyHigh selected)
              (Concrete.singleAttemptScheme.verify keyHigh.1.publicKey
                handled.1.1.epoch handled.1.1.message
                  handled.1.1.signature)).run handled.2)).run := by
    rw [simulateQ_bind, WriterT.run_bind']
    simp
  have htail (handled : Forgery × MonitoredTracedState) :
      (do
        let verified ← (simulateQ
          (filteredHighMonitoredVerifierImpl keyHigh selected table)
          (Concrete.singleAttemptScheme.verify keyHigh.1.publicKey handled.1.epoch
            handled.1.message handled.1.signature)).run handled.2
        pure ((((handled.1, verified.1), verified.2.2),
          verified.2.1.causal), verified.2.1.trace)) =
        (fun result : ((Bool × CausalHashState) ×
            RevealProbeOracleSimulation.ActionTrace ChainValueIndex) =>
          ((((handled.1, result.1.1), handled.2.2), result.1.2),
            result.2)) <$>
          ((fun result : ((Bool × CausalHashState) ×
              RevealProbeOracleSimulation.ActionTrace ChainValueIndex) =>
            (result.1, handled.2.1.trace ++ result.2)) <$>
            (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
              ((simulateQ (filteredHighVerifierImpl keyHigh selected)
                (Concrete.singleAttemptScheme.verify keyHigh.1.publicKey handled.1.epoch
                  handled.1.message handled.1.signature)).run
                    handled.2.1.causal)).run) := by
    have hverifier :=
      map_simulate_filteredHighMonitoredVerifier_action_projection keyHigh
        selected table keyHigh.1.publicKey handled.1 handled.2.1 handled.2.2
    simpa [Functor.map_map] using congrArg
      (fun candidate =>
        (fun result : (((Bool × AttackerActionTrace) × CausalHashState) ×
            RevealProbeOracleSimulation.ActionTrace ChainValueIndex) =>
          ((((handled.1, result.1.1.1), result.1.1.2), result.1.2),
            result.2)) <$> candidate)
      hverifier
  simp_rw [htail]
  let initial : MonitoredCausalState :=
    ⟨filteredCausalKeygenState selected keyHigh.1,
      some AdaptiveRevealMonitor.State.empty, []⟩
  let project := fun result : Forgery × MonitoredTracedState =>
    (((result.1, result.2.2), result.2.1.causal), result.2.1.trace)
  let tail := fun head : (((Forgery × AttackerActionTrace) ×
      CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex) =>
    (fun result : ((Bool × CausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) =>
      ((((head.1.1.1, result.1.1), head.1.1.2), result.1.2),
        result.2)) <$>
      ((fun result : ((Bool × CausalHashState) ×
          RevealProbeOracleSimulation.ActionTrace ChainValueIndex) =>
        (result.1, head.2 ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          ((simulateQ (filteredHighVerifierImpl keyHigh selected)
            (Concrete.singleAttemptScheme.verify keyHigh.1.publicKey head.1.1.1.epoch
              head.1.1.1.message head.1.1.1.signature)).run
                head.1.2)).run)
  change (do
    let head ← (simulateQ
      (filteredHighMonitoredMappedAdversaryImpl keyHigh selected table)
      (adversary.main keyHigh.1.publicKey)).run (initial, [])
    tail (project head)) = _
  rw [← bind_map_left project]
  have hhead := map_simulate_filteredHighMonitoredMapped_action_projection
    table keyHigh selected (adversary.main keyHigh.1.publicKey) initial []
  change project <$> (simulateQ
      (filteredHighMonitoredMappedAdversaryImpl keyHigh selected table)
      (adversary.main keyHigh.1.publicKey)).run (initial, []) = _ at hhead
  simp only [initial, List.nil_append] at hhead
  rw [hhead, bind_map_left]
  apply bind_congr
  intro head
  simp only [tail, StateT.run_pure]
  rw [heagerTail head.1]
  simp only [Functor.map_map, Prod.map, id_eq]

set_option maxHeartbeats 1000000 in
theorem filteredHighMonitoredProgram_action_projection_eq_eagerExperiment
    (adversary : Adversary Concrete.singleAttemptScheme) (selected : ChainIndex) :
    filteredHighMonitoredProgramProjection <$>
        filteredHighMonitoredProgram adversary selected =
      RevealProbeOracleSimulation.eagerExperiment
        (filteredHighDirectProgram adversary selected) := by
  unfold filteredHighMonitoredProgram filteredHighMonitoredProgramProjection
    filteredHighDirectProgram
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
  change _ = (do
    let result ← (simulateQ
      (RevealProbeOracleSimulation.eagerTraceImpl table)
      ((fun execution => (keyHigh, execution)) <$>
        (filteredHighDetailedGameAfterKeygen adversary keyHigh selected).run
          (filteredCausalKeygenState selected keyHigh.1))).run
    pure (table, Prod.map id (fun trace => trace) result))
  rw [simulateQ_map, WriterT.run_map']
  have hdetail :=
    map_filteredHighMonitoredDetailedExecution_action_projection adversary
      keyHigh selected table
  simpa only [map_eq_bind_pure_comp, Functor.map_map,
    Function.comp_apply, Function.comp_def, Prod.map, Prod.map_apply, id_eq,
    bind_assoc, pure_bind, Prod.eta] using congrArg
      (fun candidate =>
        (fun result : ((((Forgery × Bool) × AttackerActionTrace) ×
            CausalHashState) ×
            RevealProbeOracleSimulation.ActionTrace ChainValueIndex) =>
          ((table, ((keyHigh, result.1), result.2)) :
            (ChainValueIndex → Digest) ×
              (FilteredHighDirectResult ×
                RevealProbeOracleSimulation.ActionTrace ChainValueIndex))) <$>
          candidate)
      hdetail

def SourceFilteredHighBoundedProgramRelation
    (queries : Nat) (selected : ChainIndex)
    (left : SourceDirectTracedProgramResult)
    (right : FilteredHighMonitoredProgramResult) : Prop :=
  ProgrammedActualKeygenTreeCacheHighRelation selected left.1 right.1 ∧
    ((((left.2.1 = right.2.1 ∧
      MonitoredTracedStateRelation left.1.secretKey.parameter selected
        left.1.cache right.1.1.1.cache right.1.1.2 left.2.2 right.2.2) ∧
      RevealProbeOracleSimulation.observedProbeCount right.2.2.1.trace ≤
        queries) ∨
      MonitoredBoundedObservedHit queries right.1.1.2 right.2.2.1) ∧
    right.2.2.1.TraceConsistent right.1.1.2)

attribute [local irreducible]
  actualFixedChainKeygen
  uniformCoupledWarmedFixedChainKeygenWithHigh
  programmedWarmedFixedChainKeygen

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 3000000 in
theorem relTriple_sourceDirect_filteredHighMonitored_program_boundedHit
    (queries : Nat) (adversary : Adversary Concrete.singleAttemptScheme)
    (selected : ChainIndex)
    (hbound : HasHashQueryBound Concrete.singleAttemptScheme adversary queries) :
    RelTriple
      (sourceDirectTracedProgram adversary selected)
      (filteredHighMonitoredProgram adversary selected)
      (SourceFilteredHighBoundedProgramRelation queries selected) := by
  unfold sourceDirectTracedProgram filteredHighMonitoredProgram
  apply relTriple_bind
    (relTriple_with_support
      (relTriple_programmedWarmedFixedChainKeygen_uniformHigh_tree selected))
  intro left right hkeygen
  obtain ⟨hrel, hleftSupport, hrightSupport⟩ := hkeygen
  have hrightActual :=
    uniformCoupledWarmedFixedChainKeygenWithHigh_support_actual selected right
      hrightSupport
  have hexecutionCoupling :=
    relTriple_sourceDirect_filteredHighMonitored_detailedExecution_boundedHit
      queries adversary selected left right hrel hleftSupport hrightActual
        hbound
  apply relTriple_bind (relTriple_with_support hexecutionCoupling)
  intro leftExecution rightExecution hexecution
  apply relTriple_pure_pure
  exact ⟨hrel, hexecution.1,
    filteredHighMonitoredDetailedExecution_traceConsistent adversary
      (right.1.1, right.2) selected right.1.2 rightExecution
        hexecution.2.2⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 3000000 in
theorem filteredHighMonitoredProgram_support_info
    (adversary : Adversary Concrete.singleAttemptScheme) (selected : ChainIndex)
    (result : FilteredHighMonitoredProgramResult)
    (hresult : result ∈ support
      (filteredHighMonitoredProgram adversary selected)) :
    result.1.1.1 ∈ support (actualFixedChainKeygen selected) ∧
      result.2 ∈ support
        (filteredHighMonitoredDetailedExecution adversary
          (result.1.1.1, result.1.2) selected result.1.1.2) := by
  unfold filteredHighMonitoredProgram at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨keyHigh, hkeyHigh, hrest⟩ := hresult
  rw [mem_support_bind_iff] at hrest
  obtain ⟨execution, hexecution, hpure⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  rcases hpure with rfl
  exact ⟨uniformCoupledWarmedFixedChainKeygenWithHigh_support_actual selected
      keyHigh hkeyHigh, hexecution⟩

def filteredHighBoundedMonitoredProgramProjection
    (queries : Nat) (result : FilteredHighMonitoredProgramResult) :
    (ChainValueIndex → Digest) ×
      (FilteredHighDirectResult ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex) :=
  RevealProbeOracleSimulation.enforceEagerResult queries
    (filteredHighMonitoredProgramProjection result)

set_option maxHeartbeats 1000000 in
theorem filteredHighBoundedMonitoredProgram_projection_eq_eagerExperiment
    (queries : Nat) (adversary : Adversary Concrete.singleAttemptScheme)
    (selected : ChainIndex) :
    filteredHighBoundedMonitoredProgramProjection queries <$>
        filteredHighMonitoredProgram adversary selected =
      RevealProbeOracleSimulation.eagerExperiment
        (boundedFilteredHighDirectProgram queries adversary selected) := by
  unfold boundedFilteredHighDirectProgram
  rw [RevealProbeOracleSimulation.eagerExperiment_enforceProbeBound_eq_map]
  rw [← filteredHighMonitoredProgram_action_projection_eq_eagerExperiment]
  calc
    filteredHighBoundedMonitoredProgramProjection queries <$>
        filteredHighMonitoredProgram adversary selected =
      (fun result => RevealProbeOracleSimulation.enforceEagerResult queries
        (filteredHighMonitoredProgramProjection result)) <$>
          filteredHighMonitoredProgram adversary selected := by rfl
    _ = RevealProbeOracleSimulation.enforceEagerResult queries <$>
        filteredHighMonitoredProgramProjection <$>
          filteredHighMonitoredProgram adversary selected := by
      rw [Functor.map_map]

set_option maxHeartbeats 1000000 in
theorem sourceFilteredHighBoundedProgramRelation_hit_implies_observedHit
    (queries : Nat) (adversary : Adversary Concrete.singleAttemptScheme)
    (selected : ChainIndex)
    (left : SourceDirectTracedProgramResult)
    (right : FilteredHighMonitoredProgramResult)
    (hleftSupport : left ∈ support
      (sourceDirectTracedProgram adversary selected))
    (hrightSupport : right ∈ support
      (filteredHighMonitoredProgram adversary selected))
    (hrel : SourceFilteredHighBoundedProgramRelation queries selected left
      right)
    (hhit : WarmedActionTracedChainProbeHit queries selected
      (sourceDirectProgramResult left)) :
    RevealProbeOracleSimulation.ObservedHit
      (filteredHighBoundedMonitoredProgramProjection queries right) := by
  have hleftKeySupport := sourceDirectTracedProgram_support_keygen adversary
    selected left hleftSupport
  obtain ⟨hrightKeySupport, hrightExecutionSupport⟩ :=
    filteredHighMonitoredProgram_support_info adversary selected right
      hrightSupport
  rcases hrel with ⟨hkeyRel, hgoodOrHit, hconsistent⟩
  rcases hgoodOrHit with hgood | hboundedHit
  · have hunbounded :=
      sourceFilteredHighMonitoredProgramRelation_hit_implies_observedHit
        queries adversary selected left right hleftKeySupport hrightKeySupport
          hrightExecutionSupport
          ⟨hkeyRel, Or.inl hgood.1, hconsistent⟩ hhit
    have hcount : RevealProbeOracleSimulation.observedProbeCount
        (filteredHighMonitoredProgramProjection right).2.2 ≤ queries := by
      exact hgood.2
    unfold filteredHighBoundedMonitoredProgramProjection
    exact
      (RevealProbeOracleSimulation.observedHit_enforceEagerResult_iff_of_count_le
        queries (filteredHighMonitoredProgramProjection right) hcount).2
          hunbounded
  · exact hboundedHit

def ProgrammedFilteredHighDirectHitRelation
    (queries : Nat) (selected : ChainIndex)
    (real : FixedChainActionTracedResult)
    (ideal : (ChainValueIndex → Digest) ×
      (FilteredHighDirectResult ×
        RevealProbeOracleSimulation.ActionTrace ChainValueIndex)) : Prop :=
  WarmedActionTracedChainProbeHit queries selected real →
    RevealProbeOracleSimulation.ObservedHit ideal

def HasBoundedFilteredHighDirectReduction
    (queries : Nat) (adversary : Adversary Concrete.singleAttemptScheme)
    (selected : ChainIndex) : Prop :=
  RelTriple
    (programmedWarmedDetailedGame adversary selected)
    (RevealProbeOracleSimulation.eagerExperiment
      (boundedFilteredHighDirectProgram queries adversary selected))
    (ProgrammedFilteredHighDirectHitRelation queries selected)

set_option maxHeartbeats 1000000 in
theorem hasBoundedFilteredHighDirectReduction_of_hashQueryBound
    (queries : Nat) (adversary : Adversary Concrete.singleAttemptScheme)
    (selected : ChainIndex)
    (hbound : HasHashQueryBound Concrete.singleAttemptScheme adversary queries) :
    HasBoundedFilteredHighDirectReduction queries adversary selected := by
  have hbase := relTriple_with_support
    (relTriple_sourceDirect_filteredHighMonitored_program_boundedHit queries
      adversary selected hbound)
  have hhit : RelTriple
      (sourceDirectTracedProgram adversary selected)
      (filteredHighMonitoredProgram adversary selected)
      (fun left right => ProgrammedFilteredHighDirectHitRelation queries selected
        (sourceDirectProgramResult left)
        (filteredHighBoundedMonitoredProgramProjection queries right)) := by
    apply relTriple_post_mono hbase
    intro left right hresult hsourceHit
    exact sourceFilteredHighBoundedProgramRelation_hit_implies_observedHit
      queries adversary selected left right hresult.2.1 hresult.2.2 hresult.1
        hsourceHit
  have hmapped := relTriple_map
    (f := sourceDirectProgramResult)
    (g := filteredHighBoundedMonitoredProgramProjection queries) hhit
  rw [sourceDirectTracedProgram_eq_programmedWarmedDetailedGame] at hmapped
  rw [filteredHighBoundedMonitoredProgram_projection_eq_eagerExperiment]
    at hmapped
  exact hmapped

theorem hasActionTracedEagerViewReduction_of_boundedFilteredHighDirectProbability
    (queries : Nat) (adversary : Adversary Concrete.singleAttemptScheme)
    (selected : ChainIndex)
    (hprogrammed :
      Pr[WarmedActionTracedChainProbeHit queries selected |
          programmedWarmedDetailedGame adversary selected] ≤
        Pr[RevealProbeOracleSimulation.ObservedHit |
          RevealProbeOracleSimulation.eagerExperiment
            (boundedFilteredHighDirectProgram queries adversary selected)]) :
    HasActionTracedEagerViewReduction queries adversary selected := by
  refine ⟨FilteredHighDirectResult,
    boundedFilteredHighDirectProgram queries adversary selected,
    boundedFilteredHighDirectProgram_isProbeQueryBoundP queries adversary
      selected, ?_⟩
  calc
    Pr[ActionTracedChainProbeHit queries selected |
        detailedGameWithKeygenCacheAndActionTrace adversary] =
        Pr[WarmedActionTracedChainProbeHit queries selected |
          chronologicallyWarmedDetailedGame adversary selected] :=
      actionTracedChainProbeHit_probability_eq_warmed queries adversary selected
    _ = Pr[WarmedActionTracedChainProbeHit queries selected |
          programmedWarmedDetailedGame adversary selected] :=
      probEvent_congr' (fun _ _ => Iff.rfl)
        (evalDist_chronologicallyWarmedDetailedGame_eq_programmed adversary
          selected)
    _ ≤ Pr[RevealProbeOracleSimulation.ObservedHit |
          RevealProbeOracleSimulation.eagerExperiment
            (boundedFilteredHighDirectProgram queries adversary selected)] :=
      hprogrammed

theorem hasActionTracedEagerViewReduction_of_boundedFilteredHighDirectRelTriple
    (queries : Nat) (adversary : Adversary Concrete.singleAttemptScheme)
    (selected : ChainIndex)
    (hcoupling : RelTriple
      (programmedWarmedDetailedGame adversary selected)
      (RevealProbeOracleSimulation.eagerExperiment
        (boundedFilteredHighDirectProgram queries adversary selected))
      (ProgrammedFilteredHighDirectHitRelation queries selected)) :
    HasActionTracedEagerViewReduction queries adversary selected := by
  apply hasActionTracedEagerViewReduction_of_boundedFilteredHighDirectProbability
    queries adversary selected
  apply probEvent_le_of_relTriple hcoupling
  intro real ideal hrel hhit
  exact hrel hhit

theorem hasActionTracedEagerViewReduction_of_boundedFilteredHighDirectReduction
    (queries : Nat) (adversary : Adversary Concrete.singleAttemptScheme)
    (selected : ChainIndex)
    (hreduction :
      HasBoundedFilteredHighDirectReduction queries adversary selected) :
    HasActionTracedEagerViewReduction queries adversary selected := by
  exact hasActionTracedEagerViewReduction_of_boundedFilteredHighDirectRelTriple
    queries adversary selected hreduction

end XmssSecurity
