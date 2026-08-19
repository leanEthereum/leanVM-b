import XmssSecurity.Proof.CappedGlobalChainHighMonitor

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

theorem globalCausalAttackerHashQueryFromHigh_cached_replays
    (table high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (output : HashOutput)
    (hplan : globalFilteredCausalAttackerHashPlan secretKey input state =
      .cached output)
    (result : (HashOutput × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalAttackerHashQueryFromHigh high secretKey input).run
          state)).run)) :
    ReplaysCausalReveals state.revealed result.2 result.1.2.revealed := by
  rw [globalCausalAttackerHashQueryFromHigh_run, hplan] at hresult
  simp only [simulateQ_pure, WriterT.run_pure', support_pure,
    Set.mem_singleton_iff] at hresult
  subst result
  simpa [globalCausalRecordedState_revealed] using
    ReplaysCausalReveals.nil state.revealed

theorem globalCausalAttackerHashQueryFromHigh_redirect_replays
    (table high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (output : HashOutput)
    (hplan : globalFilteredCausalAttackerHashPlan secretKey input state =
      .redirect output)
    (result : (HashOutput × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalAttackerHashQueryFromHigh high secretKey input).run
          state)).run)) :
    ReplaysCausalReveals state.revealed result.2 result.1.2.revealed := by
  rw [globalCausalAttackerHashQueryFromHigh_run, hplan] at hresult
  simp only [simulateQ_pure, WriterT.run_pure', support_pure,
    Set.mem_singleton_iff] at hresult
  subst result
  simpa using ReplaysCausalReveals.nil state.revealed

theorem globalCausalAttackerHashQueryFromHigh_fresh_replays
    (table high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (hplan : globalFilteredCausalAttackerHashPlan secretKey input state =
      .fresh)
    (result : (HashOutput × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalAttackerHashQueryFromHigh high secretKey input).run
          state)).run)) :
    ReplaysCausalReveals state.revealed result.2 result.1.2.revealed := by
  rw [globalCausalAttackerHashQueryFromHigh_run, hplan,
    simulate_eagerTrace_globalCausalHashQuery, support_map] at hresult
  obtain ⟨sample, _hsample, rfl⟩ := hresult
  rw [GlobalCausalHashState.setCache_revealed,
    globalCausalRecordedState_revealed]
  exact ReplaysCausalReveals.nil state.revealed

theorem globalCausalAttackerHashQueryFromHigh_reveal_replays
    (table high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex)
    (hplan : globalFilteredCausalAttackerHashPlan secretKey input state =
      .reveal index)
    (result : (HashOutput × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalAttackerHashQueryFromHigh high secretKey input).run
          state)).run)) :
    ReplaysCausalReveals state.revealed result.2 result.1.2.revealed := by
  rw [globalCausalAttackerHashQueryFromHigh_run, hplan,
    simulate_eagerTrace_globalCausalRevealHashQueryFromHigh] at hresult
  simp only [support_pure, Set.mem_singleton_iff] at hresult
  subst result
  apply ReplaysCausalReveals.reveal state.revealed _ index (table index) []
    (globalFilteredCausalRevealResultState secretKey input state index
      (table index) (Rom.hashOutputEquivDigestPair.symm
        (high index, table index))).revealed
  · exact globalFilteredCausalRevealResultState_transition secretKey input state
      index (table index) _
  · exact ReplaysCausalReveals.nil _

theorem globalCausalAttackerHashQueryFromHigh_probeThenFresh_replays
    (table high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex)
    (target : Digest)
    (hplan : globalFilteredCausalAttackerHashPlan secretKey input state =
      .probeThenFresh index target)
    (result : (HashOutput × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalAttackerHashQueryFromHigh high secretKey input).run
          state)).run)) :
    ReplaysCausalReveals state.revealed result.2 result.1.2.revealed := by
  rw [simulate_eagerTrace_globalCausalAttackerHashQueryFromHigh_probeThenFresh
    table high secretKey input state index target hplan, support_map] at hresult
  obtain ⟨sample, _hsample, rfl⟩ := hresult
  apply ReplaysCausalReveals.probe state.revealed _ index target []
  rw [GlobalCausalHashState.setCache_revealed,
    globalCausalRecordedState_revealed]
  exact ReplaysCausalReveals.nil state.revealed

theorem simulate_eagerTrace_globalCausalAttackerHashQueryFromHigh_support_replays
    (table high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (result : (HashOutput × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalAttackerHashQueryFromHigh high secretKey input).run
          state)).run)) :
    ReplaysCausalReveals state.revealed result.2 result.1.2.revealed := by
  generalize hplan : globalFilteredCausalAttackerHashPlan secretKey input state =
    plan
  cases plan with
  | cached output =>
      exact globalCausalAttackerHashQueryFromHigh_cached_replays table high
        secretKey input state output hplan result hresult
  | redirect output =>
      exact globalCausalAttackerHashQueryFromHigh_redirect_replays table high
        secretKey input state output hplan result hresult
  | fresh =>
      exact globalCausalAttackerHashQueryFromHigh_fresh_replays table high
        secretKey input state hplan result hresult
  | reveal index =>
      exact globalCausalAttackerHashQueryFromHigh_reveal_replays table high
        secretKey input state index hplan result hresult
  | probeThenFresh index target =>
      exact globalCausalAttackerHashQueryFromHigh_probeThenFresh_replays table
        high secretKey input state index target hplan result hresult

theorem relTriple_programmed_monitoredGlobalAttackerHashQuery_until_hit
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftCache : QueryCache HashSpec)
    (rightState : GlobalMonitoredCausalState)
    (hstate : GlobalMonitoredFilteredStateRelation left right.1 leftCache
      rightState)
    (input : HashInput) :
    RelTriple
      ((randomOracle input).run leftCache)
      ((monitorGlobalCausalTrace right.1.2 fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
          ((globalCausalAttackerHashQueryFromHigh
            (globalChainValueHighTableOfEdges right.2)
              right.1.1.secretKey input).run causalState)).run).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredFilteredStateRelation left right.1 leftResult.2
            rightResult.2) ∨ rightResult.2.bad) := by
  rcases hstate with
    ⟨monitor, hmonitor, hmonitorAgrees, hrevealed, hcausal, hretained⟩
  apply relTriple_monitorGlobalCausalTrace_of_filtered_until_hit left right.1
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

end XmssSecurity.CappedChain
