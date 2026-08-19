import XmssSecurity.Proof.CappedGlobalChainHighAttackerHashComplete

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

set_option maxRecDepth 10000000
set_option maxHeartbeats 2000000

theorem GlobalMerkleKeygenCacheRetained.recordedState
    {secretKey : SecretKey} {state : GlobalCausalHashState}
    (hretained : GlobalMerkleKeygenCacheRetained secretKey state)
    (input : HashInput) :
    GlobalMerkleKeygenCacheRetained secretKey
      (globalCausalRecordedState secretKey input state) := by
  intro candidate hmerkle output hkeygen
  rw [globalCausalRecordedState_keygenCache] at hkeygen
  rw [globalCausalRecordedState_cache]
  exact hretained candidate hmerkle output hkeygen

theorem GlobalMerkleKeygenCacheRetained.cacheQuery_of_none
    {secretKey : SecretKey} {state : GlobalCausalHashState}
    (hretained : GlobalMerkleKeygenCacheRetained secretKey state)
    (input : HashInput) (output : HashOutput)
    (hcache : state.cache input = none) :
    GlobalMerkleKeygenCacheRetained secretKey
      { state with cache := state.cache.cacheQuery input output } := by
  intro candidate hmerkle candidateOutput hkeygen
  change state.keygenCache candidate = some candidateOutput at hkeygen
  change state.cache.cacheQuery input output candidate = some candidateOutput
  by_cases heq : candidate = input
  · subst candidate
    have hcurrent := hretained input hmerkle candidateOutput hkeygen
    rw [hcache] at hcurrent
    contradiction
  · rw [QueryCache.cacheQuery_of_ne _ _ heq]
    exact hretained candidate hmerkle candidateOutput hkeygen

theorem simulate_eagerTrace_globalCausalHashQuery_merkleRetained_of_cache_none
    (table : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (hretained : GlobalMerkleKeygenCacheRetained secretKey state)
    (hcache : state.cache input = none)
    (result : (HashOutput × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalHashQuery input).run state)).run)) :
    GlobalMerkleKeygenCacheRetained secretKey result.1.2 := by
  rw [simulate_eagerTrace_globalCausalHashQuery, support_map] at hresult
  obtain ⟨raw, hraw, rfl⟩ := hresult
  rw [randomOracle, QueryImpl.withCaching_run_none _ hcache, support_map] at hraw
  obtain ⟨output, _houtput, rfl⟩ := hraw
  exact hretained.cacheQuery_of_none input output hcache

theorem globalFilteredCausalUncachedAttackerHashPlan_ne_cached
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (probe : Option (GlobalChainValueIndex × Digest))
    (output : HashOutput) :
    globalFilteredCausalUncachedAttackerHashPlan secretKey input state probe ≠
      .cached output := by
  intro hplan
  unfold globalFilteredCausalUncachedAttackerHashPlan at hplan
  split at hplan
  · split at hplan
    · split at hplan
      · split at hplan <;> contradiction
      · contradiction
    · split at hplan <;> contradiction
  · unfold globalFilteredCausalLeafHashPlan at hplan
    split at hplan
    · contradiction
    · split at hplan
      · contradiction
      · split at hplan
        · split at hplan <;> contradiction
        · contradiction

theorem simulate_eagerTrace_globalCausalAttackerHashQueryFromHigh_merkleRetained
    (table high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (hretained : GlobalMerkleKeygenCacheRetained secretKey state)
    (result : (HashOutput × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalAttackerHashQueryFromHigh high secretKey input).run
          state)).run)) :
    GlobalMerkleKeygenCacheRetained secretKey result.1.2 := by
  cases hcache : state.cache input with
  | some cachedOutput =>
      have hplan : globalFilteredCausalAttackerHashPlan secretKey input state =
          .cached cachedOutput := by
        simp [globalFilteredCausalAttackerHashPlan, hcache]
      rw [globalCausalAttackerHashQueryFromHigh_run, hplan, simulateQ_pure,
        WriterT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact hretained.recordedState input
  | none =>
      generalize hplan : globalFilteredCausalAttackerHashPlan secretKey input
        state = plan
      cases plan with
      | cached output =>
          have huncached : globalFilteredCausalUncachedAttackerHashPlan
              secretKey input state
                (globalChainInputProbe? secretKey.parameter input) =
              .cached output := by
            rw [globalFilteredCausalAttackerHashPlan, hcache] at hplan
            exact hplan
          exact (globalFilteredCausalUncachedAttackerHashPlan_ne_cached
            secretKey input state
              (globalChainInputProbe? secretKey.parameter input) output
                huncached).elim
      | redirect output =>
          rw [globalCausalAttackerHashQueryFromHigh_run, hplan, simulateQ_pure,
            WriterT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
          subst result
          simpa [globalFilteredCausalRedirectResultState] using
            (hretained.recordedState input).cacheQuery_of_none input output
              (by simpa using hcache)
      | probeThenFresh index target =>
          rw [simulate_eagerTrace_globalCausalAttackerHashQueryFromHigh_probeThenFresh
            table high secretKey input state index target hplan, support_map]
              at hresult
          obtain ⟨raw, hraw, rfl⟩ := hresult
          rw [randomOracle, QueryImpl.withCaching_run_none _ hcache,
            support_map] at hraw
          obtain ⟨output, _houtput, rfl⟩ := hraw
          simpa [GlobalCausalHashState.setCache] using
            (hretained.recordedState input).cacheQuery_of_none input output
              (by simpa using hcache)
      | fresh =>
          rw [globalCausalAttackerHashQueryFromHigh_run, hplan] at hresult
          exact simulate_eagerTrace_globalCausalHashQuery_merkleRetained_of_cache_none
            table secretKey input (globalCausalRecordedState secretKey input state)
              (hretained.recordedState input) (by simpa using hcache) result
                hresult
      | reveal index =>
          rw [globalCausalAttackerHashQueryFromHigh_run, hplan,
            simulate_eagerTrace_globalCausalRevealHashQueryFromHigh,
            support_pure, Set.mem_singleton_iff] at hresult
          subst result
          simpa [GlobalMerkleKeygenCacheRetained,
            globalFilteredCausalRevealResultState] using
            hretained.cacheQuery_of_none input
              (Rom.hashOutputEquivDigestPair.symm (high index, table index))
                hcache

end XmssSecurity.CappedChain
