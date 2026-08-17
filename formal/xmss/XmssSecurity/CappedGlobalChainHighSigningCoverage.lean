import XmssSecurity.CappedGlobalChainHighRevealCoverage
import XmssSecurity.CappedChain.CausalEagerHighRevealCoverage

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

theorem globalSignatureRevealResult_covered
    (table : GlobalChainValueIndex → Digest)
    (request : SignRequest) (encoding : ChainIndex → Digit)
    (chains : List ChainIndex) (signature : Signature)
    (state : GlobalCausalHashState)
    (covered : Set GlobalChainValueIndex)
    (hcovered : GlobalCausalRevealsCovered covered state)
    (hindices : ∀ chain ∈ chains,
      (chain, request.epoch, encoding chain) ∈ covered) :
    GlobalCausalRevealsCovered covered
        (globalSignatureRevealResult table request encoding chains signature
          state).2 ∧
      GlobalCausalTraceRevealsCovered covered
        (globalSignatureRevealTrace table request encoding chains) := by
  induction chains generalizing signature state with
  | nil =>
      exact ⟨hcovered, by
        simp [globalSignatureRevealTrace,
          GlobalCausalTraceRevealsCovered]⟩
  | cons chain chains ih =>
      let index : GlobalChainValueIndex :=
        (chain, request.epoch, encoding chain)
      have hindex : index ∈ covered := hindices chain (by simp)
      have htailIndices : ∀ candidate ∈ chains,
          (candidate, request.epoch, encoding candidate) ∈ covered := by
        intro candidate hcandidate
        exact hindices candidate (List.mem_cons_of_mem chain hcandidate)
      rw [globalSignatureRevealResult, globalSignatureRevealTrace]
      have htail := ih
        (replaceSignatureChainValue signature chain (table index))
        (state.recordReveal index (table index))
        (hcovered.recordReveal index (table index) hindex) htailIndices
      constructor
      · exact htail.1
      · intro candidate value hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with hhead | htailMem
        · cases hhead
          exact hindex
        · exact htail.2 candidate value htailMem

set_option maxRecDepth 100000 in
theorem simulate_eagerTrace_globalFilteredCausalSigningAttempt_support_covered_of_final
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (covered : Set GlobalChainValueIndex)
    (finalCache : QueryCache HashSpec)
    (result : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hcovered : GlobalCausalRevealsCovered covered state)
    (hcacheLe : result.1.2.cache ≤ finalCache)
    (hdirect : ∀ returnedSignature encoding chain,
      result.1.1 = some returnedSignature →
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash finalCache
          keyView.secretKey.parameter request.epoch
          (request.message, returnedSignature.randomness)) = some encoding →
      (chain, request.epoch, encoding chain) ∈ covered)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalFilteredCausalSigningAttempt keyView request state)).run)) :
    GlobalCausalResultCovered covered result := by
  unfold globalFilteredCausalSigningAttempt at hresult
  rw [simulateQ_bind, WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp,
    mem_support_bind_iff] at hresult
  obtain ⟨randomnessTrace, hrandomnessTrace, hresult⟩ := hresult
  rw [support_map] at hrandomnessTrace
  obtain ⟨randomness, _hrandomness, rfl⟩ := hrandomnessTrace
  simp only [List.nil_append] at hresult
  rw [show (Prod.map id
    (fun trace : RevealProbeOracleSimulation.ActionTrace
      GlobalChainValueIndex => trace)) = id from rfl, id_map] at hresult
  rw [simulateQ_bind, WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp,
    mem_support_bind_iff] at hresult
  obtain ⟨encodedTrace, hencodedTrace, hresult⟩ := hresult
  rw [support_map] at hencodedTrace
  obtain ⟨encoded, hencoded, rfl⟩ := hencodedTrace
  simp only [List.nil_append] at hresult
  cases hdecode : TargetSum.decodeDigest encoded.1 with
  | none =>
      simp only [hdecode, simulateQ_pure, WriterT.run_pure] at hresult
      subst result
      exact ⟨hcovered.setCache encoded.2,
        by simp [GlobalCausalTraceRevealsCovered]⟩
  | some encoding =>
      rw [hdecode, simulateQ_bind, WriterT.run_bind',
        simulate_eagerTrace_revealGlobalSignatureChains] at hresult
      simp only [pure_bind, simulateQ_pure, WriterT.run_pure] at hresult
      subst result
      let initialSignature := Concrete.CacheReplay.signWithEncoding
        keyView.cache keyView.secretKey request.epoch randomness encoding
      let encodedState : GlobalCausalHashState := { state with cache := encoded.2 }
      let returned := globalSignatureRevealResult table request encoding
        allChains initialSignature encodedState
      have hstable : Concrete.CacheView.encodingHash finalCache
          keyView.secretKey.parameter request.epoch
          (request.message, randomness) = encoded.1 := by
        apply encodingHash_eq_of_run_support_of_cache_le
          keyView.secretKey.parameter state.cache encoded.2 finalCache
            request.epoch request.message randomness encoded.1 hencoded
        simpa [Prod.map, returned, encodedState,
          globalSignatureRevealResult_cache]
          using hcacheLe
      have hindices : ∀ chain ∈ allChains,
          (chain, request.epoch, encoding chain) ∈ covered := by
        intro chain _hchain
        apply hdirect returned.1 encoding chain
        · rfl
        · simpa [returned, initialSignature,
            Concrete.CacheReplay.signWithEncoding,
            globalSignatureRevealResult_randomness, hstable] using hdecode
      simpa [GlobalCausalResultCovered, returned, initialSignature,
        encodedState] using
        (globalSignatureRevealResult_covered table request encoding allChains
          initialSignature encodedState covered (hcovered.setCache encoded.2)
            hindices)

set_option maxRecDepth 100000 in
theorem simulate_eagerTrace_globalFilteredCausalSignBoundedAttempts_support_covered_of_final
    (attempts : Nat) (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (covered : Set GlobalChainValueIndex)
    (finalCache : QueryCache HashSpec)
    (result : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hcovered : GlobalCausalRevealsCovered covered state)
    (hcacheLe : result.1.2.cache ≤ finalCache)
    (hdirect : ∀ returnedSignature encoding chain,
      result.1.1 = some returnedSignature →
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash finalCache
          keyView.secretKey.parameter request.epoch
          (request.message, returnedSignature.randomness)) = some encoding →
      (chain, request.epoch, encoding chain) ∈ covered)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalFilteredCausalSignBoundedAttempts attempts keyView request
          state)).run)) :
    GlobalCausalResultCovered covered result := by
  induction attempts generalizing state result with
  | zero =>
      simp only [globalFilteredCausalSignBoundedAttempts, simulateQ_pure,
        WriterT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨hcovered, by simp [GlobalCausalTraceRevealsCovered]⟩
  | succ attempts ih =>
      rw [simulate_eagerTrace_globalFilteredCausalSignBoundedAttempts_succ,
        mem_support_bind_iff] at hresult
      obtain ⟨attemptResult, hattempt, hcontinuation⟩ := hresult
      cases hoption : attemptResult.1.1 with
      | some signature =>
          unfold globalFilteredCausalSignTraceContinuation at hcontinuation
          rw [hoption] at hcontinuation
          simp only [support_pure, Set.mem_singleton_iff] at hcontinuation
          subst result
          exact
            simulate_eagerTrace_globalFilteredCausalSigningAttempt_support_covered_of_final
              table keyView request state covered finalCache attemptResult
                hcovered hcacheLe hdirect hattempt
      | none =>
          unfold globalFilteredCausalSignTraceContinuation at hcontinuation
          rw [hoption, support_map] at hcontinuation
          obtain ⟨rest, hrest, rfl⟩ := hcontinuation
          have hrestCacheLe : rest.1.2.cache ≤ finalCache := hcacheLe
          have hattemptCacheLe : attemptResult.1.2.cache ≤ finalCache :=
            (simulate_eagerTrace_globalFilteredCausalSignBoundedAttempts_stateExtends
              attempts table keyView request attemptResult.1.2 rest hrest).1.trans
                hrestCacheLe
          have hattemptCovered :=
            simulate_eagerTrace_globalFilteredCausalSigningAttempt_support_covered_of_final
              table keyView request state covered finalCache attemptResult
                hcovered hattemptCacheLe (by
                  intro returnedSignature encoding chain hreturned _hdecode
                  rw [hoption] at hreturned
                  contradiction) hattempt
          have hrestCovered := ih attemptResult.1.2 rest hattemptCovered.1
            hrestCacheLe hdirect hrest
          exact ⟨hrestCovered.1,
            hattemptCovered.2.append hrestCovered.2⟩

set_option maxRecDepth 100000 in
theorem simulate_eagerTrace_globalFilteredCausalSigningQuery_support_covered_of_final
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (covered : Set GlobalChainValueIndex)
    (finalCache : QueryCache HashSpec)
    (result : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hcovered : GlobalCausalRevealsCovered covered state)
    (hcacheLe : result.1.2.cache ≤ finalCache)
    (hdirect : ∀ returnedSignature encoding chain,
      result.1.1 = some returnedSignature →
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash finalCache
          keyView.secretKey.parameter request.epoch
          (request.message, returnedSignature.randomness)) = some encoding →
      (chain, request.epoch, encoding chain) ∈ covered)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalFilteredCausalSigningQuery keyView request state)).run)) :
    GlobalCausalResultCovered covered result := by
  exact
    simulate_eagerTrace_globalFilteredCausalSignBoundedAttempts_support_covered_of_final
      signingAttemptLimit table keyView request state covered finalCache result
        hcovered hcacheLe hdirect hresult

theorem globalFilteredCausalAttackerHashPlan_cache_none_of_noncached
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (plan : GlobalFilteredCausalHashPlan)
    (hplan : globalFilteredCausalAttackerHashPlan secretKey input state = plan)
    (hnoncached : ∀ output, plan ≠ .cached output) :
    state.cache input = none := by
  unfold globalFilteredCausalAttackerHashPlan at hplan
  cases hcache : state.cache input with
  | none => rfl
  | some output =>
      simp only [hcache] at hplan
      exact (hnoncached output hplan.symm).elim

theorem simulate_eagerTrace_globalCausalHashQuery_support_cache_le
    (table : GlobalChainValueIndex → Digest) (input : HashInput)
    (state : GlobalCausalHashState)
    (result : (HashOutput × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalHashQuery input).run state)).run)) :
    state.cache ≤ result.1.2.cache := by
  rw [simulate_eagerTrace_globalCausalHashQuery, support_map] at hresult
  obtain ⟨sample, hsample, rfl⟩ := hresult
  have hsample' : sample ∈ support
      ((uniformSampleImpl.withCaching input).run state.cache) := by
    simpa [randomOracle] using hsample
  exact QueryImpl.withCaching_cache_le uniformSampleImpl input state.cache
    sample hsample'

theorem simulate_eagerTrace_globalCausalAttackerHashQueryFromHigh_support_cache_le
    (table high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (result : (HashOutput × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalAttackerHashQueryFromHigh high secretKey input).run
          state)).run)) :
    state.cache ≤ result.1.2.cache := by
  generalize hplan : globalFilteredCausalAttackerHashPlan secretKey input state =
    plan
  cases plan with
  | cached output =>
      rw [globalCausalAttackerHashQueryFromHigh_run, hplan] at hresult
      simp only [simulateQ_pure, WriterT.run_pure', support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      simpa only [globalCausalRecordedState_cache] using
        (le_rfl : state.cache ≤ state.cache)
  | redirect output =>
      rw [globalCausalAttackerHashQueryFromHigh_run, hplan] at hresult
      simp only [simulateQ_pure, WriterT.run_pure', support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      have habsent := globalFilteredCausalAttackerHashPlan_cache_none_of_noncached
        secretKey input state (.redirect output) hplan (by intro; simp)
      simpa [globalFilteredCausalRedirectResultState,
        globalCausalRecordedState_cache] using
          QueryCache.le_cacheQuery state.cache habsent
  | fresh =>
      rw [globalCausalAttackerHashQueryFromHigh_run, hplan] at hresult
      simpa only [globalCausalRecordedState_cache] using
        (simulate_eagerTrace_globalCausalHashQuery_support_cache_le table
          input (globalCausalRecordedState secretKey input state) result hresult)
  | reveal index =>
      rw [globalCausalAttackerHashQueryFromHigh_run, hplan,
        simulate_eagerTrace_globalCausalRevealHashQueryFromHigh] at hresult
      simp only [support_pure, Set.mem_singleton_iff] at hresult
      subst result
      have habsent := globalFilteredCausalAttackerHashPlan_cache_none_of_noncached
        secretKey input state (.reveal index) hplan (by intro; simp)
      simpa [globalFilteredCausalRevealResultState] using
        QueryCache.le_cacheQuery state.cache habsent
  | probeThenFresh index target =>
      rw [simulate_eagerTrace_globalCausalAttackerHashQueryFromHigh_probeThenFresh
        table high secretKey input state index target hplan, support_map]
        at hresult
      obtain ⟨sample, hsample, rfl⟩ := hresult
      have hsample' : sample ∈ support
          ((uniformSampleImpl.withCaching input).run state.cache) := by
        simpa [randomOracle] using hsample
      simpa [globalCausalRecordedState_cache,
        GlobalCausalHashState.setCache] using
          (QueryImpl.withCaching_cache_le uniformSampleImpl input state.cache
            sample hsample')


end XmssSecurity.CappedChain
