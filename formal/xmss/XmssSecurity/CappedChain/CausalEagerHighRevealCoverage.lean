import XmssSecurity.CappedChain.CausalEagerHighVerifierCoverage
import XmssSecurity.CappedChain.CausalRevealCoverage
import XmssSecurity.CausalEagerHighRevealCoverage

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000
set_option linter.constructorNameAsVariable false

theorem filteredCausalUncachedHashPlanAt_reveal_has_predecessor
    (secretKey : SecretKey) (input : HashInput) (state : CausalHashState)
    (probe : Option (ChainValueIndex × Digest)) (index : ChainValueIndex)
    (hplan : filteredCausalUncachedHashPlanAt secretKey input state probe =
      .reveal index) :
    ∃ predecessor value,
      state.revealed predecessor = some value ∧
      predecessor.1 = index.1 ∧ predecessor.2.val + 1 = index.2.val := by
  cases probe with
  | none =>
      unfold filteredCausalUncachedHashPlanAt at hplan
      cases hleaf : state.keygenCache
          (keygenLeafTargetInput secretKey state.keygenCache input) with
      | none =>
          simp only [hleaf] at hplan
          cases hplan
      | some output =>
          simp only [hleaf] at hplan
          cases hplan
  | some probe =>
      rcases probe with ⟨predecessor, target⟩
      unfold filteredCausalUncachedHashPlanAt at hplan
      cases hrevealed : state.revealed predecessor with
      | none =>
          simp only [hrevealed] at hplan
          cases hplan
      | some value =>
          simp only [hrevealed] at hplan
          by_cases htarget : value = target
          · subst target
            rw [if_pos rfl] at hplan
            by_cases hnext : predecessor.2.val + 1 < chainLength
            · rw [dif_pos hnext] at hplan
              have hindex :
                  (predecessor.1,
                    ⟨predecessor.2.val + 1, hnext⟩) = index :=
                FilteredCausalHashPlan.reveal.inj hplan
              subst index
              exact ⟨predecessor, value, hrevealed, rfl, rfl⟩
            · rw [dif_neg hnext] at hplan
              cases hplan
          · rw [if_neg htarget] at hplan
            cases hplan

theorem filteredCausalAttackerHashPlan_reveal_has_predecessor
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (index : ChainValueIndex)
    (hplan : filteredCausalAttackerHashPlan secretKey selected input state =
      .reveal index) :
    ∃ predecessor value,
      state.revealed predecessor = some value ∧
      predecessor.1 = index.1 ∧ predecessor.2.val + 1 = index.2.val := by
  unfold filteredCausalAttackerHashPlan at hplan
  cases hcache : state.cache input with
  | some output =>
      simp only [hcache] at hplan
      cases hplan
  | none =>
      simp only [hcache] at hplan
      unfold filteredCausalUncachedHashPlan at hplan
      exact filteredCausalUncachedHashPlanAt_reveal_has_predecessor
        secretKey input state
          (chainInputProbe? secretKey.parameter selected input) index hplan

theorem filteredCausalAttackerHashPlan_reveal_mem_of_covered
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (index : ChainValueIndex)
    (covered : Set ChainValueIndex)
    (hplan : filteredCausalAttackerHashPlan secretKey selected input state =
      .reveal index)
    (hcovered : CausalRevealsCovered covered state)
    (hforward : ChainValueIndicesForwardClosed covered) :
    index ∈ covered := by
  obtain ⟨predecessor, value, hrevealed, hepoch, hnext⟩ :=
    filteredCausalAttackerHashPlan_reveal_has_predecessor secretKey selected
      input state index hplan
  apply hforward index.1 predecessor.2 index.2
  · rw [← hepoch]
    exact hcovered predecessor value hrevealed
  · change predecessor.2.val ≤ index.2.val
    omega

theorem simulate_eagerTrace_filteredCausalAttackerHashQueryFromHigh_support_revealsCovered
    (table high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (covered : Set ChainValueIndex)
    (hcovered : CausalRevealsCovered covered state)
    (hforward : ChainValueIndicesForwardClosed covered)
    (result : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((filteredCausalAttackerHashQueryFromHigh high secretKey selected input
          ).run state)).run)) :
    CausalResultCovered covered result := by
  have hcovered' : XmssSecurity.CausalRevealsCovered covered state := by
    simpa only [XmssSecurity.CausalRevealsCovered, CausalRevealsCovered]
      using hcovered
  have hforward' : XmssSecurity.ChainValueIndicesForwardClosed covered := by
    simpa only [XmssSecurity.ChainValueIndicesForwardClosed,
      ChainValueIndicesForwardClosed] using hforward
  have hresult' :=
    XmssSecurity.simulate_eagerTrace_filteredCausalAttackerHashQueryFromHigh_support_revealsCovered
      table high secretKey selected input state covered hcovered' hforward'
        result hresult
  simpa only [XmssSecurity.CausalResultCovered,
    XmssSecurity.CausalRevealsCovered,
    XmssSecurity.CausalTraceRevealsCovered, CausalResultCovered,
    CausalRevealsCovered, CausalTraceRevealsCovered] using hresult'

theorem simulate_eagerTrace_filteredProbingAttackerHashQueryAtFromHigh_support_revealsCovered
    (table high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (probe : Option (ChainValueIndex × Digest))
    (covered : Set ChainValueIndex)
    (hcovered : CausalRevealsCovered covered state)
    (hforward : ChainValueIndicesForwardClosed covered)
    (result : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredProbingAttackerHashQueryAtFromHigh high secretKey selected input
          state probe)).run)) :
    CausalResultCovered covered result := by
  cases probe with
  | none =>
      exact
        simulate_eagerTrace_filteredCausalAttackerHashQueryFromHigh_support_revealsCovered
          table high secretKey selected input state covered hcovered hforward
            result hresult
  | some probe =>
      cases hrevealed : state.revealed probe.1 with
      | some value =>
          rw [filteredProbingAttackerHashQueryAtFromHigh, hrevealed] at hresult
          exact
            simulate_eagerTrace_filteredCausalAttackerHashQueryFromHigh_support_revealsCovered
              table high secretKey selected input state covered hcovered hforward
                result hresult
      | none =>
          rw [simulate_eagerTrace_filteredProbingAttackerHashQueryAtFromHigh_hidden_eq_map
            table high secretKey selected input state probe.1 probe.2 hrevealed,
              support_map] at hresult
          obtain ⟨tail, htail, rfl⟩ := hresult
          have htailCovered :=
            simulate_eagerTrace_filteredCausalAttackerHashQueryFromHigh_support_revealsCovered
              table high secretKey selected input state covered hcovered hforward
                tail htail
          constructor
          · exact htailCovered.1
          · intro index value hmem
            simp only [List.mem_cons] at hmem
            rcases hmem with hhead | htailMem
            · cases hhead
            · exact htailCovered.2 index value htailMem

theorem filteredTreeHashProgram_support_revealsCovered
    (table high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (program : FilteredTreeHashProgram)
    (covered : Set ChainValueIndex)
    (hcovered : CausalRevealsCovered covered state)
    (hforward : ChainValueIndicesForwardClosed covered)
    (result : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (program.computation high secretKey selected input state)).run)) :
    CausalResultCovered covered result := by
  cases program with
  | chain probe =>
      apply
        simulate_eagerTrace_filteredProbingAttackerHashQueryAtFromHigh_support_revealsCovered
          table high secretKey selected input state (some probe) covered hcovered
            hforward result
      simpa [FilteredTreeHashProgram.computation,
        filteredTreeChainHashComputation] using hresult
  | currentCached =>
      cases hcache : state.cache input with
      | none =>
          rw [FilteredTreeHashProgram.computation, hcache,
            filteredTreeFreshHashComputation,
            simulate_eagerTrace_causalHashQuery, support_map] at hresult
          obtain ⟨raw, _hraw, rfl⟩ := hresult
          exact ⟨hcovered.setCache raw.2,
            by simp [CausalTraceRevealsCovered]⟩
      | some output =>
          simp only [FilteredTreeHashProgram.computation, hcache,
            filteredTreePureHashComputation, simulateQ_pure, WriterT.run_pure,
            support_pure, Set.mem_singleton_iff] at hresult
          subst result
          exact ⟨hcovered, by simp [CausalTraceRevealsCovered]⟩
  | keygenCached =>
      cases hcache : state.keygenCache input with
      | none =>
          rw [FilteredTreeHashProgram.computation, hcache,
            filteredTreeFreshHashComputation,
            simulate_eagerTrace_causalHashQuery, support_map] at hresult
          obtain ⟨raw, _hraw, rfl⟩ := hresult
          exact ⟨hcovered.setCache raw.2,
            by simp [CausalTraceRevealsCovered]⟩
      | some output =>
          simp only [FilteredTreeHashProgram.computation, hcache,
            filteredTreePureHashComputation, simulateQ_pure, WriterT.run_pure,
            support_pure, Set.mem_singleton_iff] at hresult
          subst result
          exact ⟨hcovered, by simp [CausalTraceRevealsCovered]⟩
  | leafCached =>
      cases hcache : filteredTreeKeygenLeafOutput secretKey input state with
      | none =>
          rw [FilteredTreeHashProgram.computation, hcache,
            filteredTreeFreshHashComputation,
            simulate_eagerTrace_causalHashQuery, support_map] at hresult
          obtain ⟨raw, _hraw, rfl⟩ := hresult
          exact ⟨hcovered.setCache raw.2,
            by simp [CausalTraceRevealsCovered]⟩
      | some output =>
          simp only [FilteredTreeHashProgram.computation, hcache,
            filteredTreePureHashComputation, simulateQ_pure, WriterT.run_pure,
            support_pure, Set.mem_singleton_iff] at hresult
          subst result
          exact ⟨hcovered, by simp [CausalTraceRevealsCovered]⟩
  | fresh =>
      rw [FilteredTreeHashProgram.computation,
        filteredTreeFreshHashComputation,
        simulate_eagerTrace_causalHashQuery, support_map] at hresult
      obtain ⟨raw, _hraw, rfl⟩ := hresult
      exact ⟨hcovered.setCache raw.2,
        by simp [CausalTraceRevealsCovered]⟩
  | leafProbe probe =>
      rw [FilteredTreeHashProgram.computation,
        filteredTreeProbeThenFreshHashComputation,
        filteredTreeFreshHashComputation, simulateQ_bind, WriterT.run_bind',
        simulate_eagerTrace_probeQuery] at hresult
      simp only [map_eq_bind_pure_comp] at hresult
      rw [simulate_eagerTrace_causalHashQuery, map_eq_bind_pure_comp,
        mem_support_bind_iff] at hresult
      obtain ⟨raw, _hraw, hpure⟩ := hresult
      simp only [support_pure, Set.mem_singleton_iff] at _hraw
      subst raw
      rw [mem_support_bind_iff] at hpure
      obtain ⟨middle, hmiddle, hresultEq⟩ := hpure
      simp only [support_pure, Set.mem_singleton_iff,
        Function.comp_apply] at hresultEq
      subst result
      rw [mem_support_bind_iff] at hmiddle
      obtain ⟨hashResult, _hhashResult, hmiddleEq⟩ := hmiddle
      simp only [support_pure, Set.mem_singleton_iff,
        Function.comp_apply] at hmiddleEq
      subst middle
      exact ⟨hcovered.setCache hashResult.2,
        by simp [CausalTraceRevealsCovered]⟩

set_option maxHeartbeats 1000000 in
set_option linter.constructorNameAsVariable false in
theorem filteredTreeHashComputation_support_revealsCovered
    (table high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (covered : Set ChainValueIndex)
    (hcovered : CausalRevealsCovered covered state)
    (hforward : ChainValueIndicesForwardClosed covered)
    (result : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredTreeHashComputationAtFromHigh high secretKey selected input
          state)).run)) :
    CausalResultCovered covered result := by
  generalize hprogram : filteredTreeProbingAttackerHashQueryAtFromHigh high
    secretKey selected input state = program
  unfold filteredTreeHashComputationAtFromHigh at hresult
  rw [hprogram] at hresult
  exact filteredTreeHashProgram_support_revealsCovered table high secretKey
    selected input state program covered hcovered hforward result hresult

theorem encodingHash_eq_of_run_support_of_cache_le
    (parameter : PublicParameter)
    (initialCache resultCache largerCache : QueryCache HashSpec)
    (epoch : Epoch) (message : Message) (randomness : Randomness)
    (digest : Digest)
    (hresult : (digest, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.encodingHash parameter epoch message randomness)).run
          initialCache))
    (hle : resultCache ≤ largerCache) :
    Concrete.CacheView.encodingHash largerCache parameter epoch
      (message, randomness) = digest := by
  have hmapped : (digest, resultCache) ∈ support
      ((fun result : HashOutput × QueryCache HashSpec =>
        (truncateHash result.1, result.2)) <$> (randomOracle
          (Concrete.CacheView.encodingInput parameter epoch
            (message, randomness))).run initialCache) := by
    simpa [Concrete.encodingHash, Concrete.tweakableHash,
      Concrete.oracleHash, Concrete.CacheView.encodingInput,
      map_eq_bind_pure_comp] using hresult
  rw [support_map] at hmapped
  obtain ⟨result, hquery, heq⟩ := hmapped
  have hcached := Concrete.CacheReplay.randomOracle_query_caches
    (Concrete.CacheView.encodingInput parameter epoch (message, randomness))
    initialCache result.1 result.2 hquery
  rw [show result.2 = resultCache from congrArg Prod.snd heq] at hcached
  have hcachedLarger := hle hcached
  rw [Concrete.CacheView.encodingHash,
    Concrete.CacheView.digestAt_eq_of_cache_eq_some hcachedLarger]
  exact congrArg Prod.fst heq

theorem simulate_eagerTrace_filteredCausalSigningAttempt_support_cache_le
    (table : ChainValueIndex → Digest)
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (request : SignRequest) (state : CausalHashState)
    (result : (Option Signature × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredCausalSigningAttempt keyView selected request state)).run)) :
    state.cache ≤ result.1.2.cache := by
  rw [simulate_eagerTrace_filteredCausalSigningAttempt_eq_original] at hresult
  exact
    XmssSecurity.simulate_eagerTrace_filteredCausalSigningQuery_support_cache_le
      table keyView selected request state result hresult

theorem simulate_eagerTrace_filteredCausalSignBoundedAttempts_support_cache_le
    (attempts : Nat) (table : ChainValueIndex → Digest)
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (request : SignRequest) (state : CausalHashState)
    (result : (Option Signature × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredCausalSignBoundedAttempts attempts keyView selected request
          state)).run)) :
    state.cache ≤ result.1.2.cache := by
  induction attempts generalizing state result with
  | zero =>
      simp only [filteredCausalSignBoundedAttempts, simulateQ_pure,
        WriterT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact le_rfl
  | succ attempts ih =>
      rw [simulate_eagerTrace_filteredCausalSignBoundedAttempts_succ,
        mem_support_bind_iff] at hresult
      obtain ⟨attemptResult, hattempt, hcontinuation⟩ := hresult
      have hattemptLe :=
        simulate_eagerTrace_filteredCausalSigningAttempt_support_cache_le table
          keyView selected request state attemptResult hattempt
      cases hoption : attemptResult.1.1 with
      | some signature =>
          unfold filteredCausalSignTraceContinuation at hcontinuation
          rw [hoption] at hcontinuation
          simp only [support_pure, Set.mem_singleton_iff] at hcontinuation
          subst result
          exact hattemptLe
      | none =>
          unfold filteredCausalSignTraceContinuation at hcontinuation
          rw [hoption, support_map] at hcontinuation
          obtain ⟨rest, hrest, rfl⟩ := hcontinuation
          exact le_trans hattemptLe (ih attemptResult.1.2 rest hrest)

theorem simulate_eagerTrace_filteredCausalSigningQuery_support_cache_le
    (table : ChainValueIndex → Digest)
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (request : SignRequest) (state : CausalHashState)
    (result : (Option Signature × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredCausalSigningQuery keyView selected request state)).run)) :
    state.cache ≤ result.1.2.cache := by
  unfold filteredCausalSigningQuery at hresult
  exact
    simulate_eagerTrace_filteredCausalSignBoundedAttempts_support_cache_le
      signingAttemptLimit table keyView selected request state result hresult

set_option maxRecDepth 100000 in
theorem simulate_eagerTrace_filteredCausalSigningAttempt_support_resultCovered_of_final
    (table : ChainValueIndex → Digest)
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (request : SignRequest) (state : CausalHashState)
    (covered : Set ChainValueIndex) (finalCache : QueryCache HashSpec)
    (result : (Option Signature × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hcovered : CausalRevealsCovered covered state)
    (hcacheLe : result.1.2.cache ≤ finalCache)
    (hdirect : ∀ returnedSignature encoding,
      result.1.1 = some returnedSignature →
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash finalCache
          keyView.secretKey.parameter request.epoch
          (request.message, returnedSignature.randomness)) = some encoding →
      (request.epoch, encoding selected) ∈ covered)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredCausalSigningAttempt keyView selected request state)).run)) :
    CausalResultCovered covered result := by
  rw [simulate_eagerTrace_filteredCausalSigningAttempt_eq_original] at hresult
  exact
    XmssSecurity.simulate_eagerTrace_filteredCausalSigningQuery_support_resultCovered_of_final
      table keyView selected request state covered finalCache result hcovered
        hcacheLe hdirect hresult

set_option maxRecDepth 100000 in
theorem simulate_eagerTrace_filteredCausalSignBoundedAttempts_support_resultCovered_of_final
    (attempts : Nat) (table : ChainValueIndex → Digest)
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (request : SignRequest) (state : CausalHashState)
    (covered : Set ChainValueIndex) (finalCache : QueryCache HashSpec)
    (result : (Option Signature × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hcovered : CausalRevealsCovered covered state)
    (hcacheLe : result.1.2.cache ≤ finalCache)
    (hdirect : ∀ returnedSignature encoding,
      result.1.1 = some returnedSignature →
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash finalCache
          keyView.secretKey.parameter request.epoch
          (request.message, returnedSignature.randomness)) = some encoding →
      (request.epoch, encoding selected) ∈ covered)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredCausalSignBoundedAttempts attempts keyView selected request
          state)).run)) :
    CausalResultCovered covered result := by
  induction attempts generalizing state result with
  | zero =>
      simp only [filteredCausalSignBoundedAttempts, simulateQ_pure,
        WriterT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨hcovered, by simp [CausalTraceRevealsCovered]⟩
  | succ attempts ih =>
      rw [simulate_eagerTrace_filteredCausalSignBoundedAttempts_succ,
        mem_support_bind_iff] at hresult
      obtain ⟨attemptResult, hattempt, hcontinuation⟩ := hresult
      cases hoption : attemptResult.1.1 with
      | some signature =>
          unfold filteredCausalSignTraceContinuation at hcontinuation
          rw [hoption] at hcontinuation
          simp only [support_pure, Set.mem_singleton_iff] at hcontinuation
          subst result
          exact
            simulate_eagerTrace_filteredCausalSigningAttempt_support_resultCovered_of_final
              table keyView selected request state covered finalCache
                attemptResult hcovered hcacheLe hdirect hattempt
      | none =>
          unfold filteredCausalSignTraceContinuation at hcontinuation
          rw [hoption, support_map] at hcontinuation
          obtain ⟨rest, hrest, rfl⟩ := hcontinuation
          have hrestCacheLe :=
            simulate_eagerTrace_filteredCausalSignBoundedAttempts_support_cache_le
              attempts table keyView selected request attemptResult.1.2 rest hrest
          have hattemptCacheLe : attemptResult.1.2.cache ≤ finalCache :=
            le_trans hrestCacheLe hcacheLe
          have hattemptCovered :=
            simulate_eagerTrace_filteredCausalSigningAttempt_support_resultCovered_of_final
              table keyView selected request state covered finalCache
                attemptResult hcovered hattemptCacheLe (by
                  intro returnedSignature encoding hreturned _hdecode
                  rw [hoption] at hreturned
                  contradiction) hattempt
          have hrestCovered :=
            ih attemptResult.1.2 rest hattemptCovered.1 hcacheLe hdirect hrest
          exact ⟨hrestCovered.1,
            hattemptCovered.2.append hrestCovered.2⟩

set_option maxRecDepth 100000 in
theorem simulate_eagerTrace_filteredCausalSigningQuery_support_resultCovered_of_final
    (table : ChainValueIndex → Digest)
    (keyView : ProgrammedFixedChainKeygenView) (selected : ChainIndex)
    (request : SignRequest) (state : CausalHashState)
    (covered : Set ChainValueIndex) (finalCache : QueryCache HashSpec)
    (result : (Option Signature × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hcovered : CausalRevealsCovered covered state)
    (hcacheLe : result.1.2.cache ≤ finalCache)
    (hdirect : ∀ returnedSignature encoding,
      result.1.1 = some returnedSignature →
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash finalCache
          keyView.secretKey.parameter request.epoch
          (request.message, returnedSignature.randomness)) = some encoding →
      (request.epoch, encoding selected) ∈ covered)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredCausalSigningQuery keyView selected request state)).run)) :
    CausalResultCovered covered result := by
  unfold filteredCausalSigningQuery at hresult
  exact
    simulate_eagerTrace_filteredCausalSignBoundedAttempts_support_resultCovered_of_final
      signingAttemptLimit table keyView selected request state covered finalCache
        result hcovered hcacheLe hdirect hresult

theorem filteredCausalAttackerHashPlan_cache_none_of_noncached
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (plan : FilteredCausalHashPlan)
    (hplan : filteredCausalAttackerHashPlan secretKey selected input state =
      plan)
    (hnoncached : ∀ output, plan ≠ .cached output) :
    state.cache input = none := by
  unfold filteredCausalAttackerHashPlan at hplan
  cases hcache : state.cache input with
  | none => rfl
  | some output =>
      simp only [hcache] at hplan
      exact (hnoncached output hplan.symm).elim

theorem simulate_eagerTrace_causalHashQuery_support_cache_le
    (table : ChainValueIndex → Digest) (input : HashInput)
    (state : CausalHashState)
    (result : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((causalHashQuery input).run state)).run)) :
    state.cache ≤ result.1.2.cache := by
  rw [simulate_eagerTrace_causalHashQuery, support_map] at hresult
  obtain ⟨sample, hsample, rfl⟩ := hresult
  have hsample' : sample ∈ support
      ((uniformSampleImpl.withCaching input).run state.cache) := by
    simpa [randomOracle] using hsample
  exact QueryImpl.withCaching_cache_le uniformSampleImpl input state.cache
    sample hsample'

theorem simulate_eagerTrace_filteredCausalAttackerHashQueryFromHigh_support_cache_le
    (table high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState)
    (result : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((filteredCausalAttackerHashQueryFromHigh high secretKey selected input
          ).run state)).run)) :
    state.cache ≤ result.1.2.cache := by
  exact
    XmssSecurity.simulate_eagerTrace_filteredCausalAttackerHashQueryFromHigh_support_cache_le
      table high secretKey selected input state result hresult

theorem simulate_eagerTrace_filteredProbingAttackerHashQueryAtFromHigh_support_cache_le
    (table high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (probe : Option (ChainValueIndex × Digest))
    (result : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredProbingAttackerHashQueryAtFromHigh high secretKey selected input
          state probe)).run)) :
    state.cache ≤ result.1.2.cache := by
  cases probe with
  | none =>
      exact
        simulate_eagerTrace_filteredCausalAttackerHashQueryFromHigh_support_cache_le
          table high secretKey selected input state result hresult
  | some probe =>
      cases hrevealed : state.revealed probe.1 with
      | some value =>
          rw [filteredProbingAttackerHashQueryAtFromHigh, hrevealed] at hresult
          exact
            simulate_eagerTrace_filteredCausalAttackerHashQueryFromHigh_support_cache_le
              table high secretKey selected input state result hresult
      | none =>
          rw [simulate_eagerTrace_filteredProbingAttackerHashQueryAtFromHigh_hidden_eq_map
            table high secretKey selected input state probe.1 probe.2 hrevealed,
              support_map] at hresult
          obtain ⟨tail, htail, rfl⟩ := hresult
          exact
            simulate_eagerTrace_filteredCausalAttackerHashQueryFromHigh_support_cache_le
              table high secretKey selected input state tail htail

theorem filteredTreeHashProgram_support_cache_le
    (table high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState) (program : FilteredTreeHashProgram)
    (result : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (program.computation high secretKey selected input state)).run)) :
    state.cache ≤ result.1.2.cache := by
  cases program with
  | chain probe =>
      apply
        simulate_eagerTrace_filteredProbingAttackerHashQueryAtFromHigh_support_cache_le
          table high secretKey selected input state (some probe) result
      simpa [FilteredTreeHashProgram.computation,
        filteredTreeChainHashComputation] using hresult
  | currentCached =>
      cases hcache : state.cache input with
      | none =>
          rw [FilteredTreeHashProgram.computation, hcache] at hresult
          exact simulate_eagerTrace_causalHashQuery_support_cache_le table input
            state result hresult
      | some output =>
          simp only [FilteredTreeHashProgram.computation, hcache,
            filteredTreePureHashComputation, simulateQ_pure, WriterT.run_pure,
            support_pure, Set.mem_singleton_iff] at hresult
          subst result
          exact le_rfl
  | keygenCached =>
      cases hcache : state.keygenCache input with
      | none =>
          rw [FilteredTreeHashProgram.computation, hcache] at hresult
          exact simulate_eagerTrace_causalHashQuery_support_cache_le table input
            state result hresult
      | some output =>
          simp only [FilteredTreeHashProgram.computation, hcache,
            filteredTreePureHashComputation, simulateQ_pure, WriterT.run_pure,
            support_pure, Set.mem_singleton_iff] at hresult
          subst result
          exact le_rfl
  | leafCached =>
      cases hcache : filteredTreeKeygenLeafOutput secretKey input state with
      | none =>
          rw [FilteredTreeHashProgram.computation, hcache] at hresult
          exact simulate_eagerTrace_causalHashQuery_support_cache_le table input
            state result hresult
      | some output =>
          simp only [FilteredTreeHashProgram.computation, hcache,
            filteredTreePureHashComputation, simulateQ_pure, WriterT.run_pure,
            support_pure, Set.mem_singleton_iff] at hresult
          subst result
          exact le_rfl
  | fresh =>
      exact simulate_eagerTrace_causalHashQuery_support_cache_le table input
        state result hresult
  | leafProbe probe =>
      rw [FilteredTreeHashProgram.computation,
        filteredTreeProbeThenFreshHashComputation,
        filteredTreeFreshHashComputation, simulateQ_bind, WriterT.run_bind',
        simulate_eagerTrace_probeQuery] at hresult
      simp only [map_eq_bind_pure_comp] at hresult
      rw [simulate_eagerTrace_causalHashQuery, map_eq_bind_pure_comp,
        mem_support_bind_iff] at hresult
      obtain ⟨raw, _hraw, hpure⟩ := hresult
      rw [mem_support_bind_iff] at hpure
      obtain ⟨middle, hmiddle, hresultEq⟩ := hpure
      simp only [support_pure, Set.mem_singleton_iff,
        Function.comp_apply] at hresultEq
      subst result
      rw [mem_support_bind_iff] at hmiddle
      obtain ⟨hashResult, hhashResult, hmiddleEq⟩ := hmiddle
      simp only [support_pure, Set.mem_singleton_iff,
        Function.comp_apply] at hmiddleEq
      subst middle
      have hhashResult' : hashResult ∈ support
          ((uniformSampleImpl.withCaching input).run state.cache) := by
        simpa [randomOracle] using hhashResult
      exact QueryImpl.withCaching_cache_le uniformSampleImpl input state.cache
        hashResult hhashResult'

set_option maxHeartbeats 1000000 in
set_option linter.constructorNameAsVariable false in
theorem filteredTreeHashComputation_support_cache_le
    (table high : ChainValueIndex → Digest)
    (secretKey : SecretKey) (selected : ChainIndex) (input : HashInput)
    (state : CausalHashState)
    (result : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (filteredTreeHashComputationAtFromHigh high secretKey selected input
          state)).run)) :
    state.cache ≤ result.1.2.cache := by
  generalize hprogram : filteredTreeProbingAttackerHashQueryAtFromHigh high
    secretKey selected input state = program
  unfold filteredTreeHashComputationAtFromHigh at hresult
  rw [hprogram] at hresult
  exact filteredTreeHashProgram_support_cache_le table high secretKey selected
    input state program result hresult

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
theorem filteredHighMappedAdversaryStep_support_cache_le
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState)
    (result : (((OracleWorld + SigningSpec).Range input × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((filteredHighMappedAdversaryImpl keyHigh selected input).run state)
          ).run)) :
    state.cache ≤ result.1.2.cache := by
  rcases input with (n | hashInput) | request
  · change (unifSpec n × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex at result
    change result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((causalUniformImpl n).run state)).run) at hresult
    rw [simulate_eagerTrace_causalUniformImpl, support_map] at hresult
    obtain ⟨output, _houtput, rfl⟩ := hresult
    exact le_rfl
  · change (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex at result
    rw [filteredHighMappedAdversaryImpl_hash_run] at hresult
    generalize hprogram : filteredTreeProbingAttackerHashQueryAtFromHigh
      (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected
        hashInput state = program
    unfold filteredTreeHashComputationAtFromHigh at hresult
    rw [hprogram] at hresult
    exact filteredTreeHashProgram_support_cache_le table
      (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected
        hashInput state program result hresult
  · change (Option Signature × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex at result
    rw [filteredHighMappedAdversaryImpl_signing_run] at hresult
    exact simulate_eagerTrace_filteredCausalSigningQuery_support_cache_le
      table keyHigh.1 selected request state result hresult

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
theorem filteredHighMappedAdversaryStep_support_resultCovered_of_final
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState)
    (covered : Set ChainValueIndex) (finalCache : QueryCache HashSpec)
    (hcovered : CausalRevealsCovered covered state)
    (hforward : ChainValueIndicesForwardClosed covered)
    (result : (((OracleWorld + SigningSpec).Range input × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hcacheLe : result.1.2.cache ≤ finalCache)
    (hdirect : ∀ request signature encoding,
      AttackerAction.sign request (some signature) ∈
        attackerActionFragment input result.1.1 →
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash finalCache
          keyHigh.1.secretKey.parameter request.epoch
          (request.message, signature.randomness)) = some encoding →
      (request.epoch, encoding selected) ∈ covered)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((filteredHighMappedAdversaryImpl keyHigh selected input).run state)
          ).run)) :
    CausalResultCovered covered result := by
  rcases input with (n | hashInput) | request
  · change (unifSpec n × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex at result
    change result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((causalUniformImpl n).run state)).run) at hresult
    rw [simulate_eagerTrace_causalUniformImpl, support_map] at hresult
    obtain ⟨output, _houtput, rfl⟩ := hresult
    exact ⟨hcovered, by simp [CausalTraceRevealsCovered]⟩
  · change (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex at result
    rw [filteredHighMappedAdversaryImpl_hash_run] at hresult
    generalize hprogram : filteredTreeProbingAttackerHashQueryAtFromHigh
      (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected
        hashInput state = program
    unfold filteredTreeHashComputationAtFromHigh at hresult
    rw [hprogram] at hresult
    exact filteredTreeHashProgram_support_revealsCovered table
      (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected
        hashInput state program covered hcovered hforward result hresult
  · change (Option Signature × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex at result
    rw [filteredHighMappedAdversaryImpl_signing_run] at hresult
    apply
      simulate_eagerTrace_filteredCausalSigningQuery_support_resultCovered_of_final
        table keyHigh.1 selected request state covered finalCache result hcovered
          hcacheLe
    · intro returnedSignature encoding hreturned hdecode
      apply hdirect request returnedSignature encoding
      · simpa [attackerActionFragment, hreturned]
      · exact hdecode
    · exact hresult

theorem filteredHighActionTracedStep_support_cache_le
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState)
    (result : ((((OracleWorld + SigningSpec).Range input ×
      AttackerActionTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (((filteredHighActionTracedMappedAdversaryImpl keyHigh selected input
          ).run).run state)).run)) :
    state.cache ≤ result.1.2.cache := by
  rw [simulate_eagerTrace_filteredHighActionTraced_step_eq_map,
    support_map] at hresult
  obtain ⟨mapped, hmapped, rfl⟩ := hresult
  exact filteredHighMappedAdversaryStep_support_cache_le table keyHigh selected
    input state mapped hmapped

set_option maxRecDepth 100000 in
theorem filteredHighActionTracedStep_support_resultCovered_of_final
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex)
    (input : (OracleWorld + SigningSpec).Domain) (state : CausalHashState)
    (covered : Set ChainValueIndex) (finalCache : QueryCache HashSpec)
    (hcovered : CausalRevealsCovered covered state)
    (hforward : ChainValueIndicesForwardClosed covered)
    (result : ((((OracleWorld + SigningSpec).Range input ×
      AttackerActionTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hcacheLe : result.1.2.cache ≤ finalCache)
    (hdirect : ∀ request signature encoding,
      AttackerAction.sign request (some signature) ∈ result.1.1.2 →
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash finalCache
          keyHigh.1.secretKey.parameter request.epoch
          (request.message, signature.randomness)) = some encoding →
      (request.epoch, encoding selected) ∈ covered)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (((filteredHighActionTracedMappedAdversaryImpl keyHigh selected input
          ).run).run state)).run)) :
    CausalResultCovered covered result := by
  rw [simulate_eagerTrace_filteredHighActionTraced_step_eq_map,
    support_map] at hresult
  obtain ⟨mapped, hmapped, rfl⟩ := hresult
  exact filteredHighMappedAdversaryStep_support_resultCovered_of_final table
    keyHigh selected input state covered finalCache hcovered hforward mapped
      hcacheLe hdirect hmapped

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
theorem simulate_filteredHighActionTraced_support_cache_le
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CausalHashState)
    (result : (((α × AttackerActionTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (((simulateQ
          (filteredHighActionTracedMappedAdversaryImpl keyHigh selected)
            computation).run).run state)).run)) :
    state.cache ≤ result.1.2.cache := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, WriterT.run_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact le_rfl
  | query_bind input next ih =>
      simp only [simulateQ_query_bind,
        WriterT.run_bind', StateT.run_bind, simulateQ_bind] at hresult
      rw [mem_support_bind_iff] at hresult
      obtain ⟨head, hhead, htail⟩ := hresult
      rw [support_map] at htail
      obtain ⟨tail, htail, rfl⟩ := htail
      rw [simulateQ_spec_query] at hhead
      rw [simulate_eagerTrace_filteredHighActionTraced_step_eq_map,
        support_map] at hhead
      obtain ⟨rawHead, hrawHead, rfl⟩ := hhead
      rw [StateT.run_map, simulateQ_map, WriterT.run_map',
        support_map] at htail
      obtain ⟨rawTail, hrawTail, rfl⟩ := htail
      simp only [Function.comp_apply, Prod.map, Prod.map_apply, id_eq]
        at hrawTail ⊢
      exact (filteredHighMappedAdversaryStep_support_cache_le table keyHigh
        selected input state rawHead hrawHead).trans
          (ih rawHead.1.1 rawHead.1.2 rawTail hrawTail)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 1000000 in
theorem simulate_filteredHighActionTraced_support_resultCovered_of_final
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CausalHashState)
    (covered : Set ChainValueIndex) (finalCache : QueryCache HashSpec)
    (finalTrace : AttackerActionTrace)
    (hcovered : CausalRevealsCovered covered state)
    (hforward : ChainValueIndicesForwardClosed covered)
    (hdirect : ∀ request signature encoding,
      AttackerAction.sign request (some signature) ∈ finalTrace →
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash finalCache
          keyHigh.1.secretKey.parameter request.epoch
          (request.message, signature.randomness)) = some encoding →
      (request.epoch, encoding selected) ∈ covered)
    (result : (((α × AttackerActionTrace) × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex))
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (((simulateQ
          (filteredHighActionTracedMappedAdversaryImpl keyHigh selected)
            computation).run).run state)).run))
    (hcacheLe : result.1.2.cache ≤ finalCache)
    (htraceLe : ∀ action, action ∈ result.1.1.2 → action ∈ finalTrace) :
    CausalResultCovered covered result := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, WriterT.run_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨hcovered, by simp [CausalTraceRevealsCovered]⟩
  | query_bind input next ih =>
      simp only [simulateQ_query_bind,
        WriterT.run_bind', StateT.run_bind, simulateQ_bind] at hresult
      rw [mem_support_bind_iff] at hresult
      obtain ⟨head, hhead, htail⟩ := hresult
      rw [support_map] at htail
      obtain ⟨tail, htail, rfl⟩ := htail
      rw [simulateQ_spec_query] at hhead
      rw [simulate_eagerTrace_filteredHighActionTraced_step_eq_map,
        support_map] at hhead
      obtain ⟨rawHead, hrawHead, rfl⟩ := hhead
      rw [StateT.run_map, simulateQ_map, WriterT.run_map',
        support_map] at htail
      obtain ⟨rawTail, hrawTail, rfl⟩ := htail
      simp only [Function.comp_apply, Prod.map, Prod.map_apply, id_eq]
        at hrawTail ⊢
      have hheadCacheLe : rawHead.1.2.cache ≤ finalCache := by
        exact (simulate_filteredHighActionTraced_support_cache_le table keyHigh
          selected (next rawHead.1.1) rawHead.1.2 rawTail hrawTail).trans
            hcacheLe
      have hheadTraceLe : ∀ action,
          action ∈ attackerActionFragment input rawHead.1.1 →
            action ∈ finalTrace := by
        intro action haction
        apply htraceLe action
        exact List.mem_append_left rawTail.1.1.2 haction
      have hheadCovered :=
        filteredHighMappedAdversaryStep_support_resultCovered_of_final table
          keyHigh selected input state covered finalCache hcovered hforward
            rawHead hheadCacheLe
            (fun request signature encoding haction hdecode =>
              hdirect request signature encoding
                (hheadTraceLe _ haction) hdecode)
            hrawHead
      have htailTraceLe : ∀ action,
          action ∈ rawTail.1.1.2 → action ∈ finalTrace := by
        intro action haction
        apply htraceLe action
        exact List.mem_append_right
          (attackerActionFragment input rawHead.1.1) haction
      have htailCovered := ih rawHead.1.1 rawHead.1.2
        hheadCovered.1 rawTail hrawTail hcacheLe htailTraceLe
      exact ⟨htailCovered.1,
        hheadCovered.2.append htailCovered.2⟩

set_option maxHeartbeats 1000000 in
theorem filteredHighHashOnlyVerifierStep_support_cache_le
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (input : HashInput) (state : CausalHashState)
    (result : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((filteredHighHashOnlyVerifierImpl keyHigh selected input).run state)
          ).run)) :
    state.cache ≤ result.1.2.cache := by
  rw [filteredHighHashOnlyVerifierImpl_run_eq] at hresult
  generalize hprogram : filteredTreeProbingAttackerHashQueryAtFromHigh
    (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected input
      state = program
  unfold filteredTreeHashComputationAtFromHigh at hresult
  rw [hprogram] at hresult
  exact filteredTreeHashProgram_support_cache_le table
    (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected input
      state program result hresult

set_option maxHeartbeats 1000000 in
theorem filteredHighHashOnlyVerifierStep_support_resultCovered
    (table : ChainValueIndex → Digest)
    (keyHigh : ProgrammedFixedChainKeygenView ×
      (ChainEdgeIndex → Digest))
    (selected : ChainIndex) (input : HashInput) (state : CausalHashState)
    (covered : Set ChainValueIndex)
    (hcovered : CausalRevealsCovered covered state)
    (hforward : ChainValueIndicesForwardClosed covered)
    (result : (HashOutput × CausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace ChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((filteredHighHashOnlyVerifierImpl keyHigh selected input).run state)
          ).run)) :
    CausalResultCovered covered result := by
  rw [filteredHighHashOnlyVerifierImpl_run_eq] at hresult
  generalize hprogram : filteredTreeProbingAttackerHashQueryAtFromHigh
    (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected input
      state = program
  unfold filteredTreeHashComputationAtFromHigh at hresult
  rw [hprogram] at hresult
  exact filteredTreeHashProgram_support_revealsCovered table
    (chainValueHighTableOfEdges keyHigh.2) keyHigh.1.secretKey selected input
      state program covered hcovered hforward result hresult

end XmssSecurity.CappedChain
