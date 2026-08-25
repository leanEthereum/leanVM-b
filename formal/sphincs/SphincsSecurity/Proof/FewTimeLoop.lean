import SphincsSecurity.Proof.FewTimeUniform
import SphincsSecurity.Proof.MessagePrehit
import SphincsSecurity.Proof.SignerDigestSource

/-!
# Fresh successful digest attempts

An inadmissible answer already cached at a message-digest input remains there throughout the retry
loop and prevents that randomizer from being selected. Consequently, if the randomizer eventually
selected by the loop was absent from the initial cache, its successful attempt queried a fresh
input.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

set_option maxRecDepth 100000

def RejectedRandomness (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (message : Message) (randomness : Randomness) : Prop :=
  ∃ output,
    cache (tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message randomness)) = some output
      ∧ signAttemptResultOfOutput output = none

theorem signAttempt_result_of_cached (secretKey : SecretKey) (message : Message)
    (randomness : Randomness) (beforeCache afterCache : QueryCache HashSpec)
    (attempt : Option (Index × (DigestTree → FtsLeaf))) (output : HashOutput)
    (hcached : afterCache (tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message randomness)) = some output)
    (hmem : (attempt, afterCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec
        (StateT (QueryCache HashSpec) ProbComp))
        (signAttempt secretKey message randomness)).run beforeCache)) :
    attempt = signAttemptResultOfOutput output := by
  obtain ⟨_, f, hf, heval⟩ := exists_answerFn_agrees_final_of_mem_support
    (signAttempt secretKey message randomness) beforeCache attempt afterCache hmem
  have hfinput : f (tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message randomness)) = output :=
    hf hcached
  simp only [signAttempt, messageDigest, oracleHash, evalWithAnswerFn_bind,
    evalWithAnswerFn_query, hfinput] at heval
  simp only [signAttemptResultOfOutput]
  by_cases hadmissible : Admissible (truncateMessageDigest output)
  · simpa only [if_pos hadmissible, evalWithAnswerFn_pure] using heval.symm
  · simpa only [if_neg hadmissible, evalWithAnswerFn_pure] using heval.symm

theorem RejectedRandomness.mono {cache later : QueryCache HashSpec}
    {secretKey : SecretKey} {message : Message} {randomness : Randomness}
    (hrejected : RejectedRandomness cache secretKey message randomness)
    (hle : cache ≤ later) : RejectedRandomness later secretKey message randomness := by
  obtain ⟨output, hcached, hresult⟩ := hrejected
  exact ⟨output, hle hcached, hresult⟩

set_option linter.constructorNameAsVariable false in
theorem signDigestLoop_ne_selected_of_rejected
    (attempts : Nat) (secretKey : SecretKey) (message : Message)
    (beforeCache afterCache : QueryCache HashSpec)
    (rejected : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (hrejected : RejectedRandomness beforeCache secretKey message rejected)
    (hmem : (some (rejected, index, leaves), afterCache) ∈ support
      ((simulateQ romImpl
        (signDigestLoop attempts secretKey message)).run beforeCache)) : False := by
  induction attempts generalizing beforeCache afterCache with
  | zero =>
      simp [signDigestLoop] at hmem
  | succ attempts ih =>
      rw [signDigestLoop_run_succ_eq, mem_support_bind_iff] at hmem
      obtain ⟨sampledRandomness, _hsampled, hrest⟩ := hmem
      rw [mem_support_bind_iff] at hrest
      obtain ⟨⟨attempt, attemptCache⟩, hattempt, hfinish⟩ := hrest
      have hle : beforeCache ≤ attemptCache :=
        simulateQ_romImpl_cache_le
          (liftM (signAttempt secretKey message sampledRandomness :
            OracleComp HashSpec (Option (Index × (DigestTree → FtsLeaf)))) :
              OracleComp OracleWorld (Option (Index × (DigestTree → FtsLeaf))))
          beforeCache (attempt, attemptCache) (by
            simpa only [simulateQ_romImpl_liftM] using hattempt)
      cases hresult : attempt with
      | none =>
          apply ih attemptCache afterCache
            (hrejected.mono hle)
          simpa [signDigestLoopContinuation, hresult] using hfinish
      | some selected =>
          rcases selected with ⟨selectedIndex, selectedLeaves⟩
          have hfinish' :
              (some (rejected, index, leaves), afterCache) =
                (some (sampledRandomness, selectedIndex, selectedLeaves), attemptCache) := by
            simpa [signDigestLoopContinuation, hresult] using hfinish
          have hrandomness : sampledRandomness = rejected := by
            have hoption := congrArg Prod.fst hfinish'
            have hselected := Option.some.inj hoption
            exact (congrArg Prod.fst hselected).symm
          obtain ⟨output, hcached, hnone⟩ := hrejected
          have hcached' : beforeCache
              (tweakableHashInput secretKey.parameter .message
                (messageDigestPayload secretKey.root message sampledRandomness)) = some output := by
            rw [hrandomness]
            exact hcached
          have hattempt' : (attempt, attemptCache) ∈ support
              ((simulateQ (randomOracle : QueryImpl HashSpec
                  (StateT (QueryCache HashSpec) ProbComp))
                (signAttempt secretKey message sampledRandomness)).run beforeCache) := by
            simpa only [simulateQ_romImpl_liftM] using hattempt
          have hattemptResult := signAttempt_result_of_cached secretKey message sampledRandomness
            beforeCache attemptCache attempt output (hle hcached') hattempt'
          have : attempt = none := hattemptResult.trans hnone
          simp [hresult] at this

set_option linter.constructorNameAsVariable false in
theorem failed_signAttempt_preserves_selected_miss
    (attempts : Nat) (secretKey : SecretKey) (message : Message)
    (sampled selected : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (beforeCache attemptCache afterCache : QueryCache HashSpec)
    (hbefore : beforeCache (tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message selected)) = none)
    (hattempt : (none, attemptCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec
        (StateT (QueryCache HashSpec) ProbComp))
        (signAttempt secretKey message sampled)).run beforeCache))
    (hfuture : (some (selected, index, leaves), afterCache) ∈ support
      ((simulateQ romImpl
        (signDigestLoop attempts secretKey message)).run attemptCache)) :
    attemptCache (tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message selected)) = none := by
  let selectedInput := tweakableHashInput secretKey.parameter .message
    (messageDigestPayload secretKey.root message selected)
  let sampledInput := tweakableHashInput secretKey.parameter .message
    (messageDigestPayload secretKey.root message sampled)
  by_cases hsame : selectedInput = sampledInput
  · have hrandomness : sampled = selected := by
      have hpayload := (tweakableHashInput_injective secretKey.parameter (by trivial)
        (by trivial) hsame.symm).2
      exact (messageDigestPayload_injective secretKey.root hpayload).2
    by_cases hmiss : attemptCache selectedInput = none
    · exact hmiss
    obtain ⟨output, hcached⟩ := Option.ne_none_iff_exists'.mp hmiss
    exfalso
    apply signDigestLoop_ne_selected_of_rejected attempts secretKey message
      attemptCache afterCache selected index leaves
    · refine ⟨output, hcached, ?_⟩
      have hcachedSampled : attemptCache
          (tweakableHashInput secretKey.parameter .message
            (messageDigestPayload secretKey.root message sampled)) = some output := by
        rw [hrandomness]
        exact hcached
      have hresult := signAttempt_result_of_cached secretKey message sampled
        beforeCache attemptCache none output hcachedSampled hattempt
      simpa using hresult.symm
    · exact hfuture
  · apply signAttempt_cache_other_none secretKey message sampled beforeCache attemptCache
      none hattempt selectedInput hbefore
    change selectedInput ≠ sampledInput
    exact hsame

set_option linter.constructorNameAsVariable false in
theorem fresh_signAttempt_support_source
    (secretKey : SecretKey) (message : Message) (randomness : Randomness)
    (index : Index) (leaves : DigestTree → FtsLeaf)
    (beforeCache afterCache : QueryCache HashSpec)
    (hbefore : beforeCache (tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message randomness)) = none)
    (hmem : (some (index, leaves), afterCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec
        (StateT (QueryCache HashSpec) ProbComp))
        (signAttempt secretKey message randomness)).run beforeCache)) :
    ∃ output, signAttemptResultOfOutput output = some (index, leaves)
      ∧ afterCache = beforeCache.cacheQuery
          (tweakableHashInput secretKey.parameter .message
            (messageDigestPayload secretKey.root message randomness)) output := by
  let input := tweakableHashInput secretKey.parameter .message
    (messageDigestPayload secretKey.root message randomness)
  have hquery :
      simulateQ (randomOracle : QueryImpl HashSpec
          (StateT (QueryCache HashSpec) ProbComp))
          (oracleHash input : OracleComp HashSpec HashOutput) =
        randomOracle input := by
    change simulateQ (randomOracle : QueryImpl HashSpec
      (StateT (QueryCache HashSpec) ProbComp)) (liftM (HashSpec.query input)) = _
    exact simulateQ_spec_query (impl := (randomOracle : QueryImpl HashSpec
      (StateT (QueryCache HashSpec) ProbComp))) input
  rw [signAttempt, simulateQ_bind, StateT.run_bind, messageDigest,
    simulateQ_bind, StateT.run_bind, hquery] at hmem
  simp only [simulateQ_pure, StateT.run_pure, bind_assoc, pure_bind] at hmem
  rw [mem_support_bind_iff] at hmem
  let hmem' := hmem
  obtain ⟨⟨output, queryCache⟩, hquery, hresult⟩ := hmem'
  rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ (by simpa [input] using hbefore),
    support_map] at hquery
  obtain ⟨sampledOutput, _hsampled, heq⟩ := hquery
  obtain ⟨rfl, rfl⟩ := heq
  by_cases hadmissible : Admissible (truncateMessageDigest output)
  · simp only [if_pos hadmissible, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hresult
    refine ⟨output, ?_, ?_⟩
    · simp only [signAttemptResultOfOutput, if_pos hadmissible]
      exact congrArg some (Prod.ext hresult.1.1.symm hresult.1.2.symm)
    · simpa [input] using hresult.2
  · simp only [if_neg hadmissible, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at hresult

set_option linter.constructorNameAsVariable false in
theorem signDigestLoop_fresh_selected_attempt
    (attempts : Nat) (secretKey : SecretKey) (message : Message)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (initialCache finalCache : QueryCache HashSpec)
    (hinitial : initialCache (tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message randomness)) = none)
    (hmem : (some (randomness, index, leaves), finalCache) ∈ support
      ((simulateQ romImpl
        (signDigestLoop attempts secretKey message)).run initialCache)) :
    ∃ attemptIndex < attempts, ∃ (attemptCache : QueryCache HashSpec) (output : HashOutput),
      attemptCache (tweakableHashInput secretKey.parameter .message
          (messageDigestPayload secretKey.root message randomness)) = none
        ∧ signAttemptResultOfOutput output = some (index, leaves)
        ∧ finalCache = attemptCache.cacheQuery
          (tweakableHashInput secretKey.parameter .message
            (messageDigestPayload secretKey.root message randomness)) output := by
  induction attempts generalizing initialCache finalCache with
  | zero =>
      simp [signDigestLoop] at hmem
  | succ attempts ih =>
      rw [signDigestLoop_run_succ_eq, mem_support_bind_iff] at hmem
      obtain ⟨sampledRandomness, _hsampled, hrest⟩ := hmem
      rw [mem_support_bind_iff] at hrest
      obtain ⟨⟨attempt, attemptCache⟩, hattempt, hfinish⟩ := hrest
      cases hresult : attempt with
      | none =>
          have hfuture : (some (randomness, index, leaves), finalCache) ∈ support
              ((simulateQ romImpl
                (signDigestLoop attempts secretKey message)).run attemptCache) := by
            simpa [signDigestLoopContinuation, hresult] using hfinish
          have hmiss := failed_signAttempt_preserves_selected_miss attempts secretKey message
            sampledRandomness randomness index leaves initialCache attemptCache finalCache
            hinitial (by simpa only [hresult] using hattempt) hfuture
          obtain ⟨attemptIndex, hattemptIndex, sourceCache, output, hsource⟩ :=
            ih attemptCache finalCache hmiss hfuture
          exact ⟨attemptIndex + 1, by omega, sourceCache, output, hsource⟩
      | some selected =>
          rcases selected with ⟨selectedIndex, selectedLeaves⟩
          have hfinish' :
              (some (randomness, index, leaves), finalCache) =
                (some (sampledRandomness, selectedIndex, selectedLeaves), attemptCache) := by
            simpa [signDigestLoopContinuation, hresult] using hfinish
          have htuple := Option.some.inj (congrArg Prod.fst hfinish')
          have hrandomness : sampledRandomness = randomness :=
            (congrArg Prod.fst htuple).symm
          have hselected : (selectedIndex, selectedLeaves) = (index, leaves) :=
            (congrArg Prod.snd htuple).symm
          have hcache : attemptCache = finalCache :=
            (congrArg Prod.snd hfinish').symm
          have hinitial' : initialCache
              (tweakableHashInput secretKey.parameter .message
                (messageDigestPayload secretKey.root message sampledRandomness)) = none := by
            rw [hrandomness]
            exact hinitial
          obtain ⟨output, hattemptResult, hattemptCache⟩ :=
            fresh_signAttempt_support_source secretKey message sampledRandomness
              selectedIndex selectedLeaves initialCache attemptCache hinitial'
              (by simpa only [hresult] using hattempt)
          refine ⟨0, by omega, initialCache, output, hinitial, ?_, ?_⟩
          · rw [← hselected]
            exact hattemptResult
          · rw [← hcache, ← hrandomness]
            exact hattemptCache

end SphincsSecurity.Concrete
