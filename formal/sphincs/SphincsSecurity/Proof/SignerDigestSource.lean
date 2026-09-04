import SphincsSecurity.Proof.NoMessage
import SphincsSecurity.Proof.SignSupport

/-!
# Message inputs inserted by a signer

The signer's only message-domain hash calls are the attempts in its digest loop. Once one attempt is
admissible the rest of signing avoids that domain entirely.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

@[simp] theorem queriedInputs_signAttempt (f : QueryImpl HashSpec Id)
    (secretKey : SecretKey) (message : Message) (randomness : Randomness) :
    queriedInputs f (signAttempt secretKey message randomness) =
      [tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root message randomness)] := by
  rw [signAttempt, queriedInputs_bind]
  change queriedInputs f
      (liftM (HashSpec.query (tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root message randomness))) >>=
          fun answer => pure (truncateMessageDigest answer)) ++ _ = _
  rw [queriedInputs_query_bind, queriedInputs_pure]
  split <;> simp

theorem signAttempt_cache_other_none (secretKey : SecretKey) (message : Message)
    (randomness : Randomness) (beforeCache afterCache : QueryCache HashSpec)
    (attempt : Option (Index × (DigestTree → FtsLeaf)))
    (hmem : (attempt, afterCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (signAttempt secretKey message randomness)).run beforeCache))
    (target : HashInput) (hbefore : beforeCache target = none)
    (hne : target ≠ tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message randomness)) :
    afterCache target = none := by
  obtain ⟨f, hf⟩ := QueryCache.exists_agreesWithFn (spec := HashSpec) afterCache
  apply cache_eq_none_of_not_mem_queriedInputs
    (signAttempt secretKey message randomness) beforeCache attempt afterCache hmem f hf target hbefore
  simp [hne]

theorem signAfterDigest_cache_message_none (secretKey : SecretKey)
    (randomness : Randomness) (index : Index)
    (leaves : DigestTree → FtsLeaf) (beforeCache afterCache : QueryCache HashSpec)
    (result : Option Signature)
    (hmem : (result, afterCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (signAfterDigest secretKey randomness index leaves)).run beforeCache))
    (payload : HashInput) (hbefore : beforeCache
      (tweakableHashInput secretKey.parameter .message payload) = none) :
    afterCache (tweakableHashInput secretKey.parameter .message payload) = none := by
  obtain ⟨answerFn, hagree⟩ := QueryCache.exists_agreesWithFn (spec := HashSpec) afterCache
  apply cache_eq_none_of_not_mem_queriedInputs
    (signAfterDigest secretKey randomness index leaves) beforeCache result afterCache
      hmem answerFn hagree _ hbefore
  exact avoidsMessage_signAfterDigest answerFn secretKey randomness index leaves payload

theorem signDigestLoop_message_source (attempts : Nat) (secretKey : SecretKey)
    (message : Message) (beforeCache afterCache : QueryCache HashSpec)
    (result : Option (Randomness × Index × (DigestTree → FtsLeaf)))
    (hmem : (result, afterCache) ∈ support
      ((simulateQ romImpl (signDigestLoop attempts secretKey message)).run beforeCache))
    (targetPayload : HashInput)
    (hbefore : beforeCache
      (tweakableHashInput secretKey.parameter .message targetPayload) = none)
    (hafter : afterCache
      (tweakableHashInput secretKey.parameter .message targetPayload) ≠ none) :
    ∃ (attemptIndex : Nat) (randomness : Randomness),
      attemptIndex < attempts
        ∧ randomness ∈ support sampleRandomness
        ∧ targetPayload = messageDigestPayload secretKey.root message randomness := by
  induction attempts generalizing beforeCache afterCache result with
  | zero =>
      simp only [signDigestLoop, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      exact (hafter hbefore).elim
  | succ attempts ih =>
      rw [signDigestLoop, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨randomness, sampleCache⟩, hsample, hrest⟩ := hmem
      have hsampleRun : (randomness, sampleCache) ∈ support
          ((simulateQ (unifFwdImpl HashSpec) sampleRandomness).run beforeCache) := by
        simpa only [romImpl, QueryImpl.simulateQ_add_liftM_left] using hsample
      rw [unifFwdImpl.simulateQ_run, support_map] at hsampleRun
      obtain ⟨sampledRandomness, hrandomness, heq⟩ := hsampleRun
      obtain ⟨rfl, rfl⟩ := heq
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
      obtain ⟨⟨attempt, attemptCache⟩, hattempt, hfinish⟩ := hrest
      have hattempt' : (attempt, attemptCache) ∈ support
          ((simulateQ (randomOracle : QueryImpl HashSpec _)
            (signAttempt secretKey message randomness)).run beforeCache) := by
        simpa only [simulateQ_romImpl_liftM] using hattempt
      by_cases heqInput : targetPayload =
          messageDigestPayload secretKey.root message randomness
      · exact ⟨0, randomness, by omega, hrandomness, heqInput⟩
      have hattemptNone : attemptCache
          (tweakableHashInput secretKey.parameter .message targetPayload) = none := by
        apply signAttempt_cache_other_none secretKey message randomness beforeCache attemptCache
          attempt hattempt' _ hbefore
        intro hinput
        have hpayload := (tweakableHashInput_injective secretKey.parameter (by trivial)
          (by trivial) hinput).2
        exact heqInput hpayload
      cases attempt with
      | none =>
          obtain ⟨attemptIndex, sourceRandomness, hindex, hsampled, hpayload⟩ :=
            ih attemptCache afterCache result hfinish hattemptNone hafter
          exact ⟨attemptIndex + 1, sourceRandomness, by omega, hsampled, hpayload⟩
      | some selected =>
          simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hfinish
          obtain ⟨rfl, rfl⟩ := hfinish
          exact (hafter hattemptNone).elim

theorem sign_message_source (secretKey : SecretKey) (message : Message)
    (beforeCache afterCache : QueryCache HashSpec) (result : Option Signature)
    (hmem : (result, afterCache) ∈ support
      ((simulateQ romImpl (sign secretKey message)).run beforeCache))
    (targetPayload : HashInput)
    (hbefore : beforeCache
      (tweakableHashInput secretKey.parameter .message targetPayload) = none)
    (hafter : afterCache
      (tweakableHashInput secretKey.parameter .message targetPayload) ≠ none) :
    ∃ (attemptIndex : Nat) (randomness : Randomness),
      attemptIndex < digestAttemptLimit
        ∧ randomness ∈ support sampleRandomness
        ∧ targetPayload = messageDigestPayload secretKey.root message randomness := by
  rw [sign_eq_digestLoop_afterDigest, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at hmem
  obtain ⟨⟨loopResult, loopCache⟩, hloop, hrest⟩ := hmem
  by_cases hloopHit : loopCache
      (tweakableHashInput secretKey.parameter .message targetPayload) ≠ none
  · exact signDigestLoop_message_source digestAttemptLimit secretKey message
      beforeCache loopCache loopResult hloop targetPayload hbefore hloopHit
  have hloopNone : loopCache
      (tweakableHashInput secretKey.parameter .message targetPayload) = none :=
    not_ne_iff.mp hloopHit
  cases loopResult with
  | none =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hrest
      obtain ⟨rfl, rfl⟩ := hrest
      exact (hafter hloopNone).elim
  | some data =>
      rcases data with ⟨randomness, index, leaves⟩
      have hrest' : (result, afterCache) ∈ support
          ((simulateQ (randomOracle : QueryImpl HashSpec _)
            (signAfterDigest secretKey randomness index leaves)).run loopCache) := by
        simpa only [simulateQ_romImpl_liftM] using hrest
      have hnone := signAfterDigest_cache_message_none secretKey randomness index leaves
        loopCache afterCache result hrest' targetPayload hloopNone
      exact (hafter hnone).elim

end SphincsSecurity.Concrete
