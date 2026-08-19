import XmssSecurity.Proof.BoundedSign
import XmssSecurity.Proof.CacheQuerySupport
import XmssSecurity.Proof.ConcreteQueryBound
import XmssSecurity.Proof.SignCacheHitProbability

open OracleComp OracleSpec

namespace XmssSecurity

theorem Concrete.signAttempt_none_attemptedInput_ne_of_later_decode
    (secretKey : SecretKey) (epoch targetEpoch : Epoch)
    (message : Message) (randomness : Randomness) (targetInput : Message × Randomness)
    (initialCache resultCache largerCache : QueryCache HashSpec)
    (hmem : (none, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.signAttempt secretKey epoch message randomness :
          OracleComp HashSpec (Option Signature))).run initialCache))
    (hle : resultCache ≤ largerCache)
    (encoding : Encoding)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash largerCache secretKey.parameter targetEpoch
        targetInput) = some encoding) :
    Concrete.CacheView.encodingInput secretKey.parameter epoch (message, randomness) ≠
      Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput := by
  intro heq
  have heval := Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
    (Concrete.signAttempt secretKey epoch message randomness :
      OracleComp HashSpec (Option Signature)) initialCache resultCache largerCache none hmem hle
  rw [Concrete.CacheReplay.eval_signAttempt] at heval
  have hattemptDecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash largerCache secretKey.parameter epoch
        (message, randomness)) = some encoding := by
    unfold Concrete.CacheView.encodingHash at hdecode ⊢
    rw [heq]
    exact hdecode
  unfold Concrete.CacheReplay.signAttempt at heval
  rw [hattemptDecode] at heval
  cases heval

theorem Concrete.signAttempt_none_preserves_later_valid_encodingInput
    (secretKey : SecretKey) (epoch targetEpoch : Epoch)
    (message : Message) (randomness : Randomness) (targetInput : Message × Randomness)
    (initialCache resultCache largerCache : QueryCache HashSpec)
    (hmem : (none, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.signAttempt secretKey epoch message randomness :
          OracleComp HashSpec (Option Signature))).run initialCache))
    (hle : resultCache ≤ largerCache)
    (encoding : Encoding)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash largerCache secretKey.parameter targetEpoch
        targetInput) = some encoding)
    (hnone : initialCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput) = none) :
    resultCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput) = none := by
  apply Concrete.CacheReplay.cache_none_of_zero_query_bound
    (Concrete.signAttempt secretKey epoch message randomness :
      OracleComp HashSpec (Option Signature))
    (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput)
    initialCache resultCache none
  · exact Concrete.signAttempt_queryBound_zero_at_other_encodingInput secretKey epoch
      targetEpoch message randomness targetInput
        (Concrete.signAttempt_none_attemptedInput_ne_of_later_decode secretKey epoch
          targetEpoch message randomness targetInput initialCache resultCache largerCache hmem
          hle encoding hdecode)
  · exact hnone
  · exact hmem

theorem Concrete.signAttempt_some_preserves_other_encodingInput
    (secretKey : SecretKey) (epoch targetEpoch : Epoch)
    (message : Message) (randomness : Randomness) (targetInput : Message × Randomness)
    (initialCache resultCache : QueryCache HashSpec) (signature : Signature)
    (hmem : (some signature, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.signAttempt secretKey epoch message randomness :
          OracleComp HashSpec (Option Signature))).run initialCache))
    (hne : Concrete.CacheView.encodingInput secretKey.parameter epoch
        (message, signature.randomness) ≠
      Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput)
    (hnone : initialCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput) = none) :
    resultCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput) = none := by
  have hrandomness := Concrete.signAttempt_support_randomness secretKey epoch message
    randomness initialCache resultCache signature hmem
  apply Concrete.CacheReplay.cache_none_of_zero_query_bound
    (Concrete.signAttempt secretKey epoch message randomness :
      OracleComp HashSpec (Option Signature))
    (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput)
    initialCache resultCache (some signature)
  · apply Concrete.signAttempt_queryBound_zero_at_other_encodingInput
    simpa [hrandomness] using hne
  · exact hnone
  · exact hmem

theorem Concrete.signBoundedAttempts_preserves_later_valid_other_encodingInput
    (attempts : Nat) (secretKey : SecretKey) (epoch targetEpoch : Epoch)
    (message : Message) (targetInput : Message × Randomness)
    (initialCache resultCache largerCache : QueryCache HashSpec)
    (result : Option Signature)
    (hmem : (result, resultCache) ∈ support
      ((simulateQ xmssRomImpl
        (Concrete.signBoundedAttempts attempts secretKey epoch message)).run initialCache))
    (hle : resultCache ≤ largerCache)
    (encoding : Encoding)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash largerCache secretKey.parameter targetEpoch
        targetInput) = some encoding)
    (hother : ∀ signature, result = some signature →
      Concrete.CacheView.encodingInput secretKey.parameter epoch
          (message, signature.randomness) ≠
        Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput)
    (hnone : initialCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput) = none) :
    resultCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput) = none := by
  induction attempts generalizing initialCache resultCache result with
  | zero =>
      simp only [Concrete.signBoundedAttempts, simulateQ_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨_, hcache⟩ := hmem
      subst resultCache
      exact hnone
  | succ attempts ih =>
      rw [Concrete.signBoundedAttempts] at hmem
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨randomness, randomnessCache⟩, hrandomness, hrest⟩ := hmem
      have hrandomnessCache : randomnessCache = initialCache :=
        xmssRom_lift_probComp_cache_eq Concrete.signingRandomness initialCache
          (randomness, randomnessCache) hrandomness
      subst randomnessCache
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
      obtain ⟨⟨attemptResult, attemptCache⟩, hattempt, hcontinue⟩ := hrest
      have hroute :
          simulateQ xmssRomImpl
              (liftM (Concrete.signAttempt secretKey epoch message randomness :
                OracleComp HashSpec (Option Signature))) =
            simulateQ randomOracle
              (Concrete.signAttempt secretKey epoch message randomness :
                OracleComp HashSpec (Option Signature)) := by
        change simulateQ (unifFwdImpl HashSpec + randomOracle)
            (liftM (Concrete.signAttempt secretKey epoch message randomness :
              OracleComp HashSpec (Option Signature))) = _
        exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
          (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
          (Concrete.signAttempt secretKey epoch message randomness :
            OracleComp HashSpec (Option Signature))
      rw [hroute] at hattempt
      cases attemptResult with
      | none =>
          have hattemptLeResult : attemptCache ≤ resultCache :=
            xmssRom_cache_le
              (Concrete.signBoundedAttempts attempts secretKey epoch message)
              attemptCache (result, resultCache) hcontinue
          have hattemptNone :=
            Concrete.signAttempt_none_preserves_later_valid_encodingInput secretKey epoch
              targetEpoch message randomness targetInput initialCache attemptCache largerCache
              hattempt (hattemptLeResult.trans hle) encoding hdecode hnone
          exact ih attemptCache resultCache result hcontinue hle hother hattemptNone
      | some signature =>
          simp only [simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq] at hcontinue
          obtain ⟨hresult, hcache⟩ := hcontinue
          have hsignature : result = some signature := hresult
          subst resultCache
          exact Concrete.signAttempt_some_preserves_other_encodingInput secretKey epoch
            targetEpoch message randomness targetInput initialCache attemptCache signature
            hattempt (hother signature hsignature) hnone

theorem Concrete.cappedSign_preserves_later_valid_other_encodingInput
    (publicKey : PublicKey) (secretKey : SecretKey) (epoch targetEpoch : Epoch)
    (message : Message) (targetInput : Message × Randomness)
    (initialCache resultCache largerCache : QueryCache HashSpec)
    (result : Option Signature)
    (hmem : (result, resultCache) ∈ support
      ((simulateQ xmssRomImpl
        (Concrete.cappedSign publicKey secretKey epoch message)).run initialCache))
    (hle : resultCache ≤ largerCache)
    (encoding : Encoding)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash largerCache secretKey.parameter targetEpoch
        targetInput) = some encoding)
    (hother : ∀ signature, result = some signature →
      Concrete.CacheView.encodingInput secretKey.parameter epoch
          (message, signature.randomness) ≠
        Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput)
    (hnone : initialCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput) = none) :
    resultCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput) = none := by
  rw [Concrete.cappedSign_eq] at hmem
  exact Concrete.signBoundedAttempts_preserves_later_valid_other_encodingInput
    signingAttemptLimit secretKey epoch targetEpoch message targetInput initialCache resultCache
    largerCache result hmem hle encoding hdecode hother hnone

theorem Concrete.signBoundedAttempts_preserves_other_epoch_encodingInput
    (attempts : Nat) (secretKey : SecretKey) (epoch targetEpoch : Epoch)
    (message : Message) (targetInput : Message × Randomness)
    (initialCache finalCache : QueryCache HashSpec) (result : Option Signature)
    (hmem : (result, finalCache) ∈ support
      ((simulateQ xmssRomImpl
        (Concrete.signBoundedAttempts attempts secretKey epoch message)).run initialCache))
    (hne : epoch ≠ targetEpoch)
    (hnone : initialCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput) = none) :
    finalCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput) = none := by
  induction attempts generalizing initialCache finalCache result with
  | zero =>
      simp only [Concrete.signBoundedAttempts, simulateQ_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨_, hcache⟩ := hmem
      subst finalCache
      exact hnone
  | succ attempts ih =>
      rw [Concrete.signBoundedAttempts] at hmem
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨randomness, randomnessCache⟩, hrandomness, hrest⟩ := hmem
      have hrandomnessCache : randomnessCache = initialCache :=
        xmssRom_lift_probComp_cache_eq Concrete.signingRandomness initialCache
          (randomness, randomnessCache) hrandomness
      subst randomnessCache
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
      obtain ⟨⟨attemptResult, attemptCache⟩, hattempt, hcontinue⟩ := hrest
      have hroute :
          simulateQ xmssRomImpl
              (liftM (Concrete.signAttempt secretKey epoch message randomness :
                OracleComp HashSpec (Option Signature))) =
            simulateQ randomOracle
              (Concrete.signAttempt secretKey epoch message randomness :
                OracleComp HashSpec (Option Signature)) := by
        change simulateQ (unifFwdImpl HashSpec + randomOracle)
            (liftM (Concrete.signAttempt secretKey epoch message randomness :
              OracleComp HashSpec (Option Signature))) = _
        exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
          (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
          (Concrete.signAttempt secretKey epoch message randomness :
            OracleComp HashSpec (Option Signature))
      rw [hroute] at hattempt
      have hattemptNone : attemptCache
          (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput) =
            none := by
        apply Concrete.CacheReplay.cache_none_of_zero_query_bound
          (Concrete.signAttempt secretKey epoch message randomness :
            OracleComp HashSpec (Option Signature))
          (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput)
          initialCache attemptCache attemptResult
        · apply Concrete.signAttempt_queryBound_zero_at_other_encodingInput
          intro heq
          exact hne (Concrete.CacheView.epoch_eq_of_encodingInput_eq
            secretKey.parameter heq)
        · exact hnone
        · exact hattempt
      cases attemptResult with
      | none => exact ih attemptCache finalCache result hcontinue hattemptNone
      | some signature =>
          simp only [simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq] at hcontinue
          obtain ⟨_, hcache⟩ := hcontinue
          subst finalCache
          exact hattemptNone

theorem Concrete.cappedSign_preserves_other_epoch_encodingInput
    (publicKey : PublicKey) (secretKey : SecretKey) (epoch targetEpoch : Epoch)
    (message : Message) (targetInput : Message × Randomness)
    (initialCache finalCache : QueryCache HashSpec) (result : Option Signature)
    (hmem : (result, finalCache) ∈ support
      ((simulateQ xmssRomImpl
        (Concrete.cappedSign publicKey secretKey epoch message)).run initialCache))
    (hne : epoch ≠ targetEpoch)
    (hnone : initialCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput) = none) :
    finalCache
      (Concrete.CacheView.encodingInput secretKey.parameter targetEpoch targetInput) = none := by
  rw [Concrete.cappedSign_eq] at hmem
  exact Concrete.signBoundedAttempts_preserves_other_epoch_encodingInput
    signingAttemptLimit secretKey epoch targetEpoch message targetInput initialCache finalCache
    result hmem hne hnone

end XmssSecurity
