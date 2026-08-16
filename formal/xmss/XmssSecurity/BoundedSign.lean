import XmssSecurity.CacheReplay
import XmssSecurity.ConcreteCorrectness
import XmssSecurity.Execution

open OracleComp OracleSpec

namespace XmssSecurity

theorem Concrete.signBoundedAttempts_success_origin
    (attempts : Nat) (secretKey : SecretKey) (epoch : Epoch) (message : Message)
    (initialCache finalCache : QueryCache HashSpec) (signature : Signature)
    (hmem : (some signature, finalCache) ∈ support
      ((simulateQ xmssRomImpl
        (Concrete.signBoundedAttempts attempts secretKey epoch message)).run initialCache)) :
    ∃ randomness attemptCache resultCache,
      (some signature, resultCache) ∈ support
        ((simulateQ randomOracle
          (Concrete.signAttempt secretKey epoch message randomness :
            OracleComp HashSpec (Option Signature))).run attemptCache) ∧
      resultCache ≤ finalCache := by
  induction attempts generalizing initialCache finalCache signature with
  | zero =>
      simp [Concrete.signBoundedAttempts] at hmem
  | succ attempts ih =>
      rw [Concrete.signBoundedAttempts] at hmem
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨randomness, randomnessCache⟩, hrandomness, hrest⟩ := hmem
      have hrandomnessCache : randomnessCache = initialCache :=
        xmssRom_lift_probComp_cache_eq Concrete.signingRandomness initialCache
          (randomness, randomnessCache) hrandomness
      subst randomnessCache
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
      obtain ⟨⟨result, resultCache⟩, hattempt, hcontinue⟩ := hrest
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
      cases result with
      | none =>
          exact ih resultCache finalCache signature hcontinue
      | some found =>
          simp only [simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq] at hcontinue
          obtain ⟨hsignature, hcache⟩ := hcontinue
          have hsignature' : signature = found := Option.some.inj hsignature
          subst found
          subst finalCache
          exact ⟨randomness, initialCache, resultCache, hattempt, le_rfl⟩

theorem Concrete.signBoundedAttempts_success_replay
    (attempts : Nat) (secretKey : SecretKey) (request : SignRequest)
    (initialCache resultCache largerCache : QueryCache HashSpec)
    (signature : Signature)
    (hmem : (some signature, resultCache) ∈ support
      ((simulateQ xmssRomImpl
        (Concrete.signBoundedAttempts attempts secretKey request.epoch request.message)).run
          initialCache))
    (hle : resultCache ≤ largerCache) :
    ∃ encoding,
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash largerCache secretKey.parameter request.epoch
          (request.message, signature.randomness)) = some encoding ∧
      signature = Concrete.CacheReplay.signWithEncoding largerCache secretKey
        request.epoch signature.randomness encoding := by
  obtain ⟨randomness, attemptCache, finalAttemptCache, hattempt, hattemptLe⟩ :=
    Concrete.signBoundedAttempts_success_origin attempts secretKey request.epoch
      request.message initialCache resultCache signature hmem
  have heval := Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
    (Concrete.signAttempt secretKey request.epoch request.message randomness :
      OracleComp HashSpec (Option Signature)) attemptCache finalAttemptCache largerCache
      (some signature) hattempt (hattemptLe.trans hle)
  rw [Concrete.CacheReplay.eval_signAttempt] at heval
  unfold Concrete.CacheReplay.signAttempt at heval
  split at heval
  · simp at heval
  · rename_i _ encoding hdecode
    simp only [Option.some.injEq] at heval
    have hrandomness : randomness = signature.randomness := by
      simpa only [Concrete.CacheReplay.signWithEncoding] using
        congrArg Signature.randomness heval
    refine ⟨encoding, ?_, ?_⟩
    · rw [← hrandomness]
      exact hdecode
    · rw [← hrandomness]
      exact heval.symm

theorem Concrete.cappedSign_success_replay
    (publicKey : PublicKey) (secretKey : SecretKey) (request : SignRequest)
    (initialCache resultCache largerCache : QueryCache HashSpec)
    (signature : Signature)
    (hmem : (some signature, resultCache) ∈ support
      ((simulateQ xmssRomImpl
        (Concrete.cappedSign publicKey secretKey request.epoch request.message)).run
          initialCache))
    (hle : resultCache ≤ largerCache) :
    ∃ encoding,
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash largerCache secretKey.parameter request.epoch
          (request.message, signature.randomness)) = some encoding ∧
      signature = Concrete.CacheReplay.signWithEncoding largerCache secretKey
        request.epoch signature.randomness encoding := by
  rw [Concrete.cappedSign_eq] at hmem
  exact Concrete.signBoundedAttempts_success_replay signingAttemptLimit secretKey request
    initialCache resultCache largerCache signature hmem hle

theorem Concrete.cappedSign_success_encodingInput_cached
    (publicKey : PublicKey) (secretKey : SecretKey)
    (request : SignRequest) (initialCache finalCache : QueryCache HashSpec)
    (signature : Signature)
    (hmem : (some signature, finalCache) ∈ support
      ((simulateQ xmssRomImpl
        (Concrete.cappedSign publicKey secretKey request.epoch request.message)).run
          initialCache)) :
    ∃ output, finalCache
      (Concrete.CacheView.encodingInput secretKey.parameter request.epoch
        (request.message, signature.randomness)) = some output := by
  obtain ⟨encoding, hdecode, _hsignature⟩ :=
    Concrete.cappedSign_success_replay publicKey secretKey request initialCache finalCache
      finalCache signature hmem le_rfl
  exact Concrete.CacheView.encodingInput_cached_of_decode_some finalCache
    secretKey.parameter request.epoch request.message signature.randomness encoding hdecode

theorem Concrete.cappedSign_success_verifyFromCache
    (publicKey : PublicKey) (secretKey : SecretKey) (request : SignRequest)
    (initialCache resultCache largerCache : QueryCache HashSpec)
    (signature : Signature)
    (hmem : (some signature, resultCache) ∈ support
      ((simulateQ xmssRomImpl
        (Concrete.cappedSign publicKey secretKey request.epoch request.message)).run
          initialCache))
    (hle : resultCache ≤ largerCache)
    (hpublicKey : publicKey = Concrete.CacheReplay.publicKeyFromCache largerCache secretKey) :
    Concrete.verifyFromCache largerCache publicKey request.epoch request.message signature =
      true := by
  obtain ⟨encoding, hdecode, hsignature⟩ :=
    Concrete.cappedSign_success_replay publicKey secretKey request initialCache resultCache
      largerCache signature hmem hle
  subst publicKey
  rw [hsignature]
  exact Concrete.CacheReplay.verifyFromCache_signWithEncoding largerCache secretKey
    request.epoch request.message signature.randomness encoding hdecode

end XmssSecurity
