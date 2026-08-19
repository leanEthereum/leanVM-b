import XmssSecurity.Proof.BoundedSign
import XmssSecurity.Proof.SignCacheHitProbability

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

set_option maxRecDepth 100000

noncomputable local instance : SampleableType Randomness :=
  SampleableType.ofFintype Randomness

noncomputable def Concrete.signBoundedAttemptsContinuation
    (attempts : Nat) (secretKey : SecretKey) (epoch : Epoch) (message : Message)
    (result : Option Signature × QueryCache HashSpec) :
    ProbComp (Option Signature × QueryCache HashSpec) :=
  match result.1 with
  | some signature => pure (some signature, result.2)
  | none => (simulateQ xmssRomImpl
      (Concrete.signBoundedAttempts attempts secretKey epoch message)).run result.2

attribute [irreducible] Concrete.signBoundedAttemptsContinuation

theorem Concrete.signBoundedAttempts_run_succ_eq
    (attempts : Nat) (secretKey : SecretKey) (epoch : Epoch) (message : Message)
    (cache : QueryCache HashSpec) :
    (simulateQ xmssRomImpl
      (Concrete.signBoundedAttempts (attempts + 1) secretKey epoch message)).run cache =
      (($ᵗ Randomness) >>= fun randomness =>
        (simulateQ randomOracle
          (Concrete.signAttempt secretKey epoch message randomness :
            OracleComp HashSpec (Option Signature))).run cache >>=
          Concrete.signBoundedAttemptsContinuation attempts secretKey epoch
            message) := by
  rw [Concrete.signBoundedAttempts, simulateQ_bind, StateT.run_bind]
  have hsampleRun :
      (simulateQ xmssRomImpl
        (liftM Concrete.signingRandomness)).run cache =
        (fun randomness => (randomness, cache)) <$> Concrete.signingRandomness := by
    change (simulateQ (unifFwdImpl HashSpec +
        (randomOracle : QueryImpl HashSpec
          (StateT (QueryCache HashSpec) ProbComp)))
      (liftM Concrete.signingRandomness)).run cache = _
    exact roSim.run_liftM
      (hashSpec := HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      Concrete.signingRandomness cache
  rw [hsampleRun, Concrete.signingRandomness_eq]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  apply bind_congr
  intro randomness
  rw [simulateQ_bind, StateT.run_bind]
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
  rw [hroute]
  apply bind_congr
  intro result
  rcases result with ⟨result, resultCache⟩
  cases result <;> simp [Concrete.signBoundedAttemptsContinuation]

theorem Concrete.signBoundedAttempts_run_succ_eq_sign_bind
    (attempts : Nat) (publicKey : PublicKey) (secretKey : SecretKey)
    (epoch : Epoch) (message : Message) (cache : QueryCache HashSpec) :
    (simulateQ xmssRomImpl
      (Concrete.signBoundedAttempts (attempts + 1) secretKey epoch message)).run cache =
      (simulateQ xmssRomImpl
        (Concrete.sign publicKey secretKey epoch message)).run cache >>=
          Concrete.signBoundedAttemptsContinuation attempts secretKey epoch
            message := by
  rw [Concrete.signBoundedAttempts_run_succ_eq, Concrete.sign_run_eq,
    bind_assoc]

set_option linter.constructorNameAsVariable false in
theorem Concrete.signBoundedAttempts_encodingInput_referenceCache_hit_le
    (attempts : Nat) (secretKey : SecretKey) (epoch : Epoch) (message : Message)
    (referenceCache workingCache : QueryCache HashSpec) :
    Pr[fun result : Option Signature × QueryCache HashSpec =>
      ∃ signature, result.1 = some signature ∧ ∃ output,
        referenceCache (Concrete.CacheView.encodingInput secretKey.parameter epoch
          (message, signature.randomness)) = some output |
      (simulateQ xmssRomImpl
        (Concrete.signBoundedAttempts attempts secretKey epoch message)).run workingCache] ≤
      (attempts : ℝ≥0∞) * QueryCache.enncard referenceCache *
        ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
  induction attempts generalizing workingCache with
  | zero =>
      simp [Concrete.signBoundedAttempts]
  | succ attempts ih =>
      rw [Concrete.signBoundedAttempts_run_succ_eq]
      refine (probEvent_bind_le_probEvent_add
        (p := fun randomness : Randomness => ∃ output,
          referenceCache (Concrete.CacheView.encodingInput secretKey.parameter epoch
            (message, randomness)) = some output)
        (ε := (attempts : ℝ≥0∞) * QueryCache.enncard referenceCache *
          ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹) ?_).trans ?_
      · intro randomness _hrandomness hmiss
        refine probEvent_bind_le_of_forall_le fun attemptResult hattempt => ?_
        cases hresult : attemptResult.1 with
        | none =>
            simpa [Concrete.signBoundedAttemptsContinuation, hresult] using
              ih attemptResult.2
        | some signature =>
            refine le_of_eq_of_le (probEvent_eq_zero ?_) zero_le
            intro result hsupport hevent
            have hsupport' : result ∈ support
                (pure (some signature, attemptResult.2) :
                  ProbComp (Option Signature × QueryCache HashSpec)) := by
              simpa [Concrete.signBoundedAttemptsContinuation, hresult] using
                hsupport
            obtain ⟨found, hfound, output, hhit⟩ := hevent
            have hreturned : result.1 = some signature := by
              simpa only [support_pure, Set.mem_singleton_iff] using
                congrArg Prod.fst hsupport'
            have hsignature : signature = found :=
              Option.some.inj (hreturned.symm.trans hfound)
            have hrandomness := Concrete.signAttempt_support_randomness secretKey epoch
              message randomness workingCache attemptResult.2 signature ?_
            · apply hmiss
              rw [← hsignature] at hhit
              rw [hrandomness] at hhit
              exact ⟨output, hhit⟩
            · have heq : attemptResult = (some signature, attemptResult.2) :=
                Prod.ext hresult rfl
              rw [← heq]
              exact hattempt
      · calc
          _ ≤ QueryCache.enncard referenceCache *
                ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ +
              (attempts : ℝ≥0∞) * QueryCache.enncard referenceCache *
                ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ :=
            add_le_add
              (uniform_signingRandomness_encodingInput_cacheHit_le
                secretKey.parameter epoch message referenceCache) le_rfl
          _ = _ := by
            push_cast
            ring

set_option linter.constructorNameAsVariable false in
theorem Concrete.cappedSign_encodingInput_initialCache_hit_le
    (publicKey : PublicKey) (secretKey : SecretKey)
    (epoch : Epoch) (message : Message) (cache : QueryCache HashSpec) :
    Pr[fun result : Option Signature × QueryCache HashSpec =>
      ∃ signature, result.1 = some signature ∧ ∃ output,
        cache (Concrete.CacheView.encodingInput secretKey.parameter epoch
          (message, signature.randomness)) = some output |
      (simulateQ xmssRomImpl
        (Concrete.cappedSign publicKey secretKey epoch message)).run cache] ≤
      (signingAttemptLimit : ℝ≥0∞) * QueryCache.enncard cache *
        ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
  rw [Concrete.cappedSign_eq]
  exact Concrete.signBoundedAttempts_encodingInput_referenceCache_hit_le
    signingAttemptLimit secretKey epoch message cache cache

end XmssSecurity
