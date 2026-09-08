import SphincsSecurity.Proof.CachedDigestRate

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signAttempt signDigestAttemptPrefix signDigestLoop

def FreshDigestAttempt (reference : QueryCache HashSpec) (key : SecretKey) (message : Message)
    (result : DigestAttemptResult) : Prop :=
  reference (tweakableHashInput key.parameter .message (messageDigestPayload key.root message result.1)) = none ∧
    result.2.1 ≠ none

theorem probEvent_signDigestAttemptPrefix_fresh_ge_of_budget
    (key : SecretKey) (message : Message) (reference cache : QueryCache HashSpec)
    (hreference : reference ≤ cache) (budget : Nat) (hcache : QueryCache.enncard cache ≤ budget) :
    (1 - (budget : ENNReal) * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹) *
        ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ ≤
      Pr[FreshDigestAttempt reference key message | signDigestAttemptPrefix key message cache] := by
  rw [signDigestAttemptPrefix]
  apply mul_le_probEvent_bind
  · exact uniform_randomness_messageInput_cacheMiss_ge_of_budget key message cache budget hcache
  · intro randomness _ hmiss
    have hrefMiss : reference (tweakableHashInput key.parameter .message
        (messageDigestPayload key.root message randomness)) = none := by
      cases hc : reference (tweakableHashInput key.parameter .message
          (messageDigestPayload key.root message randomness)) with
      | none => rfl
      | some output => simpa only [hmiss, reduceCtorEq] using hreference hc
    rw [show (fun result => pure (randomness, result)) = pure ∘ fun result => (randomness, result) from rfl,
      probEvent_bind_pure_comp]
    change ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ ≤
      Pr[fun result => reference (tweakableHashInput key.parameter .message
        (messageDigestPayload key.root message randomness)) = none ∧ result.1 ≠ none |
        (simulateQ (randomOracle : QueryImpl HashSpec _) (signAttempt key message randomness)).run cache]
    simpa only [hrefMiss, true_and] using
      (probEvent_signAttempt_fresh_success_eq key message randomness cache hmiss).ge

private theorem probEvent_digestContinuation_fresh_eq
    (attempts : Nat) (key : SecretKey) (message : Message)
    (reference : QueryCache HashSpec) (result : DigestAttemptResult) :
    Pr[fun selected => freshSelectedLoopView? reference key message selected ≠ none |
      signDigestLoopContinuation attempts key message result.1 result.2] =
      (if FreshDigestAttempt reference key message result then 1 else 0) +
        if result.2.1 = none then
          Pr[fun selected => freshSelectedLoopView? reference key message selected ≠ none |
            (simulateQ romImpl (signDigestLoop attempts key message)).run result.2.2] else 0 := by
  cases hr : result.2.1 with
  | none => simp only [signDigestLoopContinuation, FreshDigestAttempt, hr, ne_eq, not_true_eq_false,
      and_false, if_false, if_true, zero_add]
  | some selected =>
      obtain ⟨index, leaves⟩ := selected
      by_cases hc : reference (tweakableHashInput key.parameter .message
          (messageDigestPayload key.root message result.1)) = none
      · simp [signDigestLoopContinuation, FreshDigestAttempt, freshSelectedLoopView?, hr, hc]
      · simp [signDigestLoopContinuation, FreshDigestAttempt, freshSelectedLoopView?, hr, hc]

theorem probEvent_signDigestLoop_fresh_recurrence
    (attempts : Nat) (key : SecretKey) (message : Message) (reference cache : QueryCache HashSpec) :
    Pr[fun result => freshSelectedLoopView? reference key message result ≠ none |
      (simulateQ romImpl (signDigestLoop (attempts + 1) key message)).run cache] =
      Pr[FreshDigestAttempt reference key message | signDigestAttemptPrefix key message cache] +
        ∑' result, Pr[= result | signDigestAttemptPrefix key message cache] *
          if result.2.1 = none then
            Pr[fun selected => freshSelectedLoopView? reference key message selected ≠ none |
              (simulateQ romImpl (signDigestLoop attempts key message)).run result.2.2] else 0 := by
  rw [signDigestLoop_run_succ_eq_attemptPrefix, probEvent_bind_eq_tsum,
    probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
  apply tsum_congr
  intro result
  rw [probEvent_digestContinuation_fresh_eq]
  split_ifs <;> ring

theorem digestAttemptExpectation_mul_rate_le_freshSelection
    (attempts : Nat) (key : SecretKey) (message : Message) (reference cache : QueryCache HashSpec)
    (hreference : reference ≤ cache) (budget : Nat) (rate : ENNReal)
    (hrate : rate ≤ (1 - (budget : ENNReal) * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹) *
      ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹)
    (hbudget : QueryCache.enncard cache + (attempts : ENNReal) ≤ budget) :
    digestAttemptExpectation attempts key message cache * rate ≤
      Pr[fun result => freshSelectedLoopView? reference key message result ≠ none |
        (simulateQ romImpl (signDigestLoop attempts key message)).run cache] := by
  induction attempts generalizing cache with
  | zero => simp only [digestAttemptExpectation, zero_mul]; exact zero_le
  | succ attempts ih =>
      rw [digestAttemptExpectation, add_mul, one_mul, ← ENNReal.tsum_mul_right,
        probEvent_signDigestLoop_fresh_recurrence]
      apply add_le_add
      · exact hrate.trans (probEvent_signDigestAttemptPrefix_fresh_ge_of_budget key message reference cache
          hreference budget ((le_add_right le_rfl).trans hbudget))
      · apply ENNReal.tsum_le_tsum
        intro result
        by_cases hr : result ∈ support (signDigestAttemptPrefix key message cache)
        · by_cases hnone : result.2.1 = none
          · rw [if_pos hnone, if_pos hnone, mul_assoc]
            apply mul_le_mul' le_rfl
            apply ih result.2.2 (hreference.trans (signDigestAttemptPrefix_cache_le key message cache result hr))
            have hgrowth := signAttempt_enncard_le key message result.1 cache result.2
              (signDigestAttemptPrefix_support_attempt key message cache result hr)
            calc
              QueryCache.enncard result.2.2 + (attempts : ENNReal) ≤
                  (QueryCache.enncard cache + 1) + (attempts : ENNReal) := add_le_add hgrowth le_rfl
              _ = QueryCache.enncard cache + ((attempts + 1 : Nat) : ENNReal) := by push_cast; ring
              _ ≤ _ := hbudget
          · simp only [if_neg hnone, mul_zero, zero_mul, le_refl]
        · simp only [probOutput_eq_zero_of_not_mem_support hr, zero_mul, le_refl]

theorem exactDigestReuseWeight_le_fresh_mul_digestReuseWeight
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    exactDigestReuseWeight key message cache ≤
      freshDigestSelectionProbability key message cache * digestReuseWeight q := by
  let rate : ENNReal := (1 - ((q + digestAttemptLimit : Nat) : ENNReal) *
    ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹) * ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹
  have hbudget : QueryCache.enncard cache + (digestAttemptLimit : ENNReal) ≤ (q + digestAttemptLimit : Nat) := by
    simpa only [Nat.cast_add] using add_le_add hcache (le_refl (digestAttemptLimit : ENNReal))
  have hpositive : rate ≠ 0 := by
    apply digestRaceSuccessRate_ne_zero_of_budget_lt
    norm_num [digestAttemptLimit, randomnessBits] at *
    omega
  have hfinite : rate ≠ ⊤ := by dsimp only [rate]; finiteness
  have hcancel : rate * digestReuseWeight q = ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ := by
    change rate * (((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ / rate) = _
    rw [div_eq_mul_inv, mul_left_comm, ENNReal.mul_inv_cancel hpositive hfinite, mul_one]
  have h := mul_le_mul'
    (digestAttemptExpectation_mul_rate_le_freshSelection digestAttemptLimit key message cache cache le_rfl
      (q + digestAttemptLimit) rate le_rfl hbudget) (le_refl (digestReuseWeight q))
  rw [mul_assoc, hcancel] at h
  exact h

theorem nonfresh_mul_digestReuseWeight_le_reuse_gap
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    (1 - freshDigestSelectionProbability key message cache) * digestReuseWeight q ≤
      digestReuseWeight q - exactDigestReuseWeight key message cache := by
  apply ENNReal.le_of_add_le_add_left (exactDigestReuseWeight_ne_top key message cache)
  rw [add_tsub_cancel_of_le (exactDigestReuseWeight_le_digestReuseWeight key message cache q hq hcache)]
  calc
    _ ≤ freshDigestSelectionProbability key message cache * digestReuseWeight q +
        (1 - freshDigestSelectionProbability key message cache) * digestReuseWeight q :=
      add_le_add (exactDigestReuseWeight_le_fresh_mul_digestReuseWeight key message cache q hq hcache) le_rfl
    _ = _ := by
      rw [← add_mul, add_tsub_cancel_of_le (freshDigestSelectionProbability_le_one key message cache), one_mul]

end SphincsSecurity.Concrete
