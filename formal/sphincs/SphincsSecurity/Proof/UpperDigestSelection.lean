import SphincsSecurity.Proof.FreshDigestHazard

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signAttempt signDigestAttemptPrefix signDigestLoop

theorem probEvent_signDigestAttemptPrefix_fresh_le_admissibility
    (key : SecretKey) (message : Message) (reference cache : QueryCache HashSpec)
    (hinvariant : OnlyRejectedNewMessageEntries reference cache key message) :
    Pr[FreshDigestAttempt reference key message | signDigestAttemptPrefix key message cache] ≤
      ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ := by
  rw [signDigestAttemptPrefix]
  apply probEvent_bind_le_of_forall_le
  intro randomness _
  rw [show (fun result => pure (randomness, result)) = pure ∘ fun result => (randomness, result) from rfl,
    probEvent_bind_pure_comp]
  change Pr[fun result => reference (tweakableHashInput key.parameter .message
      (messageDigestPayload key.root message randomness)) = none ∧ result.1 ≠ none |
      (simulateQ (randomOracle : QueryImpl HashSpec _) (signAttempt key message randomness)).run cache] ≤ _
  by_cases href : reference (tweakableHashInput key.parameter .message
      (messageDigestPayload key.root message randomness)) = none
  · simp only [href, true_and]
    cases hc : cache (tweakableHashInput key.parameter .message
        (messageDigestPayload key.root message randomness)) with
    | none => exact (probEvent_signAttempt_fresh_success_eq key message randomness cache hc).le
    | some output =>
        apply le_of_eq_of_le (probEvent_eq_zero ?_) zero_le
        intro result hr hsuccess
        have hle : cache ≤ result.2 :=
          simulateQ_romImpl_cache_le (liftM (signAttempt key message randomness :
            OracleComp HashSpec (Option (Index × (DigestTree → FtsLeaf))))) cache result (by
              rw [simulateQ_romImpl_liftM]
              exact hr)
        exact hsuccess ((signAttempt_result_of_cached key message randomness cache result.2 result.1 output
          (hle hc) hr).trans (hinvariant randomness output href hc))
  · apply le_of_eq_of_le (probEvent_eq_zero ?_) zero_le
    intro result _ hevent
    exact href hevent.1

theorem probEvent_signDigestLoop_fresh_le_attempts_mul_admissibility
    (attempts : Nat) (key : SecretKey) (message : Message) (reference cache : QueryCache HashSpec)
    (hinvariant : OnlyRejectedNewMessageEntries reference cache key message) :
    Pr[fun result => freshSelectedLoopView? reference key message result ≠ none |
      (simulateQ romImpl (signDigestLoop attempts key message)).run cache] ≤
      digestAttemptExpectation attempts key message cache * ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ := by
  induction attempts generalizing cache with
  | zero => simp [signDigestLoop, freshSelectedLoopView?, digestAttemptExpectation]
  | succ attempts ih =>
      rw [probEvent_signDigestLoop_fresh_recurrence, digestAttemptExpectation, add_mul, one_mul,
        ← ENNReal.tsum_mul_right]
      apply add_le_add (probEvent_signDigestAttemptPrefix_fresh_le_admissibility key message reference cache hinvariant)
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support (signDigestAttemptPrefix key message cache)
      · by_cases hnone : result.2.1 = none
        · rw [if_pos hnone, if_pos hnone, mul_assoc]
          apply mul_le_mul' le_rfl
          apply ih
          apply onlyRejectedNewMessageEntries_of_failed_attempt reference cache result.2.2 key message result.1 hinvariant
          have heq : result.2 = (none, result.2.2) := Prod.ext hnone rfl
          rw [← heq]
          exact signDigestAttemptPrefix_support_attempt key message cache result hr
        · simp only [if_neg hnone, mul_zero, zero_mul, le_refl]
      · simp only [probOutput_eq_zero_of_not_mem_support hr, zero_mul, le_refl]

theorem freshDigestSelectionProbability_le_exactReuse_mul_pow118
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    freshDigestSelectionProbability key message cache ≤
      exactDigestReuseWeight key message cache * ((2 ^ 118 : Nat) : ENNReal) := by
  have hscalar : ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ * ((2 ^ 118 : Nat) : ENNReal) =
      ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, randomnessBits, ftsTreeHeight]
  apply (probEvent_signDigestLoop_fresh_le_attempts_mul_admissibility digestAttemptLimit key message cache cache
    (onlyRejectedNewMessageEntries_self cache key message)).trans_eq
  rw [exactDigestReuseWeight, mul_assoc, hscalar]

theorem nonfreshSelection_ge_cached_fraction
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hcache : QueryCache.enncard cache ≤ q) :
    cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) /
        (cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) + ((2 ^ 118 : Nat) : ENNReal)) ≤
      1 - freshDigestSelectionProbability key message cache := by
  let count := cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True)
  let cap : ENNReal := (2 ^ 118 : Nat)
  have hcount : count ≠ ⊤ := ne_top_of_le_ne_top (by finiteness)
    ((cachedMessageEntryCountWhere_le_enncard cache key.parameter key.root message (fun _ => True)).trans hcache)
  have hdenZero : count + cap ≠ 0 := by dsimp only [cap]; positivity
  have hdenTop : count + cap ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hcount, by dsimp only [cap]; finiteness⟩
  have hmass : freshDigestSelectionProbability key message cache + count * exactDigestReuseWeight key message cache ≤ 1 :=
    le_self_add.trans_eq (freshSelection_add_count_exactWeight_add_exhaustion key message cache)
  have hupper := freshDigestSelectionProbability_le_exactReuse_mul_pow118 key message cache
  have hscaled := mul_le_mul' hmass (le_refl cap)
  have hcoupled : freshDigestSelectionProbability key message cache * (count + cap) ≤ cap := by
    calc
      _ = count * freshDigestSelectionProbability key message cache + freshDigestSelectionProbability key message cache * cap := by ring
      _ ≤ count * (exactDigestReuseWeight key message cache * cap) + freshDigestSelectionProbability key message cache * cap :=
        add_le_add (mul_le_mul' le_rfl hupper) le_rfl
      _ ≤ _ := by convert hscaled using 1 <;> first | rfl | ring
  have hfresh : freshDigestSelectionProbability key message cache ≤ cap / (count + cap) :=
    (ENNReal.le_div_iff_mul_le (Or.inl hdenZero) (Or.inl hdenTop)).mpr hcoupled
  apply ENNReal.le_of_add_le_add_right (a := freshDigestSelectionProbability key message cache)
    (ne_top_of_le_ne_top (by simp) (freshDigestSelectionProbability_le_one key message cache))
  rw [tsub_add_cancel_of_le (freshDigestSelectionProbability_le_one key message cache)]
  calc
    _ ≤ count / (count + cap) + cap / (count + cap) := add_le_add le_rfl hfresh
    _ = 1 := by rw [← ENNReal.add_div, ENNReal.div_self hdenZero hdenTop]

end SphincsSecurity.Concrete
