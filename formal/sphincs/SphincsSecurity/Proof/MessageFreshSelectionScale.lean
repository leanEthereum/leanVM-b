import SphincsSecurity.Proof.MessageInputMiss
import SphincsSecurity.Proof.UpperDigestSelection

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
noncomputable local instance : SampleableType Randomness := SampleableType.ofFintype Randomness
attribute [local irreducible] signAttempt signDigestAttemptPrefix signDigestLoop

theorem probEvent_signDigestAttemptPrefix_fresh_le_referenceMiss
    (key : SecretKey) (message : Message) (reference cache : QueryCache HashSpec)
    (hinvariant : OnlyRejectedNewMessageEntries reference cache key message) :
    Pr[FreshDigestAttempt reference key message | signDigestAttemptPrefix key message cache] ≤
      messageInputMissProbability key message reference * ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ := by
  rw [signDigestAttemptPrefix, probEvent_bind_eq_tsum, messageInputMissProbability,
    probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro randomness
  rw [show (fun result => pure (randomness, result)) = pure ∘ fun result => (randomness, result) from rfl,
    probEvent_bind_pure_comp]
  change Pr[= randomness | ($ᵗ Randomness : ProbComp Randomness)] *
      Pr[fun result => reference (tweakableHashInput key.parameter .message
        (messageDigestPayload key.root message randomness)) = none ∧ result.1 ≠ none |
        (simulateQ (randomOracle : QueryImpl HashSpec _) (signAttempt key message randomness)).run cache] ≤ _
  by_cases href : reference (tweakableHashInput key.parameter .message
      (messageDigestPayload key.root message randomness)) = none
  · rw [if_pos href]
    apply mul_le_mul' le_rfl
    simp only [href, true_and]
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
  · rw [if_neg href, zero_mul]
    have hzero : Pr[fun result => reference (tweakableHashInput key.parameter .message
        (messageDigestPayload key.root message randomness)) = none ∧ result.1 ≠ none |
        (simulateQ (randomOracle : QueryImpl HashSpec _) (signAttempt key message randomness)).run cache] = 0 := by
      apply probEvent_eq_zero
      intro result _ hevent
      exact href hevent.1
    rw [hzero, mul_zero]

theorem probEvent_signDigestLoop_fresh_le_attempts_mul_referenceMiss
    (attempts : Nat) (key : SecretKey) (message : Message) (reference cache : QueryCache HashSpec)
    (hinvariant : OnlyRejectedNewMessageEntries reference cache key message) :
    Pr[fun result => freshSelectedLoopView? reference key message result ≠ none |
      (simulateQ romImpl (signDigestLoop attempts key message)).run cache] ≤
      digestAttemptExpectation attempts key message cache *
        (messageInputMissProbability key message reference * ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹) := by
  induction attempts generalizing cache with
  | zero => simp [signDigestLoop, freshSelectedLoopView?, digestAttemptExpectation]
  | succ attempts ih =>
      rw [probEvent_signDigestLoop_fresh_recurrence, digestAttemptExpectation, add_mul, one_mul,
        ← ENNReal.tsum_mul_right]
      apply add_le_add (probEvent_signDigestAttemptPrefix_fresh_le_referenceMiss key message reference cache hinvariant)
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

noncomputable def messageFreshSelectionScale (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) : ENNReal :=
  messageInputMissProbability key message cache * ((2 ^ 118 : Nat) : ENNReal)

theorem messageFreshSelectionScale_eq_count (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    messageFreshSelectionScale key message cache =
      (1 - cachedMessageEntryCount cache key.parameter key.root message * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹) *
        ((2 ^ 118 : Nat) : ENNReal) := by
  rw [messageFreshSelectionScale, messageInputMissProbability_eq_count]

theorem messageFreshSelectionScale_le_pow118 (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    messageFreshSelectionScale key message cache ≤ ((2 ^ 118 : Nat) : ENNReal) :=
  mul_le_of_le_one_left' (messageInputMissProbability_le_one key message cache)

theorem messageFreshSelectionScale_ne_top (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    messageFreshSelectionScale key message cache ≠ ⊤ :=
  ne_top_of_le_ne_top (by finiteness) (messageFreshSelectionScale_le_pow118 key message cache)

theorem freshDigestSelectionProbability_le_exactReuse_mul_messageScale
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    freshDigestSelectionProbability key message cache ≤
      exactDigestReuseWeight key message cache * messageFreshSelectionScale key message cache := by
  have hscalar : ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ * ((2 ^ 118 : Nat) : ENNReal) =
      ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, randomnessBits, ftsTreeHeight]
  apply (probEvent_signDigestLoop_fresh_le_attempts_mul_referenceMiss digestAttemptLimit key message cache cache
    (onlyRejectedNewMessageEntries_self cache key message)).trans_eq
  rw [exactDigestReuseWeight, messageFreshSelectionScale]
  calc
    _ = digestAttemptExpectation digestAttemptLimit key message cache *
        (messageInputMissProbability key message cache *
          (((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ * ((2 ^ 118 : Nat) : ENNReal))) := by rw [hscalar]
    _ = _ := by ring

theorem messageFreshSelectionScale_pos (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    0 < messageFreshSelectionScale key message cache := by
  have hmiss := uniform_randomness_messageInput_cacheMiss_ge_one_sub_one_half key message cache
    (hcache.trans (by exact_mod_cast hq))
  have hpositive : 0 < (1 - ((2 ^ 1 : Nat) : ENNReal)⁻¹) := by
    apply tsub_pos_iff_lt.mpr
    norm_num
  exact ENNReal.mul_pos (ne_of_gt (hpositive.trans_le hmiss)) (by norm_num)

theorem messageFreshSelectionScale_inv_eq (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    (messageFreshSelectionScale key message cache)⁻¹ = ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ /
      (messageInputMissProbability key message cache * ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹) := by
  have hscalar : ((2 ^ 118 : Nat) : ENNReal)⁻¹ =
      ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ * ((2 ^ ftsTreeHeight : Nat) : ENNReal) := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, randomnessBits, ftsTreeHeight]
  rw [messageFreshSelectionScale, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inr (by finiteness)) (Or.inr (by norm_num)),
    ENNReal.mul_inv (Or.inr (by finiteness)) (Or.inr (ENNReal.inv_ne_zero.mpr (by finiteness))),
    inv_inv, hscalar]
  ring

theorem inv_messageFreshSelectionScale_le_digestReuseWeight
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hcache : QueryCache.enncard cache ≤ q) :
    (messageFreshSelectionScale key message cache)⁻¹ ≤ digestReuseWeight q := by
  rw [messageFreshSelectionScale_inv_eq, digestReuseWeight]
  apply ENNReal.div_le_div_left
  apply mul_le_mul' _ le_rfl
  exact uniform_randomness_messageInput_cacheMiss_ge_of_budget key message cache (q + digestAttemptLimit)
    (hcache.trans (by exact_mod_cast Nat.le_add_right q digestAttemptLimit))

theorem nonfreshSelection_ge_message_fraction
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) /
        (cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) + messageFreshSelectionScale key message cache) ≤
      1 - freshDigestSelectionProbability key message cache := by
  let count := cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True)
  let scale := messageFreshSelectionScale key message cache
  have hcount : count ≠ ⊤ := ne_top_of_le_ne_top (by finiteness)
    ((cachedMessageEntryCountWhere_le_enncard cache key.parameter key.root message (fun _ => True)).trans hcache)
  have hdenZero : count + scale ≠ 0 := ne_of_gt
    ((messageFreshSelectionScale_pos key message cache q hq hcache).trans_le (le_add_of_nonneg_left zero_le))
  have hdenTop : count + scale ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hcount, messageFreshSelectionScale_ne_top key message cache⟩
  have hmass : freshDigestSelectionProbability key message cache + count * exactDigestReuseWeight key message cache ≤ 1 :=
    le_self_add.trans_eq (freshSelection_add_count_exactWeight_add_exhaustion key message cache)
  have hupper := freshDigestSelectionProbability_le_exactReuse_mul_messageScale key message cache
  have hscaled := mul_le_mul' hmass (le_refl scale)
  have hcoupled : freshDigestSelectionProbability key message cache * (count + scale) ≤ scale := by
    calc
      _ = count * freshDigestSelectionProbability key message cache + freshDigestSelectionProbability key message cache * scale := by ring
      _ ≤ count * (exactDigestReuseWeight key message cache * scale) + freshDigestSelectionProbability key message cache * scale :=
        add_le_add (mul_le_mul' le_rfl hupper) le_rfl
      _ ≤ _ := by convert hscaled using 1 <;> first | rfl | ring
  have hfresh : freshDigestSelectionProbability key message cache ≤ scale / (count + scale) :=
    (ENNReal.le_div_iff_mul_le (Or.inl hdenZero) (Or.inl hdenTop)).mpr hcoupled
  apply ENNReal.le_of_add_le_add_right (a := freshDigestSelectionProbability key message cache)
    (ne_top_of_le_ne_top (by simp) (freshDigestSelectionProbability_le_one key message cache))
  rw [tsub_add_cancel_of_le (freshDigestSelectionProbability_le_one key message cache)]
  calc
    _ ≤ count / (count + scale) + scale / (count + scale) := add_le_add le_rfl hfresh
    _ = 1 := by rw [← ENNReal.add_div, ENNReal.div_self hdenZero hdenTop]

end SphincsSecurity.Concrete
