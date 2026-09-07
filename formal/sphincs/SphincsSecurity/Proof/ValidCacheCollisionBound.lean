import SphincsSecurity.Proof.ValidCacheEntries
import SphincsSecurity.Proof.EncodingValidUpperBound

namespace SphincsSecurity

open _root_.OracleComp OracleSpec ENNReal
attribute [local irreducible] validCacheEntries digestCollisionCount
set_option backward.isDefEq.respectTransparency false

noncomputable def validDigestRate : ENNReal :=
  (TargetSum.validDigests.card : ENNReal) / (Fintype.card Digest : ENNReal)

theorem validDigestRate_le_one_div_32 : validDigestRate ≤ 1 / 32 := by
  rw [validDigestRate, ← probEvent_uniform_encoding_valid]
  exact probEvent_uniform_encoding_valid_le_one_div_32

theorem expected_randomOracle_validCache_card_le (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput) :
    (∑' result, Pr[= result | (randomOracle input).run cache] * (validCacheEntries result.2).card) ≤
      (validCacheEntries cache).card + validDigestRate := by
  by_cases hfresh : cache input = none
  · rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul]
    simp_rw [validCacheEntries_cacheQuery hfinite _ hfresh]
    exact le_of_eq (uniform_insertValidDigest_card _ input (validCacheEntries_fresh hfinite hfresh))
  · obtain ⟨output, ho⟩ := Option.ne_none_iff_exists'.mp hfresh
    rw [randomOracle, QueryImpl.withCaching_run_some _ ho, tsum_probOutput_pure_mul]
    exact le_self_add

theorem expected_randomOracle_validCache_pairs_le (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput) :
    (∑' result, Pr[= result | (randomOracle input).run cache] * (digestCollisionCount (validCacheEntries result.2) : ENNReal)) ≤
      (digestCollisionCount (validCacheEntries cache) : ENNReal) +
        2 * (validCacheEntries cache).card * (Fintype.card Digest : ENNReal)⁻¹ := by
  by_cases hfresh : cache input = none
  · rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul]
    simp_rw [validCacheEntries_cacheQuery hfinite _ hfresh]
    exact uniform_digestCollisionCount_insertValid_le _ input (validCacheEntries_fresh hfinite hfresh)
  · obtain ⟨output, ho⟩ := Option.ne_none_iff_exists'.mp hfresh
    rw [randomOracle, QueryImpl.withCaching_run_some _ ho, tsum_probOutput_pure_mul]
    exact le_self_add

noncomputable def validCacheCollisionEnvelope (q : Nat) (cache : QueryCache HashSpec) : ENNReal :=
  (digestCollisionCount (validCacheEntries cache) : ENNReal) +
    2 * q * (validCacheEntries cache).card * (Fintype.card Digest : ENNReal)⁻¹ +
    (q : ENNReal) ^ 2 * validDigestRate * (Fintype.card Digest : ENNReal)⁻¹

theorem expected_randomOracle_validCache_envelope_le (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput) (q : Nat) :
    (∑' result, Pr[= result | (randomOracle input).run cache] * validCacheCollisionEnvelope q result.2) ≤
      validCacheCollisionEnvelope (q + 1) cache := by
  have hmass : (∑' result, Pr[= result | (randomOracle input).run cache]) = 1 :=
    romImpl_query_mass (.inr input) cache
  have hcard := expected_randomOracle_validCache_card_le cache hfinite input
  have hpairs := expected_randomOracle_validCache_pairs_le cache hfinite input
  simp only [validCacheCollisionEnvelope, mul_add, ENNReal.tsum_add]
  have hweighted : (∑' result, Pr[= result | (randomOracle input).run cache] *
      (2 * q * (validCacheEntries result.2).card * (Fintype.card Digest : ENNReal)⁻¹)) ≤
      2 * q * ((validCacheEntries cache).card + validDigestRate) * (Fintype.card Digest : ENNReal)⁻¹ := by
    simp_rw [mul_assoc, mul_left_comm (Pr[= _ | _]) (2 : ENNReal),
      mul_left_comm (Pr[= _ | _]) (q : ENNReal)]
    simp_rw [← mul_assoc (Pr[= _ | _]) (_ : ENNReal) (Fintype.card Digest : ENNReal)⁻¹]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
    simpa only [mul_assoc] using mul_le_mul' (le_refl (2 : ENNReal))
      (mul_le_mul' (le_refl (q : ENNReal)) (mul_le_mul' hcard (le_refl (Fintype.card Digest : ENNReal)⁻¹)))
  rw [ENNReal.tsum_mul_right, hmass, one_mul]
  apply (add_le_add (add_le_add hpairs hweighted) le_rfl).trans
  calc
    _ ≤ (digestCollisionCount (validCacheEntries cache) : ENNReal) +
        2 * (validCacheEntries cache).card * (Fintype.card Digest : ENNReal)⁻¹ +
        2 * q * ((validCacheEntries cache).card + validDigestRate) * (Fintype.card Digest : ENNReal)⁻¹ +
        (q : ENNReal) ^ 2 * validDigestRate * (Fintype.card Digest : ENNReal)⁻¹ +
        validDigestRate * (Fintype.card Digest : ENNReal)⁻¹ := le_self_add
    _ = _ := by push_cast; ring

theorem expected_validCache_pairs_le_queryBudget {α : Type} (computation : OracleComp OracleWorld α)
    (q : Nat) (hbound : computation.IsQueryBoundP (· matches Sum.inr _) q)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    (∑' result, Pr[= result | (simulateQ romImpl computation).run cache] *
      (digestCollisionCount (validCacheEntries result.2) : ENNReal)) ≤ validCacheCollisionEnvelope q cache := by
  induction computation using OracleComp.inductionOn generalizing q cache with
  | pure value =>
      rw [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul]
      exact le_self_add.trans le_self_add
  | query_bind query next ih =>
      rw [simulateQ_bind, StateT.run_bind, tsum_probOutput_bind_mul, simulateQ_spec_query]
      rw [isQueryBoundP_query_bind_iff] at hbound
      cases query with
      | inl sample =>
          apply le_trans ?_ (le_refl (validCacheCollisionEnvelope q cache))
          have hu : (romImpl (.inl sample)).run cache =
              (fun output => (output, cache)) <$> (liftM (unifSpec.query sample) : ProbComp _) := rfl
          rw [hu, tsum_probOutput_map_mul]
          calc
            _ ≤ ∑' output, Pr[= output | (liftM (unifSpec.query sample) : ProbComp _)] *
                validCacheCollisionEnvelope q cache :=
              ENNReal.tsum_le_tsum fun output => mul_le_mul' le_rfl (ih output q (hbound.2 output) cache hfinite)
            _ = _ := by rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
      | inr input =>
          have hpositive : 0 < q := hbound.1.resolve_left (by simp)
          obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpositive)
          apply le_trans ?_ (expected_randomOracle_validCache_envelope_le cache hfinite input n)
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hr : result ∈ support ((romImpl (.inr input)).run cache)
          · exact mul_le_mul' le_rfl (ih result.1 n (by simpa using hbound.2 result.1) result.2
              (finite_of_mem_support_romImpl hfinite hr))
          · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul]
            exact bot_le

theorem expected_validCache_pairs_empty_le {α : Type} (computation : OracleComp OracleWorld α)
    (q : Nat) (hbound : computation.IsQueryBoundP (· matches Sum.inr _) q) :
    (∑' result, Pr[= result | (simulateQ romImpl computation).run ∅] *
      (digestCollisionCount (validCacheEntries result.2) : ENNReal)) ≤
      (q : ENNReal) ^ 2 * validDigestRate * (Fintype.card Digest : ENNReal)⁻¹ := by
  simpa only [validCacheCollisionEnvelope, validCacheEntries_empty, digestCollisionCount,
    Finset.sum_empty, Finset.card_empty, Nat.cast_zero, mul_zero, zero_mul, zero_add] using
    expected_validCache_pairs_le_queryBudget computation q hbound ∅ finite_empty

theorem validCache_collision_budget_le_127 (q : Nat) (hq : q ≤ 2 ^ 127) :
    (q : ENNReal) ^ 2 * validDigestRate * (Fintype.card Digest : ENNReal)⁻¹ *
      (Fintype.card Digest : ENNReal)⁻¹ ≤
      (q : ENNReal) * (1 / 64) * (Fintype.card Digest : ENNReal)⁻¹ := by
  have hq' : (q : ENNReal) ≤ 2 ^ 127 := by exact_mod_cast hq
  calc
    _ ≤ (q : ENNReal) * 2 ^ 127 * (1 / 32) * (Fintype.card Digest : ENNReal)⁻¹ *
        (Fintype.card Digest : ENNReal)⁻¹ := by
      rw [pow_two]
      exact mul_le_mul' (mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl hq')
        validDigestRate_le_one_div_32) le_rfl) le_rfl
    _ = _ := by
      have hc : (2 : ENNReal) ^ 127 * (1 / 32) * (Fintype.card Digest : ENNReal)⁻¹ = 1 / 64 := by
        rw [show Fintype.card Digest = 2 ^ 128 from card_bitVec digestBits]
        norm_num only [Nat.cast_pow, Nat.cast_ofNat]
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div, ENNReal.toReal_pow]
      calc
        _ = (q : ENNReal) * (2 ^ 127 * (1 / 32) * (Fintype.card Digest : ENNReal)⁻¹) *
            (Fintype.card Digest : ENNReal)⁻¹ := by ring
        _ = _ := by rw [hc]

theorem expected_validCache_pairs_scaled_le_127 {α : Type} (computation : OracleComp OracleWorld α)
    (q : Nat) (hbound : computation.IsQueryBoundP (· matches Sum.inr _) q) (hq : q ≤ 2 ^ 127) :
    (∑' result, Pr[= result | (simulateQ romImpl computation).run ∅] *
      (digestCollisionCount (validCacheEntries result.2) : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ ≤
      (q : ENNReal) * (1 / 64) * (Fintype.card Digest : ENNReal)⁻¹ :=
  (mul_le_mul' (expected_validCache_pairs_empty_le computation q hbound) le_rfl).trans
    (validCache_collision_budget_le_127 q hq)

end SphincsSecurity
