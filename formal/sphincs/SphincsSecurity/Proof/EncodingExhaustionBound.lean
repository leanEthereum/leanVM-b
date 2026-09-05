import SphincsSecurity.Proof.EncodingCountCertificate
import SphincsSecurity.Proof.EncodingExhaustionProbability

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option exponentiation.threshold 512

theorem one_sub_inv_nat_pow_mul_le (m k : Nat) (hm : 1 ≤ m) :
    (1 - (m : ℝ)⁻¹) ^ (m * k) ≤ (1 / 2 : ℝ) ^ k := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmin : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hx : (0 : ℝ) ≤ (m : ℝ)⁻¹ := inv_nonneg.mpr hmpos.le
  have hxle : (m : ℝ)⁻¹ ≤ 1 := by
    simpa using (inv_le_inv₀ hmpos (by norm_num : (0 : ℝ) < 1)).mpr hmin
  have hbase : 1 - (m : ℝ)⁻¹ ≤ (1 + (m : ℝ)⁻¹)⁻¹ := by
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 1 + (m : ℝ)⁻¹)).mpr
      (show (1 - (m : ℝ)⁻¹) * (1 + (m : ℝ)⁻¹) ≤ 1 by nlinarith [sq_nonneg ((m : ℝ)⁻¹)])
    simpa only [one_div] using h
  have hbernoulli : (2 : ℝ) ≤ (1 + (m : ℝ)⁻¹) ^ m := by
    have h := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ (m : ℝ)⁻¹) m
    simpa only [mul_inv_cancel₀ (ne_of_gt hmpos), show (1 : ℝ) + 1 = 2 by norm_num] using h
  have hblock : (1 - (m : ℝ)⁻¹) ^ m ≤ (1 / 2 : ℝ) := by
    calc
      _ ≤ ((1 + (m : ℝ)⁻¹)⁻¹) ^ m := pow_le_pow_left₀ (sub_nonneg.mpr hxle) hbase m
      _ = ((1 + (m : ℝ)⁻¹) ^ m)⁻¹ := inv_pow _ _
      _ ≤ _ := by
        rw [one_div]
        exact (inv_le_inv₀ (by positivity) (by norm_num)).mpr hbernoulli
  rw [pow_mul]
  exact pow_le_pow_left₀ (pow_nonneg (sub_nonneg.mpr hxle) m) hblock k

theorem one_sub_inv_nat_pow_mul_le_ennreal (m k : Nat) (hm : 1 ≤ m) :
    (1 - (m : ℝ≥0∞)⁻¹) ^ (m * k) ≤ ((2 ^ k : Nat) : ℝ≥0∞)⁻¹ := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmin : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hxle : (m : ℝ)⁻¹ ≤ 1 := by
    simpa using (inv_le_inv₀ hmpos (by norm_num : (0 : ℝ) < 1)).mpr hmin
  have hbase : (0 : ℝ) ≤ 1 - (m : ℝ)⁻¹ := sub_nonneg.mpr hxle
  have h := ENNReal.ofReal_le_ofReal (one_sub_inv_nat_pow_mul_le m k hm)
  rw [ENNReal.ofReal_pow hbase, ENNReal.ofReal_sub 1 (by positivity), ENNReal.ofReal_one,
    ENNReal.ofReal_inv_of_pos hmpos, ENNReal.ofReal_natCast] at h
  rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2)] at h
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ℝ≥0∞)⁻¹ := by
    rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
  rw [hhalf, ← ENNReal.inv_pow] at h
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using h

theorem encoding_exhaustion_tail_le_inv512 :
    (1 - ((2 ^ 23 : Nat) : ℝ≥0∞)⁻¹) ^ encodingAttemptLimit ≤ ((2 ^ 512 : Nat) : ℝ≥0∞)⁻¹ := by
  have hbound := one_sub_inv_nat_pow_mul_le_ennreal (2 ^ 23) 512 (by norm_num)
  have hexponent : (2 ^ 23 : Nat) * 512 = encodingAttemptLimit := by norm_num [encodingAttemptLimit]
  rw [hexponent] at hbound
  exact hbound

theorem encoding_exhaustion_global_bound_le_inv216 :
    ((3 * 2 ^ 294 : Nat) : ℝ≥0∞) *
      (1 - (TargetSum.validDigests.card : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞)) ^ encodingAttemptLimit ≤
      ((2 ^ 216 : Nat) : ℝ≥0∞)⁻¹ := by
  have hcount : ((2 ^ 105 : Nat) : ℝ≥0∞) ≤ (TargetSum.validDigests.card : ℝ≥0∞) :=
    (Nat.cast_le (α := ℝ≥0∞)).mpr TargetSum.validDigests_card_ge_pow105
  have hratio : ((2 ^ 23 : Nat) : ℝ≥0∞)⁻¹ ≤
      (TargetSum.validDigests.card : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) := by
    calc
      _ = ((2 ^ 105 : Nat) : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) := by
        have hcard : Fintype.card Digest = 2 ^ 128 := by simp [digestBits]
        rw [hcard]
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        norm_num
      _ ≤ _ := by rw [div_eq_mul_inv, div_eq_mul_inv]; exact mul_le_mul' hcount le_rfl
  have htail := (pow_le_pow_left' (tsub_le_tsub_left hratio 1) encodingAttemptLimit).trans
    encoding_exhaustion_tail_le_inv512
  calc
    _ ≤ ((3 * 2 ^ 294 : Nat) : ℝ≥0∞) * ((2 ^ 512 : Nat) : ℝ≥0∞)⁻¹ := mul_le_mul' le_rfl htail
    _ ≤ _ := by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      norm_num

theorem probEvent_anyEncodingInputsExhausted_le_inv216
    (computation : OracleComp OracleWorld α) :
    Pr[fun result => AnyEncodingInputsExhausted result.2 | (simulateQ romImpl computation).run ∅] ≤
      ((2 ^ 216 : Nat) : ℝ≥0∞)⁻¹ :=
  (probEvent_anyEncodingInputsExhausted_le computation).trans encoding_exhaustion_global_bound_le_inv216

theorem probEvent_cachedOtsEncodingFailure_le_inv216
    (computation : OracleComp OracleWorld α) :
    Pr[fun result => CachedOtsEncodingFailure result.2 | (simulateQ romImpl computation).run ∅] ≤
      ((2 ^ 216 : Nat) : ℝ≥0∞)⁻¹ :=
  (probEvent_cachedOtsEncodingFailure_le computation).trans encoding_exhaustion_global_bound_le_inv216

end SphincsSecurity.Concrete
