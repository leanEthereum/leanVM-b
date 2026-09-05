import SphincsSecurity.Proof.FewTimeParametricCount

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

set_option exponentiation.threshold 600

theorem weightedFewTime126_scaled_certificate :
    (∑ d ∈ Finset.Icc 1 14,
      (d + 1).ascFactorial (14 - d) * 2 ^ (24 * d) * d ^ 14 *
        3 ^ d * 2 ^ (27 * (14 - d))) ≤ Nat.factorial 14 * (9 * 2 ^ 395) := by
  decide

theorem weightedFewTimePatternBound_le_nine_mul_inv123_of_queries_le126
    {signatures q : Nat} (hsignatures : signatures ≤ signatureLimit) (hq : q ≤ 2 ^ 126) :
    weightedFewTimePatternBound signatures q ≤ 9 * ((2 ^ 123 : Nat) : ℝ≥0∞)⁻¹ := by
  have hweight : 1 + (q : ℝ≥0∞) * ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ ≤ (3 : ℝ≥0∞) / 2 ^ 1 := by
    calc
      _ ≤ 1 + ((2 ^ 126 : Nat) : ℝ≥0∞) * ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ := by gcongr
      _ ≤ _ := by
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
        simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
          ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_one]
        norm_num
  apply (weightedFewTimePatternBound_le_of_origin_weight hsignatures hweight
    weightedFewTime126_scaled_certificate).trans_eq
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat]
  norm_num

theorem idealOriginUnionBound_le_nine_mul_inv123_of_queries_le126 {signatures q : Nat}
    (hsignatures : signatures ≤ signatureLimit) (hq : q ≤ 2 ^ 126) :
    idealOriginUnionBound signatures q ≤ 9 * ((2 ^ 123 : Nat) : ℝ≥0∞)⁻¹ := by
  rw [idealOriginUnionBound_eq_weightedFewTimePatternBound]
  exact weightedFewTimePatternBound_le_nine_mul_inv123_of_queries_le126 hsignatures hq

theorem rawTargetOriginUnionBound_le_nine_mul_inv133 {signatures q : Nat}
    (hsignatures : signatures ≤ signatureLimit) (hq : q ≤ 2 ^ 126) :
    rawTargetOriginUnionBound signatures q ≤ 9 * ((2 ^ 133 : Nat) : ℝ≥0∞)⁻¹ := by
  rw [rawTargetOriginUnionBound_eq]
  calc
    _ ≤ ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ *
        (9 * ((2 ^ 123 : Nat) : ℝ≥0∞)⁻¹) :=
      mul_le_mul' le_rfl (idealOriginUnionBound_le_nine_mul_inv123_of_queries_le126 hsignatures hq)
    _ = _ := by
      rw [mul_left_comm, ← ENNReal.mul_inv (by left; positivity) (by right; simp),
        ← Nat.cast_mul, ← pow_add, show ftsTreeHeight + 123 = 133 by rfl]

end SphincsSecurity.Concrete
