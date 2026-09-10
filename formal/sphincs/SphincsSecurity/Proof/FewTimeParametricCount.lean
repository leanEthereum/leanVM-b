import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.FewTimeWeightedCount

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

set_option exponentiation.threshold 600

theorem weightedFewTime_scaled_sum_le {signatures numerator shift budget : Nat}
    (hsignatures : signatures ≤ signatureLimit)
    (hcertificate : (∑ d ∈ Finset.Icc 1 14,
      (d + 1).ascFactorial (14 - d) * 2 ^ (24 * d) * d ^ 14 *
        numerator ^ d * 2 ^ ((26 + shift) * (14 - d))) ≤ Nat.factorial 14 * budget) :
    (∑ d ∈ Finset.Icc 1 14,
      Fintype.card (FewTimePattern signatures d) * numerator ^ d *
        2 ^ ((26 + shift) * (14 - d))) ≤ budget := by
  apply Nat.le_of_mul_le_mul_left _ (Nat.factorial_pos 14)
  rw [Finset.mul_sum]
  apply le_trans (Finset.sum_le_sum fun d hd => ?_) hcertificate
  have hd14 := (Finset.mem_Icc.mp hd).2
  have hfactorial := Nat.factorial_mul_ascFactorial d (14 - d)
  rw [Nat.add_sub_of_le hd14] at hfactorial
  calc
    _ = (d + 1).ascFactorial (14 - d) *
        (Nat.factorial d * Fintype.card (FewTimePattern signatures d)) *
          numerator ^ d * 2 ^ ((26 + shift) * (14 - d)) := by rw [← hfactorial]; ring
    _ ≤ (d + 1).ascFactorial (14 - d) *
        (2 ^ (24 * d) * d ^ (ftsTrees - 1)) * numerator ^ d *
          2 ^ ((26 + shift) * (14 - d)) := by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
        (fewTimePattern_card_scaled_le_signatureLimit hsignatures)))
    _ = _ := by rw [show ftsTrees - 1 = 14 by rfl]; ring

theorem weightedFewTime_term_common_denominator (signatures d numerator shift : Nat)
    (hd : d ≤ 14) :
    (Fintype.card (FewTimePattern signatures d) : ℝ≥0∞) *
        ((numerator : ℝ≥0∞) / 2 ^ shift) ^ d *
          ((2 ^ (26 * d + 140) : Nat) : ℝ≥0∞)⁻¹ =
      (Fintype.card (FewTimePattern signatures d) * numerator ^ d *
        2 ^ ((26 + shift) * (14 - d)) : Nat) *
          ((2 ^ ((26 + shift) * 14 + 140) : Nat) : ℝ≥0∞)⁻¹ := by
  have hden : ((2 : ℝ≥0∞) ^ shift) ^ d * ((2 ^ (26 * d + 140) : Nat) : ℝ≥0∞) =
      ((2 ^ ((26 + shift) * d + 140) : Nat) : ℝ≥0∞) := by
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  have hbase : (Fintype.card (FewTimePattern signatures d) : ℝ≥0∞) *
      ((numerator : ℝ≥0∞) / 2 ^ shift) ^ d *
        ((2 ^ (26 * d + 140) : Nat) : ℝ≥0∞)⁻¹ =
      (Fintype.card (FewTimePattern signatures d) * numerator ^ d : Nat) /
        ((2 ^ ((26 + shift) * d + 140) : Nat) : ℝ≥0∞) := by
    rw [div_eq_mul_inv, mul_pow]
    rw [div_eq_mul_inv, ← hden, ENNReal.mul_inv (by left; positivity) (by right; finiteness)]
    simp only [ENNReal.inv_pow, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    ring
  rw [hbase, ← div_eq_mul_inv]
  let factor : ℝ≥0∞ := (2 ^ ((26 + shift) * (14 - d)) : Nat)
  have hz : factor ≠ 0 := by positivity
  have ht : factor ≠ ∞ := by simp [factor]
  rw [← ENNReal.mul_div_mul_right
    (Fintype.card (FewTimePattern signatures d) * numerator ^ d : Nat)
    ((2 ^ ((26 + shift) * d + 140) : Nat) : ℝ≥0∞) hz ht]
  congr 1
  · simp [factor, Nat.cast_mul]
  · dsimp [factor]
    rw [← Nat.cast_mul, ← pow_add]
    congr 2
    calc
      (26 + shift) * d + 140 + (26 + shift) * (14 - d) =
          (26 + shift) * (d + (14 - d)) + 140 := by ring
      _ = _ := by rw [Nat.add_sub_of_le hd]

theorem weightedFewTimePatternBound_le_of_origin_weight
    {signatures q numerator shift budget : Nat}
    (hsignatures : signatures ≤ signatureLimit)
    (hweight : 1 + (q : ℝ≥0∞) * ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ ≤
      (numerator : ℝ≥0∞) / 2 ^ shift)
    (hcertificate : (∑ d ∈ Finset.Icc 1 14,
      (d + 1).ascFactorial (14 - d) * 2 ^ (24 * d) * d ^ 14 *
        numerator ^ d * 2 ^ ((26 + shift) * (14 - d))) ≤ Nat.factorial 14 * budget) :
    weightedFewTimePatternBound signatures q ≤
      (budget : ℝ≥0∞) * ((2 ^ ((26 + shift) * 14 + 140) : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 14, ∑ _pattern : FewTimePattern signatures d,
        ((numerator : ℝ≥0∞) / 2 ^ shift) ^ d *
          ((2 ^ (26 * d + 140) : Nat) : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro pattern _
      gcongr
      calc
        _ ≤ (1 + q * ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹) ^ Fintype.card pattern.selected :=
          originChoiceMass_le _ _ _
        _ = (1 + q * ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹) ^ d := by
          rw [Fintype.card_coe, pattern.card_selected]
        _ ≤ _ := pow_le_pow_left' hweight d
    _ = ∑ d ∈ Finset.Icc 1 14,
        (Fintype.card (FewTimePattern signatures d) * numerator ^ d *
          2 ^ ((26 + shift) * (14 - d)) : Nat) *
            ((2 ^ ((26 + shift) * 14 + 140) : Nat) : ℝ≥0∞)⁻¹ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      apply Finset.sum_congr rfl
      intro d hd
      rw [← mul_assoc]
      exact weightedFewTime_term_common_denominator signatures d numerator shift
        (Finset.mem_Icc.mp hd).2
    _ = ((∑ d ∈ Finset.Icc 1 14,
        Fintype.card (FewTimePattern signatures d) * numerator ^ d *
          2 ^ ((26 + shift) * (14 - d)) : Nat) : ℝ≥0∞) *
            ((2 ^ ((26 + shift) * 14 + 140) : Nat) : ℝ≥0∞)⁻¹ := by
      rw [← Finset.sum_mul, Nat.cast_sum]
    _ ≤ _ := mul_le_mul' (Nat.cast_le.mpr
      (weightedFewTime_scaled_sum_le hsignatures hcertificate)) le_rfl

end SphincsSecurity.Concrete
