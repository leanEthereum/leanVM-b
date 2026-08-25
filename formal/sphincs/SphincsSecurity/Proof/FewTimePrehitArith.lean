import SphincsSecurity.Proof.FewTimeSourceCount

/-!
# Arithmetic for cached few-time views

A selected prehit pays one fresh-answer admissibility factor and one capped randomizer-reuse
factor. Below the range where the final security bound is already trivial, all prehits together add
at most `2^14` effective slots to the `2^24` honest signer slots. Raising that inflation through all
fourteen selected entries costs less than one bit.
-/

namespace SphincsSecurity.Concrete

open ENNReal

theorem prehit_selected_entry_weight :
    (digestAttemptLimit : ℝ≥0∞) *
        ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ *
        ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ =
      ((2 ^ 106 : Nat) : ℝ≥0∞)⁻¹ := by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  norm_num [digestAttemptLimit, randomnessBits, ftsTreeHeight]

theorem prehit_effective_slots_le {q : Nat} (hq : q ≤ 2 ^ 120) :
    (signatureLimit : ℝ≥0∞) +
        q * ((2 ^ 106 : Nat) : ℝ≥0∞)⁻¹ ≤
      (signatureLimit : ℝ≥0∞) * (1025 / 1024) := by
  have hq' : (q : ℝ≥0∞) ≤ ((2 ^ 120 : Nat) : ℝ≥0∞) := by
    exact_mod_cast hq
  calc
    (signatureLimit : ℝ≥0∞) +
          q * ((2 ^ 106 : Nat) : ℝ≥0∞)⁻¹ ≤
        (signatureLimit : ℝ≥0∞) +
          ((2 ^ 120 : Nat) : ℝ≥0∞) *
            ((2 ^ 106 : Nat) : ℝ≥0∞)⁻¹ := by
      gcongr
    _ = (signatureLimit : ℝ≥0∞) + ((2 ^ 14 : Nat) : ℝ≥0∞) := by
      congr 1
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
      norm_num
    _ = (signatureLimit : ℝ≥0∞) * (1025 / 1024) := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_natCast]
      norm_num [signatureLimit]

theorem prehit_effective_slots_inflation_pow :
    ((1025 / 1024 : ℝ≥0∞) ^ 14) ≤ 2 := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_pow, ENNReal.toReal_div]
  norm_num

theorem prehit_effective_slots_pow_le {q : Nat} (hq : q ≤ 2 ^ 120) :
    ((signatureLimit : ℝ≥0∞) +
        q * ((2 ^ 106 : Nat) : ℝ≥0∞)⁻¹) ^ 14 ≤
      2 * (signatureLimit : ℝ≥0∞) ^ 14 := by
  calc
    ((signatureLimit : ℝ≥0∞) +
          q * ((2 ^ 106 : Nat) : ℝ≥0∞)⁻¹) ^ 14 ≤
        ((signatureLimit : ℝ≥0∞) * (1025 / 1024)) ^ 14 := by
      gcongr
      exact prehit_effective_slots_le hq
    _ = (signatureLimit : ℝ≥0∞) ^ 14 * (1025 / 1024) ^ 14 := by
      rw [mul_pow]
    _ ≤ (signatureLimit : ℝ≥0∞) ^ 14 * 2 := by
      gcongr
      exact prehit_effective_slots_inflation_pow
    _ = 2 * (signatureLimit : ℝ≥0∞) ^ 14 := by rw [mul_comm]

end SphincsSecurity.Concrete
