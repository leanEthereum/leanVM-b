import SphincsSecurity.Proof.FewTimeSourceCount

/-!
# Arithmetic for cached few-time views

A selected prehit wins a race against the next fresh admissible answer. A working cache of at most
`2^121` entries leaves at least `2^-11` fresh stopping probability per retry, so one favorable
cached input costs at most `2^-117`. Its fresh source also had to be admissible, restoring a
`2^-127` effective weight. Below the range where the final security bound is already trivial, the
resulting fourteen-entry inflation costs less than one bit.
-/

namespace SphincsSecurity.Concrete

open ENNReal

theorem prehit_race_source_weight :
    ((2 ^ 117 : Nat) : ℝ≥0∞)⁻¹ *
        ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ =
      ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ := by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  norm_num [ftsTreeHeight]

theorem prehit_effective_slots_le {q : Nat} (hq : q ≤ 2 ^ 120) :
    (signatureLimit : ℝ≥0∞) *
        (1 + q * ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹) ≤
      (signatureLimit : ℝ≥0∞) * (129 / 128) := by
  have hq' : (q : ℝ≥0∞) ≤ ((2 ^ 120 : Nat) : ℝ≥0∞) := by
    exact_mod_cast hq
  gcongr
  calc
    1 + (q : ℝ≥0∞) * ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ ≤
        1 + ((2 ^ 120 : Nat) : ℝ≥0∞) *
          ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ := by gcongr
    _ = 129 / 128 := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
      simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div,
        ENNReal.toReal_natCast, ENNReal.toReal_one]
      norm_num

theorem prehit_effective_slots_inflation_pow :
    ((129 / 128 : ℝ≥0∞) ^ 14) ≤ 2 := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_pow, ENNReal.toReal_div]
  norm_num

theorem prehit_effective_slots_pow_le {q : Nat} (hq : q ≤ 2 ^ 120) :
    ((signatureLimit : ℝ≥0∞) *
        (1 + q * ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹)) ^ 14 ≤
      2 * (signatureLimit : ℝ≥0∞) ^ 14 := by
  calc
    ((signatureLimit : ℝ≥0∞) *
          (1 + q * ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹)) ^ 14 ≤
        ((signatureLimit : ℝ≥0∞) * (129 / 128)) ^ 14 := by
      exact ENNReal.pow_le_pow_left (prehit_effective_slots_le hq)
    _ = (signatureLimit : ℝ≥0∞) ^ 14 * (129 / 128) ^ 14 := by
      rw [mul_pow]
    _ ≤ (signatureLimit : ℝ≥0∞) ^ 14 * 2 := by
      gcongr
      exact prehit_effective_slots_inflation_pow
    _ = 2 * (signatureLimit : ℝ≥0∞) ^ 14 := by rw [mul_comm]

end SphincsSecurity.Concrete
