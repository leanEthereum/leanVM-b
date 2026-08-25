import SphincsSecurity.Proof.MandatoryQueries

/-!
# Arithmetic budget for the terminal bounds

The structural charge and the complete proper few-time term consume less than 24 of the 32 units
available at denominator `2^125`. The mandatory root computation supplies the lower bound on `q`
needed to absorb the few-time term's single final-verifier candidate.
-/

namespace SphincsSecurity.Concrete

open ENNReal

theorem structural_add_properFewTime_le {q : Nat} (hq : numChains ≤ q) :
    ((44 * q : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
        ((2 * q + 1 : Nat) : ℝ≥0∞) *
          (9 * ((2 ^ 125 : Nat) : ℝ≥0∞)⁻¹) ≤
      ((24 * q : Nat) : ℝ≥0∞) * ((2 ^ 125 : Nat) : ℝ≥0∞)⁻¹ := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  have hpow : (2 : ℝ) ^ digestBits = 8 * (2 : ℝ) ^ 125 := by
    norm_num [digestBits]
  push_cast
  simp only [ENNReal.toReal_ofNat]
  rw [hpow, mul_inv]
  norm_num only [pow_succ, pow_zero] at ⊢
  calc
    44 * (q : ℝ) * (1 / 340282366920938463463374607431768211456) +
          (2 * (q : ℝ) + 1) * (9 / 42535295865117307932921825928971026432) =
        ((47 / 2 : ℝ) * q + 9) /
          42535295865117307932921825928971026432 := by
      norm_num
      ring
    _ ≤ (24 * (q : ℝ)) /
        42535295865117307932921825928971026432 := by
      gcongr
      have h18Nat : 18 ≤ q := le_trans (by norm_num [numChains]) hq
      have h18 : (18 : ℝ) ≤ (q : ℝ) := by exact_mod_cast h18Nat
      linarith
    _ = 24 * (q : ℝ) *
        (1 / 42535295865117307932921825928971026432) := by ring

theorem terminal_budget_remainder :
    ((24 : Nat) : ℝ≥0∞) * ((2 ^ 125 : Nat) : ℝ≥0∞)⁻¹ +
        ((64 : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ =
      ((2 ^ 120 : Nat) : ℝ≥0∞)⁻¹ := by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  norm_num [digestBits]

end SphincsSecurity.Concrete
