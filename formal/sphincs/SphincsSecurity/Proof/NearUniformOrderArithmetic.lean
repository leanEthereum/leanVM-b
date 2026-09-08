import SphincsSecurity.Proof.NearUniformOrderBinomial
import SphincsSecurity.Proof.NearUniformFactorialEnvelope
import SphincsSecurity.Proof.SigningOrderArithmetic

namespace SphincsSecurity.Concrete

open ENNReal

def nearUniformSigningOrderCoefficientRow (steps : Nat) : Nat :=
  ∑ degree ∈ Finset.range 15, steps.choose degree * 24585 ^ degree * coverageFactorialCoefficient degree * degree.factorial

theorem nearUniformSigningOrderMajorant_initial_eq_row (steps : Nat) :
    (nearUniformSigningOrderMajorant^[steps] (fun order => (1025 / 1024 : ENNReal) * initialMixedDerivativeVector 0 order)) 0 =
      ((1025 * 2 ^ 26 * nearUniformSigningOrderCoefficientRow steps : Nat) : ENNReal) / (1024 * (65536 : ENNReal) ^ steps) := by
  rw [nearUniformSigningOrderMajorant_iterate_eq_binomial]
  simp only [Nat.zero_add]
  have htrunc := mixedBinomial_sum_truncate
    (fun degree => (24585 : ENNReal) ^ degree * ((1025 / 1024 : ENNReal) * initialMixedDerivativeVector 0 degree)) steps 14
    (fun degree hdegree => by rw [initialMixedDerivativeVector_order_zero 0 degree (by omega), mul_zero, mul_zero])
  simp only [mul_assoc]
  rw [htrunc]
  simp only [initialMixedDerivativeVector_zero_eq, nearUniformSigningOrderCoefficientRow, Nat.cast_mul, Nat.cast_sum, Nat.cast_pow,
    Nat.cast_ofNat, Finset.mul_sum, div_eq_mul_inv, Finset.sum_mul]
  rw [ENNReal.mul_inv (Or.inl (show (1024 : ENNReal) ≠ 0 by norm_num)) (Or.inl (show (1024 : ENNReal) ≠ ∞ by finiteness))]
  apply Finset.sum_congr rfl
  intro degree _
  norm_num only [Index, totalHeight, Fintype.card_fin]
  ring

theorem nearUniformSigningFactorialEnvelope_eq_rows : nearUniformSigningFactorialEnvelope =
    ∑ steps ∈ Finset.range 29, ((1025 * 2 ^ 26 * nearUniformSigningOrderCoefficientRow steps : Nat) : ENNReal) /
      ((1024 * 65536 ^ steps * steps.factorial : Nat) : ENNReal) := by
  unfold nearUniformSigningFactorialEnvelope
  apply Finset.sum_congr rfl
  intro steps _
  rw [nearUniformSigningOrderMajorant_initial_eq_row]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inr (show (steps.factorial : ENNReal) ≠ ∞ from ENNReal.natCast_ne_top _))
    (Or.inl (show (1024 * (65536 : ENNReal) ^ steps) ≠ ∞ by finiteness))]
  ring

def nearUniformSigningOrderCommonNumerator : Nat :=
  1025 * 2 ^ 26 * ∑ steps ∈ Finset.range 29,
    (steps + 1).ascFactorial (28 - steps) * 65536 ^ (28 - steps) * nearUniformSigningOrderCoefficientRow steps

theorem nearUniformSigningFactorialEnvelope_eq_common_fraction : nearUniformSigningFactorialEnvelope =
    (nearUniformSigningOrderCommonNumerator : ENNReal) / (signingOrderCommonDenominator : ENNReal) := by
  rw [nearUniformSigningFactorialEnvelope_eq_rows]
  have hrow (steps : Nat) (hsteps : steps ∈ Finset.range 29) :
      ((1025 * 2 ^ 26 * nearUniformSigningOrderCoefficientRow steps : Nat) : ENNReal) / ((1024 * 65536 ^ steps * steps.factorial : Nat) : ENNReal) =
        ((1025 * 2 ^ 26 * ((steps + 1).ascFactorial (28 - steps) * 65536 ^ (28 - steps) * nearUniformSigningOrderCoefficientRow steps) : Nat) : ENNReal) /
          (signingOrderCommonDenominator : ENNReal) := by
    let factor := (steps + 1).ascFactorial (28 - steps) * 65536 ^ (28 - steps)
    have hfactor : factor ≠ 0 := by dsimp [factor]; positivity
    have hden := signingOrder_denominator_factor steps (by have := Finset.mem_range.mp hsteps; omega)
    have hnum : (1025 * 2 ^ 26 * ((steps + 1).ascFactorial (28 - steps) * 65536 ^ (28 - steps) * nearUniformSigningOrderCoefficientRow steps) : Nat) =
        (1025 * 2 ^ 26 * nearUniformSigningOrderCoefficientRow steps) * factor := by dsimp [factor]; ring
    rw [hnum, ← hden]
    have hc := (ENNReal.mul_div_mul_right
      (((1025 * 2 ^ 26 * nearUniformSigningOrderCoefficientRow steps : Nat) : ENNReal))
      (((1024 * 65536 ^ steps * steps.factorial : Nat) : ENNReal))
      (by exact_mod_cast hfactor) (ENNReal.natCast_ne_top factor)).symm
    simpa only [factor, Nat.cast_mul] using hc
  rw [Finset.sum_congr rfl hrow]
  simp only [nearUniformSigningOrderCommonNumerator, Nat.cast_mul, Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat, Finset.mul_sum,
    div_eq_mul_inv, Finset.sum_mul]

theorem nearUniformSigningOrder_arithmetic_certificate : nearUniformSigningOrderCommonNumerator ≤ 3 * 2 ^ 44 * signingOrderCommonDenominator := by
  decide

theorem nearUniformSigningFactorialEnvelope_le : nearUniformSigningFactorialEnvelope ≤ (3 : ENNReal) * 2 ^ 44 := by
  rw [nearUniformSigningFactorialEnvelope_eq_common_fraction]
  have hden : signingOrderCommonDenominator ≠ 0 := by unfold signingOrderCommonDenominator; positivity
  apply (ENNReal.div_le_iff (by exact_mod_cast hden) (ENNReal.natCast_ne_top _)).mpr
  exact_mod_cast nearUniformSigningOrder_arithmetic_certificate

end SphincsSecurity.Concrete
