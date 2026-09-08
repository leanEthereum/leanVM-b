import SphincsSecurity.Proof.SigningFactorialEnvelope
import SphincsSecurity.Proof.OrderBinomialExpansion
import Mathlib.Data.List.GetD

namespace SphincsSecurity.Concrete

open ENNReal
set_option backward.isDefEq.respectTransparency false

def signingOrderCoefficientRow (steps : Nat) : Nat :=
  ∑ degree ∈ Finset.range 15, steps.choose degree * 32784 ^ degree * coverageFactorialCoefficient degree * degree.factorial

theorem coverageFactorialCoefficient_of_ge (degree : Nat) (hdegree : 15 ≤ degree) : coverageFactorialCoefficient degree = 0 := by
  apply List.getD_eq_default
  exact hdegree

theorem initialMixedDerivativeVector_zero_eq (order : Nat) : initialMixedDerivativeVector 0 order =
    (coverageFactorialCoefficient order * order.factorial : Nat) * (Fintype.card Index : ENNReal) := by
  by_cases horder : order < 15
  · simp only [initialMixedDerivativeVector, horder, and_self, if_true]
  · simp only [initialMixedDerivativeVector, horder, and_false, if_false, coverageFactorialCoefficient_of_ge order (by omega),
      Nat.cast_zero, zero_mul]

theorem signingOrderMajorant_initial_eq_row (steps : Nat) :
    (signingOrderMajorant^[steps] (fun order => (1025 / 1024 : ENNReal) * initialMixedDerivativeVector 0 order)) 0 =
      ((1025 * 2 ^ 26 * signingOrderCoefficientRow steps : Nat) : ENNReal) / (1024 * (65536 : ENNReal) ^ steps) := by
  rw [signingOrderMajorant_iterate_eq_binomial]
  simp only [Nat.zero_add]
  have htrunc := mixedBinomial_sum_truncate
    (fun degree => (32784 : ENNReal) ^ degree * ((1025 / 1024 : ENNReal) * initialMixedDerivativeVector 0 degree)) steps 14
    (fun degree hdegree => by rw [initialMixedDerivativeVector_order_zero 0 degree (by omega), mul_zero, mul_zero])
  simp only [mul_assoc]
  rw [htrunc]
  simp only [initialMixedDerivativeVector_zero_eq, signingOrderCoefficientRow, Nat.cast_mul, Nat.cast_sum, Nat.cast_pow,
    Nat.cast_ofNat, Finset.mul_sum, div_eq_mul_inv, Finset.sum_mul]
  rw [ENNReal.mul_inv (Or.inl (show (1024 : ENNReal) ≠ 0 by norm_num)) (Or.inl (show (1024 : ENNReal) ≠ ∞ by finiteness))]
  apply Finset.sum_congr rfl
  intro degree _
  norm_num only [Index, totalHeight, Fintype.card_fin]
  ring

theorem signingFactorialEnvelope_eq_rows : signingFactorialEnvelope =
    ∑ steps ∈ Finset.range 29, ((1025 * 2 ^ 26 * signingOrderCoefficientRow steps : Nat) : ENNReal) /
      ((1024 * 65536 ^ steps * steps.factorial : Nat) : ENNReal) := by
  unfold signingFactorialEnvelope
  apply Finset.sum_congr rfl
  intro steps _
  rw [signingOrderMajorant_initial_eq_row]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inr (show (steps.factorial : ENNReal) ≠ ∞ from ENNReal.natCast_ne_top _))
    (Or.inl (show (1024 * (65536 : ENNReal) ^ steps) ≠ ∞ by finiteness))]
  ring

def signingOrderCommonNumerator : Nat :=
  1025 * 2 ^ 26 * ∑ steps ∈ Finset.range 29,
    (steps + 1).ascFactorial (28 - steps) * 65536 ^ (28 - steps) * signingOrderCoefficientRow steps

def signingOrderCommonDenominator : Nat := 1024 * Nat.factorial 28 * 65536 ^ 28

theorem signingOrder_denominator_factor (steps : Nat) (hsteps : steps ≤ 28) :
    (1024 * 65536 ^ steps * steps.factorial) * ((steps + 1).ascFactorial (28 - steps) * 65536 ^ (28 - steps)) =
      signingOrderCommonDenominator := by
  have hfactor : steps.factorial * (steps + 1).ascFactorial (28 - steps) = Nat.factorial 28 := by
    rw [Nat.factorial_mul_ascFactorial, Nat.add_sub_of_le hsteps]
  have hpow : (65536 : Nat) ^ steps * 65536 ^ (28 - steps) = 65536 ^ 28 := by
    rw [← pow_add, Nat.add_sub_of_le hsteps]
  calc
    _ = 1024 * (steps.factorial * (steps + 1).ascFactorial (28 - steps)) * (65536 ^ steps * 65536 ^ (28 - steps)) := by ring
    _ = _ := by rw [hfactor, hpow]; rfl

theorem signingFactorialEnvelope_eq_common_fraction : signingFactorialEnvelope =
    (signingOrderCommonNumerator : ENNReal) / (signingOrderCommonDenominator : ENNReal) := by
  rw [signingFactorialEnvelope_eq_rows]
  have hrow (steps : Nat) (hsteps : steps ∈ Finset.range 29) :
      ((1025 * 2 ^ 26 * signingOrderCoefficientRow steps : Nat) : ENNReal) / ((1024 * 65536 ^ steps * steps.factorial : Nat) : ENNReal) =
        ((1025 * 2 ^ 26 * ((steps + 1).ascFactorial (28 - steps) * 65536 ^ (28 - steps) * signingOrderCoefficientRow steps) : Nat) : ENNReal) /
          (signingOrderCommonDenominator : ENNReal) := by
    let factor := (steps + 1).ascFactorial (28 - steps) * 65536 ^ (28 - steps)
    have hfactor : factor ≠ 0 := by dsimp [factor]; positivity
    have hden := signingOrder_denominator_factor steps (by have := Finset.mem_range.mp hsteps; omega)
    have hnum : (1025 * 2 ^ 26 * ((steps + 1).ascFactorial (28 - steps) * 65536 ^ (28 - steps) * signingOrderCoefficientRow steps) : Nat) =
        (1025 * 2 ^ 26 * signingOrderCoefficientRow steps) * factor := by dsimp [factor]; ring
    rw [hnum, ← hden]
    have hc := (ENNReal.mul_div_mul_right
      (((1025 * 2 ^ 26 * signingOrderCoefficientRow steps : Nat) : ENNReal))
      (((1024 * 65536 ^ steps * steps.factorial : Nat) : ENNReal))
      (by exact_mod_cast hfactor) (ENNReal.natCast_ne_top factor)).symm
    simpa only [factor, Nat.cast_mul] using hc
  rw [Finset.sum_congr rfl hrow]
  simp only [signingOrderCommonNumerator, Nat.cast_mul, Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat, Finset.mul_sum,
    div_eq_mul_inv, Finset.sum_mul]

theorem signingOrder_arithmetic_certificate : signingOrderCommonNumerator ≤ 29 * 2 ^ 43 * signingOrderCommonDenominator := by
  decide

theorem signingFactorialEnvelope_le : signingFactorialEnvelope ≤ (29 : ENNReal) * 2 ^ 43 := by
  rw [signingFactorialEnvelope_eq_common_fraction]
  have hden : signingOrderCommonDenominator ≠ 0 := by unfold signingOrderCommonDenominator; positivity
  apply (ENNReal.div_le_iff (by exact_mod_cast hden) (ENNReal.natCast_ne_top _)).mpr
  exact_mod_cast signingOrder_arithmetic_certificate

theorem signingOrder_arithmetic_certificate_sharp : signingOrderCommonNumerator ≤ 27 * 2 ^ 43 * signingOrderCommonDenominator := by
  decide

theorem signingFactorialEnvelope_le_sharp : signingFactorialEnvelope ≤ (27 : ENNReal) * 2 ^ 43 := by
  rw [signingFactorialEnvelope_eq_common_fraction]
  have hden : signingOrderCommonDenominator ≠ 0 := by unfold signingOrderCommonDenominator; positivity
  apply (ENNReal.div_le_iff (by exact_mod_cast hden) (ENNReal.natCast_ne_top _)).mpr
  exact_mod_cast signingOrder_arithmetic_certificate_sharp

end SphincsSecurity.Concrete
