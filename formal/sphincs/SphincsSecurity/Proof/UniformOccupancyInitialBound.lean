import SphincsSecurity.Proof.UniformOccupancyPolynomial

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem uniformOccupancyIncrement_empty (remaining : Nat) (key : SecretKey) (cache : QueryCache HashSpec) :
    uniformOccupancyIncrement remaining key cache [] =
      ∑ degree ∈ Finset.range 14, (coverageFactorialCoefficient (degree + 1) * (degree + 1).factorial : Nat) *
        (remaining.choose degree : ENNReal) * (Fintype.card Index : ENNReal)⁻¹ ^ degree := by
  have hempty : (fun degree => observedLogBinomialOccupancy key degree (cache, [])) =
      (fun degree => if degree = 0 then (Fintype.card Index : ENNReal) else 0) := by
    funext degree
    cases degree with
    | zero => simp only [observedLogBinomialOccupancy, binomialOccupancyMoment_zero, if_true]
    | succ degree => simp only [observedLogBinomialOccupancy, binomialOccupancyMoment_empty, Nat.cast_zero, Nat.succ_ne_zero, if_false]
  have hcancel : (Fintype.card Index : ENNReal) * (Fintype.card Index : ENNReal)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (by norm_num [Index, totalHeight]) (by finiteness)
  rw [uniformOccupancyIncrement_eq_polynomial, hempty]
  simp only [occupancyUniformIncrementPolynomial, binomialCompletion_empty, div_eq_mul_inv, mul_assoc, hcancel, mul_one]

theorem uniformOccupancyIncrement_empty_le_power (remaining : Nat) (key : SecretKey) (cache : QueryCache HashSpec) :
    uniformOccupancyIncrement remaining key cache [] ≤
      ∑ degree ∈ Finset.range 14, (coverageFactorialCoefficient (degree + 1) : ENNReal) * (degree + 1) *
        ((remaining : ENNReal) / (Fintype.card Index : ENNReal)) ^ degree := by
  rw [uniformOccupancyIncrement_empty]
  apply Finset.sum_le_sum
  intro degree _
  have hchoose : (degree + 1).factorial * remaining.choose degree ≤ (degree + 1) * remaining ^ degree := by
    rw [Nat.factorial_succ, Nat.mul_assoc, ← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow _ _)
  have hcast : ((degree + 1).factorial : ENNReal) * (remaining.choose degree : ENNReal) ≤
      ((degree : ENNReal) + 1) * (remaining : ENNReal) ^ degree := by exact_mod_cast hchoose
  simp only [Nat.cast_mul]
  calc
    _ = (coverageFactorialCoefficient (degree + 1) : ENNReal) *
        ((degree + 1).factorial * (remaining.choose degree : ENNReal)) * (Fintype.card Index : ENNReal)⁻¹ ^ degree := by ring
    _ ≤ (coverageFactorialCoefficient (degree + 1) : ENNReal) *
        (((degree : ENNReal) + 1) * (remaining : ENNReal) ^ degree) * (Fintype.card Index : ENNReal)⁻¹ ^ degree :=
      mul_le_mul' (mul_le_mul' le_rfl hcast) le_rfl
    _ = _ := by rw [div_eq_mul_inv, mul_pow]; ring

theorem uniformOccupancyIncrement_empty_signatureLimit_le (key : SecretKey) (cache : QueryCache HashSpec) :
    uniformOccupancyIncrement signatureLimit key cache [] ≤ (2 : ENNReal) ^ 21 := by
  apply (uniformOccupancyIncrement_empty_le_power signatureLimit key cache).trans
  have hratio : ((signatureLimit : ENNReal) / (Fintype.card Index : ENNReal)) ≠ ∞ := by
    apply ENNReal.div_ne_top (by finiteness)
    norm_num [Index, totalHeight]
  have hfinite (degree : Nat) : (coverageFactorialCoefficient (degree + 1) : ENNReal) * (degree + 1) *
      ((signatureLimit : ENNReal) / (Fintype.card Index : ENNReal)) ^ degree ≠ ∞ :=
    ENNReal.mul_ne_top (by finiteness) (ENNReal.pow_ne_top hratio)
  apply (ENNReal.toReal_le_toReal (ENNReal.sum_ne_top.mpr (fun degree _ => hfinite degree)) (by finiteness)).mp
  rw [ENNReal.toReal_sum (fun degree _ => hfinite degree)]
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_add,
    signatureLimit, Index, totalHeight, Finset.sum_range_succ, coverageFactorialCoefficient, List.getD]

end SphincsSecurity.Concrete
