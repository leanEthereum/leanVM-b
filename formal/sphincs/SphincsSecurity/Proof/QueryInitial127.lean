import SphincsSecurity.Proof.QueryPowerInitialBound

namespace SphincsSecurity.Concrete

open ENNReal
set_option backward.isDefEq.respectTransparency false

theorem queryMean127 :
    ((2 ^ 127 : Nat) : ENNReal) *
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ / (Fintype.card Index : ENNReal)) = (2 : ENNReal) ^ 91 := by
  have hfinite : (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ / (Fintype.card Index : ENNReal)) ≠ ∞ := by
    apply ENNReal.div_ne_top (by finiteness)
    norm_num [Index, totalHeight]
  apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.mul_ne_top (by finiteness) hfinite) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv, ftsTreeHeight, Index, totalHeight]

theorem initialMixedDerivativeVector_eq_zeroCachePowerVector :
    initialMixedDerivativeVector = zeroCachePowerVector (initialMixedDerivativeVector 0) := by
  funext power order
  cases power with
  | zero => simp only [zeroCachePowerVector, if_true]
  | succ power => simp only [initialMixedDerivativeVector, zeroCachePowerVector, Nat.succ_ne_zero, false_and, if_false]

theorem queryInitial127_power_bound (weight : Nat → ENNReal) (power order : Nat) (hpower : power ≤ 14) :
    (mixedQueryEnvelope (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ / (Fintype.card Index : ENNReal)))^[2 ^ 127]
      (zeroCachePowerVector weight) power order ≤
      ((1025 : ENNReal) / 1024) * ((2 : ENNReal) ^ 91) ^ power * weight order := by
  by_cases hzero : power = 0
  · subst power
    rw [mixedQueryEnvelope_iterate_eq_binomial]
    simp only [Nat.zero_add, Finset.sum_range_one, Nat.choose_zero_right, Nat.cast_one, Function.iterate_zero, id_eq,
      zeroCachePowerVector, if_true, one_mul, pow_zero, mul_one]
    apply le_mul_of_one_le_left'
    exact (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by finiteness))).mpr (by norm_num)
  · have hmean : 1 ≤ ((2 ^ 127 : Nat) : ENNReal) *
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ / (Fintype.card Index : ENNReal)) := by rw [queryMean127]; norm_num
    have hbound := mixedQueryEnvelope_initial_remainder_le
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ / (Fintype.card Index : ENNReal)) (2 ^ 127) weight power order hmean hpower
    rw [queryMean127] at hbound
    apply hbound.trans
    have hcoeff : (14 : ENNReal) ^ 15 ≤ ((1 : ENNReal) / 1024) * (2 : ENNReal) ^ 91 := by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
    have htail : (14 : ENNReal) ^ 15 * ((2 : ENNReal) ^ 91) ^ (power - 1) ≤
        ((1 : ENNReal) / 1024) * ((2 : ENNReal) ^ 91) ^ power := by
      apply (mul_le_mul_left hcoeff (((2 : ENNReal) ^ 91) ^ (power - 1))).trans_eq
      rw [mul_assoc, ← pow_succ', show power - 1 + 1 = power by omega]
    have hfactor : (1 : ENNReal) + 1 / 1024 = 1025 / 1024 := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_add, ENNReal.toReal_div]
    apply (mul_le_mul' (add_le_add le_rfl htail) le_rfl).trans_eq
    rw [← hfactor]
    ring

theorem queryInitialEnvelope_le_scaled (q : Nat) (hq : q ≤ 2 ^ 127) (power order : Nat) (hpower : power ≤ 14) :
    (mixedQueryEnvelope (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ / (Fintype.card Index : ENNReal)))^[q]
      initialMixedDerivativeVector power order ≤
      ((1025 : ENNReal) / 1024) * ((2 : ENNReal) ^ 91) ^ power * initialMixedDerivativeVector 0 order := by
  apply (Function.monotone_iterate_of_id_le (le_mixedQueryEnvelope _) hq initialMixedDerivativeVector power order).trans
  rw [initialMixedDerivativeVector_eq_zeroCachePowerVector]
  exact queryInitial127_power_bound _ power order hpower

end SphincsSecurity.Concrete
