import SphincsSecurity.Proof.MixedIncrementBounds

namespace SphincsSecurity.Concrete

open ENNReal
set_option backward.isDefEq.respectTransparency false

noncomputable def zeroCachePowerVector (weight : Nat → ENNReal) : MixedMomentVector :=
  fun power order => if power = 0 then weight order else 0

theorem mixedPowerLower_monomial (scalar base : ENNReal) (weight : Nat → ENNReal) (power order : Nat) :
    mixedPowerLower (fun p o => scalar * base ^ p * weight o) power order = scalar * cachePowerArrival power base * weight order := by
  simp only [mixedPowerLower, cachePowerArrival, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro lower _
  ring

theorem mixedQueryIncrement_initial_le (arrival : ENNReal) (weight : Nat → ENNReal) (steps power order : Nat) :
    (mixedQueryIncrement arrival)^[steps] (zeroCachePowerVector weight) power order ≤
      arrival ^ steps * (steps : ENNReal) ^ power * weight order := by
  induction steps generalizing power order with
  | zero =>
      cases power with
      | zero => simp only [Function.iterate_zero, id_eq, zeroCachePowerVector, if_true, pow_zero, one_mul, le_refl]
      | succ power => simp only [Function.iterate_zero, id_eq, zeroCachePowerVector, Nat.succ_ne_zero, if_false,
          Nat.cast_zero, zero_pow (Nat.succ_ne_zero power), mul_zero, zero_mul, le_refl]
  | succ steps ih =>
      rw [Function.iterate_succ_apply']
      calc
        _ ≤ mixedQueryIncrement arrival (fun p o => arrival ^ steps * (steps : ENNReal) ^ p * weight o) power order := by
          apply mul_le_mul' le_rfl
          exact mixedPowerLower_mono (fun p o => ih p o) power order
        _ = arrival ^ (steps + 1) * cachePowerArrival power (steps : ENNReal) * weight order := by
          simp only [mixedQueryIncrement, mixedPowerLower_monomial, pow_succ]
          ring
        _ ≤ _ := by
          apply mul_le_mul' (mul_le_mul' le_rfl _) le_rfl
          rw [Nat.cast_add, Nat.cast_one, add_one_pow_eq_cachePowerArrival]
          exact le_add_self

theorem mixedQueryIncrement_initial_diagonal (arrival : ENNReal) (weight : Nat → ENNReal) (power order : Nat) :
    (mixedQueryIncrement arrival)^[power] (zeroCachePowerVector weight) power order =
      arrival ^ power * (power.factorial : ENNReal) * weight order := by
  induction power with
  | zero => simp only [Function.iterate_zero, id_eq, zeroCachePowerVector, if_true, pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul]
  | succ power ih =>
      rw [Function.iterate_succ_apply']
      change arrival * (∑ lower ∈ Finset.range (power + 1), ((power + 1).choose lower : ENNReal) *
        (mixedQueryIncrement arrival)^[power] (zeroCachePowerVector weight) lower order) = _
      rw [Finset.sum_eq_single power]
      · rw [Nat.choose_succ_self_right, ih, Nat.factorial_succ, Nat.cast_mul, pow_succ]
        ring
      · intro lower hlower hne
        rw [mixedQueryIncrement_iterate_zero arrival _ power lower order (by have := Finset.mem_range.mp hlower; omega), mul_zero]
      · intro hnot
        exact False.elim (hnot (Finset.mem_range.mpr (by omega)))

theorem mixedQueryEnvelope_initial_remainder_le (arrival : ENNReal) (queries : Nat) (weight : Nat → ENNReal) (power order : Nat)
    (hmean : 1 ≤ (queries : ENNReal) * arrival) (hpower : power ≤ 14) :
    (mixedQueryEnvelope arrival)^[queries] (zeroCachePowerVector weight) power order ≤
      (((queries : ENNReal) * arrival) ^ power + (14 : ENNReal) ^ 15 * ((queries : ENNReal) * arrival) ^ (power - 1)) * weight order := by
  rw [mixedQueryEnvelope_iterate_eq_binomial, Finset.sum_range_succ, mixedQueryIncrement_initial_diagonal]
  have hleading : (queries.choose power : ENNReal) * (arrival ^ power * (power.factorial : ENNReal) * weight order) ≤
      ((queries : ENNReal) * arrival) ^ power * weight order := by
    have hchoose : (queries.choose power : ENNReal) * (power.factorial : ENNReal) ≤ (queries : ENNReal) ^ power := by
      have h := Nat.descFactorial_le_pow queries power
      rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.mul_comm] at h
      exact_mod_cast h
    calc
      _ = ((queries.choose power : ENNReal) * (power.factorial : ENNReal)) * arrival ^ power * weight order := by ring
      _ ≤ (queries : ENNReal) ^ power * arrival ^ power * weight order := mul_le_mul' (mul_le_mul' hchoose le_rfl) le_rfl
      _ = _ := by rw [mul_pow]
  have hterm (degree : Nat) (hdegree : degree ∈ Finset.range power) :
      (queries.choose degree : ENNReal) * (mixedQueryIncrement arrival)^[degree] (zeroCachePowerVector weight) power order ≤
        ((queries : ENNReal) * arrival) ^ (power - 1) * (14 : ENNReal) ^ 14 * weight order := by
    have hlt := Finset.mem_range.mp hdegree
    have hchoose : (queries.choose degree : ENNReal) ≤ (queries : ENNReal) ^ degree := by
      exact_mod_cast Nat.choose_le_pow queries degree
    calc
      _ ≤ (queries : ENNReal) ^ degree * (arrival ^ degree * (degree : ENNReal) ^ power * weight order) :=
        mul_le_mul' hchoose (mixedQueryIncrement_initial_le arrival weight degree power order)
      _ = ((queries : ENNReal) * arrival) ^ degree * (degree : ENNReal) ^ power * weight order := by rw [mul_pow]; ring
      _ ≤ ((queries : ENNReal) * arrival) ^ (power - 1) * (14 : ENNReal) ^ 14 * weight order := by
        apply mul_le_mul' (mul_le_mul' (pow_le_pow_right₀ hmean (by omega)) _) le_rfl
        exact (pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr (show degree ≤ 14 by omega)) power).trans
          (pow_le_pow_right₀ (by norm_num) hpower)
  have hlower : (∑ degree ∈ Finset.range power, (queries.choose degree : ENNReal) *
      (mixedQueryIncrement arrival)^[degree] (zeroCachePowerVector weight) power order) ≤
      (14 : ENNReal) ^ 15 * ((queries : ENNReal) * arrival) ^ (power - 1) * weight order := by
    apply (Finset.sum_le_sum hterm).trans
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc
      _ ≤ (14 : ENNReal) * (((queries : ENNReal) * arrival) ^ (power - 1) * (14 : ENNReal) ^ 14 * weight order) :=
        mul_le_mul_left (Nat.cast_le.mpr hpower) _
      _ = _ := by ring
  exact (add_le_add hlower hleading).trans_eq (by ring)

end SphincsSecurity.Concrete
