import SphincsSecurity.Proof.OccupancyBinomialExpansion

namespace SphincsSecurity.Concrete

def powerDifferenceStep (values : Nat → Nat) (degree : Nat) : Nat :=
  ∑ lower ∈ Finset.range degree, degree.choose lower * values lower

def powerDifferenceValue (order count degree : Nat) : Nat :=
  powerDifferenceStep^[order] (fun degree => count ^ degree) degree

theorem powerDifferenceStep_add (left right : Nat → Nat) :
    powerDifferenceStep (fun degree => left degree + right degree) = fun degree => powerDifferenceStep left degree + powerDifferenceStep right degree := by
  funext degree
  simp only [powerDifferenceStep, Nat.mul_add, Finset.sum_add_distrib]

theorem powerDifferenceStep_iterate_add (order : Nat) (left right : Nat → Nat) :
    powerDifferenceStep^[order] (fun degree => left degree + right degree) =
      fun degree => powerDifferenceStep^[order] left degree + powerDifferenceStep^[order] right degree := by
  induction order with
  | zero => rfl
  | succ order ih => simp only [Function.iterate_succ_apply', ih, powerDifferenceStep_add]

theorem power_add_one_eq_difference (count degree : Nat) :
    (count + 1) ^ degree = count ^ degree + powerDifferenceStep (fun lower => count ^ lower) degree := by
  rw [add_pow, Finset.sum_range_succ]
  simp only [one_pow, Nat.mul_one, Nat.choose_self, Nat.cast_id]
  rw [Nat.add_comm]
  apply congrArg (fun value => count ^ degree + value)
  apply Finset.sum_congr rfl
  intro lower _
  exact Nat.mul_comm _ _

theorem powerDifferenceValue_succ_count (order count degree : Nat) :
    powerDifferenceValue order (count + 1) degree = powerDifferenceValue order count degree + powerDifferenceValue (order + 1) count degree := by
  have hpowers : (fun degree => (count + 1) ^ degree) =
      fun degree => count ^ degree + powerDifferenceStep (fun lower => count ^ lower) degree := funext (power_add_one_eq_difference count)
  simp only [powerDifferenceValue, hpowers, powerDifferenceStep_iterate_add, Function.iterate_succ_apply]

def binomialDifferenceValue (order count : Nat) : Nat :=
  ∑ degree ∈ Finset.range (15 - order), coverageFactorialCoefficient (degree + order) * (degree + order).factorial * count.choose degree

theorem binomialDifferenceValue_of_ge (order count : Nat) (horder : 15 ≤ order) : binomialDifferenceValue order count = 0 := by
  simp only [binomialDifferenceValue, Nat.sub_eq_zero_of_le horder, Finset.range_zero, Finset.sum_empty]

theorem binomialDifferenceValue_succ_count (order count : Nat) :
    binomialDifferenceValue order (count + 1) = binomialDifferenceValue order count + binomialDifferenceValue (order + 1) count := by
  by_cases horder : 15 ≤ order
  · simp only [binomialDifferenceValue_of_ge order _ horder, binomialDifferenceValue_of_ge (order + 1) _ (by omega), Nat.zero_add]
  · have hsize : 15 - order = (15 - (order + 1)) + 1 := by omega
    unfold binomialDifferenceValue
    rw [hsize, Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, Nat.mul_one, Nat.zero_add, Nat.choose_succ_succ, Nat.mul_add, Finset.sum_add_distrib,
      Nat.add_assoc, Nat.add_comm 1 order, Nat.succ_eq_add_one]
    omega

theorem powerDifferenceValue_fourteen (order count : Nat) :
    powerDifferenceValue order count 14 = binomialDifferenceValue order count := by
  induction order generalizing count with
  | zero => simpa only [powerDifferenceValue, Function.iterate_zero, id_eq, binomialDifferenceValue, Nat.sub_zero, Nat.add_zero] using coverage_power_eq_binomial count
  | succ order ih =>
      have h := powerDifferenceValue_succ_count order count 14
      rw [ih (count + 1), ih count, binomialDifferenceValue_succ_count] at h
      exact (Nat.add_left_cancel h).symm

theorem powerDifferenceValue_zero_fourteen (order : Nat) :
    powerDifferenceValue order 0 14 = if order < 15 then coverageFactorialCoefficient order * order.factorial else 0 := by
  rw [powerDifferenceValue_fourteen]
  by_cases horder : order < 15
  · rw [if_pos horder]
    unfold binomialDifferenceValue
    rw [Finset.sum_eq_single 0]
    · simp only [Nat.zero_add, Nat.choose_zero_right, Nat.mul_one]
    · intro degree _ hne
      rw [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hne), Nat.mul_zero]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (by omega))).elim
  · rw [if_neg horder, binomialDifferenceValue_of_ge order 0 (by omega)]

end SphincsSecurity.Concrete
