import SphincsSecurity.Proof.FewTimeBinomialOccupancy
import Mathlib.RingTheory.Polynomial.Pochhammer

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal Polynomial
set_option backward.isDefEq.respectTransparency false

def coverageFactorialCoefficient (degree : Nat) : Nat :=
  [0, 1, 8191, 788970, 10391745, 40075035, 63436373, 49329280,
    20912320, 5135130, 752752, 66066, 3367, 91, 1].getD degree 0

theorem coverage_power_polynomial :
    (X ^ 14 : Polynomial ℤ) = ∑ degree ∈ Finset.range 15,
      C (coverageFactorialCoefficient degree : ℤ) * descPochhammer ℤ degree := by
  norm_num [Finset.sum_range_succ, coverageFactorialCoefficient, List.getD, descPochhammer_succ_right, descPochhammer_zero]
  ring

theorem coverage_power_eq_binomial (count : Nat) :
    count ^ 14 = ∑ degree ∈ Finset.range 15,
      coverageFactorialCoefficient degree * degree.factorial * count.choose degree := by
  have h := congrArg (fun polynomial : Polynomial ℤ => polynomial.eval (count : ℤ)) coverage_power_polynomial
  simp only [eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul] at h
  simp_rw [mul_assoc]
  exact_mod_cast h

theorem coverageOccupancyMoment_eq_binomial {n : Nat} (views : Fin n → Option FewTimeView) :
    coverageOccupancyMoment views = ∑ degree ∈ Finset.range 15,
      coverageFactorialCoefficient degree * degree.factorial * binomialOccupancyMoment views degree := by
  simp only [coverageOccupancyMoment, ftsTrees, Nat.reduceSub]
  simp_rw [coverage_power_eq_binomial]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro degree _
  rw [binomialOccupancyMoment, Finset.mul_sum]

theorem coverageOccupancyMoment_eq_positive_binomial {n : Nat} (views : Fin n → Option FewTimeView) :
    (coverageOccupancyMoment views : ENNReal) = ∑ degree ∈ Finset.range 14,
      (coverageFactorialCoefficient (degree + 1) * (degree + 1).factorial : Nat) *
        (binomialOccupancyMoment views (degree + 1) : ENNReal) := by
  rw [coverageOccupancyMoment_eq_binomial, Nat.cast_sum, Finset.sum_range_succ']
  simp only [Nat.cast_mul]
  have hzero : coverageFactorialCoefficient 0 = 0 := rfl
  simp only [hzero, Nat.cast_zero, zero_mul, add_zero]

end SphincsSecurity.Concrete
