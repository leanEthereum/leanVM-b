import SphincsSecurity.Proof.BinomialCompletion

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

def shiftBinomialMoments (moments : Nat → ENNReal) : Nat → ENNReal
  | 0 => 0
  | degree + 1 => moments degree

theorem binomialCompletion_shift_zero (moments : Nat → ENNReal) (remaining : Nat) :
    binomialCompletion (shiftBinomialMoments moments) remaining 0 = 0 :=
  binomialCompletion_degree_zero _ _

theorem binomialCompletion_shift_succ (moments : Nat → ENNReal) (remaining degree : Nat) :
    binomialCompletion (shiftBinomialMoments moments) remaining (degree + 1) = binomialCompletion moments remaining degree := by
  induction remaining generalizing degree with
  | zero => rfl
  | succ remaining ih =>
      cases degree with
      | zero =>
          rw [binomialCompletion_succ, ih, binomialCompletion_shift_zero, ENNReal.zero_div, add_zero,
            binomialCompletion_degree_zero, binomialCompletion_degree_zero]
      | succ degree => rw [binomialCompletion_succ, ih, ih, binomialCompletion_succ]

theorem binomialCompletion_mul_right (moments : Nat → ENNReal) (factor : ENNReal) (remaining degree : Nat) :
    binomialCompletion (fun degree => moments degree * factor) remaining degree =
      binomialCompletion moments remaining degree * factor := by
  induction remaining generalizing degree with
  | zero => rfl
  | succ remaining ih =>
      cases degree with
      | zero => exact ih 0
      | succ degree =>
          simp only [binomialCompletion_succ, ih, div_eq_mul_inv]
          ring

end SphincsSecurity.Concrete
