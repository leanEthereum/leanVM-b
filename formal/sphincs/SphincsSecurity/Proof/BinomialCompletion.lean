import SphincsSecurity.Proof.FewTimeBinomialOccupancy

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

noncomputable def binomialStep (moments : Nat → ENNReal) : Nat → ENNReal
  | 0 => moments 0
  | degree + 1 => moments (degree + 1) + moments degree / (Fintype.card Index : ENNReal)

noncomputable def binomialCompletion (moments : Nat → ENNReal) : Nat → Nat → ENNReal
  | 0 => moments
  | remaining + 1 => binomialStep (binomialCompletion moments remaining)

theorem binomialCompletion_zero (moments : Nat → ENNReal) (degree : Nat) :
    binomialCompletion moments 0 degree = moments degree := rfl

theorem binomialCompletion_degree_zero (moments : Nat → ENNReal) (remaining : Nat) :
    binomialCompletion moments remaining 0 = moments 0 := by
  induction remaining with
  | zero => rfl
  | succ remaining ih => exact ih

theorem binomialCompletion_succ (moments : Nat → ENNReal) (remaining degree : Nat) :
    binomialCompletion moments (remaining + 1) (degree + 1) =
      binomialCompletion moments remaining (degree + 1) +
        binomialCompletion moments remaining degree / (Fintype.card Index : ENNReal) := rfl

theorem binomialCompletion_step (moments : Nat → ENNReal) (remaining degree : Nat) :
    binomialCompletion (binomialStep moments) remaining degree =
      binomialCompletion moments (remaining + 1) degree := by
  induction remaining generalizing degree with
  | zero => rfl
  | succ remaining ih =>
      cases degree with
      | zero => exact ih 0
      | succ degree => simp only [binomialCompletion_succ, ih]

theorem binomialCompletion_mono {first second : Nat → ENNReal}
    (h : ∀ degree, first degree ≤ second degree) (remaining degree : Nat) :
    binomialCompletion first remaining degree ≤ binomialCompletion second remaining degree := by
  induction remaining generalizing degree with
  | zero => exact h degree
  | succ remaining ih =>
      cases degree with
      | zero => exact ih 0
      | succ degree => exact add_le_add (ih _) (mul_le_mul' (ih _) le_rfl)

theorem le_binomialCompletion (moments : Nat → ENNReal) (remaining degree : Nat) :
    moments degree ≤ binomialCompletion moments remaining degree := by
  induction remaining generalizing degree with
  | zero => exact le_rfl
  | succ remaining ih =>
      cases degree with
      | zero => exact ih 0
      | succ degree => exact (ih _).trans le_self_add

theorem binomialCompletion_add (first second : Nat → ENNReal) (remaining degree : Nat) :
    binomialCompletion (fun degree => first degree + second degree) remaining degree =
      binomialCompletion first remaining degree + binomialCompletion second remaining degree := by
  induction remaining generalizing degree with
  | zero => rfl
  | succ remaining ih =>
      cases degree with
      | zero => exact ih 0
      | succ degree =>
          simp only [binomialCompletion_succ, ih, ENNReal.add_div]
          ac_rfl

theorem expected_binomialCompletion {α : Type} (computation : ProbComp α)
    (moments : α → Nat → ENNReal) (remaining degree : Nat) :
    (∑' result, Pr[= result | computation] * binomialCompletion (moments result) remaining degree) =
      binomialCompletion (fun degree => ∑' result, Pr[= result | computation] * moments result degree) remaining degree := by
  induction remaining generalizing degree with
  | zero => rfl
  | succ remaining ih =>
      cases degree with
      | zero => exact ih 0
      | succ degree =>
          simp only [binomialCompletion_succ, mul_add, div_eq_mul_inv, ENNReal.tsum_add, ← mul_assoc]
          rw [ENNReal.tsum_mul_right, ih, ih]

theorem expected_binomialCompletion_le {α : Type} (computation : ProbComp α)
    (after : α → Nat → ENNReal) (before reuse : Nat → ENNReal)
    (hstep : ∀ degree, (∑' result, Pr[= result | computation] * after result degree) ≤
      binomialStep before degree + reuse degree) (remaining degree : Nat) :
    (∑' result, Pr[= result | computation] * binomialCompletion (after result) remaining degree) ≤
      binomialCompletion before (remaining + 1) degree + binomialCompletion reuse remaining degree := by
  rw [expected_binomialCompletion]
  exact (binomialCompletion_mono hstep remaining degree).trans_eq
    ((binomialCompletion_add _ _ _ _).trans (congrArg (· + binomialCompletion reuse remaining degree)
      (binomialCompletion_step before remaining degree)))

theorem binomialCompletion_empty (remaining degree : Nat) :
    binomialCompletion (fun degree => if degree = 0 then (Fintype.card Index : ENNReal) else 0) remaining degree =
      (remaining.choose degree : ENNReal) * (Fintype.card Index : ENNReal)⁻¹ ^ degree * (Fintype.card Index : ENNReal) := by
  induction remaining generalizing degree with
  | zero =>
      cases degree <;> simp [binomialCompletion_zero]
  | succ remaining ih =>
      cases degree with
      | zero => simp only [binomialCompletion_degree_zero, if_true, Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, one_mul]
      | succ degree =>
          rw [binomialCompletion_succ, ih, ih, Nat.choose_succ_succ, Nat.cast_add, pow_succ]
          simp only [div_eq_mul_inv, add_mul]
          ring

end SphincsSecurity.Concrete
