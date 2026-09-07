import SphincsSecurity.Proof.AllMessageCompletionShift

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

noncomputable def occupancyDerivativePolynomial (order : Nat) (moments : Nat → ENNReal) (remaining : Nat) : ENNReal :=
  ∑ degree ∈ Finset.range (15 - order), (coverageFactorialCoefficient (degree + order) * (degree + order).factorial : Nat) *
    binomialCompletion moments remaining degree

theorem occupancyDerivativePolynomial_of_ge (order : Nat) (horder : 15 ≤ order)
    (moments : Nat → ENNReal) (remaining : Nat) : occupancyDerivativePolynomial order moments remaining = 0 := by
  simp only [occupancyDerivativePolynomial, Nat.sub_eq_zero_of_le horder, Finset.range_zero, Finset.sum_empty]

theorem occupancyDerivativePolynomial_shift (order : Nat) (moments : Nat → ENNReal) (remaining : Nat) :
    occupancyDerivativePolynomial order (shiftBinomialMoments moments) remaining =
      occupancyDerivativePolynomial (order + 1) moments remaining := by
  by_cases horder : 15 ≤ order
  · rw [occupancyDerivativePolynomial_of_ge order horder, occupancyDerivativePolynomial_of_ge (order + 1) (by omega)]
  · have hsize : 15 - order = (15 - (order + 1)) + 1 := by omega
    unfold occupancyDerivativePolynomial
    rw [hsize, Finset.sum_range_succ']
    simp only [binomialCompletion_shift_zero, mul_zero, add_zero, binomialCompletion_shift_succ,
      Nat.add_assoc, Nat.add_comm 1 order]

theorem occupancyDerivativePolynomial_add (order : Nat) (first second : Nat → ENNReal) (remaining : Nat) :
    occupancyDerivativePolynomial order (fun degree => first degree + second degree) remaining =
      occupancyDerivativePolynomial order first remaining + occupancyDerivativePolynomial order second remaining := by
  simp only [occupancyDerivativePolynomial, binomialCompletion_add, mul_add, Finset.sum_add_distrib]

theorem occupancyDerivativePolynomial_mul_right (order : Nat) (moments : Nat → ENNReal) (remaining : Nat) (factor : ENNReal) :
    occupancyDerivativePolynomial order (fun degree => moments degree * factor) remaining =
      occupancyDerivativePolynomial order moments remaining * factor := by
  simp only [occupancyDerivativePolynomial, binomialCompletion_mul_right, ← mul_assoc, Finset.sum_mul]

theorem expected_occupancyDerivativePolynomial {α : Type} (computation : ProbComp α) (order : Nat)
    (moments : α → Nat → ENNReal) (remaining : Nat) :
    (∑' result, Pr[= result | computation] * occupancyDerivativePolynomial order (moments result) remaining) =
      occupancyDerivativePolynomial order (fun degree => ∑' result, Pr[= result | computation] * moments result degree) remaining := by
  simp only [occupancyDerivativePolynomial, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro degree _
  simp_rw [mul_left_comm (Pr[= _ | computation])]
  rw [ENNReal.tsum_mul_left, expected_binomialCompletion]

theorem occupancyDerivativePolynomial_succ (order : Nat) (moments : Nat → ENNReal) (remaining : Nat) :
    occupancyDerivativePolynomial order moments (remaining + 1) = occupancyDerivativePolynomial order moments remaining +
      occupancyDerivativePolynomial (order + 1) moments remaining / (Fintype.card Index : ENNReal) := by
  have hstep : binomialStep moments =
      (fun degree => moments degree + shiftBinomialMoments (fun degree => moments degree / (Fintype.card Index : ENNReal)) degree) := by
    funext degree
    cases degree with
    | zero => exact (add_zero _).symm
    | succ degree => rfl
  have hbefore : occupancyDerivativePolynomial order moments (remaining + 1) =
      occupancyDerivativePolynomial order (binomialStep moments) remaining := by
    simp only [occupancyDerivativePolynomial, binomialCompletion_step]
  rw [hbefore, hstep, occupancyDerivativePolynomial_add, occupancyDerivativePolynomial_shift]
  simp only [div_eq_mul_inv, occupancyDerivativePolynomial_mul_right]

theorem occupancyDerivativePolynomial_allMessageReuse (order : Nat) (key : SecretKey) (q : Nat)
    (state : CoverLogState) (remaining : Nat) :
    occupancyDerivativePolynomial order (allMessageBinomialReuseMoments key q state) remaining =
      occupancyDerivativePolynomial (order + 1) (cachedIndexBinomialMoments key state) remaining * digestReuseWeight q := by
  rw [allMessageBinomialReuseMoments_eq_shift, occupancyDerivativePolynomial_shift, occupancyDerivativePolynomial_mul_right]

theorem expected_logTraced_sign_occupancyDerivative_le (order remaining : Nat) (key : SecretKey) (q : Nat)
    (hq : q ≤ 2 ^ 127) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcache : QueryCache.enncard state.1 ≤ q) (message : Message) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      occupancyDerivativePolynomial order (fun degree => observedLogBinomialOccupancy key degree result.2) remaining) ≤
      occupancyDerivativePolynomial order (fun degree => observedLogBinomialOccupancy key degree state) (remaining + 1) +
        occupancyDerivativePolynomial (order + 1) (cachedIndexBinomialMoments key state) remaining * digestReuseWeight q := by
  rw [← occupancyDerivativePolynomial_allMessageReuse order key q state remaining]
  simp only [occupancyDerivativePolynomial, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro degree _
  simp_rw [mul_left_comm (Pr[= _ | _])]
  rw [ENNReal.tsum_mul_left, ← mul_add]
  exact mul_le_mul' le_rfl (expected_logTraced_sign_completion_le_allMessage key q remaining degree hq state hsigned hcache message)

theorem occupancyUniformIncrementPolynomial_eq_derivative (moments : Nat → ENNReal) (remaining : Nat) :
    occupancyUniformIncrementPolynomial moments remaining =
      occupancyDerivativePolynomial 1 moments remaining / (Fintype.card Index : ENNReal) := by
  simp only [occupancyUniformIncrementPolynomial, occupancyDerivativePolynomial, show 15 - 1 = 14 from rfl,
    div_eq_mul_inv, ← mul_assoc, Finset.sum_mul]

theorem coverageOccupancyCompletion_eq_derivative {n : Nat} (views : Fin n → Option FewTimeView) (remaining : Nat) :
    coverageOccupancyCompletion views remaining =
      occupancyDerivativePolynomial 0 (fun degree => (binomialOccupancyMoment views degree : ENNReal)) remaining := by
  unfold occupancyDerivativePolynomial
  simp only [Nat.sub_zero, Nat.add_zero]
  rw [show 15 = 14 + 1 from rfl, Finset.sum_range_succ']
  simp only [show coverageFactorialCoefficient 0 = 0 from rfl, Nat.cast_zero, zero_mul, add_zero]
  rfl

end SphincsSecurity.Concrete
