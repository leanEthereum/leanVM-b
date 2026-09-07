import SphincsSecurity.Proof.OccupancyDerivative

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
set_option backward.isDefEq.respectTransparency false

theorem coverageOccupancyCompletionIncrement_eq_derivative {n : Nat} (views : Fin n → Option FewTimeView)
    (remaining : Nat) (source : FewTimeView) :
    coverageOccupancyCompletionIncrement views remaining source =
      occupancyDerivativePolynomial 1 (fun degree => ((signingSlotsAtIndex views source.1).card.choose degree : ENNReal)) remaining := by
  have hmoments : (fun degree => (binomialOccupancyMoment (insertFewTimeView views source) degree : ENNReal)) =
      (fun degree => (binomialOccupancyMoment views degree : ENNReal) +
        shiftBinomialMoments (fun degree => ((signingSlotsAtIndex views source.1).card.choose degree : ENNReal)) degree) := by
    funext degree
    cases degree with
    | zero => simp only [binomialOccupancyMoment_zero, shiftBinomialMoments, add_zero]
    | succ degree => simp only [binomialOccupancyMoment_insert, Nat.cast_add, shiftBinomialMoments]
  have hcompletion : coverageOccupancyCompletion (insertFewTimeView views source) remaining =
      coverageOccupancyCompletion views remaining +
        occupancyDerivativePolynomial 1 (fun degree => ((signingSlotsAtIndex views source.1).card.choose degree : ENNReal)) remaining := by
    rw [coverageOccupancyCompletion_eq_derivative, hmoments, occupancyDerivativePolynomial_add,
      occupancyDerivativePolynomial_shift, ← coverageOccupancyCompletion_eq_derivative]
  rw [coverageOccupancyCompletionIncrement, hcompletion,
    ENNReal.add_sub_cancel_left (coverageOccupancyCompletion_ne_top views remaining)]

theorem cacheMessageWeight_binomialCompletion (parameter : PublicParameter)
    (moments : HashInput → FewTimeView → Nat → ENNReal) (cache : QueryCache HashSpec) (remaining degree : Nat) :
    cacheMessageWeight parameter (fun input source => binomialCompletion (moments input source) remaining degree) cache =
      binomialCompletion (fun degree => cacheMessageWeight parameter (fun input source => moments input source degree) cache) remaining degree := by
  induction remaining generalizing degree with
  | zero => rfl
  | succ remaining ih =>
      cases degree with
      | zero => exact ih 0
      | succ degree =>
          simp only [binomialCompletion_succ, div_eq_mul_inv, cacheMessageWeight_add, cacheMessageWeight_mul_right, ih]

theorem cacheMessageWeight_occupancyDerivative (parameter : PublicParameter) (order : Nat)
    (moments : HashInput → FewTimeView → Nat → ENNReal) (cache : QueryCache HashSpec) (remaining : Nat) :
    cacheMessageWeight parameter (fun input source => occupancyDerivativePolynomial order (moments input source) remaining) cache =
      occupancyDerivativePolynomial order
        (fun degree => cacheMessageWeight parameter (fun input source => moments input source degree) cache) remaining := by
  unfold occupancyDerivativePolynomial
  rw [cacheMessageWeight_sum]
  apply Finset.sum_congr rfl
  intro degree _
  simp_rw [mul_comm ((coverageFactorialCoefficient (degree + order) * (degree + order).factorial : Nat) : ENNReal)]
  rw [cacheMessageWeight_mul_right, cacheMessageWeight_binomialCompletion]

theorem allMessageOccupancyReuseCharge_eq_cachedDerivative (remaining : Nat) (key : SecretKey)
    (cache : QueryCache HashSpec) (log : QueryLog SigningSpec) (q : Nat) :
    allMessageOccupancyReuseCharge remaining key cache log q =
      occupancyDerivativePolynomial 1 (cachedIndexBinomialMoments key (cache, log)) remaining * digestReuseWeight q := by
  rw [allMessageOccupancyReuseCharge]
  simp only [coverageOccupancyCompletionIncrement_eq_derivative, cacheMessageWeight_occupancyDerivative]
  rfl

theorem occupancyUniformIncrementPolynomial_allMessageReuse_eq_derivative (remaining : Nat) (key : SecretKey)
    (state : CoverLogState) (q : Nat) :
    occupancyUniformIncrementPolynomial (allMessageBinomialReuseMoments key q state) remaining =
      occupancyDerivativePolynomial 2 (cachedIndexBinomialMoments key state) remaining * digestReuseWeight q /
        (Fintype.card Index : ENNReal) := by
  rw [occupancyUniformIncrementPolynomial_eq_derivative, occupancyDerivativePolynomial_allMessageReuse]

end SphincsSecurity.Concrete
