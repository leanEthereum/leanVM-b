import SphincsSecurity.Proof.AllMessageBinomialReuse
import SphincsSecurity.Proof.BinomialCompletionShift

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem allMessageBinomialReuseMoments_eq_shift (key : SecretKey) (q : Nat) (state : CoverLogState) :
    allMessageBinomialReuseMoments key q state =
      shiftBinomialMoments (fun degree => cachedIndexBinomialMoments key state degree * digestReuseWeight q) := by
  funext degree
  cases degree <;> rfl

theorem binomialCompletion_allMessageReuse_zero (key : SecretKey) (q : Nat) (state : CoverLogState) (remaining : Nat) :
    binomialCompletion (allMessageBinomialReuseMoments key q state) remaining 0 = 0 :=
  binomialCompletion_degree_zero _ _

theorem binomialCompletion_allMessageReuse_succ (key : SecretKey) (q : Nat) (state : CoverLogState) (remaining degree : Nat) :
    binomialCompletion (allMessageBinomialReuseMoments key q state) remaining (degree + 1) =
      binomialCompletion (cachedIndexBinomialMoments key state) remaining degree * digestReuseWeight q := by
  rw [allMessageBinomialReuseMoments_eq_shift, binomialCompletion_shift_succ, binomialCompletion_mul_right]

theorem occupancyUniformIncrementPolynomial_allMessageReuse (key : SecretKey) (q : Nat)
    (state : CoverLogState) (remaining : Nat) :
    occupancyUniformIncrementPolynomial (allMessageBinomialReuseMoments key q state) remaining =
      (∑ degree ∈ Finset.range 13, (coverageFactorialCoefficient (degree + 2) * (degree + 2).factorial : Nat) *
        (binomialCompletion (cachedIndexBinomialMoments key state) remaining degree / (Fintype.card Index : ENNReal))) * digestReuseWeight q := by
  unfold occupancyUniformIncrementPolynomial
  rw [show 14 = 13 + 1 from rfl, Finset.sum_range_succ']
  simp only [binomialCompletion_allMessageReuse_zero, ENNReal.zero_div, mul_zero, add_zero, binomialCompletion_allMessageReuse_succ]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro degree _
  simp only [div_eq_mul_inv]
  ring

end SphincsSecurity.Concrete
