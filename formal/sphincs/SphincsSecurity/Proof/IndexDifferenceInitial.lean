import SphincsSecurity.Proof.PowerDifferenceCoefficients
import SphincsSecurity.Proof.IndexDifferenceTransform
import SphincsSecurity.Proof.InitialRawIndexEnvelope
import SphincsSecurity.Proof.InitialMixedEnvelope

namespace SphincsSecurity.Concrete

open ENNReal

theorem targetIndexTreeLower_nat (weights : Nat → ENNReal) (values : Nat → Nat) :
    targetIndexTreeLower (fun p r => weights p * (values r : ENNReal)) =
      fun p r => weights p * (powerDifferenceStep values r : ENNReal) := by
  funext power degree
  simp only [targetIndexTreeLower, powerDifferenceStep, Nat.cast_sum, Nat.cast_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro lower _
  ring

theorem targetIndexTreeLower_iterate_nat (order : Nat) (weights : Nat → ENNReal) (values : Nat → Nat) :
    targetIndexTreeLower^[order] (fun p r => weights p * (values r : ENNReal)) =
      fun p r => weights p * (powerDifferenceStep^[order] values r : ENNReal) := by
  induction order with
  | zero => rfl
  | succ order ih => simp only [Function.iterate_succ_apply', ih, targetIndexTreeLower_nat]

theorem indexDifferenceTransform_initial : indexDifferenceTransform initialTargetIndexVector = initialMixedDerivativeVector := by
  have hinitial : initialTargetIndexVector = fun p r =>
      (if p = 0 then (Fintype.card Index : ENNReal) else 0) * ((0 : Nat) ^ r : Nat) := by
    funext power degree
    cases power <;> cases degree <;> simp [initialTargetIndexVector]
  rw [hinitial]
  funext power order
  simp only [indexDifferenceTransform, targetIndexTreeLower_iterate_nat]
  change (if power = 0 then (Fintype.card Index : ENNReal) else 0) * (powerDifferenceValue order 0 14 : ENNReal) = _
  rw [powerDifferenceValue_zero_fourteen]
  by_cases hpower : power = 0 <;> by_cases horder : order < 15 <;>
    simp only [initialMixedDerivativeVector, hpower, horder, and_self, and_false, false_and, if_true, if_false, Nat.cast_zero, mul_zero, zero_mul]
  exact mul_comm _ _

end SphincsSecurity.Concrete
