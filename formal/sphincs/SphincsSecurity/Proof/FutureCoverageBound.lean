import SphincsSecurity.Proof.FutureCoverage
import SphincsSecurity.Proof.UniformCompletionBound

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def coverageOccupancyCompletion {n : Nat} (views : Fin n → Option FewTimeView)
    (remaining : Nat) : ENNReal :=
  ∑ degree ∈ Finset.range 14, (coverageFactorialCoefficient (degree + 1) * (degree + 1).factorial : Nat) *
    binomialCompletion (fun d => (binomialOccupancyMoment views d : ENNReal)) remaining (degree + 1)

theorem coverageOccupancyCompletion_zero {n : Nat} (views : Fin n → Option FewTimeView) :
    coverageOccupancyCompletion views 0 = (coverageOccupancyMoment views : ENNReal) :=
  (coverageOccupancyMoment_eq_positive_binomial views).symm

theorem expected_coverageOccupancyCompletion_insert {n : Nat} (views : Fin n → Option FewTimeView)
    (remaining : Nat) :
    (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
      coverageOccupancyCompletion (insertFewTimeView views source) remaining) =
      coverageOccupancyCompletion views (remaining + 1) := by
  have hstep : (fun degree => ∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
      (binomialOccupancyMoment (insertFewTimeView views source) degree : ENNReal)) =
      binomialStep (fun degree => (binomialOccupancyMoment views degree : ENNReal)) := by
    funext degree
    cases degree with
    | zero =>
        have hmass : (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)]) = 1 :=
          tsum_probOutput_eq_one' (by simp)
        simp only [binomialOccupancyMoment_zero, binomialStep, ENNReal.tsum_mul_right, hmass, one_mul]
    | succ degree => exact expected_binomialOccupancyMoment_insert views degree
  simp only [coverageOccupancyCompletion, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro degree _
  simp_rw [mul_left_comm (Pr[= _ | _])]
  rw [ENNReal.tsum_mul_left, expected_binomialCompletion, hstep, binomialCompletion_step]

theorem expected_futureFewTimeCoverage_succ {n : Nat} (views : Fin n → Option FewTimeView)
    (remaining : Nat) :
    (∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
      futureFewTimeCoverage (remaining + 1) (uncoveredFewTimeTrees views target) target) =
      ∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
        ∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
          futureFewTimeCoverage remaining (uncoveredFewTimeTrees (insertFewTimeView views source) target) target := by
  simp only [futureFewTimeCoverage, ← uncoveredFewTimeTrees_insert, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro source
  apply tsum_congr
  intro target
  rw [mul_left_comm]

theorem expected_futureFewTimeCoverage_le_occupancyCompletion {n : Nat}
    (views : Fin n → Option FewTimeView) (remaining : Nat) :
    (∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
      futureFewTimeCoverage remaining (uncoveredFewTimeTrees views target) target) ≤
      coverageOccupancyCompletion views remaining / (Fintype.card FewTimeView : ENNReal) := by
  induction remaining generalizing n with
  | zero =>
      simp only [futureFewTimeCoverage_zero, mul_ite, mul_one, mul_zero, ← probEvent_eq_tsum_ite,
        coverageOccupancyCompletion_zero]
      exact probEvent_uniform_coveredFewTimeView_le_occupancy views
  | succ remaining ih =>
      rw [expected_futureFewTimeCoverage_succ]
      calc
        _ ≤ ∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
            (coverageOccupancyCompletion (insertFewTimeView views source) remaining / (Fintype.card FewTimeView : ENNReal)) :=
          ENNReal.tsum_le_tsum (fun source => mul_le_mul' le_rfl (ih (insertFewTimeView views source)))
        _ = _ := by
          simp only [div_eq_mul_inv, ← mul_assoc, ENNReal.tsum_mul_right, expected_coverageOccupancyCompletion_insert]

theorem expected_uniformHashOutput_admissible_weight (weight : FewTimeView → ENNReal) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Admissible (truncateMessageDigest output) then weight (hashOutputFewTimeView output) else 0)) =
      ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ *
        ∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] * weight target := by
  have hexpand (output : HashOutput) :
      (if Admissible (truncateMessageDigest output) then weight (hashOutputFewTimeView output) else 0) =
        ∑' target, if Admissible (truncateMessageDigest output) ∧ hashOutputFewTimeView output = target then weight target else 0 := by
    by_cases h : Admissible (truncateMessageDigest output) <;> simp only [h, true_and, false_and, if_true, if_false, tsum_zero]
    simp
  simp_rw [hexpand, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro target
  calc
    _ = Pr[fun output => Admissible (truncateMessageDigest output) ∧ hashOutputFewTimeView output = target |
        ($ᵗ HashOutput : ProbComp HashOutput)] * weight target := by
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro output
      split_ifs <;> simp
    _ = _ := by
      simp only [← signAttemptResultOfOutput_ne_none_iff]
      rw [probEvent_uniformHashOutput_admissible_view (fun view => view = target),
        probEvent_eq_eq_probOutput, mul_assoc]

theorem expected_uniformHashOutput_futureCoverage_le {n : Nat}
    (views : Fin n → Option FewTimeView) (remaining : Nat) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Admissible (truncateMessageDigest output) then
        futureFewTimeCoverage remaining (uncoveredFewTimeTrees views (hashOutputFewTimeView output))
          (hashOutputFewTimeView output) else 0)) ≤
      coverageOccupancyCompletion views remaining * ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
  rw [expected_uniformHashOutput_admissible_weight
    (fun target => futureFewTimeCoverage remaining (uncoveredFewTimeTrees views target) target)]
  apply (mul_le_mul' le_rfl (expected_futureFewTimeCoverage_le_occupancyCompletion views remaining)).trans_eq
  have hrate : ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card FewTimeView : ENNReal)⁻¹ =
      ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
    rw [fewTimeView_card]
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ftsTreeHeight, totalHeight, ftsTrees]
  rw [div_eq_mul_inv, mul_left_comm, hrate]

theorem coverageOccupancyCompletion_empty (views : Fin 0 → Option FewTimeView) (remaining : Nat) :
    coverageOccupancyCompletion views remaining = uniformCoverageCompletion remaining := by
  have hempty : (fun degree => (binomialOccupancyMoment views degree : ENNReal)) =
      (fun degree => if degree = 0 then (Fintype.card Index : ENNReal) else 0) := by
    funext degree
    cases degree with
    | zero => simp only [binomialOccupancyMoment_zero, if_true]
    | succ degree => simp only [binomialOccupancyMoment_empty, Nat.cast_zero, Nat.succ_ne_zero, if_false]
  simp only [coverageOccupancyCompletion, hempty, binomialCompletion_empty, uniformCoverageCompletion]

theorem expected_uniformHashOutput_futureCoverage_empty_le (views : Fin 0 → Option FewTimeView) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Admissible (truncateMessageDigest output) then
        futureFewTimeCoverage signatureLimit (uncoveredFewTimeTrees views (hashOutputFewTimeView output))
          (hashOutputFewTimeView output) else 0)) ≤
      7 * (2 : ENNReal) ^ 40 * ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
  apply (expected_uniformHashOutput_futureCoverage_le views signatureLimit).trans
  rw [coverageOccupancyCompletion_empty]
  exact mul_le_mul' uniformCoverageCompletion_signatureLimit_le le_rfl

end SphincsSecurity.Concrete
