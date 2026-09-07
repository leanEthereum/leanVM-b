import SphincsSecurity.Proof.TargetAssignmentExpectation
import SphincsSecurity.Proof.FewTimeTargetIncrementBound

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

noncomputable def futureTargetAssignmentCount : {n : Nat} → (Fin n → Option FewTimeView) → Nat → FewTimeView → ENNReal
  | _, views, 0, target => (targetAssignmentCount views target : ENNReal)
  | _, views, remaining + 1, target =>
      ∑' next, Pr[= next | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
        futureTargetAssignmentCount (insertFewTimeView views next) remaining target

noncomputable def futureTargetAssignmentIncrement : {n : Nat} → (Fin n → Option FewTimeView) → Nat → FewTimeView → FewTimeView → ENNReal
  | _, views, 0, target, source => (targetAssignmentIncrement views target source : ENNReal)
  | _, views, remaining + 1, target, source =>
      ∑' next, Pr[= next | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
        futureTargetAssignmentIncrement (insertFewTimeView views next) remaining target source

theorem futureTargetAssignmentCount_mono (remaining : Nat) {n m : Nat} (before : Fin n → Option FewTimeView)
    (after : Fin m → Option FewTimeView) (target : FewTimeView)
    (hcounts : ∀ tree, targetTreeMatchCount before target tree ≤ targetTreeMatchCount after target tree) :
    futureTargetAssignmentCount before remaining target ≤ futureTargetAssignmentCount after remaining target := by
  induction remaining generalizing n m with
  | zero => exact Nat.cast_le.mpr (Finset.prod_le_prod' (fun tree _ => hcounts tree))
  | succ remaining ih =>
      apply ENNReal.tsum_le_tsum
      intro next
      apply mul_le_mul' le_rfl
      apply ih
      intro tree
      simp only [targetTreeMatchCount_insert]
      exact Nat.add_le_add_right (hcounts tree) _

theorem futureTargetAssignmentIncrement_mono (remaining : Nat) {n m : Nat} (before : Fin n → Option FewTimeView)
    (after : Fin m → Option FewTimeView) (target source : FewTimeView)
    (hcounts : ∀ tree, targetTreeMatchCount before target tree ≤ targetTreeMatchCount after target tree) :
    futureTargetAssignmentIncrement before remaining target source ≤ futureTargetAssignmentIncrement after remaining target source := by
  induction remaining generalizing n m with
  | zero => exact Nat.cast_le.mpr (targetAssignmentIncrement_mono before after target source hcounts)
  | succ remaining ih =>
      apply ENNReal.tsum_le_tsum
      intro next
      apply mul_le_mul' le_rfl
      apply ih
      intro tree
      simp only [targetTreeMatchCount_insert]
      exact Nat.add_le_add_right (hcounts tree) _

theorem futureTargetAssignmentCount_insert_comm {n : Nat} (views : Fin n → Option FewTimeView)
    (remaining : Nat) (target first second : FewTimeView) :
    futureTargetAssignmentCount (insertFewTimeView (insertFewTimeView views first) second) remaining target =
      futureTargetAssignmentCount (insertFewTimeView (insertFewTimeView views second) first) remaining target := by
  apply le_antisymm <;> apply futureTargetAssignmentCount_mono <;> intro tree <;>
    simp only [targetTreeMatchCount_insert, Nat.add_right_comm, le_refl]

theorem futureTargetAssignmentCount_add_increment {n : Nat} (views : Fin n → Option FewTimeView)
    (remaining : Nat) (target source : FewTimeView) :
    futureTargetAssignmentCount views remaining target + futureTargetAssignmentIncrement views remaining target source =
      futureTargetAssignmentCount (insertFewTimeView views source) remaining target := by
  induction remaining generalizing n with
  | zero =>
      change (targetAssignmentCount views target : ENNReal) + (targetAssignmentIncrement views target source : ENNReal) = _
      rw [← Nat.cast_add, targetAssignmentCount_add_increment]
      rfl
  | succ remaining ih =>
      simp only [futureTargetAssignmentCount, futureTargetAssignmentIncrement]
      rw [← ENNReal.tsum_add]
      apply tsum_congr
      intro next
      rw [← mul_add, ih, futureTargetAssignmentCount_insert_comm]

theorem futureTargetAssignmentIncrement_le_insert {n : Nat} (views : Fin n → Option FewTimeView)
    (remaining : Nat) (target source next : FewTimeView) :
    futureTargetAssignmentIncrement views remaining target source ≤
      futureTargetAssignmentIncrement (insertFewTimeView views next) remaining target source := by
  apply futureTargetAssignmentIncrement_mono
  intro tree
  rw [targetTreeMatchCount_insert]
  exact Nat.le_add_right _ _

theorem futureFewTimeCoverage_le_assignment {n : Nat} (views : Fin n → Option FewTimeView) (remaining : Nat) (target : FewTimeView) :
    futureFewTimeCoverage remaining (uncoveredFewTimeTrees views target) target ≤ futureTargetAssignmentCount views remaining target := by
  induction remaining generalizing n with
  | zero => rw [futureFewTimeCoverage_zero]; exact coveredFewTimeView_indicator_le_assignment views target
  | succ remaining ih =>
      simp only [futureFewTimeCoverage, futureTargetAssignmentCount, ← uncoveredFewTimeTrees_insert]
      exact ENNReal.tsum_le_tsum (fun next => mul_le_mul' le_rfl (ih _))

theorem futureFewTimeCoverageIncrement_le_assignment {n : Nat} (views : Fin n → Option FewTimeView)
    (remaining : Nat) (target source : FewTimeView) :
    futureFewTimeCoverageIncrement remaining (uncoveredFewTimeTrees views target) target source ≤
      futureTargetAssignmentIncrement views remaining target source := by
  induction remaining generalizing n with
  | zero => rw [futureFewTimeCoverageIncrement_zero_eq]; exact completesFewTimeView_indicator_le_assignmentIncrement views target source
  | succ remaining ih =>
      simp only [futureFewTimeCoverageIncrement_succ, futureTargetAssignmentIncrement, ← uncoveredFewTimeTrees_insert]
      exact ENNReal.tsum_le_tsum (fun next => mul_le_mul' le_rfl (ih _))

theorem expected_uniform_futureTargetAssignmentCount {n : Nat} (views : Fin n → Option FewTimeView) (remaining : Nat) :
    (∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] * futureTargetAssignmentCount views remaining target) =
      coverageOccupancyCompletion views remaining / (Fintype.card FewTimeView : ENNReal) := by
  induction remaining generalizing n with
  | zero => rw [coverageOccupancyCompletion_zero]; exact expected_uniform_targetAssignmentCount views
  | succ remaining ih =>
      simp only [futureTargetAssignmentCount, ← ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_comm]
      calc
        _ = ∑' next, Pr[= next | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
            (∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
              futureTargetAssignmentCount (insertFewTimeView views next) remaining target) := by
          apply tsum_congr
          intro next
          rw [← ENNReal.tsum_mul_left]
          apply tsum_congr
          intro target
          exact mul_left_comm _ _ _
        _ = _ := by simp only [ih, div_eq_mul_inv, ← mul_assoc, ENNReal.tsum_mul_right, expected_coverageOccupancyCompletion_insert]

theorem expected_uniform_futureTargetAssignmentIncrement {n : Nat} (views : Fin n → Option FewTimeView)
    (remaining : Nat) (source : FewTimeView) :
    (∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] * futureTargetAssignmentIncrement views remaining target source) =
      coverageOccupancyCompletionIncrement views remaining source / (Fintype.card FewTimeView : ENNReal) := by
  induction remaining generalizing n with
  | zero => rw [coverageOccupancyCompletionIncrement_zero]; exact expected_uniform_targetAssignmentIncrement views source
  | succ remaining ih =>
      simp only [futureTargetAssignmentIncrement, ← ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_comm]
      calc
        _ = ∑' next, Pr[= next | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
            (∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
              futureTargetAssignmentIncrement (insertFewTimeView views next) remaining target source) := by
          apply tsum_congr
          intro next
          rw [← ENNReal.tsum_mul_left]
          apply tsum_congr
          intro target
          exact mul_left_comm _ _ _
        _ = _ := by simp only [ih, div_eq_mul_inv, ← mul_assoc, ENNReal.tsum_mul_right, expected_coverageOccupancyCompletionIncrement_insert]

theorem expected_source_futureTargetAssignmentIncrement {n : Nat} (views : Fin n → Option FewTimeView)
    (remaining : Nat) (target : FewTimeView) :
    futureTargetAssignmentCount views remaining target +
      (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] * futureTargetAssignmentIncrement views remaining target source) =
      futureTargetAssignmentCount views (remaining + 1) target := by
  have hmass : (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)]) = 1 := tsum_probOutput_eq_one' (by simp)
  conv_lhs => lhs; rw [← one_mul (futureTargetAssignmentCount views remaining target), ← hmass, ← ENNReal.tsum_mul_right]
  rw [← ENNReal.tsum_add]
  simp only [← mul_add, futureTargetAssignmentCount_add_increment, futureTargetAssignmentCount]

theorem expected_uniformHashOutput_futureTargetAssignmentIncrement {n : Nat} (views : Fin n → Option FewTimeView)
    (remaining : Nat) (source : FewTimeView) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Admissible (truncateMessageDigest output) then
        futureTargetAssignmentIncrement views remaining (hashOutputFewTimeView output) source else 0)) =
      coverageOccupancyCompletionIncrement views remaining source * ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
  rw [expected_uniformHashOutput_admissible_weight
    (fun target => futureTargetAssignmentIncrement views remaining target source), expected_uniform_futureTargetAssignmentIncrement]
  have hrate : ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card FewTimeView : ENNReal)⁻¹ =
      ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
    rw [fewTimeView_card]
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ftsTreeHeight, totalHeight, ftsTrees]
  rw [div_eq_mul_inv, mul_left_comm, hrate]

end SphincsSecurity.Concrete
