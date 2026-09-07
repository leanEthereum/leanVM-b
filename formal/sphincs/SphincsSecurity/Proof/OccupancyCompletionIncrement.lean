import SphincsSecurity.Proof.OccupancyCompletionGrowth

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem coverageOccupancyCompletion_le_insert {n : Nat} (views : Fin n → Option FewTimeView)
    (source : FewTimeView) (remaining : Nat) :
    coverageOccupancyCompletion views remaining ≤ coverageOccupancyCompletion (insertFewTimeView views source) remaining := by
  apply coverageOccupancyCompletion_mono_moments
  intro degree
  apply Finset.sum_le_sum
  intro index _
  apply Nat.choose_le_choose
  rw [signingSlotsAtIndex_insert_card]
  exact Nat.le_add_right _ _

theorem coverageOccupancyCompletion_insert_comm {n : Nat} (views : Fin n → Option FewTimeView)
    (first second : FewTimeView) (remaining : Nat) :
    coverageOccupancyCompletion (insertFewTimeView (insertFewTimeView views first) second) remaining =
      coverageOccupancyCompletion (insertFewTimeView (insertFewTimeView views second) first) remaining := by
  have hmoments : (fun degree => (binomialOccupancyMoment (insertFewTimeView (insertFewTimeView views first) second) degree : ENNReal)) =
      (fun degree => (binomialOccupancyMoment (insertFewTimeView (insertFewTimeView views second) first) degree : ENNReal)) := by
    funext degree
    apply congrArg (fun value : Nat => (value : ENNReal))
    unfold binomialOccupancyMoment
    apply Finset.sum_congr rfl
    intro index _
    simp only [signingSlotsAtIndex_insert_card, Nat.add_right_comm]
  simp only [coverageOccupancyCompletion, hmoments]

noncomputable def coverageOccupancyCompletionIncrement {n : Nat} (views : Fin n → Option FewTimeView)
    (remaining : Nat) (source : FewTimeView) : ENNReal :=
  coverageOccupancyCompletion (insertFewTimeView views source) remaining - coverageOccupancyCompletion views remaining

theorem coverageOccupancyCompletion_add_increment {n : Nat} (views : Fin n → Option FewTimeView)
    (remaining : Nat) (source : FewTimeView) :
    coverageOccupancyCompletion views remaining + coverageOccupancyCompletionIncrement views remaining source =
      coverageOccupancyCompletion (insertFewTimeView views source) remaining :=
  add_tsub_cancel_of_le (coverageOccupancyCompletion_le_insert views source remaining)

theorem coverageOccupancyCompletionIncrement_zero {n : Nat} (views : Fin n → Option FewTimeView)
    (source : FewTimeView) :
    coverageOccupancyCompletionIncrement views 0 source = (occupancyIncrementAtIndex views source.1 : ENNReal) := by
  rw [coverageOccupancyCompletionIncrement, coverageOccupancyCompletion_zero, coverageOccupancyCompletion_zero,
    coverageOccupancyMoment_insert_eq, Nat.cast_add, ENNReal.add_sub_cancel_left (by finiteness)]

theorem expected_coverageOccupancyCompletionIncrement_insert {n : Nat} (views : Fin n → Option FewTimeView)
    (remaining : Nat) (source : FewTimeView) :
    (∑' next, Pr[= next | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
      coverageOccupancyCompletionIncrement (insertFewTimeView views next) remaining source) =
      coverageOccupancyCompletionIncrement views (remaining + 1) source := by
  have hadd : coverageOccupancyCompletion views (remaining + 1) +
      (∑' next, Pr[= next | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
        coverageOccupancyCompletionIncrement (insertFewTimeView views next) remaining source) =
      coverageOccupancyCompletion (insertFewTimeView views source) (remaining + 1) := by
    calc
      _ = ∑' next, Pr[= next | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
          (coverageOccupancyCompletion (insertFewTimeView views next) remaining +
            coverageOccupancyCompletionIncrement (insertFewTimeView views next) remaining source) := by
        simp only [mul_add, ENNReal.tsum_add, expected_coverageOccupancyCompletion_insert]
      _ = _ := by
        simp only [coverageOccupancyCompletion_add_increment,
          coverageOccupancyCompletion_insert_comm views _ source remaining, expected_coverageOccupancyCompletion_insert]
  rw [coverageOccupancyCompletionIncrement, ← hadd,
    ENNReal.add_sub_cancel_left (coverageOccupancyCompletion_ne_top views (remaining + 1))]

end SphincsSecurity.Concrete
