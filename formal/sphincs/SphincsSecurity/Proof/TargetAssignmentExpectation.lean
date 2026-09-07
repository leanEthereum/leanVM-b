import SphincsSecurity.Proof.TargetAssignmentCount
import SphincsSecurity.Proof.FutureCoverageBound
import SphincsSecurity.Proof.OccupancyCompletionIncrement

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem sum_targetTreeMatchCount_leaf {n : Nat} (views : Fin n → Option FewTimeView) (index : Index) (tree : FtsTree) :
    (∑ leaf : FtsLeaf, targetTreeMatchCount views (index, fun _ => leaf) tree) = (signingSlotsAtIndex views index).card := by
  simp only [targetTreeMatchCount]
  rw [Finset.sum_comm, signingSlotsAtIndex, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro slot _
  cases hview : views slot with
  | none => simp only [reduceCtorEq, false_and, exists_false, if_false, Finset.sum_const_zero]
  | some view =>
      simp only [Option.some.injEq, exists_eq_left']
      by_cases hindex : view.1 = index
      · simp only [hindex, true_and, if_true, Finset.sum_ite_eq, Finset.mem_univ]
      · simp only [hindex, false_and, if_false, Finset.sum_const_zero]

theorem sum_targetAssignmentCount_eq_occupancy {n : Nat} (views : Fin n → Option FewTimeView) :
    (∑ target : FewTimeView, targetAssignmentCount views target) = coverageOccupancyMoment views := by
  rw [Fintype.sum_prod_type]
  unfold coverageOccupancyMoment
  apply Finset.sum_congr rfl
  intro index _
  have hpoint (leaves : FtsTree → FtsLeaf) : targetAssignmentCount views (index, leaves) =
      ∏ tree : FtsTree, targetTreeMatchCount views (index, fun _ => leaves tree) tree := rfl
  simp only [hpoint]
  rw [← Fintype.prod_sum (fun (tree : FtsTree) (leaf : FtsLeaf) => targetTreeMatchCount views (index, fun _ => leaf) tree)]
  simp only [sum_targetTreeMatchCount_leaf, Finset.prod_const, Finset.card_univ, FtsTree, Fintype.card_fin]

theorem expected_uniform_targetAssignmentCount {n : Nat} (views : Fin n → Option FewTimeView) :
    (∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] * (targetAssignmentCount views target : ENNReal)) =
      (coverageOccupancyMoment views : ENNReal) / (Fintype.card FewTimeView : ENNReal) := by
  simp only [probOutput_uniformSample, tsum_fintype]
  rw [← Finset.mul_sum, ← Nat.cast_sum, sum_targetAssignmentCount_eq_occupancy]
  exact mul_comm _ _

theorem expected_uniform_targetAssignmentIncrement {n : Nat} (views : Fin n → Option FewTimeView) (source : FewTimeView) :
    (∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] * (targetAssignmentIncrement views target source : ENNReal)) =
      (occupancyIncrementAtIndex views source.1 : ENNReal) / (Fintype.card FewTimeView : ENNReal) := by
  have hnat : (∑ target : FewTimeView, targetAssignmentIncrement views target source) = occupancyIncrementAtIndex views source.1 := by
    have hadd := congrArg (fun f : FewTimeView → Nat => ∑ target, f target)
      (funext fun target => targetAssignmentCount_add_increment views target source)
    simp only [Finset.sum_add_distrib, sum_targetAssignmentCount_eq_occupancy, coverageOccupancyMoment_insert_eq] at hadd
    exact Nat.add_left_cancel hadd
  simp only [probOutput_uniformSample, tsum_fintype]
  rw [← Finset.mul_sum, ← Nat.cast_sum, hnat]
  exact mul_comm _ _

theorem expected_uniformHashOutput_targetAssignmentCount {n : Nat} (views : Fin n → Option FewTimeView) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Admissible (truncateMessageDigest output) then (targetAssignmentCount views (hashOutputFewTimeView output) : ENNReal) else 0)) =
      (coverageOccupancyMoment views : ENNReal) * ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
  rw [expected_uniformHashOutput_admissible_weight (fun target : FewTimeView => (targetAssignmentCount views target : ENNReal)),
    expected_uniform_targetAssignmentCount, fewTimeView_card]
  have hrate : (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * ((2 ^ 166 : Nat) : ENNReal)⁻¹) =
      ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ftsTreeHeight]
  simpa only [totalHeight, ftsTreeHeight, ftsTrees, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd,
    div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
    congrArg (fun rate => (coverageOccupancyMoment views : ENNReal) * rate) hrate

end SphincsSecurity.Concrete
