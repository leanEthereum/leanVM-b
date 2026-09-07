import SphincsSecurity.Proof.FutureCoverageIncrement

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def targetTreeMatchCount {n : Nat} (views : Fin n → Option FewTimeView) (target : FewTimeView) (tree : FtsTree) : Nat :=
  ∑ slot : Fin n, if ∃ view, views slot = some view ∧ view.1 = target.1 ∧ view.2 tree = target.2 tree then 1 else 0

noncomputable def sourceTreeMatch (target source : FewTimeView) (tree : FtsTree) : Nat :=
  if source.1 = target.1 ∧ source.2 tree = target.2 tree then 1 else 0

noncomputable def targetAssignmentCount {n : Nat} (views : Fin n → Option FewTimeView) (target : FewTimeView) : Nat :=
  ∏ tree : FtsTree, targetTreeMatchCount views target tree

theorem targetTreeMatchCount_pos_iff {n : Nat} (views : Fin n → Option FewTimeView) (target : FewTimeView) (tree : FtsTree) :
    0 < targetTreeMatchCount views target tree ↔ ∃ slot view, views slot = some view ∧ view.1 = target.1 ∧ view.2 tree = target.2 tree := by
  simp only [targetTreeMatchCount, Finset.sum_pos_iff, Finset.mem_univ, true_and]
  apply exists_congr
  intro slot
  split_ifs <;> simp_all

theorem targetAssignmentCount_pos_iff {n : Nat} (views : Fin n → Option FewTimeView) (target : FewTimeView) :
    0 < targetAssignmentCount views target ↔ CoveredFewTimeView views target := by
  rw [Nat.pos_iff_ne_zero]
  simp only [targetAssignmentCount, Finset.prod_ne_zero_iff, Finset.mem_univ, forall_true_left]
  simp only [← Nat.pos_iff_ne_zero, targetTreeMatchCount_pos_iff, CoveredFewTimeView]

theorem coveredFewTimeView_indicator_le_assignment {n : Nat} (views : Fin n → Option FewTimeView) (target : FewTimeView) :
    (if CoveredFewTimeView views target then (1 : ENNReal) else 0) ≤ (targetAssignmentCount views target : ENNReal) := by
  split_ifs with hcover
  · exact_mod_cast (targetAssignmentCount_pos_iff views target).mpr hcover
  · exact bot_le

theorem targetTreeMatchCount_insert {n : Nat} (views : Fin n → Option FewTimeView) (target source : FewTimeView) (tree : FtsTree) :
    targetTreeMatchCount (insertFewTimeView views source) target tree =
      targetTreeMatchCount views target tree + sourceTreeMatch target source tree := by
  unfold targetTreeMatchCount
  rw [Fin.sum_univ_succ]
  simp only [insertFewTimeView, Fin.cons_zero, Fin.cons_succ, Option.some.injEq, exists_eq_left']
  exact add_comm _ _

noncomputable def assignmentProductIncrement (counts additions : FtsTree → Nat) : Nat :=
  ∑ selected ∈ (Finset.univ : Finset FtsTree).powerset.erase ∅,
    (∏ tree ∈ selected, additions tree) * ∏ tree ∈ (Finset.univ : Finset FtsTree) \ selected, counts tree

theorem assignmentProduct_add_increment (counts additions : FtsTree → Nat) :
    (∏ tree, counts tree) + assignmentProductIncrement counts additions = ∏ tree, (counts tree + additions tree) := by
  rw [show (∏ tree, (counts tree + additions tree)) = ∏ tree, (additions tree + counts tree) by simp only [add_comm]]
  rw [Finset.prod_add]
  have hmem : (∅ : Finset FtsTree) ∈ (Finset.univ : Finset FtsTree).powerset := Finset.empty_mem_powerset _
  rw [← Finset.add_sum_erase _ _ hmem]
  simp only [Finset.prod_empty, Finset.sdiff_empty, one_mul, assignmentProductIncrement]

theorem assignmentProductIncrement_mono (additions : FtsTree → Nat) : Monotone (fun counts => assignmentProductIncrement counts additions) := by
  intro left right h
  apply Finset.sum_le_sum
  intro selected _
  exact Nat.mul_le_mul_left _ (Finset.prod_le_prod' (fun tree _ => h tree))

noncomputable def targetAssignmentIncrement {n : Nat} (views : Fin n → Option FewTimeView) (target source : FewTimeView) : Nat :=
  assignmentProductIncrement (targetTreeMatchCount views target) (sourceTreeMatch target source)

theorem targetAssignmentCount_add_increment {n : Nat} (views : Fin n → Option FewTimeView) (target source : FewTimeView) :
    targetAssignmentCount views target + targetAssignmentIncrement views target source =
      targetAssignmentCount (insertFewTimeView views source) target := by
  simp only [targetAssignmentCount, targetAssignmentIncrement, targetTreeMatchCount_insert]
  exact assignmentProduct_add_increment _ _

theorem targetAssignmentIncrement_mono {n m : Nat} (before : Fin n → Option FewTimeView) (after : Fin m → Option FewTimeView)
    (target source : FewTimeView) (hcounts : ∀ tree, targetTreeMatchCount before target tree ≤ targetTreeMatchCount after target tree) :
    targetAssignmentIncrement before target source ≤ targetAssignmentIncrement after target source :=
  assignmentProductIncrement_mono _ hcounts

theorem targetAssignmentIncrement_le_insert {n : Nat} (views : Fin n → Option FewTimeView) (target source next : FewTimeView) :
    targetAssignmentIncrement views target source ≤ targetAssignmentIncrement (insertFewTimeView views next) target source := by
  apply targetAssignmentIncrement_mono
  intro tree
  rw [targetTreeMatchCount_insert]
  exact Nat.le_add_right _ _

theorem completesFewTimeView_indicator_le_assignmentIncrement {n : Nat} (views : Fin n → Option FewTimeView)
    (target source : FewTimeView) :
    (if CompletesFewTimeView views target source then (1 : ENNReal) else 0) ≤ (targetAssignmentIncrement views target source : ENNReal) := by
  split_ifs with hcomplete
  · have hbefore : targetAssignmentCount views target = 0 := by
      have hnot : ¬ 0 < targetAssignmentCount views target := fun h => hcomplete.1 ((targetAssignmentCount_pos_iff views target).mp h)
      omega
    have hafter := (targetAssignmentCount_pos_iff (insertFewTimeView views source) target).mpr hcomplete.2
    rw [← targetAssignmentCount_add_increment, hbefore, Nat.zero_add] at hafter
    exact_mod_cast hafter
  · exact bot_le

end SphincsSecurity.Concrete
