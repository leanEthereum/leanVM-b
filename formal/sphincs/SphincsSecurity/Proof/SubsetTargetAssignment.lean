import SphincsSecurity.Proof.TargetAssignmentCount

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def sourceSubsetMatch (target source : FewTimeView) (required : Finset FtsTree) : Nat :=
  ∏ tree ∈ required, sourceTreeMatch target source tree

noncomputable def partialTargetAssignmentCount {n : Nat} (views : Fin n → Option FewTimeView)
    (target : FewTimeView) (required : Finset FtsTree) : Nat :=
  ∏ tree ∈ required, targetTreeMatchCount views target tree

noncomputable def partialTargetAssignmentIncrement {n : Nat} (views : Fin n → Option FewTimeView)
    (target source : FewTimeView) (required : Finset FtsTree) : Nat :=
  ∑ selected ∈ required.powerset.erase ∅,
    sourceSubsetMatch target source selected * partialTargetAssignmentCount views target (required \ selected)

theorem partialTargetAssignmentCount_univ {n : Nat} (views : Fin n → Option FewTimeView) (target : FewTimeView) :
    partialTargetAssignmentCount views target Finset.univ = targetAssignmentCount views target := rfl

theorem partialTargetAssignmentIncrement_univ {n : Nat} (views : Fin n → Option FewTimeView) (target source : FewTimeView) :
    partialTargetAssignmentIncrement views target source Finset.univ = targetAssignmentIncrement views target source := rfl

theorem partialTargetAssignmentCount_add_increment {n : Nat} (views : Fin n → Option FewTimeView)
    (target source : FewTimeView) (required : Finset FtsTree) :
    partialTargetAssignmentCount views target required + partialTargetAssignmentIncrement views target source required =
      partialTargetAssignmentCount (insertFewTimeView views source) target required := by
  simp only [partialTargetAssignmentCount, targetTreeMatchCount_insert]
  rw [show (∏ tree ∈ required, (targetTreeMatchCount views target tree + sourceTreeMatch target source tree)) =
    ∏ tree ∈ required, (sourceTreeMatch target source tree + targetTreeMatchCount views target tree) by simp only [add_comm]]
  rw [Finset.prod_add, ← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset required)]
  simp only [Finset.prod_empty, Finset.sdiff_empty, one_mul, partialTargetAssignmentIncrement,
    sourceSubsetMatch, partialTargetAssignmentCount]

theorem partialTargetAssignmentCount_mono {n m : Nat} (before : Fin n → Option FewTimeView)
    (after : Fin m → Option FewTimeView) (target : FewTimeView) (required : Finset FtsTree)
    (hcounts : ∀ tree, targetTreeMatchCount before target tree ≤ targetTreeMatchCount after target tree) :
    partialTargetAssignmentCount before target required ≤ partialTargetAssignmentCount after target required :=
  Finset.prod_le_prod' (fun tree _ => hcounts tree)

theorem partialTargetAssignmentIncrement_mono {n m : Nat} (before : Fin n → Option FewTimeView)
    (after : Fin m → Option FewTimeView) (target source : FewTimeView) (required : Finset FtsTree)
    (hcounts : ∀ tree, targetTreeMatchCount before target tree ≤ targetTreeMatchCount after target tree) :
    partialTargetAssignmentIncrement before target source required ≤ partialTargetAssignmentIncrement after target source required := by
  apply Finset.sum_le_sum
  intro selected _
  exact Nat.mul_le_mul_left _ (partialTargetAssignmentCount_mono before after target _ hcounts)

theorem partialTargetAssignmentIncrement_empty {n : Nat} (views : Fin n → Option FewTimeView) (target source : FewTimeView) :
    partialTargetAssignmentIncrement views target source ∅ = 0 := by
  simp [partialTargetAssignmentIncrement]

theorem partialTargetAssignmentIncrement_degree_decreases (required selected : Finset FtsTree)
    (hselected : selected ∈ required.powerset.erase ∅) : (required \ selected).card < required.card := by
  obtain ⟨hne, hsub⟩ := Finset.mem_erase.mp hselected
  have hsubset := Finset.mem_powerset.mp hsub
  rw [Finset.card_sdiff_of_subset hsubset]
  have hpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
  have hle := Finset.card_le_card hsubset
  omega

theorem sourceTreeMatch_mul_self (target source : FewTimeView) (tree : FtsTree) :
    sourceTreeMatch target source tree * sourceTreeMatch target source tree = sourceTreeMatch target source tree := by
  unfold sourceTreeMatch
  split_ifs <;> decide

theorem sourceSubsetMatch_mul (target source : FewTimeView) (left right : Finset FtsTree) :
    sourceSubsetMatch target source left * sourceSubsetMatch target source right =
      sourceSubsetMatch target source (left ∪ right) := by
  induction left using Finset.induction_on with
  | empty => simp [sourceSubsetMatch]
  | @insert tree left hnot ih =>
      by_cases hright : tree ∈ right
      · rw [Finset.insert_union, Finset.insert_eq_of_mem (Finset.mem_union_right left hright)]
        simp only [sourceSubsetMatch, Finset.prod_insert hnot] at *
        rw [mul_assoc, ih]
        have hmem : tree ∈ left ∪ right := Finset.mem_union_right left hright
        rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem hmem, ← mul_assoc, sourceTreeMatch_mul_self]
      · have hnotunion : tree ∉ left ∪ right := by simp only [Finset.mem_union, not_or]; exact ⟨hnot, hright⟩
        simp only [sourceSubsetMatch, Finset.prod_insert hnot, Finset.insert_union,
          Finset.prod_insert hnotunion] at *
        rw [mul_assoc, ih]

end SphincsSecurity.Concrete
