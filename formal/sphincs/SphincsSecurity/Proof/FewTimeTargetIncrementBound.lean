import SphincsSecurity.Proof.FewTimeOccupancyGrowth
import SphincsSecurity.Proof.FutureCoverage

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

private noncomputable def allSomeAssignmentEquiv (ι α : Type) :
    {assignment : ι → Option α // ¬ ∃ index, assignment index = none} ≃ (ι → α) where
  toFun assignment index := ((Option.ne_none_iff_exists').mp (fun h => assignment.2 ⟨index, h⟩)).choose
  invFun assignment := ⟨fun index => some (assignment index), by simp⟩
  left_inv assignment := by
    apply Subtype.ext
    funext index
    exact ((Option.ne_none_iff_exists').mp (fun h => assignment.2 ⟨index, h⟩)).choose_spec.symm
  right_inv assignment := by
    funext index
    exact Option.some.inj ((Option.ne_none_iff_exists').mp
      (show (some (assignment index) : Option α) ≠ none by simp)).choose_spec.symm

private theorem assignmentWithNone_card (ι α : Type) [Fintype ι] [Fintype α] :
    Nat.card {assignment : ι → Option α // ∃ index, assignment index = none} =
      (Fintype.card α + 1) ^ Fintype.card ι - Fintype.card α ^ Fintype.card ι := by
  have hsome := Fintype.card_congr (allSomeAssignmentEquiv ι α)
  have hcompl := Fintype.card_subtype_compl (fun assignment : ι → Option α => ¬ ∃ index, assignment index = none)
  simpa only [Nat.card_eq_fintype_card, not_not, hsome, Fintype.card_fun, Fintype.card_option] using hcompl

private noncomputable def assignedTargetLeaf {n : Nat} (views : Fin n → Option FewTimeView)
    (source : FewTimeView) (assignment : FtsTree → Option (signingSlotsAtIndex views source.1)) (tree : FtsTree) : FtsLeaf :=
  match assignment tree with
  | none => source.2 tree
  | some slot => ((views slot.1).getD default).2 tree

private theorem exists_newlyCoveredAssignment {n : Nat} (views : Fin n → Option FewTimeView)
    (source target : FewTimeView) (hcomplete : CompletesFewTimeView views target source) :
    ∃ assignment : {assignment : FtsTree → Option (signingSlotsAtIndex views source.1) // ∃ tree, assignment tree = none},
      target = (source.1, assignedTargetLeaf views source assignment.1) := by
  have hindex := ((coveredFewTimeView_insert_iff views target source hcomplete.1).mp hcomplete.2).1
  have hchoices (tree : FtsTree) : ∃ slot : Option (signingSlotsAtIndex views source.1),
      (match slot with
       | none => source.2 tree
       | some slot => ((views slot.1).getD default).2 tree) = target.2 tree := by
    obtain ⟨slot, view, hview, hi, hl⟩ := hcomplete.2 tree
    cases slot using Fin.cases with
    | zero =>
        have heq : source = view := Option.some.inj hview
        exact ⟨none, heq ▸ hl⟩
    | succ slot =>
        have hold : views slot = some view := hview
        have hslot : slot ∈ signingSlotsAtIndex views source.1 :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, view, hold, hi.trans hindex.symm⟩
        exact ⟨some ⟨slot, hslot⟩, by simpa only [hold, Option.getD_some] using hl⟩
  choose assignment hleaf using hchoices
  have hnone : ∃ tree, assignment tree = none := by
    by_contra hnone
    apply hcomplete.1
    intro tree
    cases hslot : assignment tree with
    | none => exact (hnone ⟨tree, hslot⟩).elim
    | some slot =>
        obtain ⟨view, hview, hi⟩ := (Finset.mem_filter.mp slot.2).2
        refine ⟨slot.1, view, hview, hi.trans hindex, ?_⟩
        simpa only [hslot, hview, Option.getD_some] using hleaf tree
  refine ⟨⟨assignment, hnone⟩, Prod.ext hindex.symm ?_⟩
  funext tree
  exact (hleaf tree).symm

theorem newlyCoveredFewTimeView_card_le_increment {n : Nat} (views : Fin n → Option FewTimeView)
    (source : FewTimeView) :
    Fintype.card {target // CompletesFewTimeView views target source} ≤ occupancyIncrementAtIndex views source.1 := by
  let assignment := fun target : {target // CompletesFewTimeView views target source} =>
    (exists_newlyCoveredAssignment views source target.1 target.2).choose
  have hinjective : Function.Injective assignment := by
    intro first second heq
    apply Subtype.ext
    exact (exists_newlyCoveredAssignment views source first.1 first.2).choose_spec.trans
      ((congrArg (fun selected : {a : FtsTree → Option (signingSlotsAtIndex views source.1) // ∃ tree, a tree = none} =>
          (source.1, assignedTargetLeaf views source selected.1)) heq).trans
        (exists_newlyCoveredAssignment views source second.1 second.2).choose_spec.symm)
  calc
    _ ≤ Fintype.card {a : FtsTree → Option (signingSlotsAtIndex views source.1) // ∃ tree, a tree = none} :=
      Fintype.card_le_of_injective assignment hinjective
    _ = occupancyIncrementAtIndex views source.1 := by
      have htrees : Fintype.card FtsTree = ftsTrees - 1 := Fintype.card_fin _
      simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, htrees, occupancyIncrementAtIndex] using
        assignmentWithNone_card FtsTree (signingSlotsAtIndex views source.1)

theorem probEvent_uniform_newlyCoveredFewTimeView_le_increment {n : Nat} (views : Fin n → Option FewTimeView)
    (source : FewTimeView) :
    Pr[fun target => CompletesFewTimeView views target source | ($ᵗ FewTimeView : ProbComp FewTimeView)] ≤
      (occupancyIncrementAtIndex views source.1 : ENNReal) / (Fintype.card FewTimeView : ENNReal) := by
  rw [probEvent_uniformSample, ← Fintype.card_subtype]
  exact mul_le_mul' (Nat.cast_le.mpr (newlyCoveredFewTimeView_card_le_increment views source)) le_rfl

theorem futureFewTimeCoverageIncrement_zero_eq {n : Nat} (views : Fin n → Option FewTimeView)
    (target source : FewTimeView) :
    futureFewTimeCoverageIncrement 0 (uncoveredFewTimeTrees views target) target source =
      if CompletesFewTimeView views target source then 1 else 0 := by
  simp only [futureFewTimeCoverageIncrement, ← uncoveredFewTimeTrees_insert, futureFewTimeCoverage_zero]
  by_cases hcovered : CoveredFewTimeView views target
  · simp only [hcovered, hcovered.insert source, if_true, tsub_self, CompletesFewTimeView,
      not_true_eq_false, false_and, if_false]
  · simp only [hcovered, if_false, tsub_zero, CompletesFewTimeView, not_false_eq_true, true_and]

theorem expected_uniform_futureCoverageIncrement_zero_le {n : Nat} (views : Fin n → Option FewTimeView)
    (source : FewTimeView) :
    (∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
      futureFewTimeCoverageIncrement 0 (uncoveredFewTimeTrees views target) target source) ≤
      (occupancyIncrementAtIndex views source.1 : ENNReal) / (Fintype.card FewTimeView : ENNReal) := by
  simp only [futureFewTimeCoverageIncrement_zero_eq, mul_ite, mul_one, mul_zero, ← probEvent_eq_tsum_ite]
  exact probEvent_uniform_newlyCoveredFewTimeView_le_increment views source

end SphincsSecurity.Concrete
