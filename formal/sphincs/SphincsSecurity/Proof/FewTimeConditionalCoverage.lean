import SphincsSecurity.Proof.FewTimeFresh

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def CoveredFewTimeView {n : Nat} (views : Fin n → Option FewTimeView) (target : FewTimeView) : Prop :=
  ∀ tree, ∃ slot view, views slot = some view ∧ view.1 = target.1 ∧ view.2 tree = target.2 tree

noncomputable def signingSlotsAtIndex {n : Nat} (views : Fin n → Option FewTimeView) (index : Index) : Finset (Fin n) :=
  Finset.univ.filter (fun slot => ∃ view, views slot = some view ∧ view.1 = index)

noncomputable def coverageOccupancyMoment {n : Nat} (views : Fin n → Option FewTimeView) : Nat :=
  ∑ index : Index, (signingSlotsAtIndex views index).card ^ (ftsTrees - 1)

private noncomputable def assignedCoveredView {n : Nat} (views : Fin n → Option FewTimeView)
    (assignment : Σ index : Index, FtsTree → signingSlotsAtIndex views index) : {target // CoveredFewTimeView views target} := by
  refine ⟨(assignment.1, fun tree => ((views (assignment.2 tree).1).getD default).2 tree), ?_⟩
  intro tree
  obtain ⟨view, hview, hindex⟩ := (Finset.mem_filter.mp (assignment.2 tree).2).2
  exact ⟨(assignment.2 tree).1, view, hview, hindex, by simp [hview]⟩

private theorem assignedCoveredView_surjective {n : Nat} (views : Fin n → Option FewTimeView) :
    Function.Surjective (assignedCoveredView views) := by
  intro target
  choose slot view hview hindex hleaf using target.2
  let assignment : FtsTree → signingSlotsAtIndex views target.1.1 := fun tree =>
    ⟨slot tree, Finset.mem_filter.mpr ⟨Finset.mem_univ _, view tree, hview tree, hindex tree⟩⟩
  refine ⟨⟨target.1.1, assignment⟩, Subtype.ext ?_⟩
  apply Prod.ext
  · rfl
  · funext tree
    change ((views (slot tree)).getD default).2 tree = target.1.2 tree
    simpa only [hview tree, Option.getD_some] using hleaf tree

theorem coveredFewTimeView_card_le_occupancy {n : Nat} (views : Fin n → Option FewTimeView) :
    Fintype.card {target // CoveredFewTimeView views target} ≤ coverageOccupancyMoment views := by
  calc
    _ ≤ Fintype.card (Σ index : Index, FtsTree → signingSlotsAtIndex views index) :=
      Fintype.card_le_of_surjective (assignedCoveredView views) (assignedCoveredView_surjective views)
    _ = _ := by simp [coverageOccupancyMoment, FtsTree]

theorem probEvent_uniform_coveredFewTimeView_le_occupancy {n : Nat} (views : Fin n → Option FewTimeView) :
    Pr[CoveredFewTimeView views | ($ᵗ FewTimeView : ProbComp FewTimeView)] ≤
      (coverageOccupancyMoment views : ENNReal) / (Fintype.card FewTimeView : ENNReal) := by
  rw [probEvent_uniformSample, ← Fintype.card_subtype (CoveredFewTimeView views)]
  simp only [div_eq_mul_inv]
  exact mul_le_mul' (Nat.cast_le.mpr (coveredFewTimeView_card_le_occupancy views)) le_rfl

theorem probEvent_uniformHashOutput_covered_le_occupancy {n : Nat} (views : Fin n → Option FewTimeView) :
    Pr[fun output => Admissible (truncateMessageDigest output) ∧ CoveredFewTimeView views (hashOutputFewTimeView output) |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      (coverageOccupancyMoment views : ENNReal) * ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
  simp_rw [← signAttemptResultOfOutput_ne_none_iff]
  rw [probEvent_uniformHashOutput_admissible_view]
  apply (mul_le_mul' le_rfl (probEvent_uniform_coveredFewTimeView_le_occupancy views)).trans_eq
  rw [fewTimeView_card]
  have hrate : (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * ((2 ^ 166 : Nat) : ENNReal)⁻¹) =
      ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ftsTreeHeight]
  simpa only [totalHeight, ftsTreeHeight, ftsTrees, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd,
    div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
    congrArg (fun rate => (coverageOccupancyMoment views : ENNReal) * rate) hrate

end SphincsSecurity.Concrete
