import SphincsSecurity.Proof.FewTimeConditionalCoverage

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def coveredLeavesAtIndex {n : Nat} (views : Fin n → Option FewTimeView)
    (index : Index) (tree : FtsTree) : Finset FtsLeaf :=
  (signingSlotsAtIndex views index).image (fun slot => ((views slot).getD default).2 tree)

theorem mem_coveredLeavesAtIndex_iff {n : Nat} (views : Fin n → Option FewTimeView)
    (index : Index) (tree : FtsTree) (leaf : FtsLeaf) :
    leaf ∈ coveredLeavesAtIndex views index tree ↔
      ∃ slot view, views slot = some view ∧ view.1 = index ∧ view.2 tree = leaf := by
  constructor
  · intro h
    obtain ⟨slot, hs, hl⟩ := Finset.mem_image.mp h
    obtain ⟨view, hv, hi⟩ := (Finset.mem_filter.mp hs).2
    exact ⟨slot, view, hv, hi, by simpa only [hv, Option.getD_some] using hl⟩
  · rintro ⟨slot, view, hv, hi, hl⟩
    exact Finset.mem_image.mpr ⟨slot, Finset.mem_filter.mpr ⟨Finset.mem_univ _, view, hv, hi⟩,
      by simpa only [hv, Option.getD_some] using hl⟩

noncomputable def coveredFewTimeViewEquiv {n : Nat} (views : Fin n → Option FewTimeView) :
    {target // CoveredFewTimeView views target} ≃
      Σ index : Index, (tree : FtsTree) → coveredLeavesAtIndex views index tree where
  toFun target := ⟨target.1.1, fun tree => ⟨target.1.2 tree,
    (mem_coveredLeavesAtIndex_iff views _ _ _).mpr (target.2 tree)⟩⟩
  invFun leaves := ⟨(leaves.1, fun tree => (leaves.2 tree).1), fun tree =>
    (mem_coveredLeavesAtIndex_iff views _ _ _).mp (leaves.2 tree).2⟩
  left_inv target := by rfl
  right_inv leaves := by rfl

noncomputable def distinctCoverageCount {n : Nat} (views : Fin n → Option FewTimeView) : Nat :=
  ∑ index : Index, ∏ tree : FtsTree, (coveredLeavesAtIndex views index tree).card

theorem coveredFewTimeView_card_eq_distinct {n : Nat} (views : Fin n → Option FewTimeView) :
    Fintype.card {target // CoveredFewTimeView views target} = distinctCoverageCount views := by
  rw [Fintype.card_congr (coveredFewTimeViewEquiv views)]
  simp only [Fintype.card_sigma, Fintype.card_pi, Fintype.card_coe, distinctCoverageCount]

theorem distinctCoverageCount_le_occupancy {n : Nat} (views : Fin n → Option FewTimeView) :
    distinctCoverageCount views ≤ coverageOccupancyMoment views := by
  rw [← coveredFewTimeView_card_eq_distinct]
  exact coveredFewTimeView_card_le_occupancy views

theorem probEvent_uniformHashOutput_covered_eq_distinct {n : Nat} (views : Fin n → Option FewTimeView) :
    Pr[fun output => Admissible (truncateMessageDigest output) ∧ CoveredFewTimeView views (hashOutputFewTimeView output) |
      ($ᵗ HashOutput : ProbComp HashOutput)] =
      (distinctCoverageCount views : ENNReal) * ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
  simp_rw [← signAttemptResultOfOutput_ne_none_iff]
  rw [probEvent_uniformHashOutput_admissible_view, probEvent_uniformSample,
    ← Fintype.card_subtype (CoveredFewTimeView views), coveredFewTimeView_card_eq_distinct, fewTimeView_card]
  have hrate : (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * ((2 ^ 166 : Nat) : ENNReal)⁻¹) =
      ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ftsTreeHeight]
  simpa only [totalHeight, ftsTreeHeight, ftsTrees, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd,
    div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
    congrArg (fun rate => (distinctCoverageCount views : ENNReal) * rate) hrate

def distinctViewsAtIndex (index : Index) (n : Nat) (hn : n ≤ 2 ^ ftsTreeHeight) : Fin n → Option FewTimeView :=
  fun slot => some (index, fun _ => ⟨slot.val, slot.isLt.trans_le hn⟩)

theorem distinctCoverageCount_distinctViewsAtIndex (index : Index) (n : Nat) (hn : n ≤ 2 ^ ftsTreeHeight) :
    distinctCoverageCount (distinctViewsAtIndex index n hn) = n ^ (ftsTrees - 1) := by
  have hleaf : Function.Injective (fun slot : Fin n => (⟨slot.val, slot.isLt.trans_le hn⟩ : FtsLeaf)) := by
    intro first second h
    exact Fin.ext (congrArg (fun leaf : FtsLeaf => leaf.val) h)
  unfold distinctCoverageCount
  rw [Finset.sum_eq_single index]
  · simp [coveredLeavesAtIndex, signingSlotsAtIndex, distinctViewsAtIndex,
      Finset.card_image_of_injective _ hleaf, FtsTree]
  · intro other _ hother
    simp [coveredLeavesAtIndex, signingSlotsAtIndex, distinctViewsAtIndex, Ne.symm hother, FtsTree, ftsTrees]
  · simp

theorem uniform_coverage_twelve_gt_127 (index : Index) :
    ((2 ^ 127 : Nat) : ENNReal)⁻¹ <
      Pr[fun output => Admissible (truncateMessageDigest output) ∧
        CoveredFewTimeView (distinctViewsAtIndex index 12 (by norm_num [ftsTreeHeight])) (hashOutputFewTimeView output) |
        ($ᵗ HashOutput : ProbComp HashOutput)] := by
  rw [probEvent_uniformHashOutput_covered_eq_distinct, distinctCoverageCount_distinctViewsAtIndex]
  apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ftsTrees]

end SphincsSecurity.Concrete
