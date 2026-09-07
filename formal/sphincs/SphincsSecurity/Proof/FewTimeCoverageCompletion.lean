import SphincsSecurity.Proof.FewTimeConditionalCoverage

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def uncoveredFewTimeTrees {n : Nat} (views : Fin n → Option FewTimeView)
    (target : FewTimeView) : Finset FtsTree :=
  Finset.univ.filter (fun tree => ¬ ∃ slot view,
    views slot = some view ∧ view.1 = target.1 ∧ view.2 tree = target.2 tree)

def insertFewTimeView {n : Nat} (views : Fin n → Option FewTimeView) (source : FewTimeView) :
    Fin (n + 1) → Option FewTimeView := Fin.cons (some source) views

def CompletesFewTimeView {n : Nat} (views : Fin n → Option FewTimeView)
    (target source : FewTimeView) : Prop :=
  ¬ CoveredFewTimeView views target ∧ CoveredFewTimeView (insertFewTimeView views source) target

theorem coveredFewTimeView_insert_iff {n : Nat} (views : Fin n → Option FewTimeView)
    (target source : FewTimeView) (hnot : ¬ CoveredFewTimeView views target) :
    CoveredFewTimeView (insertFewTimeView views source) target ↔
      source.1 = target.1 ∧ ∀ tree ∈ uncoveredFewTimeTrees views target, source.2 tree = target.2 tree := by
  have hmissing : ∃ tree, tree ∈ uncoveredFewTimeTrees views target := by
    by_contra hnone
    apply hnot
    intro tree
    have htree : tree ∉ uncoveredFewTimeTrees views target := fun h => hnone ⟨tree, h⟩
    simpa only [uncoveredFewTimeTrees, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using htree
  constructor
  · intro hcover
    have hsource : ∀ tree ∈ uncoveredFewTimeTrees views target,
        source.1 = target.1 ∧ source.2 tree = target.2 tree := by
      intro tree htree
      obtain ⟨slot, view, hview, hindex, hleaf⟩ := hcover tree
      have hmissing := (Finset.mem_filter.mp htree).2
      cases slot using Fin.cases with
      | zero =>
        have heq : source = view := Option.some.inj hview
        exact heq ▸ ⟨hindex, hleaf⟩
      | succ old =>
        exact (hmissing ⟨old, view, hview, hindex, hleaf⟩).elim
    obtain ⟨tree, htree⟩ := hmissing
    exact ⟨(hsource tree htree).1, fun tree htree => (hsource tree htree).2⟩
  · rintro ⟨hindex, hleaves⟩ tree
    by_cases htree : tree ∈ uncoveredFewTimeTrees views target
    · exact ⟨0, source, rfl, hindex, hleaves tree htree⟩
    · have hold : ∃ slot view, views slot = some view ∧ view.1 = target.1 ∧ view.2 tree = target.2 tree := by
        simpa only [uncoveredFewTimeTrees, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using htree
      obtain ⟨slot, view, hview, hindex, hleaf⟩ := hold
      exact ⟨slot.succ, view, hview, hindex, hleaf⟩

def MatchesFewTimeTrees (target : FewTimeView) (required : Finset FtsTree) (source : FewTimeView) : Prop :=
  source.1 = target.1 ∧ ∀ tree ∈ required, source.2 tree = target.2 tree

private noncomputable def matchingFewTimeViewEquiv (target : FewTimeView) (required : Finset FtsTree) :
    {source // MatchesFewTimeTrees target required source} ≃ ({tree : FtsTree // tree ∉ required} → FtsLeaf) where
  toFun source := fun tree => source.1.2 tree.1
  invFun leaves := ⟨(target.1, fun tree => if h : tree ∈ required then target.2 tree else leaves ⟨tree, h⟩),
    rfl, fun tree htree => by simp only [dif_pos htree]⟩
  left_inv source := by
    apply Subtype.ext
    apply Prod.ext
    · exact source.2.1.symm
    · funext tree
      by_cases htree : tree ∈ required
      · simpa only [dif_pos htree] using (source.2.2 tree htree).symm
      · simp only [dif_neg htree]
  right_inv leaves := by
    funext tree
    simp only [dif_neg tree.2]

theorem matchingFewTimeView_card (target : FewTimeView) (required : Finset FtsTree) :
    Fintype.card {source // MatchesFewTimeTrees target required source} =
      (2 ^ ftsTreeHeight) ^ (ftsTrees - 1 - required.card) := by
  rw [Fintype.card_congr (matchingFewTimeViewEquiv target required)]
  simp only [Fintype.card_fun, Fintype.card_subtype_compl, Fintype.card_coe, FtsLeaf, FtsTree, Fintype.card_fin]

noncomputable def completionProbability {n : Nat} (views : Fin n → Option FewTimeView) (target : FewTimeView) : ENNReal :=
  if CoveredFewTimeView views target then 0 else
    (((2 ^ ftsTreeHeight) ^ (ftsTrees - 1 - (uncoveredFewTimeTrees views target).card) : Nat) : ENNReal) /
      (Fintype.card FewTimeView : ENNReal)

theorem completionProbability_eq {n : Nat} (views : Fin n → Option FewTimeView) (target : FewTimeView) :
    completionProbability views target = if CoveredFewTimeView views target then 0 else
      ((2 ^ (totalHeight + ftsTreeHeight * (uncoveredFewTimeTrees views target).card) : Nat) : ENNReal)⁻¹ := by
  rw [completionProbability]
  split_ifs with hcovered
  · rfl
  · have hcard : (uncoveredFewTimeTrees views target).card ≤ ftsTrees - 1 := by
      simpa only [FtsTree, Fintype.card_fin] using (uncoveredFewTimeTrees views target).card_le_univ
    have hexponent : ftsTreeHeight * (ftsTrees - 1 - (uncoveredFewTimeTrees views target).card) +
        (totalHeight + ftsTreeHeight * (uncoveredFewTimeTrees views target).card) =
          totalHeight + ftsTreeHeight * (ftsTrees - 1) := by
      simp only [ftsTreeHeight, ftsTrees, totalHeight] at *
      omega
    have hden : Fintype.card FewTimeView =
        (2 ^ ftsTreeHeight) ^ (ftsTrees - 1 - (uncoveredFewTimeTrees views target).card) *
          2 ^ (totalHeight + ftsTreeHeight * (uncoveredFewTimeTrees views target).card) := by
      rw [fewTimeView_card, ← pow_mul, ← pow_add, hexponent]
    rw [hden, Nat.cast_mul]
    apply Eq.symm
    apply (ENNReal.eq_div_iff (by positivity) (by finiteness)).mpr
    rw [mul_assoc, ENNReal.mul_inv_cancel (by positivity) (by finiteness), mul_one]

theorem probEvent_uniform_completesFewTimeView {n : Nat} (views : Fin n → Option FewTimeView) (target : FewTimeView) :
    Pr[CompletesFewTimeView views target | ($ᵗ FewTimeView : ProbComp FewTimeView)] = completionProbability views target := by
  by_cases hcovered : CoveredFewTimeView views target
  · rw [completionProbability, if_pos hcovered]
    exact probEvent_eq_zero (fun _ _ h => h.1 hcovered)
  · rw [completionProbability, if_neg hcovered]
    have hevent : CompletesFewTimeView views target = MatchesFewTimeTrees target (uncoveredFewTimeTrees views target) := by
      funext source
      apply propext
      simp only [CompletesFewTimeView, hcovered, not_false_eq_true, true_and, MatchesFewTimeTrees,
        coveredFewTimeView_insert_iff views target source hcovered]
    rw [hevent, probEvent_uniformSample, ← Fintype.card_subtype, matchingFewTimeView_card]

theorem probEvent_fresh_signer_completesFewTimeView_le {n : Nat}
    (views : Fin n → Option FewTimeView) (target : FewTimeView)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    Pr[FreshSuccessfulSignerView cache key message (CompletesFewTimeView views target) |
      (simulateQ romImpl (signWithView key message)).run cache] ≤ completionProbability views target := by
  exact (probEvent_signWithView_freshSuccessful_le_uniform key message cache _).trans_eq
    (probEvent_uniform_completesFewTimeView views target)

end SphincsSecurity.Concrete
