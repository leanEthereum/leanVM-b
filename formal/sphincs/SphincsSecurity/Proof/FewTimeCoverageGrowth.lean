import SphincsSecurity.Proof.FewTimeConditionalSignerCompletion

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem CoveredFewTimeView.insert {n : Nat} {views : Fin n → Option FewTimeView}
    {target : FewTimeView} (hcovered : CoveredFewTimeView views target) (source : FewTimeView) :
    CoveredFewTimeView (insertFewTimeView views source) target := by
  intro tree
  obtain ⟨slot, view, hview, hindex, hleaf⟩ := hcovered tree
  exact ⟨slot.succ, view, hview, hindex, hleaf⟩

theorem probEvent_uniform_covered_insert_eq {n : Nat}
    (views : Fin n → Option FewTimeView) (target : FewTimeView) :
    Pr[fun source => CoveredFewTimeView (insertFewTimeView views source) target | ($ᵗ FewTimeView : ProbComp FewTimeView)] =
      (if CoveredFewTimeView views target then 1 else 0) + completionProbability views target := by
  by_cases hcovered : CoveredFewTimeView views target
  · have hevent : (fun source => CoveredFewTimeView (insertFewTimeView views source) target) = (fun _ => True) := by
      funext source
      exact propext ⟨fun _ => trivial, fun _ => hcovered.insert source⟩
    rw [hevent, if_pos hcovered, completionProbability, if_pos hcovered]
    simp
  · have hevent : CompletesFewTimeView views target =
        (fun source => CoveredFewTimeView (insertFewTimeView views source) target) := by
      funext source
      simp only [CompletesFewTimeView, hcovered, not_false_eq_true, true_and]
    rw [if_neg hcovered, zero_add, ← hevent]
    exact probEvent_uniform_completesFewTimeView views target

noncomputable def coveredFewTimeTargetCount {α : Type} {n : Nat} (targets : Finset α)
    (views : α → Fin n → Option FewTimeView) (targetView : α → FewTimeView) : ENNReal :=
  ∑ target ∈ targets, if CoveredFewTimeView (views target) (targetView target) then 1 else 0

noncomputable def newlyCoveredFewTimeTargetCount {α : Type} {n : Nat} (targets : Finset α)
    (views : α → Fin n → Option FewTimeView) (targetView : α → FewTimeView) (source : FewTimeView) : ENNReal :=
  ∑ target ∈ targets, if CompletesFewTimeView (views target) (targetView target) source then 1 else 0

theorem coveredFewTimeTargetCount_insert_eq {α : Type} {n : Nat} (targets : Finset α)
    (views : α → Fin n → Option FewTimeView) (targetView : α → FewTimeView) (source : FewTimeView) :
    coveredFewTimeTargetCount targets (fun target => insertFewTimeView (views target) source) targetView =
      coveredFewTimeTargetCount targets views targetView + newlyCoveredFewTimeTargetCount targets views targetView source := by
  rw [coveredFewTimeTargetCount, coveredFewTimeTargetCount, newlyCoveredFewTimeTargetCount, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro target _
  by_cases hcovered : CoveredFewTimeView (views target) (targetView target)
  · simp only [hcovered.insert source, hcovered, CompletesFewTimeView, not_true_eq_false, false_and, if_false, if_true, add_zero]
  · simp only [hcovered, CompletesFewTimeView, not_false_eq_true, true_and, if_false, zero_add]

theorem expected_newlyCoveredFewTimeTargetCount_eq {α : Type} {n : Nat} (targets : Finset α)
    (views : α → Fin n → Option FewTimeView) (targetView : α → FewTimeView) :
    (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] * newlyCoveredFewTimeTargetCount targets views targetView source) =
      ∑ target ∈ targets, completionProbability (views target) (targetView target) := by
  simp_rw [newlyCoveredFewTimeTargetCount, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro target _
  simp only [mul_ite, mul_one, mul_zero, ← probEvent_eq_tsum_ite, probEvent_uniform_completesFewTimeView]

theorem expected_coveredFewTimeTargetCount_insert_eq {α : Type} {n : Nat} (targets : Finset α)
    (views : α → Fin n → Option FewTimeView) (targetView : α → FewTimeView) :
    (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
      coveredFewTimeTargetCount targets (fun target => insertFewTimeView (views target) source) targetView) =
        coveredFewTimeTargetCount targets views targetView + ∑ target ∈ targets, completionProbability (views target) (targetView target) := by
  simp_rw [coveredFewTimeTargetCount, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro target _
  simp only [mul_ite, mul_one, mul_zero, ← probEvent_eq_tsum_ite, probEvent_uniform_covered_insert_eq]

theorem probEvent_signer_completesSomeFewTimeTarget_le_expectedGrowth {α : Type} {n : Nat}
    (targets : Finset α) (views : α → Fin n → Option FewTimeView) (targetView : α → FewTimeView)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    Pr[SuccessfulSignerViewSatisfies (CompletesSomeFewTimeTarget targets views targetView) |
      (simulateQ romImpl (signWithView key message)).run cache] ≤
      (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] * newlyCoveredFewTimeTargetCount targets views targetView source) +
        cachedMessageEntryCountWhere cache key.parameter key.root message
          (CompletesSomeFewTimeTarget targets views targetView) * digestReuseWeight q := by
  rw [expected_newlyCoveredFewTimeTargetCount_eq]
  exact probEvent_signer_completesSomeFewTimeTarget_le targets views targetView key message cache q hq hcache

end SphincsSecurity.Concrete
