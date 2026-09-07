import SphincsSecurity.Proof.FewTimeCoverageGrowth

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def remainingFewTimeTrees (required : Finset FtsTree)
    (target source : FewTimeView) : Finset FtsTree :=
  required.filter (fun tree => ¬ (source.1 = target.1 ∧ source.2 tree = target.2 tree))

theorem remainingFewTimeTrees_subset (required : Finset FtsTree) (target source : FewTimeView) :
    remainingFewTimeTrees required target source ⊆ required := Finset.filter_subset _ _

theorem remainingFewTimeTrees_mono {a b : Finset FtsTree} (h : a ⊆ b)
    (target source : FewTimeView) :
    remainingFewTimeTrees a target source ⊆ remainingFewTimeTrees b target source :=
  Finset.filter_subset_filter _ h

theorem uncoveredFewTimeTrees_eq_empty_iff {n : Nat} (views : Fin n → Option FewTimeView)
    (target : FewTimeView) : uncoveredFewTimeTrees views target = ∅ ↔ CoveredFewTimeView views target := by
  simp [uncoveredFewTimeTrees, Finset.filter_eq_empty_iff, CoveredFewTimeView]

theorem uncoveredFewTimeTrees_insert {n : Nat} (views : Fin n → Option FewTimeView)
    (target source : FewTimeView) :
    uncoveredFewTimeTrees (insertFewTimeView views source) target =
      remainingFewTimeTrees (uncoveredFewTimeTrees views target) target source := by
  ext tree
  simp only [uncoveredFewTimeTrees, remainingFewTimeTrees, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    exact ⟨fun ⟨slot, view, hview, hi, hl⟩ => h ⟨slot.succ, view, hview, hi, hl⟩,
      fun ⟨hi, hl⟩ => h ⟨0, source, rfl, hi, hl⟩⟩
  · rintro ⟨hold, hsource⟩ ⟨slot, view, hview, hi, hl⟩
    cases slot using Fin.cases with
    | zero =>
        have heq : source = view := Option.some.inj hview
        exact hsource (heq ▸ ⟨hi, hl⟩)
    | succ slot => exact hold ⟨slot, view, hview, hi, hl⟩

noncomputable def futureFewTimeCoverage : Nat → Finset FtsTree → FewTimeView → ENNReal
  | 0, required, _ => if required = ∅ then 1 else 0
  | remaining + 1, required, target =>
      ∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
        futureFewTimeCoverage remaining (remainingFewTimeTrees required target source) target

theorem futureFewTimeCoverage_le_one (remaining : Nat) (required : Finset FtsTree)
    (target : FewTimeView) : futureFewTimeCoverage remaining required target ≤ 1 := by
  induction remaining generalizing required with
  | zero => simp only [futureFewTimeCoverage]; split_ifs <;> simp
  | succ remaining ih =>
      unfold futureFewTimeCoverage
      calc
        _ ≤ ∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] * 1 :=
          ENNReal.tsum_le_tsum (fun source => mul_le_mul' le_rfl (ih _))
        _ ≤ 1 := by simpa only [mul_one] using (tsum_probOutput_le_one (mx := ($ᵗ FewTimeView : ProbComp FewTimeView)))

theorem futureFewTimeCoverage_antitone (remaining : Nat) {a b : Finset FtsTree}
    (h : a ⊆ b) (target : FewTimeView) :
    futureFewTimeCoverage remaining b target ≤ futureFewTimeCoverage remaining a target := by
  induction remaining generalizing a b with
  | zero =>
      simp only [futureFewTimeCoverage]
      by_cases hb : b = ∅
      · have ha : a = ∅ := Finset.subset_empty.mp (hb ▸ h)
        simp only [ha, hb, if_true, le_refl]
      · simp only [hb, if_false, zero_le]
  | succ remaining ih =>
      exact ENNReal.tsum_le_tsum (fun source =>
        mul_le_mul' le_rfl (ih (remainingFewTimeTrees_mono h target source)))

theorem futureFewTimeCoverage_le_after_source (remaining : Nat) (required : Finset FtsTree)
    (target source : FewTimeView) :
    futureFewTimeCoverage remaining required target ≤
      futureFewTimeCoverage remaining (remainingFewTimeTrees required target source) target :=
  futureFewTimeCoverage_antitone remaining (remainingFewTimeTrees_subset required target source) target

noncomputable def futureFewTimeCoverageIncrement (remaining : Nat) (required : Finset FtsTree)
    (target source : FewTimeView) : ENNReal :=
  futureFewTimeCoverage remaining (remainingFewTimeTrees required target source) target -
    futureFewTimeCoverage remaining required target

theorem futureFewTimeCoverage_add_increment (remaining : Nat) (required : Finset FtsTree)
    (target source : FewTimeView) :
    futureFewTimeCoverage remaining required target + futureFewTimeCoverageIncrement remaining required target source =
      futureFewTimeCoverage remaining (remainingFewTimeTrees required target source) target :=
  add_tsub_cancel_of_le (futureFewTimeCoverage_le_after_source remaining required target source)

theorem expected_futureFewTimeCoverageIncrement (remaining : Nat) (required : Finset FtsTree)
    (target : FewTimeView) :
    futureFewTimeCoverage remaining required target +
      (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
        futureFewTimeCoverageIncrement remaining required target source) =
      futureFewTimeCoverage (remaining + 1) required target := by
  have hmass : (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)]) = 1 :=
    tsum_probOutput_eq_one' (by simp)
  conv_rhs =>
    unfold futureFewTimeCoverage
    arg 1
    ext source
    rw [← futureFewTimeCoverage_add_increment remaining required target source, mul_add]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul]

theorem futureFewTimeCoverage_mono (required : Finset FtsTree) (target : FewTimeView) :
    Monotone (fun remaining => futureFewTimeCoverage remaining required target) := by
  apply monotone_nat_of_le_succ
  intro remaining
  rw [← expected_futureFewTimeCoverageIncrement]
  exact le_self_add

theorem futureFewTimeCoverage_empty (remaining : Nat) (target : FewTimeView) :
    futureFewTimeCoverage remaining ∅ target = 1 := by
  induction remaining with
  | zero => simp only [futureFewTimeCoverage, if_true]
  | succ remaining ih =>
      simp only [futureFewTimeCoverage, remainingFewTimeTrees, Finset.filter_empty, ih, mul_one]
      exact tsum_probOutput_eq_one' (by simp)

theorem futureFewTimeCoverage_zero {n : Nat} (views : Fin n → Option FewTimeView)
    (target : FewTimeView) :
    futureFewTimeCoverage 0 (uncoveredFewTimeTrees views target) target =
      if CoveredFewTimeView views target then 1 else 0 := by
  simp only [futureFewTimeCoverage, uncoveredFewTimeTrees_eq_empty_iff]

theorem futureFewTimeCoverage_one {n : Nat} (views : Fin n → Option FewTimeView)
    (target : FewTimeView) :
    futureFewTimeCoverage 1 (uncoveredFewTimeTrees views target) target =
      (if CoveredFewTimeView views target then 1 else 0) + completionProbability views target := by
  simp only [futureFewTimeCoverage, ← uncoveredFewTimeTrees_insert,
    uncoveredFewTimeTrees_eq_empty_iff, mul_ite, mul_one, mul_zero, ← probEvent_eq_tsum_ite]
  exact probEvent_uniform_covered_insert_eq views target

end SphincsSecurity.Concrete
