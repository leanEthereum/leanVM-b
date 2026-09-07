import SphincsSecurity.Proof.FutureCoverage

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem remainingFewTimeTrees_comm (required : Finset FtsTree) (target first second : FewTimeView) :
    remainingFewTimeTrees (remainingFewTimeTrees required target first) target second =
      remainingFewTimeTrees (remainingFewTimeTrees required target second) target first := by
  ext tree
  simp only [remainingFewTimeTrees, Finset.mem_filter]
  tauto

theorem futureFewTimeCoverageIncrement_succ (remaining : Nat) (required : Finset FtsTree)
    (target source : FewTimeView) :
    futureFewTimeCoverageIncrement (remaining + 1) required target source =
      ∑' next, Pr[= next | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
        futureFewTimeCoverageIncrement remaining (remainingFewTimeTrees required target next) target source := by
  have hadd : futureFewTimeCoverage (remaining + 1) required target +
      (∑' next, Pr[= next | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
        futureFewTimeCoverageIncrement remaining (remainingFewTimeTrees required target next) target source) =
      futureFewTimeCoverage (remaining + 1) (remainingFewTimeTrees required target source) target := by
    calc
      _ = ∑' next, Pr[= next | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
          (futureFewTimeCoverage remaining (remainingFewTimeTrees required target next) target +
            futureFewTimeCoverageIncrement remaining (remainingFewTimeTrees required target next) target source) := by
        simp only [futureFewTimeCoverage, mul_add, ENNReal.tsum_add]
      _ = _ := by
        simp only [futureFewTimeCoverage_add_increment, futureFewTimeCoverage]
        apply tsum_congr
        intro next
        rw [remainingFewTimeTrees_comm required target next source]
  rw [futureFewTimeCoverageIncrement, ← hadd, ENNReal.add_sub_cancel_left
    (ne_top_of_le_ne_top (by simp) (futureFewTimeCoverage_le_one (remaining + 1) required target))]

theorem expected_target_futureCoverageIncrement_succ {n : Nat} (views : Fin n → Option FewTimeView)
    (remaining : Nat) (source : FewTimeView) :
    (∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
      futureFewTimeCoverageIncrement (remaining + 1) (uncoveredFewTimeTrees views target) target source) =
      ∑' next, Pr[= next | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
        ∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
          futureFewTimeCoverageIncrement remaining (uncoveredFewTimeTrees (insertFewTimeView views next) target) target source := by
  simp only [futureFewTimeCoverageIncrement_succ, ← uncoveredFewTimeTrees_insert, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro next
  apply tsum_congr
  intro target
  rw [mul_left_comm]

end SphincsSecurity.Concrete
