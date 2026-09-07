import SphincsSecurity.Proof.FutureCoverageIncrement
import SphincsSecurity.Proof.OccupancyCompletionIncrement
import SphincsSecurity.Proof.FewTimeTargetIncrementBound

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem expected_uniform_futureCoverageIncrement_le {n : Nat} (views : Fin n → Option FewTimeView)
    (remaining : Nat) (source : FewTimeView) :
    (∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
      futureFewTimeCoverageIncrement remaining (uncoveredFewTimeTrees views target) target source) ≤
      coverageOccupancyCompletionIncrement views remaining source / (Fintype.card FewTimeView : ENNReal) := by
  induction remaining generalizing n with
  | zero =>
      rw [coverageOccupancyCompletionIncrement_zero]
      exact expected_uniform_futureCoverageIncrement_zero_le views source
  | succ remaining ih =>
      rw [expected_target_futureCoverageIncrement_succ]
      calc
        _ ≤ ∑' next, Pr[= next | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
            (coverageOccupancyCompletionIncrement (insertFewTimeView views next) remaining source /
              (Fintype.card FewTimeView : ENNReal)) :=
          ENNReal.tsum_le_tsum (fun next => mul_le_mul' le_rfl (ih (insertFewTimeView views next)))
        _ = _ := by
          simp only [div_eq_mul_inv, ← mul_assoc, ENNReal.tsum_mul_right,
            expected_coverageOccupancyCompletionIncrement_insert]

theorem expected_uniformHashOutput_futureCoverageIncrement_le {n : Nat} (views : Fin n → Option FewTimeView)
    (remaining : Nat) (source : FewTimeView) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Admissible (truncateMessageDigest output) then
        futureFewTimeCoverageIncrement remaining (uncoveredFewTimeTrees views (hashOutputFewTimeView output))
          (hashOutputFewTimeView output) source else 0)) ≤
      coverageOccupancyCompletionIncrement views remaining source * ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
  rw [expected_uniformHashOutput_admissible_weight
    (fun target => futureFewTimeCoverageIncrement remaining (uncoveredFewTimeTrees views target) target source)]
  apply (mul_le_mul' le_rfl (expected_uniform_futureCoverageIncrement_le views remaining source)).trans_eq
  have hrate : ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card FewTimeView : ENNReal)⁻¹ =
      ((2 ^ 176 : Nat) : ENNReal)⁻¹ := by
    rw [fewTimeView_card]
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ftsTreeHeight, totalHeight, ftsTrees]
  rw [div_eq_mul_inv, mul_left_comm, hrate]

end SphincsSecurity.Concrete
