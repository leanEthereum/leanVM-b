import SphincsSecurity.Proof.Base.BernoulliExcessMoments
import SphincsSecurity.Proof.Fts.CachedIndexHashMoments

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

theorem messageDeficit_secondMoment_le (score : ℝ) :
    (1 / 1024 : ℝ) * max (score - 1023) 0 ^ 2 +
      (1023 / 1024 : ℝ) * max (score + 1) 0 ^ 2 ≤ max score 0 ^ 2 + 1023 := by
  calc
    _ ≤ (1 / 1024 : ℝ) * (max score 0 - 1023) ^ 2 + (1023 / 1024 : ℝ) * (max score 0 + 1) ^ 2 := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (positivePart_shift_even_le score (-1023) 2 (by decide)) (by norm_num)
      · exact mul_le_mul_of_nonneg_left (positivePart_shift_even_le score 1 2 (by decide)) (by norm_num)
    _ = _ := by ring

theorem messageDeficit_secondMoment_ennreal (score : ℝ) :
    (1024 : ENNReal)⁻¹ * positiveScoreMoment (score - 1023) 2 +
      (1 - (1024 : ENNReal)⁻¹) * positiveScoreMoment (score + 1) 2 ≤ positiveScoreMoment score 2 + 1023 := by
  have hsub : (1 - (1024 : ENNReal)⁻¹).toReal = (1023 / 1024 : ℝ) := by
    rw [ENNReal.toReal_sub_of_le (by norm_num) (by finiteness)]
    norm_num [ENNReal.toReal_inv]
  apply (ENNReal.toReal_le_toReal (by unfold positiveScoreMoment; finiteness) (by unfold positiveScoreMoment; finiteness)).mp
  rw [ENNReal.toReal_add (by unfold positiveScoreMoment; finiteness) (by unfold positiveScoreMoment; finiteness),
    ENNReal.toReal_add (positiveScoreMoment_ne_top _ _) (by finiteness)]
  simpa only [ENNReal.toReal_mul, hsub, ENNReal.toReal_inv, ENNReal.toReal_ofNat, positiveScoreMoment,
    ENNReal.toReal_ofReal (pow_nonneg (le_max_right _ _) _), one_div] using messageDeficit_secondMoment_le score

end SphincsSecurity
