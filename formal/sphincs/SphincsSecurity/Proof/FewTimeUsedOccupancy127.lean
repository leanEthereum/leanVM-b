import SphincsSecurity.Proof.FewTimeUsedTargetCount
import SphincsSecurity.Proof.FewTimeOccupancy127

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

set_option exponentiation.threshold 600

theorem usedWeightedFewTime_occupancy127_scaled_certificate :
    (∑ d ∈ Finset.Icc 1 14,
      (d + 1).ascFactorial (14 - d) * 2 ^ (24 * d) * surjectiveAssignmentCount 14 d *
        65 ^ d * 2 ^ (31 * (14 - d))) ≤ Nat.factorial 14 * (29 * 2 ^ 451) := by
  decide

theorem usedWeightedRawTargetOriginUnionBound_le_twenty_nine_mul_inv133
    {signatures q : Nat} (hsignatures : signatures ≤ signatureLimit) (hq : q ≤ 2 ^ 127) :
    usedWeightedRawTargetOriginUnionBound signatures q (digestReuseWeight q) ≤
      29 * ((2 ^ 133 : Nat) : ℝ≥0∞)⁻¹ := by
  have hweight : 1 + (q : ℝ≥0∞) *
      (((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ * digestReuseWeight q) ≤ (65 : ℝ≥0∞) / 2 ^ 5 := by
    simpa only [show (2 : ℝ≥0∞) ^ 5 = 32 by norm_num] using
      digestOriginInflation_le_sixty_five_thirty_seconds q hq
  rw [usedWeightedRawTargetOriginUnionBound_eq]
  apply (mul_le_mul' le_rfl (usedParametricFewTimePatternBound_le_of_origin_weight _
    hsignatures hweight usedWeightedFewTime_occupancy127_scaled_certificate)).trans_eq
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ftsTreeHeight]

theorem probEvent_sampled_honest_leak_le_usedOccupancy127
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    Pr[SampledViewedEvent ViewedHonestProperFewTimeLeakWitness | sampledViewedGame adversary] ≤
      ((2 * q + 1 : Nat) : ENNReal) * (29 * ((2 ^ 133 : Nat) : ENNReal)⁻¹) :=
  (probEvent_sampled_honest_leak_le_usedWeighted adversary q hq hqMax).trans
    (mul_le_mul' le_rfl (usedWeightedRawTargetOriginUnionBound_le_twenty_nine_mul_inv133 le_rfl hqMax))

end SphincsSecurity.Concrete
