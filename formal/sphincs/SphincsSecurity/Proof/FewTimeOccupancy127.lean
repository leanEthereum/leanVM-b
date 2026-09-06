import SphincsSecurity.Proof.FewTimeOccupancyCount

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

set_option exponentiation.threshold 600

theorem digestOriginInflation_le_sixty_five_thirty_seconds (q : Nat) (hq : q ≤ 2 ^ 127) :
    1 + (q : ℝ≥0∞) *
      (((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ * digestReuseWeight q) ≤ 65 / 32 := by
  rw [digestReuseWeight_source]
  have hden : ((2 ^ randomnessBits - (2 ^ 127 + digestAttemptLimit) : Nat) : ℝ≥0∞) ≤
      ((2 ^ randomnessBits : Nat) : ℝ≥0∞) - (q + digestAttemptLimit : Nat) := by
    rw [ENNReal.natCast_sub]
    exact tsub_le_tsub_left (Nat.cast_le.mpr (Nat.add_le_add_right hq _)) _
  have hinv : ((2 ^ randomnessBits - (2 ^ 127 + digestAttemptLimit) : Nat) : ℝ≥0∞)⁻¹ ≠ ∞ := by
    apply ENNReal.inv_ne_top.mpr
    norm_num [randomnessBits, digestAttemptLimit]
  have hmul : ((2 ^ 127 : Nat) : ℝ≥0∞) *
      ((2 ^ randomnessBits - (2 ^ 127 + digestAttemptLimit) : Nat) : ℝ≥0∞)⁻¹ ≠ ∞ :=
    ENNReal.mul_ne_top (by finiteness) hinv
  calc
    _ ≤ 1 + ((2 ^ 127 : Nat) : ℝ≥0∞) *
        ((2 ^ randomnessBits - (2 ^ 127 + digestAttemptLimit) : Nat) : ℝ≥0∞)⁻¹ :=
      add_le_add_right (mul_le_mul' (Nat.cast_le.mpr hq) (ENNReal.inv_le_inv.mpr hden)) _
    _ ≤ _ := by
      apply (ENNReal.toReal_le_toReal (ENNReal.add_ne_top.mpr ⟨by finiteness, hmul⟩) (by finiteness)).mp
      rw [ENNReal.toReal_add (by finiteness) hmul]
      norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div,
        randomnessBits, digestAttemptLimit]

theorem weightedFewTime_occupancy127_scaled_certificate :
    (∑ d ∈ Finset.Icc 1 14,
      (d + 1).ascFactorial (14 - d) * 2 ^ (24 * d) * d ^ 14 *
        65 ^ d * 2 ^ (31 * (14 - d))) ≤ Nat.factorial 14 * (3 * 2 ^ 455) := by
  decide

theorem weightedRawTargetOriginUnionBound_le_three_mul_inv129
    {signatures q : Nat} (hsignatures : signatures ≤ signatureLimit) (hq : q ≤ 2 ^ 127) :
    weightedRawTargetOriginUnionBound signatures q (digestReuseWeight q) ≤
      3 * ((2 ^ 129 : Nat) : ℝ≥0∞)⁻¹ := by
  have hweight : 1 + (q : ℝ≥0∞) *
      (((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ * digestReuseWeight q) ≤ (65 : ℝ≥0∞) / 2 ^ 5 := by
    simpa only [show (2 : ℝ≥0∞) ^ 5 = 32 by norm_num] using
      digestOriginInflation_le_sixty_five_thirty_seconds q hq
  rw [weightedRawTargetOriginUnionBound_eq]
  apply (mul_le_mul' le_rfl (parametricFewTimePatternBound_le_of_origin_weight _
    hsignatures hweight weightedFewTime_occupancy127_scaled_certificate)).trans_eq
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ftsTreeHeight]

theorem probEvent_sampled_honest_leak_le_occupancy127
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    Pr[SampledViewedEvent ViewedHonestProperFewTimeLeakWitness | sampledViewedGame adversary] ≤
      ((2 * q + 1 : Nat) : ENNReal) * (3 * ((2 ^ 129 : Nat) : ENNReal)⁻¹) :=
  (probEvent_sampled_honest_leak_le_weighted adversary q hq hqMax).trans
    (mul_le_mul' le_rfl (weightedRawTargetOriginUnionBound_le_three_mul_inv129 le_rfl hqMax))

end SphincsSecurity.Concrete
