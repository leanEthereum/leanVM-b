import SphincsSecurity.Proof.FewTimeWeightedHonestLeak
import SphincsSecurity.Proof.MandatoryQueries

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

set_option exponentiation.threshold 600

theorem digestOriginInflation_le_eleven_eighths (q : Nat) (hq : q ≤ 2 ^ 126) :
    1 + (q : ℝ≥0∞) *
      (((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ * digestReuseWeight q) ≤ 11 / 8 := by
  rw [digestReuseWeight_source]
  have hden : ((2 ^ randomnessBits - (2 ^ 126 + digestAttemptLimit) : Nat) : ℝ≥0∞) ≤
      ((2 ^ randomnessBits : Nat) : ℝ≥0∞) - (q + digestAttemptLimit : Nat) := by
    rw [ENNReal.natCast_sub]
    exact tsub_le_tsub_left (Nat.cast_le.mpr (Nat.add_le_add_right hq _)) _
  have hinv : ((2 ^ randomnessBits - (2 ^ 126 + digestAttemptLimit) : Nat) : ℝ≥0∞)⁻¹ ≠ ∞ := by
    apply ENNReal.inv_ne_top.mpr
    norm_num [randomnessBits, digestAttemptLimit]
  have hmul : ((2 ^ 126 : Nat) : ℝ≥0∞) *
      ((2 ^ randomnessBits - (2 ^ 126 + digestAttemptLimit) : Nat) : ℝ≥0∞)⁻¹ ≠ ∞ :=
    ENNReal.mul_ne_top (by finiteness) hinv
  calc
    _ ≤ 1 + ((2 ^ 126 : Nat) : ℝ≥0∞) *
        ((2 ^ randomnessBits - (2 ^ 126 + digestAttemptLimit) : Nat) : ℝ≥0∞)⁻¹ :=
      add_le_add_right (mul_le_mul' (Nat.cast_le.mpr hq) (ENNReal.inv_le_inv.mpr hden)) _
    _ ≤ _ := by
      apply (ENNReal.toReal_le_toReal (ENNReal.add_ne_top.mpr ⟨by finiteness, hmul⟩) (by finiteness)).mp
      rw [ENNReal.toReal_add (by finiteness) hmul]
      norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div,
        randomnessBits, digestAttemptLimit]

theorem weightedFewTime_occupancy_scaled_certificate :
    (∑ d ∈ Finset.Icc 1 14,
      (d + 1).ascFactorial (14 - d) * 2 ^ (24 * d) * d ^ 14 *
        11 ^ d * 2 ^ (29 * (14 - d))) ≤ Nat.factorial 14 * (11 * 2 ^ 422) := by
  decide

theorem weightedRawTargetOriginUnionBound_le_eleven_mul_inv134
    {signatures q : Nat} (hsignatures : signatures ≤ signatureLimit) (hq : q ≤ 2 ^ 126) :
    weightedRawTargetOriginUnionBound signatures q (digestReuseWeight q) ≤
      11 * ((2 ^ 134 : Nat) : ℝ≥0∞)⁻¹ := by
  have hweight : 1 + (q : ℝ≥0∞) *
      (((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ * digestReuseWeight q) ≤ (11 : ℝ≥0∞) / 2 ^ 3 := by
    simpa only [show (2 : ℝ≥0∞) ^ 3 = 8 by norm_num] using
      digestOriginInflation_le_eleven_eighths q hq
  rw [weightedRawTargetOriginUnionBound_eq]
  apply (mul_le_mul' le_rfl (parametricFewTimePatternBound_le_of_origin_weight _
    hsignatures hweight weightedFewTime_occupancy_scaled_certificate)).trans_eq
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ftsTreeHeight]

theorem probEvent_gameAfterSecretsWithViewTrace_honest_leak_le_twenty_three_mul_inv134
    (adversary : Adversary) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    Pr[ViewedHonestProperFewTimeLeakWitness parameter otsSecret ftsSecret |
      gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] ≤
      ((23 * q : Nat) : ℝ≥0∞) * ((2 ^ 134 : Nat) : ℝ≥0∞)⁻¹ := by
  have hminimum := numChains_le_of_hasHashQueryBound adversary q hq
    parameter hparameter otsSecret hots ftsSecret hfts
  norm_num [numChains] at hminimum
  calc
    _ ≤ q * weightedRawTargetOriginUnionBound signatureLimit q (digestReuseWeight q) +
        ((q + 1 : Nat) : ℝ≥0∞) *
          weightedRawTargetOriginUnionBound signatureLimit q (digestReuseWeight q) :=
      probEvent_gameAfterSecretsWithViewTrace_honest_leak_le_weighted adversary q hq
        (hqMax.trans (by norm_num)) parameter hparameter otsSecret hots ftsSecret hfts
    _ = ((2 * q + 1 : Nat) : ℝ≥0∞) *
        weightedRawTargetOriginUnionBound signatureLimit q (digestReuseWeight q) := by
      push_cast
      ring
    _ ≤ ((2 * q + 1 : Nat) : ℝ≥0∞) * (11 * ((2 ^ 134 : Nat) : ℝ≥0∞)⁻¹) :=
      mul_le_mul' le_rfl (weightedRawTargetOriginUnionBound_le_eleven_mul_inv134 le_rfl hqMax)
    _ = (((2 * q + 1) * 11 : Nat) : ℝ≥0∞) * ((2 ^ 134 : Nat) : ℝ≥0∞)⁻¹ := by
      push_cast
      ring
    _ ≤ _ := mul_le_mul' (Nat.cast_le.mpr (by omega)) le_rfl

end SphincsSecurity.Concrete
