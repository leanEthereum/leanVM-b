import SphincsSecurity.Proof.EncodingTerminalView
import SphincsSecurity.Proof.TerminalSampling

/-!
# Encoding selection risk across secret sampling

The fixed-secret adaptive bound is uniform in the sampled parameter and secret tables, so averaging
it at the actual sampling boundary preserves the same bound.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

theorem probEvent_sampled_cleanEncoding_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) :
    Pr[SampledViewedEvent cleanEncodingEvent | sampledViewedGame adversary] ≤
      ((44 * q : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  rw [probEvent_sampledViewedGame_eq_weighted]
  calc
    _ ≤ ∑' secrets : SampledSecrets, Pr[= secrets | sampleSecrets] *
          (((44 * q : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) := by
      apply ENNReal.tsum_le_tsum
      intro secrets
      by_cases hsecrets : secrets ∈ support sampleSecrets
      · obtain ⟨hparameter, hots, hfts⟩ := secrets.support_components hsecrets
        apply mul_le_mul' le_rfl
        have hgame := isQueryBoundP_gameAfterSecrets adversary q hq hparameter hots hfts
        change Pr[fun result =>
            ¬Bad secrets.parameter secrets.otsSecret secrets.ftsSecret result.2.cache ∧
              ViewedEncodingCollisionWitness secrets.parameter secrets.otsSecret
                secrets.ftsSecret result |
          gameAfterSecretsWithViewTrace adversary secrets.parameter secrets.otsSecret
            secrets.ftsSecret] ≤ _
        calc
          _ ≤ (44 * (q : ℝ≥0∞)) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
            simpa only [Digest, card_bitVec] using
              probEvent_clean_viewedEncodingCollision_le adversary secrets.parameter
                secrets.otsSecret secrets.ftsSecret q hgame
          _ = ((44 * q : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
            push_cast
            rfl
      · rw [probOutput_eq_zero_of_not_mem_support hsecrets, zero_mul, zero_mul]
    _ ≤ ((44 * q : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left zero_le tsum_probOutput_le_one

end SphincsSecurity.Concrete
