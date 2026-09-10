import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.FewTime126Count
import SphincsSecurity.Proof.FewTimeHonestLeakBound
import SphincsSecurity.Proof.MandatoryQueries

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

theorem probEvent_gameAfterSecretsWithViewTrace_honest_leak_le_nineteen_mul_inv133
    (adversary : Adversary) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    Pr[ViewedHonestProperFewTimeLeakWitness parameter otsSecret ftsSecret |
      gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] ≤
      ((19 * q : Nat) : ℝ≥0∞) * ((2 ^ 133 : Nat) : ℝ≥0∞)⁻¹ := by
  have hminimum := numChains_le_of_hasHashQueryBound adversary q hq parameter hparameter otsSecret hots ftsSecret hfts
  norm_num [numChains] at hminimum
  calc
    _ ≤ q * rawTargetOriginUnionBound signatureLimit q +
        ((q + 1 : Nat) : ℝ≥0∞) * rawTargetOriginUnionBound signatureLimit q :=
      probEvent_gameAfterSecretsWithViewTrace_honest_leak_le adversary q hq hqMax
        parameter hparameter otsSecret hots ftsSecret hfts
    _ = ((2 * q + 1 : Nat) : ℝ≥0∞) * rawTargetOriginUnionBound signatureLimit q := by
      push_cast
      ring
    _ ≤ ((2 * q + 1 : Nat) : ℝ≥0∞) * (9 * ((2 ^ 133 : Nat) : ℝ≥0∞)⁻¹) :=
      mul_le_mul' le_rfl (rawTargetOriginUnionBound_le_nine_mul_inv133 le_rfl hqMax)
    _ = (((2 * q + 1) * 9 : Nat) : ℝ≥0∞) * ((2 ^ 133 : Nat) : ℝ≥0∞)⁻¹ := by
      push_cast
      ring
    _ ≤ _ := mul_le_mul' (Nat.cast_le.mpr (by omega)) le_rfl

end SphincsSecurity.Concrete
