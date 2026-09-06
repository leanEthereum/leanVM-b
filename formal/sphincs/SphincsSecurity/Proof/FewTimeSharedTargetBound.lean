import SphincsSecurity.Proof.FewTimeUsedOccupancy127

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

set_option exponentiation.threshold 600

theorem probEvent_gameAfterSecretsWithViewTrace_honest_leak_le_sharedTargetBudget
    (adversary : Adversary) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    Pr[ViewedHonestProperFewTimeLeakWitness parameter otsSecret ftsSecret |
      gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] ≤
      (q : ENNReal) * (15 * ((2 ^ 132 : Nat) : ENNReal)⁻¹) := by
  have hminimum := numChains_le_of_hasHashQueryBound adversary q hq
    parameter hparameter otsSecret hots ftsSecret hfts
  norm_num [numChains] at hminimum
  calc
    _ ≤ ((q + 1 : Nat) : ENNReal) *
        usedWeightedRawTargetOriginUnionBound signatureLimit q (digestReuseWeight q) :=
      probEvent_gameAfterSecretsWithViewTrace_honest_leak_le_sharedTargets adversary q hq hqMax
        parameter hparameter otsSecret hots ftsSecret hfts
    _ ≤ ((q + 1 : Nat) : ENNReal) * (29 * ((2 ^ 133 : Nat) : ENNReal)⁻¹) :=
      mul_le_mul' le_rfl (usedWeightedRawTargetOriginUnionBound_le_twenty_nine_mul_inv133 le_rfl hqMax)
    _ = (((q + 1) * 29 : Nat) : ENNReal) * ((2 ^ 133 : Nat) : ENNReal)⁻¹ := by
      push_cast
      ring
    _ ≤ ((30 * q : Nat) : ENNReal) * ((2 ^ 133 : Nat) : ENNReal)⁻¹ :=
      mul_le_mul' (Nat.cast_le.mpr (by omega)) le_rfl
    _ = (q : ENNReal) * (30 * ((2 ^ 133 : Nat) : ENNReal)⁻¹) := by
      push_cast
      ring
    _ = _ := by
      congr 1
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv]

theorem probEvent_sampled_honest_leak_le_sharedTargetBudget
    (adversary : Adversary) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    Pr[SampledViewedEvent ViewedHonestProperFewTimeLeakWitness | sampledViewedGame adversary] ≤
      (q : ENNReal) * (15 * ((2 ^ 132 : Nat) : ENNReal)⁻¹) := by
  rw [sampledViewedGame]
  apply probEvent_bind_le_of_forall_le
  intro secrets hsecrets
  obtain ⟨hparameter, hots, hfts⟩ := secrets.support_components hsecrets
  rw [bind_pure_comp, probEvent_map]
  change Pr[ViewedHonestProperFewTimeLeakWitness secrets.parameter secrets.otsSecret secrets.ftsSecret |
    gameAfterSecretsWithViewTrace adversary secrets.parameter secrets.otsSecret secrets.ftsSecret] ≤ _
  exact probEvent_gameAfterSecretsWithViewTrace_honest_leak_le_sharedTargetBudget adversary q hq hqMax
    secrets.parameter hparameter secrets.otsSecret hots secrets.ftsSecret hfts

end SphincsSecurity.Concrete
