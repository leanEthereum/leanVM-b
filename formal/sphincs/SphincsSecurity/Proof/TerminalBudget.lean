import SphincsSecurity.Proof.TerminalArith
import SphincsSecurity.Proof.TerminalView

/-!
# Reserving the completed terminal budget

The structural bad event and the complete proper few-time event fit in the first 24 units at
denominator `2^125`. This module packages that fact around the trace-aware decomposition, leaving
only the five unresolved clean terminal probabilities.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

theorem probEvent_win_le_reserved_add_remaining
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqMax : q ≤ 2 ^ 120)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    let run := gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret
    Pr[= true | (simulateQ romImpl
        (gameAfterSecrets adversary parameter otsSecret ftsSecret)).run' ∅] ≤
      ((24 * q : Nat) : ℝ≥0∞) * ((2 ^ 125 : Nat) : ℝ≥0∞)⁻¹ +
      (Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
          ViewedFreshLayerOpeningWitness parameter otsSecret ftsSecret result | run] +
      (Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
          ViewedEncodingCollisionWitness parameter otsSecret ftsSecret result | run] +
      (Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
          ViewedBackwardChainOpeningWitness parameter otsSecret ftsSecret result | run] +
      (Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
          ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result | run] +
       Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
          ViewedUncoveredFtsSecretWitness parameter otsSecret ftsSecret result | run])))) := by
  dsimp only
  let run := gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret
  have hgameBound := isQueryBoundP_gameAfterSecrets adversary q hq hparameter hots hfts
  have hqMin := numChains_le_of_hasHashQueryBound adversary q hq parameter hparameter otsSecret
    hots ftsSecret hfts
  have hbad := probEvent_bad_gameAfterSecretsWithViewTrace_le adversary parameter otsSecret
    ftsSecret q hgameBound
  have hproper := probEvent_clean_properFewTimeLeak_le_nine_mul_inv adversary q hq hqMax
    parameter hparameter otsSecret hots ftsSecret hfts
  calc
    _ ≤ Pr[fun result => Bad parameter otsSecret ftsSecret result.2.cache | run] +
        (Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
          ViewedFreshLayerOpeningWitness parameter otsSecret ftsSecret result | run] +
        (Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
          ViewedEncodingCollisionWitness parameter otsSecret ftsSecret result | run] +
        (Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
          ViewedBackwardChainOpeningWitness parameter otsSecret ftsSecret result | run] +
        (Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
          ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result | run] +
        (Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
          ViewedProperFewTimeLeakWitness parameter otsSecret ftsSecret result | run] +
        Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
          ViewedUncoveredFtsSecretWitness parameter otsSecret ftsSecret result | run]))))) :=
      probEvent_win_le_viewed_bad_add_terminal_cases adversary parameter otsSecret ftsSecret
    _ ≤ (((44 * q : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) +
        (Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
          ViewedFreshLayerOpeningWitness parameter otsSecret ftsSecret result | run] +
        (Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
          ViewedEncodingCollisionWitness parameter otsSecret ftsSecret result | run] +
        (Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
          ViewedBackwardChainOpeningWitness parameter otsSecret ftsSecret result | run] +
        (Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
          ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result | run] +
        (((2 * q + 1 : Nat) : ℝ≥0∞) * (9 * ((2 ^ 125 : Nat) : ℝ≥0∞)⁻¹) +
        Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
          ViewedUncoveredFtsSecretWitness parameter otsSecret ftsSecret result | run]))))) := by
      gcongr
    _ = ((((44 * q : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) +
          ((2 * q + 1 : Nat) : ℝ≥0∞) * (9 * ((2 ^ 125 : Nat) : ℝ≥0∞)⁻¹)) +
        (Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
          ViewedFreshLayerOpeningWitness parameter otsSecret ftsSecret result | run] +
        (Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
          ViewedEncodingCollisionWitness parameter otsSecret ftsSecret result | run] +
        (Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
          ViewedBackwardChainOpeningWitness parameter otsSecret ftsSecret result | run] +
        (Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
          ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret result | run] +
        Pr[fun result => ¬Bad parameter otsSecret ftsSecret result.2.cache ∧
          ViewedUncoveredFtsSecretWitness parameter otsSecret ftsSecret result | run])))) := by
      ac_rfl
    _ ≤ _ := by
      gcongr
      exact structural_add_properFewTime_le hqMin

end SphincsSecurity.Concrete
