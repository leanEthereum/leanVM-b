import SphincsSecurity.Proof.MessageCollisionWeightedBound
import SphincsSecurity.Proof.FewTimeWeightedTargetCount

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

theorem weightedSingletonOriginUnionBound_eq (signatures sources : Nat) (reuseWeight : ℝ≥0∞) :
    weightedSingletonOriginUnionBound signatures sources reuseWeight =
      ∑ pattern : FewTimePattern signatures 1,
        originChoiceMass pattern.selected sources
          (((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ * reuseWeight) *
            ((2 ^ 166 : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  rw [weightedSingletonOriginUnionBound]
  apply Finset.sum_congr rfl
  intro pattern _
  apply (ENNReal.mul_right_inj
    (show ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ ≠ 0 by simp)
    (show ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ ≠ ∞ by norm_num [ftsTreeHeight])).mp
  have hsum := sum_rawTargetBound_eq (sources := sources) pattern reuseWeight
  have hraw : (∑ configuration : OriginConfiguration pattern sources,
      configuration.rawTargetBound reuseWeight) =
      ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ *
        ∑ configuration : OriginConfiguration pattern sources, configuration.targetBound reuseWeight := by
    simp only [OriginConfiguration.rawTargetBound, OriginConfiguration.targetBound, Finset.mul_sum]
  rw [hraw] at hsum
  simpa only [show totalHeight * 1 + ftsTreeHeight * (ftsTrees - 1) = 166 by rfl] using hsum

theorem digestOriginInflation_le_five_halves (q : Nat) (hq : q ≤ 2 ^ 127) :
    1 + (q : ℝ≥0∞) *
      (((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ * digestReuseWeight q) ≤ 5 / 2 := by
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

theorem weightedSingletonOriginUnionBound_le_five_mul_inv143 (q : Nat) (hq : q ≤ 2 ^ 127) :
    weightedSingletonOriginUnionBound signatureLimit q (digestReuseWeight q) ≤
      5 * ((2 ^ 143 : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  have hratio := digestOriginInflation_le_five_halves q hq
  rw [weightedSingletonOriginUnionBound_eq]
  calc
    (∑ pattern : FewTimePattern signatureLimit 1,
        originChoiceMass pattern.selected q (((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ * digestReuseWeight q) *
          ((2 ^ 166 : Nat) : ℝ≥0∞)⁻¹) ≤
        ∑ _pattern : FewTimePattern signatureLimit 1,
          (5 / 2) * ((2 ^ 166 : Nat) : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_le_sum
      intro pattern _
      have hmass := originChoiceMass_le pattern.selected q (((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ * digestReuseWeight q)
      rw [Fintype.card_coe, pattern.card_selected, pow_one] at hmass
      have hmass : originChoiceMass pattern.selected q (((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ * digestReuseWeight q) ≤ 5 / 2 :=
        hmass.trans hratio
      simpa only [mul_comm] using
        (mul_le_mul_left hmass ((2 ^ 166 : Nat) : ℝ≥0∞)⁻¹)
    _ = (Fintype.card (FewTimePattern signatureLimit 1) : ℝ≥0∞) *
        ((5 / 2) * ((2 ^ 166 : Nat) : ℝ≥0∞)⁻¹) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = 5 * ((2 ^ 143 : Nat) : ℝ≥0∞)⁻¹ := by
      have hcard : Fintype.card (FewTimePattern signatureLimit 1) = signatureLimit := by
        simp [fewTimePattern_card]
      rw [hcard, signatureLimit]
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
      norm_num

theorem probEvent_gameAfterSecretsWithViewTrace_messageCollision_le_inv127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    Pr[ViewedMessageDigestCollisionWitness parameter otsSecret ftsSecret |
      gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret] ≤
      (q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹ := by
  calc
    _ ≤ q * weightedSingletonOriginUnionBound signatureLimit q (digestReuseWeight q) +
        ((q + 1 : Nat) : ℝ≥0∞) * weightedSingletonOriginUnionBound signatureLimit q (digestReuseWeight q) :=
      probEvent_gameAfterSecretsWithViewTrace_messageCollision_le_weighted adversary q hq hqMax
        parameter hparameter otsSecret hots ftsSecret hfts
    _ = ((2 * q + 1 : Nat) : ℝ≥0∞) * weightedSingletonOriginUnionBound signatureLimit q (digestReuseWeight q) := by
      push_cast
      ring
    _ ≤ ((3 * q : Nat) : ℝ≥0∞) * (5 * ((2 ^ 143 : Nat) : ℝ≥0∞)⁻¹) :=
      mul_le_mul' (Nat.cast_le.mpr (by omega)) (weightedSingletonOriginUnionBound_le_five_mul_inv143 q hqMax)
    _ = (q : ℝ≥0∞) * (15 * ((2 ^ 143 : Nat) : ℝ≥0∞)⁻¹) := by
      push_cast
      ring
    _ ≤ _ := by
      apply mul_le_mul' le_rfl
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv]

theorem probEvent_sampled_cleanMessage_le127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    Pr[SampledViewedEvent cleanMessageEvent | sampledViewedGame adversary] ≤
      (q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹ := by
  rw [sampledViewedGame]
  apply probEvent_bind_le_of_forall_le
  intro secrets hsecrets
  obtain ⟨hparameter, hots, hfts⟩ := secrets.support_components hsecrets
  rw [bind_pure_comp, probEvent_map]
  change Pr[cleanMessageEvent secrets.parameter secrets.otsSecret secrets.ftsSecret |
    gameAfterSecretsWithViewTrace adversary secrets.parameter secrets.otsSecret secrets.ftsSecret] ≤ _
  apply (probEvent_mono fun _ _ event => event.2).trans
  exact probEvent_gameAfterSecretsWithViewTrace_messageCollision_le_inv127 adversary q hqPos hq hqMax
    secrets.parameter hparameter secrets.otsSecret hots secrets.ftsSecret hfts

end SphincsSecurity.Concrete
