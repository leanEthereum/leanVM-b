import SphincsSecurity.Proof.FewTimeWeightedTargetBound
import SphincsSecurity.Proof.FewTimeParametricCount

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

noncomputable def OriginConfiguration.rawTargetBound
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (reuseWeight : ℝ≥0∞) : ℝ≥0∞ :=
  ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ *
    ((((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ * reuseWeight) ^ configuration.prehit.card *
      Pr[FixedFewTimePatternHit pattern.assignment |
        ($ᵗ ((pattern.selected → FewTimeView) × FewTimeView) : ProbComp _)])

noncomputable def weightedRawTargetOriginUnionBound
    (signatures sources : Nat) (reuseWeight : ℝ≥0∞) : ℝ≥0∞ :=
  ∑ distinct ∈ Finset.Icc 1 14,
    ∑ pattern : FewTimePattern signatures distinct,
      ∑ configuration : OriginConfiguration pattern sources,
        configuration.rawTargetBound reuseWeight

theorem probEvent_rawTargetMonitored_complete_fixedPattern_le_weighted
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (q : Nat) (hq : q ≤ 2 ^ 127)
    (hcache : QueryCache.enncard initialCache ≤ q) :
    Pr[fun result : α × OriginTargetMonitorState configuration =>
        result.2.Complete ∧
          (∀ target, result.2.targetView = some target →
            FixedFewTimePatternHit pattern.assignment
              (result.2.origin.observation.views, target)) ∧
          QueryCache.enncard result.2.origin.viewed.cache ≤ q |
      (simulateQ
        (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
        computation).run (OriginTargetMonitorState.initial configuration initialCache)] ≤
      configuration.rawTargetBound (digestReuseWeight q) :=
  probEvent_rawTargetMonitored_complete_le_weighted_ideal configuration secretKey
    targetOrdinal computation initialCache (FixedFewTimePatternHit pattern.assignment) q hq hcache

theorem OriginConfiguration.rawTargetBound_eq
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (reuseWeight : ℝ≥0∞) :
    configuration.rawTargetBound reuseWeight =
      ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ *
        ((((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ * reuseWeight) ^ configuration.prehit.card *
          ((2 ^ (totalHeight * distinct + ftsTreeHeight * (ftsTrees - 1)) : Nat) : ℝ≥0∞)⁻¹) := by
  classical
  letI : Nonempty pattern.selected := ⟨pattern.assignment ⟨0, by decide⟩⟩
  have hpattern :
      Pr[FixedFewTimePatternHit pattern.assignment |
        ($ᵗ ((pattern.selected → FewTimeView) × FewTimeView) : ProbComp _)] =
      ((2 ^ (totalHeight * distinct + ftsTreeHeight * (ftsTrees - 1)) : Nat) : ℝ≥0∞)⁻¹ := by
    have h := probEvent_fixedFewTimePatternHit_eq_inv_of_evalDist pattern.assignment
      ($ᵗ ((pattern.selected → FewTimeView) × FewTimeView) : ProbComp _)
      (by simp only [evalDist_uniformSample])
    simpa only [Fintype.card_coe, pattern.card_selected] using h
  rw [rawTargetBound, hpattern]

theorem sum_rawTargetBound_eq {signatures distinct sources : Nat}
    (pattern : FewTimePattern signatures distinct) (reuseWeight : ℝ≥0∞) :
    (∑ configuration : OriginConfiguration pattern sources,
      configuration.rawTargetBound reuseWeight) =
      ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ *
        (originChoiceMass pattern.selected sources
          (((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ * reuseWeight) *
          ((2 ^ (totalHeight * distinct + ftsTreeHeight * (ftsTrees - 1)) : Nat) : ℝ≥0∞)⁻¹) := by
  classical
  simp_rw [OriginConfiguration.rawTargetBound_eq]
  rw [← Finset.mul_sum]
  congr 1
  calc
    _ = ∑ data : Σ prehit : Finset pattern.selected, InjectiveSources prehit sources,
        (((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ * reuseWeight) ^ data.1.card *
          ((2 ^ (totalHeight * distinct + ftsTreeHeight * (ftsTrees - 1)) : Nat) : ℝ≥0∞)⁻¹ := by
      apply Fintype.sum_equiv (originConfigurationEquiv pattern sources)
      intro configuration
      rfl
    _ = _ := by
      simp only [Fintype.sum_sigma, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        originChoiceMass]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro prehit _
      ring

noncomputable def parametricFewTimePatternBound
    (signatures sources : Nat) (sourceWeight : ℝ≥0∞) : ℝ≥0∞ :=
  ∑ distinct ∈ Finset.Icc 1 14,
    ∑ pattern : FewTimePattern signatures distinct,
      originChoiceMass pattern.selected sources sourceWeight *
        ((2 ^ (26 * distinct + 140) : Nat) : ℝ≥0∞)⁻¹

theorem weightedRawTargetOriginUnionBound_eq
    (signatures sources : Nat) (reuseWeight : ℝ≥0∞) :
    weightedRawTargetOriginUnionBound signatures sources reuseWeight =
      ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ *
        parametricFewTimePatternBound signatures sources
          (((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ * reuseWeight) := by
  unfold weightedRawTargetOriginUnionBound parametricFewTimePatternBound
  simp_rw [sum_rawTargetBound_eq, ← Finset.mul_sum]
  rfl

theorem parametricFewTimePatternBound_le_of_origin_weight
    {signatures q numerator shift budget : Nat}
    (sourceWeight : ℝ≥0∞)
    (hsignatures : signatures ≤ signatureLimit)
    (hweight : 1 + (q : ℝ≥0∞) * sourceWeight ≤
      (numerator : ℝ≥0∞) / 2 ^ shift)
    (hcertificate : (∑ d ∈ Finset.Icc 1 14,
      (d + 1).ascFactorial (14 - d) * 2 ^ (24 * d) * d ^ 14 *
        numerator ^ d * 2 ^ ((26 + shift) * (14 - d))) ≤ Nat.factorial 14 * budget) :
    parametricFewTimePatternBound signatures q sourceWeight ≤
      (budget : ℝ≥0∞) * ((2 ^ ((26 + shift) * 14 + 140) : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 14, ∑ _pattern : FewTimePattern signatures d,
        ((numerator : ℝ≥0∞) / 2 ^ shift) ^ d *
          ((2 ^ (26 * d + 140) : Nat) : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro pattern _
      gcongr
      calc
        _ ≤ (1 + q * sourceWeight) ^ Fintype.card pattern.selected :=
          originChoiceMass_le _ _ _
        _ = (1 + q * sourceWeight) ^ d := by
          rw [Fintype.card_coe, pattern.card_selected]
        _ ≤ _ := pow_le_pow_left' hweight d
    _ = ∑ d ∈ Finset.Icc 1 14,
        (Fintype.card (FewTimePattern signatures d) * numerator ^ d *
          2 ^ ((26 + shift) * (14 - d)) : Nat) *
            ((2 ^ ((26 + shift) * 14 + 140) : Nat) : ℝ≥0∞)⁻¹ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      apply Finset.sum_congr rfl
      intro d hd
      rw [← mul_assoc]
      exact weightedFewTime_term_common_denominator signatures d numerator shift
        (Finset.mem_Icc.mp hd).2
    _ = ((∑ d ∈ Finset.Icc 1 14,
        Fintype.card (FewTimePattern signatures d) * numerator ^ d *
          2 ^ ((26 + shift) * (14 - d)) : Nat) : ℝ≥0∞) *
            ((2 ^ ((26 + shift) * 14 + 140) : Nat) : ℝ≥0∞)⁻¹ := by
      rw [← Finset.sum_mul, Nat.cast_sum]
    _ ≤ _ := mul_le_mul' (Nat.cast_le.mpr
      (weightedFewTime_scaled_sum_le hsignatures hcertificate)) le_rfl

end SphincsSecurity.Concrete
