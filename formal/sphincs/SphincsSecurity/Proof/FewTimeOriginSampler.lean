import SphincsSecurity.Proof.FewTimeWeightedCount

/-!
# Ideal sampler for a fixed origin configuration

An origin configuration chooses the selected entries whose views come from earlier direct queries
and injectively assigns those entries to source slots. Its ideal sample contains one uniform view per
selected entry, a uniform target view and one independent `127`-bit activation value per prehit.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

structure OriginConfiguration {signatures distinct : Nat}
    (pattern : FewTimePattern signatures distinct) (sources : Nat) where
  prehit : Finset pattern.selected
  source : InjectiveSources prehit sources

def originConfigurationEquiv {signatures distinct : Nat}
    (pattern : FewTimePattern signatures distinct) (sources : Nat) :
    OriginConfiguration pattern sources ≃
      Σ prehit : Finset pattern.selected, InjectiveSources prehit sources where
  toFun configuration := ⟨configuration.prehit, configuration.source⟩
  invFun configuration := ⟨configuration.1, configuration.2⟩
  left_inv configuration := by cases configuration; rfl
  right_inv configuration := by cases configuration; rfl

noncomputable instance {signatures distinct : Nat}
    (pattern : FewTimePattern signatures distinct) (sources : Nat) :
    Fintype (OriginConfiguration pattern sources) :=
  Fintype.ofEquiv _ (originConfigurationEquiv pattern sources).symm

abbrev OriginConfiguration.Sample {signatures distinct : Nat}
    {pattern : FewTimePattern signatures distinct} {sources : Nat}
    (configuration : OriginConfiguration pattern sources) :=
  ((pattern.selected → FewTimeView) × FewTimeView) ×
    BitVec (127 * configuration.prehit.card)

def OriginConfiguration.Hit {signatures distinct : Nat}
    {pattern : FewTimePattern signatures distinct} {sources : Nat}
    (configuration : OriginConfiguration pattern sources)
    (sample : configuration.Sample) : Prop :=
  FixedFewTimePatternHit pattern.assignment sample.1
    ∧ sample.2 = 0

noncomputable instance {signatures distinct : Nat}
    {pattern : FewTimePattern signatures distinct} {sources : Nat}
    (configuration : OriginConfiguration pattern sources) :
    DecidablePred configuration.Hit :=
  fun sample => Classical.propDecidable (configuration.Hit sample)

theorem probEvent_uniformOriginActivation_zero (count : Nat) :
    Pr[fun value : BitVec (127 * count) => value = 0 |
      ($ᵗ BitVec (127 * count) : ProbComp (BitVec (127 * count)))] =
      ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ ^ count := by
  rw [probEvent_eq_eq_probOutput, probOutput_uniformSample,
    show Fintype.card (BitVec (127 * count)) = 2 ^ (127 * count) from
      card_bitVec (127 * count), pow_mul, Nat.cast_pow, ENNReal.inv_pow]

set_option maxHeartbeats 1000000 in
theorem probEvent_originConfiguration_hit {signatures distinct : Nat}
    {pattern : FewTimePattern signatures distinct} {sources : Nat}
    (configuration : OriginConfiguration pattern sources) :
    Pr[configuration.Hit |
      ($ᵗ configuration.Sample : ProbComp configuration.Sample)] =
      ((2 ^ (totalHeight * distinct + ftsTreeHeight * (ftsTrees - 1)) : Nat) :
          ℝ≥0∞)⁻¹ *
        ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ ^ configuration.prehit.card := by
  classical
  letI : Nonempty pattern.selected := ⟨pattern.assignment ⟨0, by decide⟩⟩
  change Pr[configuration.Hit |
    Prod.mk <$>
      ($ᵗ ((pattern.selected → FewTimeView) × FewTimeView) :
        ProbComp ((pattern.selected → FewTimeView) × FewTimeView)) <*>
      ($ᵗ BitVec (127 * configuration.prehit.card) :
        ProbComp (BitVec (127 * configuration.prehit.card)))] = _
  calc
    _ = Pr[FixedFewTimePatternHit pattern.assignment |
            ($ᵗ ((pattern.selected → FewTimeView) × FewTimeView) :
              ProbComp ((pattern.selected → FewTimeView) × FewTimeView))] *
          Pr[fun value : BitVec (127 * configuration.prehit.card) => value = 0 |
            ($ᵗ BitVec (127 * configuration.prehit.card) :
              ProbComp (BitVec (127 * configuration.prehit.card)))] := by
      apply probEvent_seq_map_eq_mul
      intro views _hviews activations _hactivations
      rfl
    _ = ((2 ^ (totalHeight * Fintype.card pattern.selected +
              ftsTreeHeight * (ftsTrees - 1)) : Nat) : ℝ≥0∞)⁻¹ *
          ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ ^
            configuration.prehit.card := by
      have hpattern :
          Pr[FixedFewTimePatternHit pattern.assignment |
            ($ᵗ ((pattern.selected → FewTimeView) × FewTimeView) :
              ProbComp ((pattern.selected → FewTimeView) × FewTimeView))] =
            ((2 ^ (totalHeight * Fintype.card pattern.selected +
              ftsTreeHeight * (ftsTrees - 1)) : Nat) : ℝ≥0∞)⁻¹ := by
        apply probEvent_fixedFewTimePatternHit_eq_inv_of_evalDist pattern.assignment
        simp only [evalDist_uniformSample]
      have hactivation := probEvent_uniformOriginActivation_zero configuration.prehit.card
      exact congrArg₂ (fun left right => left * right) hpattern hactivation
    _ = _ := by
      rw [Fintype.card_coe, pattern.card_selected]

theorem sum_probEvent_originConfiguration_hit {signatures distinct sources : Nat}
    (pattern : FewTimePattern signatures distinct) :
    (∑ configuration : OriginConfiguration pattern sources,
      Pr[configuration.Hit |
        ($ᵗ configuration.Sample : ProbComp configuration.Sample)]) =
      originChoiceMass pattern.selected sources ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ *
        ((2 ^ (totalHeight * distinct + ftsTreeHeight * (ftsTrees - 1)) : Nat) :
          ℝ≥0∞)⁻¹ := by
  classical
  simp_rw [probEvent_originConfiguration_hit]
  calc
    (∑ configuration : OriginConfiguration pattern sources,
        ((2 ^ (totalHeight * distinct + ftsTreeHeight * (ftsTrees - 1)) : Nat) :
            ℝ≥0∞)⁻¹ *
          ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ ^ configuration.prehit.card) =
        ∑ data : Σ prehit : Finset pattern.selected, InjectiveSources prehit sources,
          ((2 ^ (totalHeight * distinct + ftsTreeHeight * (ftsTrees - 1)) : Nat) :
              ℝ≥0∞)⁻¹ *
            ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ ^ data.1.card := by
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

noncomputable def idealOriginUnionBound (signatures sources : Nat) : ℝ≥0∞ :=
  ∑ distinct ∈ Finset.Icc 1 14,
    ∑ pattern : FewTimePattern signatures distinct,
      ∑ configuration : OriginConfiguration pattern sources,
        Pr[configuration.Hit |
          ($ᵗ configuration.Sample : ProbComp configuration.Sample)]

theorem idealOriginUnionBound_eq_weightedFewTimePatternBound (signatures sources : Nat) :
    idealOriginUnionBound signatures sources =
      weightedFewTimePatternBound signatures sources := by
  classical
  rw [idealOriginUnionBound, weightedFewTimePatternBound]
  apply Finset.sum_congr rfl
  intro distinct _
  apply Finset.sum_congr rfl
  intro pattern _
  rw [sum_probEvent_originConfiguration_hit pattern]
  simp only [totalHeight, ftsTreeHeight, ftsTrees]

theorem idealOriginUnionBound_le {signatures sources : Nat}
    (hsignatures : signatures ≤ signatureLimit) (hsources : sources ≤ 2 ^ 120) :
    idealOriginUnionBound signatures sources ≤
      ((2 ^ 121 : Nat) : ℝ≥0∞)⁻¹ := by
  rw [idealOriginUnionBound_eq_weightedFewTimePatternBound]
  exact weightedFewTimePatternBound_le hsignatures hsources

theorem idealOriginUnionBound_le_nine_mul_inv {signatures sources : Nat}
    (hsignatures : signatures ≤ signatureLimit) (hsources : sources ≤ 2 ^ 120) :
    idealOriginUnionBound signatures sources ≤
      9 * ((2 ^ 125 : Nat) : ℝ≥0∞)⁻¹ := by
  rw [idealOriginUnionBound_eq_weightedFewTimePatternBound]
  exact weightedFewTimePatternBound_le_nine_mul_inv hsignatures hsources

end SphincsSecurity.Concrete
