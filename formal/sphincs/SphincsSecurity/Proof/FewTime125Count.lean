import SphincsSecurity.Proof.FewTimeOriginSampler

/-! Weighted forest-pattern counting for budgets up to `2^125`. The bound retains the number of selected signatures in each origin weight. -/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

set_option exponentiation.threshold 600

theorem weightedFewTime125_scaled_certificate :
    (∑ d ∈ Finset.Icc 1 14,
      (d + 1).ascFactorial (14 - d) * 2 ^ (24 * d) * d ^ 14 *
        5 ^ d * 2 ^ (28 * (14 - d))) ≤ Nat.factorial 14 * 2 ^ 411 := by
  decide

theorem weightedFewTime125_scaled_sum_le {signatures : Nat}
    (hsignatures : signatures ≤ signatureLimit) :
    Nat.factorial 14 * (∑ d ∈ Finset.Icc 1 14,
      Fintype.card (FewTimePattern signatures d) * 5 ^ d * 2 ^ (28 * (14 - d))) ≤
        Nat.factorial 14 * 2 ^ 411 := by
  rw [Finset.mul_sum]
  apply le_trans (Finset.sum_le_sum fun d hd => ?_) weightedFewTime125_scaled_certificate
  have hd14 := (Finset.mem_Icc.mp hd).2
  have hfactorial := Nat.factorial_mul_ascFactorial d (14 - d)
  rw [Nat.add_sub_of_le hd14] at hfactorial
  calc
    _ = (d + 1).ascFactorial (14 - d) *
        (Nat.factorial d * Fintype.card (FewTimePattern signatures d)) *
          5 ^ d * 2 ^ (28 * (14 - d)) := by rw [← hfactorial]; ring
    _ ≤ (d + 1).ascFactorial (14 - d) *
        (2 ^ (24 * d) * d ^ (ftsTrees - 1)) * 5 ^ d * 2 ^ (28 * (14 - d)) := by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
        (fewTimePattern_card_scaled_le_signatureLimit hsignatures)))
    _ = _ := by rw [show ftsTrees - 1 = 14 by rfl]; ring

theorem FewTimePattern.originChoiceMass_le_five_fourths_pow
    {signatures distinct q : Nat} (pattern : FewTimePattern signatures distinct)
    (hq : q ≤ 2 ^ 125) :
    originChoiceMass pattern.selected q ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ ≤
      (5 / 4 : ℝ≥0∞) ^ distinct := by
  calc
    _ ≤ (1 + q * ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹) ^
        Fintype.card pattern.selected := originChoiceMass_le _ _ _
    _ = (1 + q * ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹) ^ distinct := by
      rw [Fintype.card_coe, pattern.card_selected]
    _ ≤ _ := by
      gcongr
      calc
        _ ≤ 1 + ((2 ^ 125 : Nat) : ℝ≥0∞) * ((2 ^ 127 : Nat) : ℝ≥0∞)⁻¹ := by
          gcongr
        _ = 5 / 4 := by
          apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
          rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
          simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div,
            ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
          norm_num

theorem weightedFewTime125_term_common_denominator (signatures d : Nat)
    (hd : d ≤ 14) :
    (Fintype.card (FewTimePattern signatures d) : ℝ≥0∞) * (5 / 4 : ℝ≥0∞) ^ d *
        ((2 ^ (26 * d + 140) : Nat) : ℝ≥0∞)⁻¹ =
      (Fintype.card (FewTimePattern signatures d) * 5 ^ d * 2 ^ (28 * (14 - d)) : Nat) *
        ((2 ^ 532 : Nat) : ℝ≥0∞)⁻¹ := by
  have hden : (4 : ℝ≥0∞) ^ d * ((2 ^ (26 * d + 140) : Nat) : ℝ≥0∞) =
      ((2 ^ (28 * d + 140) : Nat) : ℝ≥0∞) := by
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    rw [show (4 : ℝ≥0∞) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
    congr 1
    omega
  have hbase : (Fintype.card (FewTimePattern signatures d) : ℝ≥0∞) * (5 / 4 : ℝ≥0∞) ^ d *
      ((2 ^ (26 * d + 140) : Nat) : ℝ≥0∞)⁻¹ =
      (Fintype.card (FewTimePattern signatures d) * 5 ^ d : Nat) /
        ((2 ^ (28 * d + 140) : Nat) : ℝ≥0∞) := by
    rw [div_eq_mul_inv, mul_pow]
    rw [div_eq_mul_inv, ← hden, ENNReal.mul_inv (by left; positivity) (by right; finiteness)]
    simp only [ENNReal.inv_pow, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    ring
  rw [hbase, ← div_eq_mul_inv]
  let factor : ℝ≥0∞ := (2 ^ (28 * (14 - d)) : Nat)
  have hz : factor ≠ 0 := by positivity
  have ht : factor ≠ ∞ := by simp [factor]
  rw [← ENNReal.mul_div_mul_right
    (Fintype.card (FewTimePattern signatures d) * 5 ^ d : Nat)
    ((2 ^ (28 * d + 140) : Nat) : ℝ≥0∞) hz ht]
  congr 1
  · simp [factor, Nat.cast_mul]
  · dsimp [factor]
    rw [← Nat.cast_mul, ← pow_add, show 28 * d + 140 + 28 * (14 - d) = 532 by omega]
    norm_num

theorem weightedFewTimePatternBound_le_inv121_of_queries_le125 {signatures q : Nat}
    (hsignatures : signatures ≤ signatureLimit) (hq : q ≤ 2 ^ 125) :
    weightedFewTimePatternBound signatures q ≤ ((2 ^ 121 : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 14, ∑ _pattern : FewTimePattern signatures d,
        (5 / 4 : ℝ≥0∞) ^ d * ((2 ^ (26 * d + 140) : Nat) : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro pattern _
      gcongr
      exact pattern.originChoiceMass_le_five_fourths_pow hq
    _ = ∑ d ∈ Finset.Icc 1 14,
        (Fintype.card (FewTimePattern signatures d) * 5 ^ d * 2 ^ (28 * (14 - d)) : Nat) *
          ((2 ^ 532 : Nat) : ℝ≥0∞)⁻¹ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      apply Finset.sum_congr rfl
      intro d hd
      rw [← mul_assoc]
      exact weightedFewTime125_term_common_denominator signatures d (Finset.mem_Icc.mp hd).2
    _ = ((∑ d ∈ Finset.Icc 1 14,
        Fintype.card (FewTimePattern signatures d) * 5 ^ d * 2 ^ (28 * (14 - d)) : Nat) : ℝ≥0∞) *
          ((2 ^ 532 : Nat) : ℝ≥0∞)⁻¹ := by rw [← Finset.sum_mul, Nat.cast_sum]
    _ ≤ ((2 ^ 411 : Nat) : ℝ≥0∞) * ((2 ^ 532 : Nat) : ℝ≥0∞)⁻¹ := by
      gcongr
      exact_mod_cast Nat.le_of_mul_le_mul_left (weightedFewTime125_scaled_sum_le hsignatures)
        (Nat.factorial_pos 14)
    _ = _ := by
      rw [show 532 = 411 + 121 by decide, pow_add, Nat.cast_mul,
        ENNReal.mul_inv (by left; positivity) (by right; simp), ← mul_assoc,
        ENNReal.mul_inv_cancel (by positivity) (by simp), one_mul]

theorem idealOriginUnionBound_le_inv121_of_queries_le125 {signatures q : Nat}
    (hsignatures : signatures ≤ signatureLimit) (hq : q ≤ 2 ^ 125) :
    idealOriginUnionBound signatures q ≤ ((2 ^ 121 : Nat) : ℝ≥0∞)⁻¹ := by
  rw [idealOriginUnionBound_eq_weightedFewTimePatternBound]
  exact weightedFewTimePatternBound_le_inv121_of_queries_le125 hsignatures hq

abbrev OriginConfiguration.RawTargetSample {signatures distinct : Nat}
    {pattern : FewTimePattern signatures distinct} {sources : Nat}
    (configuration : OriginConfiguration pattern sources) :=
  ((pattern.selected → FewTimeView) × HashOutput) × BitVec (127 * configuration.prehit.card)

def OriginConfiguration.RawTargetHit {signatures distinct : Nat}
    {pattern : FewTimePattern signatures distinct} {sources : Nat}
    (configuration : OriginConfiguration pattern sources)
    (sample : configuration.RawTargetSample) : Prop :=
  (signAttemptResultOfOutput sample.1.2 ≠ none ∧
    FixedFewTimePatternHit pattern.assignment (sample.1.1, hashOutputFewTimeView sample.1.2)) ∧
      sample.2 = 0

theorem probEvent_rawTargetPatternHit_eq_admissible_mul
    {Selected : Type} [Fintype Selected] [DecidableEq Selected] [Nonempty Selected]
    (assignment : FtsTree → Selected) :
    Pr[fun sample : (Selected → FewTimeView) × HashOutput =>
      signAttemptResultOfOutput sample.2 ≠ none ∧
        FixedFewTimePatternHit assignment (sample.1, hashOutputFewTimeView sample.2) |
      ($ᵗ ((Selected → FewTimeView) × HashOutput) : ProbComp _)] =
    ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ *
      Pr[FixedFewTimePatternHit assignment |
        ($ᵗ ((Selected → FewTimeView) × FewTimeView) : ProbComp _)] := by
  let rawEvent := fun sample : (Selected → FewTimeView) × HashOutput =>
    signAttemptResultOfOutput sample.2 ≠ none ∧
      FixedFewTimePatternHit assignment (sample.1, hashOutputFewTimeView sample.2)
  have hraw : Pr[rawEvent | ($ᵗ ((Selected → FewTimeView) × HashOutput) : ProbComp _)] =
      Pr[rawEvent | (($ᵗ (Selected → FewTimeView) : ProbComp _) >>= fun views =>
        Prod.mk views <$> ($ᵗ HashOutput : ProbComp _))] := by
    apply probEvent_congr' (fun _ _ => Iff.rfl)
    simpa only [map_eq_bind_pure_comp, Function.comp_apply, evalDist_bind, evalDist_pure, evalDist_uniformSample] using
      (evalDist_independent_uniform_pair (α := Selected → FewTimeView) (β := HashOutput)).symm
  have hviews : Pr[FixedFewTimePatternHit assignment |
      ($ᵗ ((Selected → FewTimeView) × FewTimeView) : ProbComp _)] =
      Pr[FixedFewTimePatternHit assignment |
        (($ᵗ (Selected → FewTimeView) : ProbComp _) >>= fun views =>
          Prod.mk views <$> ($ᵗ FewTimeView : ProbComp _))] := by
    apply probEvent_congr' (fun _ _ => Iff.rfl)
    simpa only [map_eq_bind_pure_comp, Function.comp_apply, evalDist_bind, evalDist_pure, evalDist_uniformSample] using
      (evalDist_independent_uniform_pair (α := Selected → FewTimeView) (β := FewTimeView)).symm
  change Pr[rawEvent | _] = _
  rw [hraw, hviews]
  dsimp only [rawEvent]
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  simp only [probEvent_map, Function.comp_def]
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro views
  have hview := probEvent_uniformHashOutput_admissible_view
    (fun target => FixedFewTimePatternHit assignment (views, target))
  simp only [probEvent_uniformSample] at hview ⊢
  rw [hview]
  ring

theorem probEvent_originConfiguration_rawTargetHit
    {signatures distinct : Nat} {pattern : FewTimePattern signatures distinct} {sources : Nat}
    (configuration : OriginConfiguration pattern sources) :
    Pr[configuration.RawTargetHit |
      ($ᵗ configuration.RawTargetSample : ProbComp configuration.RawTargetSample)] =
      ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ *
        Pr[configuration.Hit | ($ᵗ configuration.Sample : ProbComp configuration.Sample)] := by
  classical
  letI : Nonempty pattern.selected := ⟨pattern.assignment ⟨0, by decide⟩⟩
  have hraw : Pr[configuration.RawTargetHit |
      ($ᵗ configuration.RawTargetSample : ProbComp configuration.RawTargetSample)] =
      Pr[fun sample : (pattern.selected → FewTimeView) × HashOutput =>
        signAttemptResultOfOutput sample.2 ≠ none ∧
          FixedFewTimePatternHit pattern.assignment (sample.1, hashOutputFewTimeView sample.2) |
        ($ᵗ ((pattern.selected → FewTimeView) × HashOutput) : ProbComp _)] *
      Pr[fun value : BitVec (127 * configuration.prehit.card) => value = 0 |
        ($ᵗ BitVec (127 * configuration.prehit.card) : ProbComp _)] := by
    apply probEvent_seq_map_eq_mul
    intro _ _ _ _
    rfl
  have hideal : Pr[configuration.Hit | ($ᵗ configuration.Sample : ProbComp configuration.Sample)] =
      Pr[FixedFewTimePatternHit pattern.assignment |
        ($ᵗ ((pattern.selected → FewTimeView) × FewTimeView) : ProbComp _)] *
      Pr[fun value : BitVec (127 * configuration.prehit.card) => value = 0 |
        ($ᵗ BitVec (127 * configuration.prehit.card) : ProbComp _)] := by
    apply probEvent_seq_map_eq_mul
    intro _ _ _ _
    rfl
  rw [hraw, hideal]
  have hpattern := probEvent_rawTargetPatternHit_eq_admissible_mul pattern.assignment
  simp only [probEvent_uniformSample] at hpattern ⊢
  rw [hpattern, mul_assoc]

noncomputable def rawTargetOriginUnionBound (signatures sources : Nat) : ℝ≥0∞ :=
  ∑ distinct ∈ Finset.Icc 1 14,
    ∑ pattern : FewTimePattern signatures distinct,
      ∑ configuration : OriginConfiguration pattern sources,
        Pr[configuration.RawTargetHit |
          ($ᵗ configuration.RawTargetSample : ProbComp configuration.RawTargetSample)]

theorem rawTargetOriginUnionBound_eq (signatures sources : Nat) :
    rawTargetOriginUnionBound signatures sources =
      ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ * idealOriginUnionBound signatures sources := by
  classical
  unfold rawTargetOriginUnionBound idealOriginUnionBound
  simp_rw [probEvent_originConfiguration_rawTargetHit, ← Finset.mul_sum]

theorem rawTargetOriginUnionBound_le_inv131 {signatures q : Nat}
    (hsignatures : signatures ≤ signatureLimit) (hq : q ≤ 2 ^ 125) :
    rawTargetOriginUnionBound signatures q ≤ ((2 ^ 131 : Nat) : ℝ≥0∞)⁻¹ := by
  rw [rawTargetOriginUnionBound_eq]
  calc
    _ ≤ ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹ * ((2 ^ 121 : Nat) : ℝ≥0∞)⁻¹ :=
      mul_le_mul_right (idealOriginUnionBound_le_inv121_of_queries_le125 hsignatures hq) _
    _ = _ := by
      rw [← ENNReal.mul_inv (by left; positivity) (by right; simp), ← Nat.cast_mul,
        ← pow_add, show ftsTreeHeight + 121 = 131 by rfl]

end SphincsSecurity.Concrete
