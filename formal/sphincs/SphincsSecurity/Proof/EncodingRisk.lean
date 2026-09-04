import SphincsSecurity.Proof.EncodingRetryCharge
import SphincsSecurity.Proof.EncodingStageCharge

/-!
# Encoding collision risk

Before a canonical encoding target is pinned, the risk at one position is the normalized number of admissible cached answers. Once a latent collision and its target coexist, that position contributes one. The structural potential pays the finite target sets used when the layer message or target becomes settled.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

noncomputable def encodingCollisionRiskContribution
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (position : EncodingPosition) : ℝ≥0∞ :=
  open Classical in
    if LatentEncodingBadAt cache secretKey position ∧
        HasEncodingTarget cache secretKey position then
      1
    else
      encodingRetryContribution cache secretKey position

noncomputable def encodingCollisionRiskPotential
    (cache : QueryCache HashSpec) (secretKey : SecretKey) : ℝ≥0∞ :=
  ∑ position : EncodingPosition,
    encodingCollisionRiskContribution cache secretKey position

noncomputable def encodingTotalRiskPotential
    (cache : QueryCache HashSpec) (secretKey : SecretKey) : ℝ≥0∞ :=
  (encodingStructuralPotential cache secretKey : ℝ≥0∞) *
      (Fintype.card Digest : ℝ≥0∞)⁻¹ +
    encodingCollisionRiskPotential cache secretKey

theorem encodingCollisionRiskContribution_eq_one
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {position : EncodingPosition}
    (hlatent : LatentEncodingBadAt cache secretKey position)
    (htarget : HasEncodingTarget cache secretKey position) :
    encodingCollisionRiskContribution cache secretKey position = 1 := by
  rw [encodingCollisionRiskContribution, if_pos ⟨hlatent, htarget⟩]

theorem encodingCollisionRiskContribution_eq_retry
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {position : EncodingPosition}
    (hclean : ¬ LatentEncodingBadAt cache secretKey position) :
    encodingCollisionRiskContribution cache secretKey position =
      encodingRetryContribution cache secretKey position := by
  rw [encodingCollisionRiskContribution, if_neg]
  exact fun hbad => hclean hbad.1

theorem encodingCollisionRiskContribution_eq_zero_of_clean_target
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {position : EncodingPosition}
    (hclean : ¬ LatentEncodingBadAt cache secretKey position)
    (htarget : HasEncodingTarget cache secretKey position) :
    encodingCollisionRiskContribution cache secretKey position = 0 := by
  rw [encodingCollisionRiskContribution_eq_retry hclean,
    encodingRetryContribution_eq_zero_of_target htarget]

theorem encodingCollisionRiskPotential_eq_retryPotential_of_not_encodingBad
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    (hclean : ¬ EncodingBad cache secretKey) :
    encodingCollisionRiskPotential cache secretKey =
      encodingRetryPotential cache secretKey := by
  rw [encodingCollisionRiskPotential, encodingRetryPotential]
  apply Finset.sum_congr rfl
  intro position _
  rw [encodingCollisionRiskContribution, if_neg]
  rintro ⟨hlatent, htarget⟩
  exact hclean (hlatent.encodingBad_of_hasTarget htarget)

theorem encodingTotalRiskPotential_eq_of_not_encodingBad
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    (hclean : ¬ EncodingBad cache secretKey) :
    encodingTotalRiskPotential cache secretKey =
      (encodingStructuralPotential cache secretKey : ℝ≥0∞) *
          (Fintype.card Digest : ℝ≥0∞)⁻¹ +
        encodingRetryPotential cache secretKey := by
  rw [encodingTotalRiskPotential,
    encodingCollisionRiskPotential_eq_retryPotential_of_not_encodingBad hclean]

@[simp] theorem encodingCollisionRiskPotential_empty (secretKey : SecretKey) :
    encodingCollisionRiskPotential ∅ secretKey = 0 := by
  rw [encodingCollisionRiskPotential]
  apply Fintype.sum_eq_zero
  intro position
  rw [encodingCollisionRiskContribution, if_neg]
  · exact encodingRetryContribution_empty secretKey position
  · rintro ⟨hlatent, _⟩
    exact not_latentEncodingBad_empty secretKey ⟨position, hlatent⟩

@[simp] theorem encodingTotalRiskPotential_empty (secretKey : SecretKey) :
    encodingTotalRiskPotential ∅ secretKey = 0 := by
  rw [encodingTotalRiskPotential, encodingStructuralPotential_empty,
    encodingCollisionRiskPotential_empty]
  simp

theorem one_le_encodingCollisionRiskPotential_of_encodingBad
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    (hbad : EncodingBad cache secretKey) :
    1 ≤ encodingCollisionRiskPotential cache secretKey := by
  obtain ⟨position, htarget, hlatent⟩ := hbad.latent_with_target
  rw [encodingCollisionRiskPotential, Fintype.sum_eq_add_sum_subtype_ne _ position,
    encodingCollisionRiskContribution_eq_one hlatent htarget]
  exact le_add_right le_rfl

theorem one_le_encodingTotalRiskPotential_of_encodingBad
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    (hbad : EncodingBad cache secretKey) :
    1 ≤ encodingTotalRiskPotential cache secretKey := by
  exact (one_le_encodingCollisionRiskPotential_of_encodingBad hbad).trans
    (le_add_left le_rfl)

theorem probEvent_encodingBad_le_expected_totalRisk
    {alpha : Type} (oa : ProbComp (alpha × QueryCache HashSpec))
    (secretKey : SecretKey) :
    Pr[fun result => EncodingBad result.2 secretKey | oa] ≤
      ∑' result, Pr[= result | oa] *
        encodingTotalRiskPotential result.2 secretKey := by
  classical
  rw [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hbad : EncodingBad result.2 secretKey
  · rw [if_pos hbad]
    exact le_mul_of_one_le_right bot_le
      (one_le_encodingTotalRiskPotential_of_encodingBad hbad)
  · rw [if_neg hbad]
    exact bot_le

theorem encodingRetry_buildThenSelect_sum_probability_le
    (steps : EncodingPosition → Nat) (q : Nat)
    (hsteps : (∑ position, steps position) ≤ q) :
    (∑ position,
      Pr[(· = true) | EncodingRetry.buildThenSelect (steps position) ∅]) ≤
        (q : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  calc
    (∑ position,
        Pr[(· = true) | EncodingRetry.buildThenSelect (steps position) ∅]) ≤
      ∑ position, (steps position : ℝ≥0∞) *
        (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
          apply Finset.sum_le_sum
          intro position _
          exact EncodingRetry.buildThenSelect_empty_true_probability_le (steps position)
    _ = ((∑ position, steps position : Nat) : ℝ≥0∞) *
        (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
      rw [Nat.cast_sum, Finset.sum_mul]
    _ ≤ (q : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
      exact mul_le_mul_left (by exact_mod_cast hsteps)
        (Fintype.card Digest : ℝ≥0∞)⁻¹

theorem encodingRetry_cachedBuildThenSelect_sum_probability_le
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    (parameter : PublicParameter) :
    (∑ position : EncodingPosition,
      Pr[(· = true) | EncodingRetry.buildThenSelect
        (encodingCachedAt parameter cache position).ncard ∅]) ≤
      QueryCache.enncard cache * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  have hbound := encodingRetry_buildThenSelect_sum_probability_le
    (fun position => (encodingCachedAt parameter cache position).ncard)
    {input | cache input ≠ none}.ncard
    (sum_encodingCachedAt_ncard_le hfinite)
  rw [hfinite.cachedInputs_ncard_toENNReal_eq_enncard] at hbound
  exact hbound

theorem encodingRetryPotential_le_enncard
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    (secretKey : SecretKey) :
    encodingRetryPotential cache secretKey ≤
      QueryCache.enncard cache *
        (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ := by
  classical
  calc
    encodingRetryPotential cache secretKey ≤
        (∑ position : EncodingPosition,
          ((encodingCachedAt secretKey.parameter cache position).ncard : ℝ≥0∞)) *
            (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ := by
      rw [encodingRetryPotential, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro position _
      rw [encodingRetryContribution]
      split
      · exact bot_le
      · exact mul_le_mul_left
          (by
            rw [encodingValidAnswers_ncard_eq_validAnswerTargets_card hfinite position]
            exact_mod_cast encodingValidAnswerTargets_card_le hfinite position)
          _
    _ = ((∑ position : EncodingPosition,
          (encodingCachedAt secretKey.parameter cache position).ncard : Nat) : ℝ≥0∞) *
            (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ := by
      rw [Nat.cast_sum]
    _ ≤ ({input | cache input ≠ none}.ncard : ℝ≥0∞) *
          (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ := by
      exact mul_le_mul_left
        (by exact_mod_cast sum_encodingCachedAt_ncard_le hfinite) _
    _ = QueryCache.enncard cache *
          (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ := by
      rw [hfinite.cachedInputs_ncard_toENNReal_eq_enncard]

end SphincsSecurity.Concrete
