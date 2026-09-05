import SphincsSecurity.Proof.TightEncodingSelectionPotential

namespace SphincsSecurity.Concrete.TightEncoding

open OracleComp OracleSpec ENNReal

noncomputable def encodingStageIncrement (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (position : EncodingPosition) : Nat :=
  open Classical in
  if HasEncodingTarget cache secretKey position then 0
  else if EncodingMessageSettledAt cache secretKey position then 1
  else 2

theorem encodingStageContribution_cacheQuery_le_increment
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {input : HashInput} {answer : HashOutput} {position : EncodingPosition}
    (hfresh : cache input = none) (hat : AtEncodingPosition secretKey.parameter input position) :
    encodingStageContribution (cache.cacheQuery input answer) secretKey position ≤
      encodingStageContribution cache secretKey position + encodingStageIncrement cache secretKey position := by
  classical
  have hle := le_cacheQuery (cache := cache) (input := input) (answer := answer) hfresh
  rw [encodingStageIncrement]
  by_cases htarget : HasEncodingTarget cache secretKey position
  · rw [if_pos htarget]
    simp [encodingStageContribution, htarget, htarget.mono hle]
  · rw [if_neg htarget]
    by_cases hmessage : EncodingMessageSettledAt cache secretKey position
    · rw [if_pos hmessage]
      have hcard : (encodingCachedAt secretKey.parameter (cache.cacheQuery input answer) position).ncard ≤
          (encodingCachedAt secretKey.parameter cache position).ncard + 1 := by
        rw [encodingCachedAt_cacheQuery_self hat]
        exact Set.ncard_insert_le _ _
      rw [encodingStageContribution, encodingStageContribution, if_neg htarget, if_pos hmessage]
      rw [if_pos (hmessage.mono hle)]
      split_ifs with hafter
      · exact Nat.zero_le _
      · exact hcard
    · rw [if_neg hmessage]
      exact encodingStageContribution_cacheQuery_le_of_atPosition hfresh hat

set_option maxRecDepth 10000 in
theorem encodingStagePotential_cacheQuery_le_increment
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {input : HashInput} {answer : HashOutput} {position : EncodingPosition}
    (hfresh : cache input = none) (hat : AtEncodingPosition secretKey.parameter input position) :
    encodingStagePotential (cache.cacheQuery input answer) secretKey ≤
      encodingStagePotential cache secretKey + encodingStageIncrement cache secretKey position := by
  classical
  rw [encodingStagePotential, encodingStagePotential]
  calc
    _ ≤ ∑ candidate : EncodingPosition,
        (encodingStageContribution cache secretKey candidate +
          if candidate = position then encodingStageIncrement cache secretKey position else 0) := by
      apply Finset.sum_le_sum
      intro candidate _
      by_cases heq : candidate = position
      · rw [heq, if_pos rfl]
        exact encodingStageContribution_cacheQuery_le_increment (answer := answer) hfresh hat
      · rw [if_neg heq, Nat.add_zero]
        exact encodingStageContribution_cacheQuery_le_of_not_atPosition hfresh
          (fun hc => heq (atEncodingPosition_unique hc hat))
    _ = _ := by rw [Finset.sum_add_distrib, Fintype.sum_ite_eq']

theorem encodingStructuralPotential_cacheQuery_le_increment
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {input : HashInput} {answer : HashOutput} {position : EncodingPosition}
    (hclean : ¬ Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache)
    (hfresh : cache input = none) (hat : AtEncodingPosition secretKey.parameter input position) :
    encodingStructuralPotential (cache.cacheQuery input answer) secretKey ≤
      encodingStructuralPotential cache secretKey + encodingStageIncrement cache secretKey position := by
  have hstructural :=
    (clean_and_tightPotential_cacheQuery_of_not_atPosition secretKey.parameter
      secretKey.otsSecret secretKey.ftsSecret (answer := answer) hclean hfresh
      (fun structural hstructural => hat.not_atPosition structural hstructural)).2
  have hstage := encodingStagePotential_cacheQuery_le_increment (answer := answer) hfresh hat
  rw [encodingStructuralPotential, encodingStructuralPotential]
  omega

theorem uniform_encodingSelectionTotalPotential_cacheQuery_le_stage_increment
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {position : EncodingPosition}
    (huncached : cache input = none)
    (hposition : AtEncodingPosition secretKey.parameter input position) :
    (∑' answer : HashOutput,
      Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
        encodingSelectionTotalPotential (cache.cacheQuery input answer)
          (finite_cacheQuery hfinite input answer) secretKey) ≤
      encodingSelectionTotalPotential cache hfinite secretKey +
        ((encodingStageIncrement cache secretKey position + 1 : Nat) : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  let eps := (Fintype.card Digest : ℝ≥0∞)⁻¹
  by_cases hbad : Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
  · have hbefore : encodingSelectionTotalPotential cache hfinite secretKey = 1 := by
      rw [encodingSelectionTotalPotential, if_pos hbad]
    rw [hbefore]
    exact (expected_encodingSelectionTotalPotential_le_one hfinite secretKey input).trans
      (le_add_right le_rfl)
  · let uncapped := (encodingStructuralPotential cache secretKey : ℝ≥0∞) * eps +
      encodingSelectionPotential cache hfinite secretKey
    by_cases hone : 1 ≤ uncapped
    · calc
        _ ≤ ∑' answer : HashOutput,
            Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] * 1 := by
              apply ENNReal.tsum_le_tsum
              intro answer
              exact mul_le_mul_right
                (encodingSelectionTotalPotential_le_one _ secretKey) _
        _ = 1 := by
              simp only [mul_one, tsum_probOutput_of_liftM_PMF]
        _ = encodingSelectionTotalPotential cache hfinite secretKey := by
              rw [encodingSelectionTotalPotential, if_neg hbad, min_eq_left]
              simpa only [uncapped] using hone
        _ ≤ encodingSelectionTotalPotential cache hfinite secretKey + ((encodingStageIncrement cache secretKey position + 1 : Nat) : ℝ≥0∞) * eps :=
              le_add_right le_rfl
    · have huncappedLe : uncapped ≤ 1 := le_of_not_ge hone
      have hbefore : encodingSelectionTotalPotential cache hfinite secretKey = uncapped := by
        rw [encodingSelectionTotalPotential, if_neg hbad, min_eq_right]
        exact huncappedLe
      calc
        _ ≤ ∑' answer : HashOutput,
            Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
              (((encodingStructuralPotential cache secretKey + encodingStageIncrement cache secretKey position : Nat) : ℝ≥0∞) * eps +
                encodingSelectionPotential (cache.cacheQuery input answer)
                  (finite_cacheQuery hfinite input answer) secretKey) := by
              apply ENNReal.tsum_le_tsum
              intro answer
              apply mul_le_mul_right
              have hcleanAfter :=
                (clean_and_tightPotential_cacheQuery_of_not_atPosition secretKey.parameter
                  secretKey.otsSecret secretKey.ftsSecret (answer := answer) hbad huncached
                  (fun structuralPosition hat => hposition.not_atPosition structuralPosition hat)).1
              refine (encodingSelectionTotalPotential_le_uncapped _ secretKey hcleanAfter).trans ?_
              have hstructuralNat :=
                encodingStructuralPotential_cacheQuery_le_increment
                  (answer := answer) hbad huncached hposition
              have hstructural :
                  (encodingStructuralPotential (cache.cacheQuery input answer)
                    secretKey : ℝ≥0∞) ≤
                    ((encodingStructuralPotential cache secretKey + encodingStageIncrement cache secretKey position : Nat) : ℝ≥0∞) :=
                Nat.cast_le.mpr hstructuralNat
              exact add_le_add (mul_le_mul_left hstructural eps) le_rfl
        _ = (((encodingStructuralPotential cache secretKey + encodingStageIncrement cache secretKey position : Nat) : ℝ≥0∞) * eps) +
            ∑' answer : HashOutput,
              Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                encodingSelectionPotential (cache.cacheQuery input answer)
                  (finite_cacheQuery hfinite input answer) secretKey := by
              simp_rw [mul_add]
              rw [ENNReal.tsum_add, ENNReal.tsum_mul_right,
                tsum_probOutput_of_liftM_PMF, one_mul]
        _ ≤ (((encodingStructuralPotential cache secretKey + encodingStageIncrement cache secretKey position : Nat) : ℝ≥0∞) * eps) +
            (encodingSelectionPotential cache hfinite secretKey + eps) := by
              exact add_le_add le_rfl
                (uniform_encodingSelectionPotential_cacheQuery_atPosition_sum_le
                  (cache := cache) (secretKey := secretKey) (input := input)
                  (position := position) hfinite huncached hposition)
        _ = uncapped + ((encodingStageIncrement cache secretKey position + 1 : Nat) : ℝ≥0∞) * eps := by
              simp only [Nat.cast_add, Nat.cast_one]
              dsimp only [uncapped]
              ring
        _ = encodingSelectionTotalPotential cache hfinite secretKey + ((encodingStageIncrement cache secretKey position + 1 : Nat) : ℝ≥0∞) * eps := by
              rw [hbefore]

end SphincsSecurity.Concrete.TightEncoding
