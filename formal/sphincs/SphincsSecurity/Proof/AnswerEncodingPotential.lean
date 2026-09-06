import SphincsSecurity.Proof.AnswerEncodingStep

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

attribute [local irreducible] instFintypePosition answerPotential answerEncodingPotential
attribute [local instance] Classical.propDecidable

noncomputable def answerEncodingTotalPotential (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (secretKey : SecretKey) : ℝ≥0∞ :=
  if Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache then 1
  else min 1 ((answerEncodingPotential cache secretKey : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
    encodingSelectionPotential cache hfinite secretKey)

theorem answerEncodingTotalPotential_le_one {cache : QueryCache HashSpec} (hfinite : Finite cache) (secretKey : SecretKey) :
    answerEncodingTotalPotential cache hfinite secretKey ≤ 1 := by
  unfold answerEncodingTotalPotential
  split_ifs <;> simp

theorem answerEncodingTotalPotential_eq_one_of_bad_or_encodingBad
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {secretKey : SecretKey}
    (hbad : Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache ∨ EncodingBad cache secretKey) :
    answerEncodingTotalPotential cache hfinite secretKey = 1 := by
  unfold answerEncodingTotalPotential
  split_ifs with hstructural
  · rfl
  · apply min_eq_left
    exact (one_le_encodingSelectionPotential_of_encodingBad hfinite (hbad.resolve_left hstructural)).trans le_add_self

@[simp] theorem answerEncodingTotalPotential_empty (secretKey : SecretKey) :
    answerEncodingTotalPotential ∅ finite_empty secretKey = 0 := by
  rw [answerEncodingTotalPotential, if_neg (not_bad_empty secretKey.parameter secretKey.otsSecret secretKey.ftsSecret),
    answerEncodingPotential_empty, encodingSelectionPotential_empty]
  simp

theorem uniform_answerEncodingTotalPotential_without_parent_le_step
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {secretKey : SecretKey} {input : HashInput}
    (cost : Nat)
    (hstep : ¬ Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache →
      ∃ targets : Finset Digest, targets.card ≤ answerEncodingPotential cache secretKey + cost ∧
        ∀ answer : HashOutput,
          ¬ ParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache input answer →
          truncateHash answer ∉ targets →
          ¬ Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret (cache.cacheQuery input answer) ∧
            answerEncodingPotential (cache.cacheQuery input answer) secretKey + targets.card ≤ answerEncodingPotential cache secretKey + cost ∧
            encodingSelectionPotential (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) secretKey ≤
              encodingSelectionPotential cache hfinite secretKey) :
    (∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache input answer then 0
        else answerEncodingTotalPotential (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) secretKey)) ≤
      answerEncodingTotalPotential cache hfinite secretKey + (cost : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  let eps := (Fintype.card Digest : ℝ≥0∞)⁻¹
  have hmass : (∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache input answer then 0
        else answerEncodingTotalPotential (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) secretKey)) ≤ 1 := by
    calc
      _ ≤ ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] * 1 := by
        apply ENNReal.tsum_le_tsum
        intro answer
        apply mul_le_mul' le_rfl
        split_ifs
        · exact bot_le
        · exact answerEncodingTotalPotential_le_one _ _
      _ = _ := by rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
  by_cases hbad : Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
  · rw [answerEncodingTotalPotential, if_pos hbad]
    exact hmass.trans le_self_add
  · let uncapped := (answerEncodingPotential cache secretKey : ℝ≥0∞) * eps + encodingSelectionPotential cache hfinite secretKey
    by_cases hlarge : 1 ≤ uncapped
    · rw [answerEncodingTotalPotential, if_neg hbad, min_eq_left hlarge]
      exact hmass.trans le_self_add
    · have hbefore : answerEncodingTotalPotential cache hfinite secretKey = uncapped := by
        rw [answerEncodingTotalPotential, if_neg hbad, min_eq_right (le_of_not_ge hlarge)]
      obtain ⟨targets, hcard, hsafe⟩ := hstep hbad
      let credit := answerEncodingPotential cache secretKey + cost - targets.card
      have hcredit : targets.card + credit = answerEncodingPotential cache secretKey + cost := Nat.add_sub_of_le hcard
      have hpoint (answer : HashOutput) :
          (if CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache input answer then 0
            else answerEncodingTotalPotential (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) secretKey) ≤
          (if truncateHash answer ∈ targets then 1 else 0) + (credit : ℝ≥0∞) * eps + encodingSelectionPotential cache hfinite secretKey := by
        by_cases hx : CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache input answer
        · rw [if_pos hx]
          exact bot_le
        · rw [if_neg hx]
          by_cases ht : truncateHash answer ∈ targets
          · rw [if_pos ht]
            exact (answerEncodingTotalPotential_le_one _ _).trans (le_self_add.trans le_self_add)
          · rw [if_neg ht, zero_add]
            obtain ⟨hclean, hp, hs⟩ := hsafe answer (fun h => hx ⟨hbad, h⟩) ht
            rw [answerEncodingTotalPotential, if_neg hclean]
            apply (min_le_right _ _).trans
            exact add_le_add (mul_le_mul' (by exact_mod_cast Nat.le_sub_of_add_le hp) le_rfl) hs
      calc
        _ ≤ ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
            ((if truncateHash answer ∈ targets then 1 else 0) + (credit : ℝ≥0∞) * eps + encodingSelectionPotential cache hfinite secretKey) :=
          ENNReal.tsum_le_tsum fun answer => mul_le_mul' le_rfl (hpoint answer)
        _ = (targets.card : ℝ≥0∞) * eps + (credit : ℝ≥0∞) * eps + encodingSelectionPotential cache hfinite secretKey := by
          simp_rw [mul_add, ENNReal.tsum_add]
          rw [uniformHashOutput_mem_bonus_sum_eq]
          rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul, one_mul]
        _ = _ := by
          rw [← add_mul, ← Nat.cast_add, hcredit, Nat.cast_add, add_mul, hbefore]
          dsimp only [uncapped]
          ring

theorem uniform_answerEncodingTotalPotential_atEncoding_le
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {secretKey : SecretKey} {input : HashInput} {position : EncodingPosition}
    (hfresh : cache input = none) (hat : AtEncodingPosition secretKey.parameter input position) :
    (∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
      answerEncodingTotalPotential (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) secretKey) ≤
      answerEncodingTotalPotential cache hfinite secretKey +
        ((TightEncoding.encodingStageIncrement cache secretKey position + 1 : Nat) : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  let eps := (Fintype.card Digest : ℝ≥0∞)⁻¹
  have hmass : (∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
      answerEncodingTotalPotential (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) secretKey) ≤ 1 := by
    calc
      _ ≤ ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] * 1 :=
        ENNReal.tsum_le_tsum fun answer => mul_le_mul' le_rfl (answerEncodingTotalPotential_le_one _ _)
      _ = _ := by rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
  by_cases hbad : Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
  · rw [answerEncodingTotalPotential, if_pos hbad]
    exact hmass.trans le_self_add
  · let uncapped := (answerEncodingPotential cache secretKey : ℝ≥0∞) * eps + encodingSelectionPotential cache hfinite secretKey
    by_cases hlarge : 1 ≤ uncapped
    · rw [answerEncodingTotalPotential, if_neg hbad, min_eq_left hlarge]
      exact hmass.trans le_self_add
    · have hbefore : answerEncodingTotalPotential cache hfinite secretKey = uncapped := by
        rw [answerEncodingTotalPotential, if_neg hbad, min_eq_right (le_of_not_ge hlarge)]
      calc
        _ ≤ ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
            (((answerEncodingPotential cache secretKey + TightEncoding.encodingStageIncrement cache secretKey position : Nat) : ℝ≥0∞) * eps +
              encodingSelectionPotential (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) secretKey) := by
          apply ENNReal.tsum_le_tsum
          intro answer
          apply mul_le_mul' le_rfl
          have hclean := (clean_and_potential_cacheQuery_of_not_atPosition secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
            (answer := answer) hbad hfresh (fun candidate hc => hat.not_atPosition candidate hc)).1
          rw [answerEncodingTotalPotential, if_neg hclean]
          exact (min_le_right _ _).trans (add_le_add (mul_le_mul' (Nat.cast_le.mpr
            (answerEncodingPotential_cacheQuery_le_increment (answer := answer) hfresh hat)) le_rfl) le_rfl)
        _ = ((answerEncodingPotential cache secretKey + TightEncoding.encodingStageIncrement cache secretKey position : Nat) : ℝ≥0∞) * eps +
            ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
              encodingSelectionPotential (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) secretKey := by
          simp_rw [mul_add, ENNReal.tsum_add]
          rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
        _ ≤ ((answerEncodingPotential cache secretKey + TightEncoding.encodingStageIncrement cache secretKey position : Nat) : ℝ≥0∞) * eps +
            (encodingSelectionPotential cache hfinite secretKey + eps) :=
          add_le_add le_rfl (uniform_encodingSelectionPotential_cacheQuery_atPosition_sum_le hfinite hfresh hat)
        _ = _ := by
          rw [hbefore]
          simp only [Nat.cast_add, Nat.cast_one]
          dsimp only [uncapped]
          ring

theorem answerEncodingTotalPotential_cacheQuery_le_of_nonstructural
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {secretKey : SecretKey} {input : HashInput} {answer : HashOutput}
    (hfresh : cache input = none)
    (hnotEncoding : ∀ position : EncodingPosition, ¬ AtEncodingPosition secretKey.parameter input position)
    (hnotStructural : ∀ position : Position, ¬ AtPosition secretKey.parameter input position) :
    answerEncodingTotalPotential (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) secretKey ≤
      answerEncodingTotalPotential cache hfinite secretKey := by
  by_cases hbad : Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
  · rw [show answerEncodingTotalPotential cache hfinite secretKey = 1 by simp [answerEncodingTotalPotential, hbad]]
    exact answerEncodingTotalPotential_le_one _ _
  · have hclean := (clean_and_potential_cacheQuery_of_not_atPosition secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
      (answer := answer) hbad hfresh hnotStructural).1
    have ha := answerPotential_cacheQuery_le_of_not_atPosition secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
      (answer := answer) hfresh hnotStructural
    have he := encodingStagePotential_cacheQuery_le_of_not_atEncoding (secretKey := secretKey) (answer := answer) hfresh hnotEncoding
    have hp : answerEncodingPotential (cache.cacheQuery input answer) secretKey ≤ answerEncodingPotential cache secretKey := by
      rw [answerEncodingPotential, answerEncodingPotential]
      exact Nat.add_le_add ha he
    have hs := encodingSelectionPotential_cacheQuery_le_of_no_new_messages (answer := answer) hfinite hfresh hnotEncoding
      (fun _ h => h.of_cacheQuery_of_not_atPosition hfresh hnotStructural)
    rw [answerEncodingTotalPotential, if_neg hclean, answerEncodingTotalPotential, if_neg hbad]
    exact min_le_min le_rfl (add_le_add (mul_le_mul' (Nat.cast_le.mpr hp) le_rfl) hs)

end SphincsSecurity.Concrete
