import SphincsSecurity.Proof.CollisionAnswerEncodingStep

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

attribute [local irreducible] instFintypePosition instFintypeEncodingPosition validCacheEntries answerPotential collisionAnswerEncodingPotential
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def collisionAnswerEncodingTotalPotential (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (secretKey : SecretKey) : ℝ≥0∞ :=
  if Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache then 1
  else min 1 ((collisionAnswerEncodingPotential cache hfinite secretKey : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ +
    encodingSelectionPotential cache hfinite secretKey)

theorem collisionAnswerEncodingTotalPotential_le_one {cache : QueryCache HashSpec} (hfinite : Finite cache) (secretKey : SecretKey) :
    collisionAnswerEncodingTotalPotential cache hfinite secretKey ≤ 1 := by
  unfold collisionAnswerEncodingTotalPotential
  split_ifs <;> simp

theorem collisionAnswerEncodingTotalPotential_eq_one_of_bad_or_encodingBad
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {secretKey : SecretKey}
    (hbad : Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache ∨ EncodingBad cache secretKey) :
    collisionAnswerEncodingTotalPotential cache hfinite secretKey = 1 := by
  unfold collisionAnswerEncodingTotalPotential
  split_ifs with hstructural
  · rfl
  · apply min_eq_left
    exact (one_le_encodingSelectionPotential_of_encodingBad hfinite (hbad.resolve_left hstructural)).trans le_add_self

@[simp] theorem collisionAnswerEncodingTotalPotential_empty (secretKey : SecretKey) :
    collisionAnswerEncodingTotalPotential ∅ finite_empty secretKey = 0 := by
  rw [collisionAnswerEncodingTotalPotential, if_neg (not_bad_empty secretKey.parameter secretKey.otsSecret secretKey.ftsSecret),
    collisionAnswerEncodingPotential_empty, encodingSelectionPotential_empty]
  simp

theorem uniform_collisionAnswerEncodingTotalPotential_without_parent_le_step
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {secretKey : SecretKey} {input : HashInput}
    (cost : Nat)
    (hstep : ¬ Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache →
      ∃ targets : Finset Digest, targets.card ≤ collisionAnswerEncodingPotential cache hfinite secretKey + cost ∧
        ∀ answer : HashOutput,
          ¬ ParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache input answer →
          truncateHash answer ∉ targets →
          ¬ Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret (cache.cacheQuery input answer) ∧
            collisionAnswerEncodingPotential (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) secretKey + targets.card ≤ collisionAnswerEncodingPotential cache hfinite secretKey + cost ∧
            encodingSelectionPotential (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) secretKey ≤
              encodingSelectionPotential cache hfinite secretKey) :
    (∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache input answer then 0
        else collisionAnswerEncodingTotalPotential (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) secretKey)) ≤
      collisionAnswerEncodingTotalPotential cache hfinite secretKey + (cost : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  let eps := (Fintype.card Digest : ℝ≥0∞)⁻¹
  have hmass : (∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache input answer then 0
        else collisionAnswerEncodingTotalPotential (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) secretKey)) ≤ 1 := by
    calc
      _ ≤ ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] * 1 := by
        apply ENNReal.tsum_le_tsum
        intro answer
        apply mul_le_mul' le_rfl
        split_ifs
        · exact bot_le
        · exact collisionAnswerEncodingTotalPotential_le_one _ _
      _ = _ := by rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
  by_cases hbad : Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
  · rw [collisionAnswerEncodingTotalPotential, if_pos hbad]
    exact hmass.trans le_self_add
  · let uncapped := (collisionAnswerEncodingPotential cache hfinite secretKey : ℝ≥0∞) * eps + encodingSelectionPotential cache hfinite secretKey
    by_cases hlarge : 1 ≤ uncapped
    · rw [collisionAnswerEncodingTotalPotential, if_neg hbad, min_eq_left hlarge]
      exact hmass.trans le_self_add
    · have hbefore : collisionAnswerEncodingTotalPotential cache hfinite secretKey = uncapped := by
        rw [collisionAnswerEncodingTotalPotential, if_neg hbad, min_eq_right (le_of_not_ge hlarge)]
      obtain ⟨targets, hcard, hsafe⟩ := hstep hbad
      let credit := collisionAnswerEncodingPotential cache hfinite secretKey + cost - targets.card
      have hcredit : targets.card + credit = collisionAnswerEncodingPotential cache hfinite secretKey + cost := Nat.add_sub_of_le hcard
      have hpoint (answer : HashOutput) :
          (if CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache input answer then 0
            else collisionAnswerEncodingTotalPotential (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) secretKey) ≤
          (if truncateHash answer ∈ targets then 1 else 0) + (credit : ℝ≥0∞) * eps + encodingSelectionPotential cache hfinite secretKey := by
        by_cases hx : CleanParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache input answer
        · rw [if_pos hx]
          exact bot_le
        · rw [if_neg hx]
          by_cases ht : truncateHash answer ∈ targets
          · rw [if_pos ht]
            exact (collisionAnswerEncodingTotalPotential_le_one _ _).trans (le_self_add.trans le_self_add)
          · rw [if_neg ht, zero_add]
            obtain ⟨hclean, hp, hs⟩ := hsafe answer (fun h => hx ⟨hbad, h⟩) ht
            rw [collisionAnswerEncodingTotalPotential, if_neg hclean]
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

theorem collisionAnswerEncodingTotalPotential_cacheQuery_le_of_nonstructural
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {secretKey : SecretKey} {input : HashInput} {answer : HashOutput}
    (hfresh : cache input = none)
    (hnotEncoding : ∀ position : EncodingPosition, ¬ AtEncodingPosition secretKey.parameter input position)
    (hnotStructural : ∀ position : Position, ¬ AtPosition secretKey.parameter input position) :
    collisionAnswerEncodingTotalPotential (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) secretKey ≤
      collisionAnswerEncodingTotalPotential cache hfinite secretKey := by
  by_cases hbad : Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
  · rw [show collisionAnswerEncodingTotalPotential cache hfinite secretKey = 1 by simp [collisionAnswerEncodingTotalPotential, hbad]]
    exact collisionAnswerEncodingTotalPotential_le_one _ _
  · have hclean := (clean_and_potential_cacheQuery_of_not_atPosition secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
      (answer := answer) hbad hfresh hnotStructural).1
    have ha := answerPotential_cacheQuery_le_of_not_atPosition secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
      (answer := answer) hfresh hnotStructural
    have he := encodingCollisionReserve_cacheQuery_le_of_not_atEncoding hfinite (key := secretKey) (answer := answer) hfresh hnotEncoding
    have hp : collisionAnswerEncodingPotential (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) secretKey ≤ collisionAnswerEncodingPotential cache hfinite secretKey := by
      rw [collisionAnswerEncodingPotential, collisionAnswerEncodingPotential]
      exact Nat.add_le_add ha he
    have hs := encodingSelectionPotential_cacheQuery_le_of_no_new_messages (answer := answer) hfinite hfresh hnotEncoding
      (fun _ h => h.of_cacheQuery_of_not_atPosition hfresh hnotStructural)
    rw [collisionAnswerEncodingTotalPotential, if_neg hclean, collisionAnswerEncodingTotalPotential, if_neg hbad]
    exact min_le_min le_rfl (add_le_add (mul_le_mul' (Nat.cast_le.mpr hp) le_rfl) hs)

theorem uniform_collisionAnswerEncodingPotential_atEncoding_le
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {key : SecretKey}
    {input : HashInput} {position : EncodingPosition}
    (hfresh : cache input = none) (hat : AtEncodingPosition key.parameter input position) :
    (∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (collisionAnswerEncodingPotential (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) key : ENNReal)) ≤
      (collisionAnswerEncodingPotential cache hfinite key : ENNReal) +
        2 * (validCacheEntries cache).card * (Fintype.card Digest : ENNReal)⁻¹ := by
  calc
    _ ≤ ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
        ((answerPotential key.parameter key.otsSecret key.ftsSecret cache : ENNReal) +
          (encodingCollisionReserve (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) key : ENNReal)) := by
      apply ENNReal.tsum_le_tsum
      intro answer
      apply mul_le_mul' le_rfl
      rw [collisionAnswerEncodingPotential, Nat.cast_add]
      apply add_le_add ?_ le_rfl
      exact Nat.cast_le.mpr (answerPotential_cacheQuery_le_of_not_atPosition key.parameter key.otsSecret key.ftsSecret
        (answer := answer) hfresh (fun candidate hc => hat.not_atPosition candidate hc))
    _ = (answerPotential key.parameter key.otsSecret key.ftsSecret cache : ENNReal) +
        ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (encodingCollisionReserve (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) key : ENNReal) := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
    _ ≤ _ := by
      have h := add_le_add (le_refl (answerPotential key.parameter key.otsSecret key.ftsSecret cache : ENNReal))
        (uniform_encodingCollisionReserve_cacheQuery_le hfinite hfresh hat)
      simpa only [collisionAnswerEncodingPotential, Nat.cast_add, add_assoc] using h

theorem uniform_collisionAnswerEncodingTotalPotential_atEncoding_le
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {key : SecretKey}
    {input : HashInput} {position : EncodingPosition}
    (hfresh : cache input = none) (hat : AtEncodingPosition key.parameter input position) :
    (∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
      collisionAnswerEncodingTotalPotential (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) key) ≤
      collisionAnswerEncodingTotalPotential cache hfinite key + (Fintype.card Digest : ENNReal)⁻¹ +
        2 * (validCacheEntries cache).card * (Fintype.card Digest : ENNReal)⁻¹ * (Fintype.card Digest : ENNReal)⁻¹ := by
  let eps := (Fintype.card Digest : ENNReal)⁻¹
  have hmass : (∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
      collisionAnswerEncodingTotalPotential (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) key) ≤ 1 := by
    calc
      _ ≤ ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] * 1 :=
        ENNReal.tsum_le_tsum fun answer => mul_le_mul' le_rfl (collisionAnswerEncodingTotalPotential_le_one _ _)
      _ = _ := by rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
  by_cases hbad : Bad key.parameter key.otsSecret key.ftsSecret cache
  · rw [collisionAnswerEncodingTotalPotential, if_pos hbad]
    exact hmass.trans (le_self_add.trans le_self_add)
  · let uncapped := (collisionAnswerEncodingPotential cache hfinite key : ENNReal) * eps +
        encodingSelectionPotential cache hfinite key
    by_cases hlarge : 1 ≤ uncapped
    · rw [collisionAnswerEncodingTotalPotential, if_neg hbad, min_eq_left hlarge]
      exact hmass.trans (le_self_add.trans le_self_add)
    · have hbefore : collisionAnswerEncodingTotalPotential cache hfinite key = uncapped := by
        rw [collisionAnswerEncodingTotalPotential, if_neg hbad, min_eq_right (le_of_not_ge hlarge)]
      calc
        _ ≤ ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
            ((collisionAnswerEncodingPotential (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) key : ENNReal) * eps +
              encodingSelectionPotential (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) key) := by
          apply ENNReal.tsum_le_tsum
          intro answer
          apply mul_le_mul' le_rfl
          have hc := (clean_and_potential_cacheQuery_of_not_atPosition key.parameter key.otsSecret key.ftsSecret
            (answer := answer) hbad hfresh (fun candidate hc => hat.not_atPosition candidate hc)).1
          rw [collisionAnswerEncodingTotalPotential, if_neg hc]
          exact min_le_right _ _
        _ = (∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
            (collisionAnswerEncodingPotential (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) key : ENNReal)) * eps +
            ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
              encodingSelectionPotential (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) key := by
          simp_rw [mul_add, ← mul_assoc]
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
        _ ≤ ((collisionAnswerEncodingPotential cache hfinite key : ENNReal) +
            2 * (validCacheEntries cache).card * eps) * eps + (encodingSelectionPotential cache hfinite key + eps) :=
          add_le_add (mul_le_mul' (uniform_collisionAnswerEncodingPotential_atEncoding_le hfinite hfresh hat) le_rfl)
            (uniform_encodingSelectionPotential_cacheQuery_atPosition_sum_le hfinite hfresh hat)
        _ = _ := by rw [hbefore]; dsimp only [uncapped, eps]; ring

end SphincsSecurity.Concrete
