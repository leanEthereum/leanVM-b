import SphincsSecurity.Proof.TightEncodingQueryCharge
import SphincsSecurity.Proof.TightEncodingStageCost
import SphincsSecurity.Proof.TightEncodingChildrenCharge

namespace SphincsSecurity.Concrete.TightEncoding

open OracleComp OracleSpec ENNReal

theorem encodingSelectionTotalPotential_cacheQuery_le_of_settled_of_avoids
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {answer : HashOutput} {position : Position}
    (hfresh : cache input = none) (hat : AtPosition secretKey.parameter input position)
    (hsettled : Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache position)
    (havoid : truncateHash answer ≠ honestValue (fromCache cache) secretKey.parameter
      secretKey.otsSecret secretKey.ftsSecret position) :
    encodingSelectionTotalPotential (cache.cacheQuery input answer)
        (finite_cacheQuery hfinite input answer) secretKey ≤
      encodingSelectionTotalPotential cache hfinite secretKey := by
  have hnotEncoding : ∀ candidate : EncodingPosition,
      ¬ AtEncodingPosition secretKey.parameter input candidate :=
    fun _ hencoding => hencoding.not_atPosition position hat
  by_cases hbad : Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
  · have hbefore : encodingSelectionTotalPotential cache hfinite secretKey = 1 := by
      rw [encodingSelectionTotalPotential, if_pos hbad]
    rw [hbefore]
    exact encodingSelectionTotalPotential_le_one _ secretKey
  · have hclean := clean_cacheQuery_of_settled_of_avoids secretKey.parameter
      secretKey.otsSecret secretKey.ftsSecret hbad hfresh hat hsettled havoid
    have hstructural := tightPotential_cacheQuery_le_of_settled secretKey.parameter
      secretKey.otsSecret secretKey.ftsSecret (answer := answer) hfresh hat hsettled
    have hstage := encodingStagePotential_cacheQuery_le_of_not_atEncoding
      (secretKey := secretKey) (answer := answer) hfresh hnotEncoding
    have hselection := encodingSelectionPotential_cacheQuery_le_of_no_new_messages
      (answer := answer) hfinite hfresh hnotEncoding
      (fun candidate hafter => hafter.of_cacheQuery_of_at_settled hfresh hat hsettled)
    have hsum : encodingStructuralPotential (cache.cacheQuery input answer) secretKey ≤
        encodingStructuralPotential cache secretKey := Nat.add_le_add hstructural hstage
    rw [encodingSelectionTotalPotential, if_neg hclean,
      encodingSelectionTotalPotential, if_neg hbad]
    exact min_le_min le_rfl (add_le_add (mul_le_mul' (Nat.cast_le.mpr hsum) le_rfl) hselection)

theorem uniform_encodingSelectionTotalPotential_cacheQuery_settled_le
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {position : Position}
    (hfresh : cache input = none) (hat : AtPosition secretKey.parameter input position)
    (hsettled : Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache position) :
    (∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
      encodingSelectionTotalPotential (cache.cacheQuery input answer)
        (finite_cacheQuery hfinite input answer) secretKey) ≤
      encodingSelectionTotalPotential cache hfinite secretKey + (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  classical
  let targets : Finset Digest :=
    {honestValue (fromCache cache) secretKey.parameter secretKey.otsSecret secretKey.ftsSecret position}
  calc
    _ ≤ ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (encodingSelectionTotalPotential cache hfinite secretKey +
          if truncateHash answer ∈ targets then 1 else 0) := by
      apply ENNReal.tsum_le_tsum
      intro answer
      apply mul_le_mul' le_rfl
      by_cases hhit : truncateHash answer ∈ targets
      · rw [if_pos hhit]
        exact (encodingSelectionTotalPotential_le_one _ secretKey).trans (le_add_left le_rfl)
      · rw [if_neg hhit, add_zero]
        exact encodingSelectionTotalPotential_cacheQuery_le_of_settled_of_avoids hfinite hfresh
          hat hsettled (by simpa only [targets, Finset.mem_singleton] using hhit)
    _ = _ := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul,
        uniformHashOutput_mem_bonus_sum_eq]
      simp [targets]

noncomputable def refinedStructuralEncodingQueryCharge (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput) : ℝ≥0∞ :=
  open Classical in
  if cache input = none then
    if hencoding : ∃ position : EncodingPosition, AtEncodingPosition secretKey.parameter input position then
      ((encodingStageIncrement cache secretKey (Classical.choose hencoding) + 1 : Nat) : ℝ≥0∞)
    else if ∃ position : Position, AtPosition secretKey.parameter input position ∧
        Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache position then 1
    else if ∃ position : Position, AtPosition secretKey.parameter input position ∧
        ∀ answer : HashOutput,
          Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
            (cache.cacheQuery input answer) position then 0
    else if ∃ position : Position, AtPosition secretKey.parameter input position ∧
        ∀ child ∈ position.children,
          Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache child then 1
    else structuralEncodingQueryCharge secretKey.parameter input
  else 0

theorem refinedStructuralEncodingQueryCharge_le_three (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput) :
    refinedStructuralEncodingQueryCharge secretKey cache input ≤ 3 := by
  classical
  unfold refinedStructuralEncodingQueryCharge
  split_ifs with hfresh hencoding hsettled hsettles hchildren
  · unfold encodingStageIncrement
    split_ifs <;> norm_num
  · norm_num
  · norm_num
  · norm_num
  · unfold structuralEncodingQueryCharge
    split_ifs <;> norm_num
  · norm_num

theorem refinedStructuralEncodingQueryCharge_le_one_of_children_settled
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (input : HashInput) (position : Position)
    (hat : AtPosition secretKey.parameter input position)
    (hchildren : ∀ child ∈ position.children,
      Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache child) :
    refinedStructuralEncodingQueryCharge secretKey cache input ≤ 1 := by
  classical
  have hnotEncoding : ¬ ∃ candidate : EncodingPosition,
      AtEncodingPosition secretKey.parameter input candidate :=
    fun ⟨candidate, hencoding⟩ => hencoding.not_atPosition position hat
  have hsomeChildren : ∃ candidate : Position, AtPosition secretKey.parameter input candidate ∧
      ∀ child ∈ candidate.children,
        Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache child :=
    ⟨position, hat, hchildren⟩
  unfold refinedStructuralEncodingQueryCharge
  split_ifs <;> simp_all only [zero_le_one, le_refl]

theorem uniform_encodingSelectionTotalPotential_cacheQuery_le_refined_charge
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} (hfresh : cache input = none) :
    (∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
      encodingSelectionTotalPotential (cache.cacheQuery input answer)
        (finite_cacheQuery hfinite input answer) secretKey) ≤
      encodingSelectionTotalPotential cache hfinite secretKey +
        refinedStructuralEncodingQueryCharge secretKey cache input *
          (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  classical
  rw [refinedStructuralEncodingQueryCharge, if_pos hfresh]
  split_ifs with hencoding hsettled hsettles hchildren
  · exact uniform_encodingSelectionTotalPotential_cacheQuery_le_stage_increment
      hfinite hfresh (Classical.choose_spec hencoding)
  · obtain ⟨position, hat, hposition⟩ := hsettled
    rw [one_mul]
    exact uniform_encodingSelectionTotalPotential_cacheQuery_settled_le hfinite hfresh hat hposition
  · obtain ⟨position, hat, hafter⟩ := hsettles
    rw [zero_mul, add_zero]
    by_cases hbad : Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
    · have hbefore : encodingSelectionTotalPotential cache hfinite secretKey = 1 := by
        rw [encodingSelectionTotalPotential, if_pos hbad]
      rw [hbefore]
      exact expected_encodingSelectionTotalPotential_le_one hfinite secretKey input
    · exact uniform_encodingSelectionTotalPotential_cacheQuery_le_of_settlingPosition
        hfinite hbad hfresh hat (fun hposition => hsettled ⟨position, hat, hposition⟩) hafter
  · obtain ⟨position, hat, hchildren⟩ := hchildren
    rw [one_mul]
    apply uniform_encodingSelectionTotalPotential_cacheQuery_le_one_of_children_settled
      hfinite hfresh hat hchildren
    intro answer hafter
    exact hsettles ⟨position, hat, settled_cacheQuery_of_settled_cacheQuery secretKey.parameter
      secretKey.otsSecret secretKey.ftsSecret hfresh hat
      (fun hposition => hsettled ⟨position, hat, hposition⟩) hafter⟩
  · exact uniform_encodingSelectionTotalPotential_cacheQuery_le_charge hfinite hfresh

end SphincsSecurity.Concrete.TightEncoding
