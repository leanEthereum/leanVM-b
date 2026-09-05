import SphincsSecurity.Proof.TightEncodingSelectionLift

namespace SphincsSecurity.Concrete.TightEncoding

open OracleComp OracleSpec ENNReal

theorem uniform_encodingSelectionTotalPotential_cacheQuery_not_encoding_sum_le
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput}
    (huncached : cache input = none)
    (hnotEncoding : ∀ position : EncodingPosition,
      ¬ AtEncodingPosition secretKey.parameter input position) :
    (∑' answer : HashOutput,
      Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
        encodingSelectionTotalPotential (cache.cacheQuery input answer)
          (finite_cacheQuery hfinite input answer) secretKey) ≤
      encodingSelectionTotalPotential cache hfinite secretKey +
        2 * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  by_cases hstructural : ∃ position : Position,
      AtPosition secretKey.parameter input position
  · obtain ⟨position, hposition⟩ := hstructural
    by_cases hsettled : Settled secretKey.parameter secretKey.otsSecret
        secretKey.ftsSecret cache position
    · have hbound :=
        uniform_encodingSelectionTotalPotential_cacheQuery_le_of_no_new_messages
          hfinite huncached hnotEncoding
          (fun answer candidate hafter =>
            hafter.of_cacheQuery_of_at_settled huncached hposition hsettled)
      exact hbound
    · by_cases hnever : ∀ answer : HashOutput,
          ¬ Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
            (cache.cacheQuery input answer) position
      · have hbound :=
          uniform_encodingSelectionTotalPotential_cacheQuery_le_of_no_new_messages
            hfinite huncached hnotEncoding
            (fun answer candidate hafter =>
              hafter.of_cacheQuery_of_at_unsettledAfter huncached hposition
                (hnever answer))
        exact hbound
      · push Not at hnever
        obtain ⟨settlingAnswer, hsettling⟩ := hnever
        obtain ⟨hinput, hchildren⟩ :=
          eq_cachedInput_and_children_of_settled_cacheQuery secretKey.parameter
            secretKey.otsSecret secretKey.ftsSecret huncached hposition hsettled hsettling
        have hsettles : ∀ answer : HashOutput,
            Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
              (cache.cacheQuery input answer) position := by
          intro answer
          have hle := le_cacheQuery (cache := cache) (input := input)
            (answer := answer) huncached
          have hchildrenAfter : ∀ child ∈ position.children,
              Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
                (cache.cacheQuery input answer) child :=
            fun child hchild => (hchildren child hchild).mono hle
          have hvalues : ∀ child ∈ position.children,
              honestValue (fromCache (cache.cacheQuery input answer)) secretKey.parameter
                  secretKey.otsSecret secretKey.ftsSecret child =
                honestValue (fromCache cache) secretKey.parameter secretKey.otsSecret
                  secretKey.ftsSecret child :=
            fun child hchild => honestValue_eq_of_settled
              (agreesWithFn_fromCache_of_le hle) (hchildren child hchild)
          have hpinned : cachedInput secretKey.parameter secretKey.otsSecret
                secretKey.ftsSecret (cache.cacheQuery input answer) position =
              cachedInput secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
                cache position :=
            honestInput_congr _ _ secretKey.parameter secretKey.otsSecret
              secretKey.ftsSecret hsettling.valid hvalues
          rw [settled_iff]
          refine ⟨hsettling.valid, ?_, hchildrenAfter⟩
          rw [hpinned, ← hinput, QueryCache.cacheQuery_self]
          simp
        by_cases hbad : Bad secretKey.parameter secretKey.otsSecret
            secretKey.ftsSecret cache
        · have hbefore : encodingSelectionTotalPotential cache hfinite secretKey = 1 := by
            rw [encodingSelectionTotalPotential, if_pos hbad]
          rw [hbefore]
          exact (expected_encodingSelectionTotalPotential_le_one hfinite secretKey input).trans
            (le_add_right le_rfl)
        · exact (uniform_encodingSelectionTotalPotential_cacheQuery_le_of_settlingPosition
            hfinite hbad huncached hposition hsettled hsettles).trans
              (le_add_right le_rfl)
  · have hbound :=
      uniform_encodingSelectionTotalPotential_cacheQuery_le_of_no_new_messages
        hfinite huncached hnotEncoding
        (fun answer candidate hafter =>
          hafter.of_cacheQuery_of_not_atPosition huncached
            (fun position hposition => hstructural ⟨position, hposition⟩))
    exact hbound


theorem encodingSelectionTotalPotential_cacheQuery_le_of_unrelated
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {answer : HashOutput}
    (huncached : cache input = none)
    (hnotEncoding : ∀ position : EncodingPosition,
      ¬ AtEncodingPosition secretKey.parameter input position)
    (hnotStructural : ∀ position : Position,
      ¬ AtPosition secretKey.parameter input position) :
    encodingSelectionTotalPotential (cache.cacheQuery input answer)
        (finite_cacheQuery hfinite input answer) secretKey ≤
      encodingSelectionTotalPotential cache hfinite secretKey := by
  by_cases hbad : Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
  · have hbefore : encodingSelectionTotalPotential cache hfinite secretKey = 1 := by
      rw [encodingSelectionTotalPotential, if_pos hbad]
    rw [hbefore]
    exact encodingSelectionTotalPotential_le_one _ secretKey
  · obtain ⟨hclean, hstructural⟩ :=
      clean_and_tightPotential_cacheQuery_of_not_atPosition secretKey.parameter
        secretKey.otsSecret secretKey.ftsSecret (answer := answer) hbad huncached hnotStructural
    have hstage := encodingStagePotential_cacheQuery_le_of_not_atEncoding
      (secretKey := secretKey) (answer := answer) huncached hnotEncoding
    have hselection := encodingSelectionPotential_cacheQuery_le_of_no_new_messages
      (answer := answer) hfinite huncached hnotEncoding
      (fun position hafter => hafter.of_cacheQuery_of_not_atPosition huncached hnotStructural)
    have hsum : encodingStructuralPotential (cache.cacheQuery input answer) secretKey ≤
        encodingStructuralPotential cache secretKey := Nat.add_le_add hstructural hstage
    rw [encodingSelectionTotalPotential, if_neg hclean,
      encodingSelectionTotalPotential, if_neg hbad]
    exact min_le_min le_rfl (add_le_add (mul_le_mul' (Nat.cast_le.mpr hsum) le_rfl) hselection)

noncomputable def structuralEncodingQueryCharge (parameter : PublicParameter)
    (input : HashInput) : ℝ≥0∞ :=
  open Classical in
  if ∃ position : EncodingPosition, AtEncodingPosition parameter input position then 3
  else if ∃ position : Position, AtPosition parameter input position then 2
  else 0

theorem uniform_encodingSelectionTotalPotential_cacheQuery_le_charge
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput}
    (huncached : cache input = none) :
    (∑' answer : HashOutput,
      Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
        encodingSelectionTotalPotential (cache.cacheQuery input answer)
          (finite_cacheQuery hfinite input answer) secretKey) ≤
      encodingSelectionTotalPotential cache hfinite secretKey +
        structuralEncodingQueryCharge secretKey.parameter input *
          (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  classical
  rw [structuralEncodingQueryCharge]
  split_ifs with hencoding hstructural
  · exact uniform_encodingSelectionTotalPotential_cacheQuery_sum_le hfinite huncached
  · exact uniform_encodingSelectionTotalPotential_cacheQuery_not_encoding_sum_le
      hfinite huncached (fun position hat => hencoding ⟨position, hat⟩)
  · rw [zero_mul, add_zero]
    calc
      _ ≤ ∑' answer : HashOutput,
          Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
            encodingSelectionTotalPotential cache hfinite secretKey := by
        exact ENNReal.tsum_le_tsum fun answer => mul_le_mul' le_rfl
          (encodingSelectionTotalPotential_cacheQuery_le_of_unrelated hfinite huncached
            (fun position hat => hencoding ⟨position, hat⟩)
            (fun position hat => hstructural ⟨position, hat⟩))
      _ = _ := by rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]

end SphincsSecurity.Concrete.TightEncoding
