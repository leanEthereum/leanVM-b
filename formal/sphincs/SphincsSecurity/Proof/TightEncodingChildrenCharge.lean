import SphincsSecurity.Proof.TightEncodingQueryCharge

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)

theorem settled_cacheQuery_of_settled_cacheQuery
    {cache : QueryCache HashSpec} {input : HashInput} {answer : HashOutput} {position : Position}
    (hfresh : cache input = none) (hat : AtPosition parameter input position)
    (hunsettled : ¬ Settled parameter otsSecret ftsSecret cache position)
    (hsettled : Settled parameter otsSecret ftsSecret (cache.cacheQuery input answer) position)
    (otherAnswer : HashOutput) :
    Settled parameter otsSecret ftsSecret (cache.cacheQuery input otherAnswer) position := by
  obtain ⟨hinput, hchildren⟩ := eq_cachedInput_and_children_of_settled_cacheQuery
    parameter otsSecret ftsSecret hfresh hat hunsettled hsettled
  have hle := le_cacheQuery (cache := cache) (input := input) (answer := otherAnswer) hfresh
  have hvalues : ∀ child ∈ position.children,
      honestValue (fromCache (cache.cacheQuery input otherAnswer)) parameter otsSecret ftsSecret child =
        honestValue (fromCache cache) parameter otsSecret ftsSecret child :=
    fun child hchild => honestValue_eq_of_settled (agreesWithFn_fromCache_of_le hle)
      (hchildren child hchild)
  have hpinned : cachedInput parameter otsSecret ftsSecret (cache.cacheQuery input otherAnswer) position =
      cachedInput parameter otsSecret ftsSecret cache position :=
    honestInput_congr _ _ parameter otsSecret ftsSecret hsettled.valid hvalues
  rw [settled_iff]
  refine ⟨hsettled.valid, ?_, fun child hchild => (hchildren child hchild).mono hle⟩
  rw [hpinned, ← hinput, QueryCache.cacheQuery_self]
  simp

theorem tightPotential_cacheQuery_le_one_of_children_settled
    {cache : QueryCache HashSpec} {input : HashInput} {answer : HashOutput} {position : Position}
    (hfresh : cache input = none) (hat : AtPosition parameter input position)
    (hchildren : ∀ child ∈ position.children, Settled parameter otsSecret ftsSecret cache child)
    (hunsettled : ¬ Settled parameter otsSecret ftsSecret (cache.cacheQuery input answer) position) :
    tightPotential parameter otsSecret ftsSecret (cache.cacheQuery input answer) ≤
      tightPotential parameter otsSecret ftsSecret cache + 1 := by
  classical
  have hle := le_cacheQuery (cache := cache) (input := input) (answer := answer) hfresh
  have hbefore : ¬ Settled parameter otsSecret ftsSecret cache position := fun h => hunsettled (h.mono hle)
  have hchildrenAfter : ∀ child ∈ position.children,
      Settled parameter otsSecret ftsSecret (cache.cacheQuery input answer) child :=
    fun child hchild => (hchildren child hchild).mono hle
  have hlocal : tightContribution parameter otsSecret ftsSecret (cache.cacheQuery input answer) position ≤
      tightContribution parameter otsSecret ftsSecret cache position + 1 := by
    rw [tightContribution, if_neg hunsettled, if_pos hchildrenAfter,
      tightContribution, if_neg hbefore, if_pos hchildren]
    simp only [Nat.add_zero, Nat.mul_one]
    rw [cachedAt_cacheQuery_self parameter hat]
    exact Set.ncard_insert_le _ _
  calc
    _ ≤ ∑ candidate : Position, (tightContribution parameter otsSecret ftsSecret cache candidate +
        if candidate = position then 1 else 0) := by
      apply Finset.sum_le_sum
      intro candidate _
      by_cases heq : candidate = position
      · rw [heq, if_pos rfl]
        exact hlocal
      · rw [if_neg heq, Nat.add_zero]
        exact tightContribution_le_of_cachedAt_eq parameter otsSecret ftsSecret hle candidate
          (cachedAt_cacheQuery_of_not_atPosition parameter
            (fun hc => heq (atPosition_unique parameter hc hat)))
    _ = _ := by
      rw [Finset.sum_add_distrib, Fintype.sum_ite_eq']
      rfl

end SphincsSecurity

namespace SphincsSecurity.Concrete.TightEncoding

open OracleComp OracleSpec ENNReal

theorem encodingSelectionTotalPotential_cacheQuery_le_one_of_children_settled
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {answer : HashOutput} {position : Position}
    (hfresh : cache input = none) (hat : AtPosition secretKey.parameter input position)
    (hchildren : ∀ child ∈ position.children,
      Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache child)
    (hunsettled : ¬ Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
      (cache.cacheQuery input answer) position) :
    encodingSelectionTotalPotential (cache.cacheQuery input answer)
        (finite_cacheQuery hfinite input answer) secretKey ≤
      encodingSelectionTotalPotential cache hfinite secretKey + (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  have hnotEncoding : ∀ candidate : EncodingPosition,
      ¬ AtEncodingPosition secretKey.parameter input candidate :=
    fun _ hencoding => hencoding.not_atPosition position hat
  by_cases hbad : Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
  · have hbefore : encodingSelectionTotalPotential cache hfinite secretKey = 1 := by
      rw [encodingSelectionTotalPotential, if_pos hbad]
    rw [hbefore]
    exact (encodingSelectionTotalPotential_le_one _ secretKey).trans (le_add_right le_rfl)
  · have hclean := clean_cacheQuery_of_unsettled secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret hbad hfresh hat hunsettled
    have hstructural := tightPotential_cacheQuery_le_one_of_children_settled secretKey.parameter
      secretKey.otsSecret secretKey.ftsSecret hfresh hat hchildren hunsettled
    have hstage := encodingStagePotential_cacheQuery_le_of_not_atEncoding
      (secretKey := secretKey) (answer := answer) hfresh hnotEncoding
    have hselection := encodingSelectionPotential_cacheQuery_le_of_no_new_messages
      (answer := answer) hfinite hfresh hnotEncoding
      (fun candidate hafter => hafter.of_cacheQuery_of_at_unsettledAfter hfresh hat hunsettled)
    have hsum : encodingStructuralPotential (cache.cacheQuery input answer) secretKey ≤
        encodingStructuralPotential cache secretKey + 1 := by
      dsimp only [encodingStructuralPotential]
      omega
    let eps := (Fintype.card Digest : ℝ≥0∞)⁻¹
    let before := (encodingStructuralPotential cache secretKey : ℝ≥0∞) * eps +
      encodingSelectionPotential cache hfinite secretKey
    by_cases hone : 1 ≤ before
    · have hbefore : encodingSelectionTotalPotential cache hfinite secretKey = 1 := by
        rw [encodingSelectionTotalPotential, if_neg hbad, min_eq_left hone]
      rw [hbefore]
      exact (encodingSelectionTotalPotential_le_one _ secretKey).trans (le_add_right le_rfl)
    · have hbefore : encodingSelectionTotalPotential cache hfinite secretKey = before := by
        rw [encodingSelectionTotalPotential, if_neg hbad, min_eq_right (le_of_not_ge hone)]
      rw [hbefore]
      calc
        _ ≤ (encodingStructuralPotential (cache.cacheQuery input answer) secretKey : ℝ≥0∞) * eps +
            encodingSelectionPotential (cache.cacheQuery input answer)
              (finite_cacheQuery hfinite input answer) secretKey :=
          encodingSelectionTotalPotential_le_uncapped _ secretKey hclean
        _ ≤ ((encodingStructuralPotential cache secretKey + 1 : Nat) : ℝ≥0∞) * eps +
            encodingSelectionPotential cache hfinite secretKey :=
          add_le_add (mul_le_mul' (Nat.cast_le.mpr hsum) le_rfl) hselection
        _ = before + eps := by
          simp only [Nat.cast_add, Nat.cast_one, before]
          ring

theorem uniform_encodingSelectionTotalPotential_cacheQuery_le_one_of_children_settled
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {position : Position}
    (hfresh : cache input = none) (hat : AtPosition secretKey.parameter input position)
    (hchildren : ∀ child ∈ position.children,
      Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache child)
    (hunsettled : ∀ answer : HashOutput,
      ¬ Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
        (cache.cacheQuery input answer) position) :
    (∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
      encodingSelectionTotalPotential (cache.cacheQuery input answer)
        (finite_cacheQuery hfinite input answer) secretKey) ≤
      encodingSelectionTotalPotential cache hfinite secretKey + (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  calc
    _ ≤ ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (encodingSelectionTotalPotential cache hfinite secretKey + (Fintype.card Digest : ℝ≥0∞)⁻¹) :=
      ENNReal.tsum_le_tsum fun answer => mul_le_mul' le_rfl
        (encodingSelectionTotalPotential_cacheQuery_le_one_of_children_settled
          hfinite hfresh hat hchildren (hunsettled answer))
    _ = _ := by rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]

end SphincsSecurity.Concrete.TightEncoding
