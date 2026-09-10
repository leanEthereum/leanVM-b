import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.TightEncodingSettledCharge

namespace SphincsSecurity.Concrete.TightEncoding

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable

theorem uniform_encodingPrehit_or_potential_le_refined_charge
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} (hfresh : cache input = none) :
    (∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if EncodingMessagePrehit cache secretKey input answer then 1
      else encodingSelectionTotalPotential (cache.cacheQuery input answer)
        (finite_cacheQuery hfinite input answer) secretKey)) ≤
      encodingSelectionTotalPotential cache hfinite secretKey +
        refinedStructuralEncodingQueryCharge secretKey cache input * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  by_cases hbad : Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
  · have hbefore : encodingSelectionTotalPotential cache hfinite secretKey = 1 := by
      simp [encodingSelectionTotalPotential, hbad]
    rw [hbefore]
    apply le_trans _ (le_self_add : (1 : ℝ≥0∞) ≤ 1 + _)
    calc
      _ ≤ ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] * 1 := by
        apply ENNReal.tsum_le_tsum
        intro answer
        apply mul_le_mul' le_rfl
        split_ifs
        · exact le_rfl
        · exact encodingSelectionTotalPotential_le_one _ secretKey
      _ = 1 := by simp only [mul_one, tsum_probOutput_of_liftM_PMF]
  · by_cases hhit : ∃ answer, EncodingMessagePrehit cache secretKey input answer
    · obtain ⟨answer, hhit⟩ := hhit
      obtain ⟨position, hat, hunsettled, hsettled⟩ := hhit.queried_settles hfinite hfresh
      have hsettles := settled_cacheQuery_of_settled_cacheQuery secretKey.parameter secretKey.otsSecret
        secretKey.ftsSecret hfresh hat hunsettled hsettled
      exact (uniform_encodingSelectionTotalPotential_cacheQuery_le_of_settlingPosition_prehit
        hfinite hbad hfresh hat hunsettled hsettles).trans le_self_add
    · have hnone : ∀ answer, ¬ EncodingMessagePrehit cache secretKey input answer := by
        simpa using hhit
      simp_rw [if_neg (hnone _)]
      exact uniform_encodingSelectionTotalPotential_cacheQuery_le_refined_charge hfinite hfresh

end SphincsSecurity.Concrete.TightEncoding
