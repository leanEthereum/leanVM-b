import SphincsSecurity.Proof.TightEncodingQueryCharge
import SphincsSecurity.Proof.RomQueryCharge
import SphincsSecurity.Proof.FirstBad

namespace SphincsSecurity.Concrete.TightEncoding

open OracleComp OracleSpec ENNReal

noncomputable def freshStructuralEncodingQueryCharge (parameter : PublicParameter)
    (cache : QueryCache HashSpec) (input : HashInput) : ℝ≥0∞ :=
  if cache input = none then structuralEncodingQueryCharge parameter input else 0

theorem freshStructuralEncodingQueryCharge_le_three (parameter : PublicParameter)
    (cache : QueryCache HashSpec) (input : HashInput) :
    freshStructuralEncodingQueryCharge parameter cache input ≤ 3 := by
  classical
  unfold freshStructuralEncodingQueryCharge structuralEncodingQueryCharge
  split_ifs <;> norm_num

theorem expected_encodingSelectionAdaptivePotential_le_queryCharge
    {α : Type} (computation : OracleComp OracleWorld α)
    (secretKey : SecretKey) (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    (∑' result, Pr[= result | (simulateQ romImpl computation).run cache] *
        encodingSelectionAdaptivePotential result.2 secretKey) ≤
      encodingSelectionAdaptivePotential cache secretKey +
        expectedQueryCharge (freshStructuralEncodingQueryCharge secretKey.parameter)
          computation cache * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  rw [← expectedQueryCharge_mul]
  refine expected_potential_simulateQ_le_queryCharge
    (fun cache => encodingSelectionAdaptivePotential cache secretKey) _ ?_
    computation cache hfinite
  apply expected_potential_romImpl_le_charge
  intro before hbefore input hfresh
  simp_rw [encodingSelectionAdaptivePotential_eq (finite_cacheQuery hbefore input _)]
  rw [encodingSelectionAdaptivePotential_eq hbefore,
    freshStructuralEncodingQueryCharge, if_pos hfresh]
  exact uniform_encodingSelectionTotalPotential_cacheQuery_le_charge hbefore hfresh

theorem probEvent_bad_or_encodingBad_le_expectedPotential
    {α : Type} (computation : OracleComp OracleWorld α) (secretKey : SecretKey) :
    Pr[fun result => Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret result.2 ∨
        EncodingBad result.2 secretKey | (simulateQ romImpl computation).run ∅] ≤
      ∑' result, Pr[= result | (simulateQ romImpl computation).run ∅] *
        encodingSelectionAdaptivePotential result.2 secretKey := by
  classical
  rw [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hevent : Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret result.2 ∨
      EncodingBad result.2 secretKey
  · rw [if_pos hevent]
    by_cases hresult : result ∈ support ((simulateQ romImpl computation).run ∅)
    · have hfinite := finite_cache_of_mem_support computation ∅ result.1 result.2
        hresult finite_empty
      rw [encodingSelectionAdaptivePotential_eq hfinite,
        encodingSelectionTotalPotential_eq_one_of_bad_or_encodingBad hfinite hevent, mul_one]
    · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul]
  · rw [if_neg hevent]
    exact bot_le

theorem probEvent_bad_or_encodingBad_le_queryCharge
    {α : Type} (computation : OracleComp OracleWorld α) (secretKey : SecretKey) :
    Pr[fun result => Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret result.2 ∨
        EncodingBad result.2 secretKey | (simulateQ romImpl computation).run ∅] ≤
      expectedQueryCharge (freshStructuralEncodingQueryCharge secretKey.parameter)
        computation ∅ * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  exact (probEvent_bad_or_encodingBad_le_expectedPotential computation secretKey).trans
    ((expected_encodingSelectionAdaptivePotential_le_queryCharge computation secretKey ∅
      finite_empty).trans_eq (by rw [encodingSelectionAdaptivePotential_empty, zero_add]))

end SphincsSecurity.Concrete.TightEncoding
