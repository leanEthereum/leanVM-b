import SphincsSecurity.Proof.NewTargetEnvelopeCharge

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem expected_signWithView_newTargetEnvelopeCharge_le (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (uniform reuse arrival : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      newTargetEnvelopeCharge key before result.2 (log ++ [⟨message, result.1.1⟩]) uniform reuse arrival queries signings groups remaining) ≤
        (Fintype.card Index : ENNReal)⁻¹ *
          targetIndexEnvelope uniform reuse arrival queries signings (targetIndexMoments key before log) groups.card remaining.card := by
  by_cases hexists : ∃ payload, before (tweakableHashInput key.parameter .message payload) = none
  · obtain ⟨reference, hreference⟩ := hexists
    let weight := fun source => targetShapeEnvelope uniform reuse arrival queries signings (targetShapeMoments key before log reference source) groups remaining
    have hbound : (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
        newTargetEnvelopeCharge key before result.2 (log ++ [⟨message, result.1.1⟩]) uniform reuse arrival queries signings groups remaining) ≤
        ∑' source, Pr[NewAdmissibleSignerView before key (· = source) | (simulateQ romImpl (signWithView key message)).run before] * weight source := by
      calc
        _ ≤ ∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
            ∑' source, if NewAdmissibleSignerView before key (· = source) result then weight source else 0 := by
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)
          · exact mul_le_mul' le_rfl (signWithView_newTargetEnvelopeCharge_le_events key message before log hsigned reference hreference uniform reuse arrival queries signings groups remaining result hresult)
          · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
        _ = _ := by
          simp only [← ENNReal.tsum_mul_left]
          rw [ENNReal.tsum_comm]
          apply tsum_congr
          intro source
          rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
          apply tsum_congr
          intro result
          split_ifs <;> simp
    apply (hbound.trans (expected_newAdmissibleSignerView_weight_le key message before weight)).trans_eq
    exact expected_fresh_targetShapeEnvelope key before log reference hreference hsigned uniform reuse arrival queries signings groups remaining hvalid
  · have hzero (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec) :
        newTargetEnvelopeCharge key before result.2 (log ++ [⟨message, result.1.1⟩]) uniform reuse arrival queries signings groups remaining = 0 :=
      newTargetEnvelopeCharge_of_no_new key before result.2 _ uniform reuse arrival queries signings groups remaining
        (fun payload _ hfresh _ _ => hexists ⟨payload, hfresh⟩)
    simp only [hzero, mul_zero, tsum_zero, zero_le]

end SphincsSecurity.Concrete
