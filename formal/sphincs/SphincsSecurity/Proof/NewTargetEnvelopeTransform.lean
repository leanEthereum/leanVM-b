import SphincsSecurity.Proof.ExpectedNewTargetEnvelope

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem signWithView_newTargetEnvelopeCharge_transform_le_events (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (reference : HashInput) (hreference : before (tweakableHashInput key.parameter .message reference) = none)
    (uniform reuse arrival : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (transform : ENNReal → ENNReal) (hzero : transform 0 = 0)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)) :
    transform (newTargetEnvelopeCharge key before result.2 (log ++ [⟨message, result.1.1⟩])
      uniform reuse arrival queries signings groups remaining) ≤
      ∑' source, if NewAdmissibleSignerView before key (· = source) result then
        transform (targetShapeEnvelope uniform reuse arrival queries signings
          (targetShapeMoments key before log reference source) groups remaining) else 0 := by
  by_cases hnew : NewAdmissibleSignerView before key (fun _ => True) result
  · obtain ⟨payload, output, hfresh, hafter, hadmissible, _⟩ := hnew
    rw [signWithView_newTargetEnvelopeCharge_of_new key message before result.2 result.1.1 result.1.2 hresult log hsigned
      payload output hfresh hafter hadmissible,
      targetShapeMoments_fresh_payload_eq key before log payload reference hfresh hreference hsigned]
    have hevent : NewAdmissibleSignerView before key (· = hashOutputFewTimeView output) result :=
      ⟨payload, output, hfresh, hafter, hadmissible, rfl⟩
    exact (le_of_eq (if_pos hevent).symm).trans (ENNReal.le_tsum (hashOutputFewTimeView output))
  · rw [newTargetEnvelopeCharge_of_no_new key before result.2 _ uniform reuse arrival queries signings groups remaining
      (fun payload output hfresh hafter hadmissible => hnew ⟨payload, output, hfresh, hafter, hadmissible, trivial⟩), hzero]
    exact zero_le

theorem expected_signWithView_newTargetEnvelopeCharge_transform_le_mass_mul (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (reference : HashInput) (hreference : before (tweakableHashInput key.parameter .message reference) = none)
    (uniform reuse arrival : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (transform : ENNReal → ENNReal) (hzero : transform 0 = 0) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      transform (newTargetEnvelopeCharge key before result.2 (log ++ [⟨message, result.1.1⟩])
        uniform reuse arrival queries signings groups remaining)) ≤
      freshDigestSelectionProbability key message before *
        ∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
        transform (targetShapeEnvelope uniform reuse arrival queries signings
          (targetShapeMoments key before log reference source) groups remaining) := by
  exact expected_signWithView_newAdmissible_cost_le_mass_mul key message before _ _
    (fun result hr => signWithView_newTargetEnvelopeCharge_transform_le_events key message before
      log hsigned reference hreference uniform reuse arrival queries signings groups remaining
      transform hzero result hr)

theorem expected_signWithView_newTargetEnvelopeCharge_transform_le (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (reference : HashInput) (hreference : before (tweakableHashInput key.parameter .message reference) = none)
    (uniform reuse arrival : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (transform : ENNReal → ENNReal) (hzero : transform 0 = 0) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      transform (newTargetEnvelopeCharge key before result.2 (log ++ [⟨message, result.1.1⟩])
        uniform reuse arrival queries signings groups remaining)) ≤
      ∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
        transform (targetShapeEnvelope uniform reuse arrival queries signings
          (targetShapeMoments key before log reference source) groups remaining) :=
  (expected_signWithView_newTargetEnvelopeCharge_transform_le_mass_mul key message before log hsigned
    reference hreference uniform reuse arrival queries signings groups remaining transform hzero).trans
      (mul_le_of_le_one_left' (freshDigestSelectionProbability_le_one key message before))

end SphincsSecurity.Concrete
