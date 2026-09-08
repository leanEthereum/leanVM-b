import SphincsSecurity.Proof.NewTargetEnvelopeCharge

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem expected_signWithView_newTargetEnvelopeCharge_le_mass_mul (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (uniform reuse arrival : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      newTargetEnvelopeCharge key before result.2 (log ++ [⟨message, result.1.1⟩]) uniform reuse arrival queries signings groups remaining) ≤
        freshDigestSelectionProbability key message before *
          ((Fintype.card Index : ENNReal)⁻¹ *
            targetIndexEnvelope uniform reuse arrival queries signings (targetIndexMoments key before log) groups.card remaining.card) := by
  by_cases hexists : ∃ payload, before (tweakableHashInput key.parameter .message payload) = none
  · obtain ⟨reference, hreference⟩ := hexists
    let weight := fun source => targetShapeEnvelope uniform reuse arrival queries signings
      (targetShapeMoments key before log reference source) groups remaining
    have hbound := expected_signWithView_newAdmissible_cost_le_mass_mul key message before _ weight
      (fun result hr => signWithView_newTargetEnvelopeCharge_le_events key message before log hsigned
        reference hreference uniform reuse arrival queries signings groups remaining result hr)
    apply hbound.trans_eq
    exact congrArg (fun value => freshDigestSelectionProbability key message before * value)
      (expected_fresh_targetShapeEnvelope key before log reference hreference hsigned
        uniform reuse arrival queries signings groups remaining hvalid)
  · have hzero (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec) :
        newTargetEnvelopeCharge key before result.2 (log ++ [⟨message, result.1.1⟩]) uniform reuse arrival queries signings groups remaining = 0 :=
      newTargetEnvelopeCharge_of_no_new key before result.2 _ uniform reuse arrival queries signings groups remaining
        (fun payload _ hfresh _ _ => hexists ⟨payload, hfresh⟩)
    simp only [hzero, mul_zero, tsum_zero, zero_le]

theorem expected_signWithView_newTargetEnvelopeCharge_le (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (uniform reuse arrival : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      newTargetEnvelopeCharge key before result.2 (log ++ [⟨message, result.1.1⟩]) uniform reuse arrival queries signings groups remaining) ≤
        (Fintype.card Index : ENNReal)⁻¹ *
          targetIndexEnvelope uniform reuse arrival queries signings (targetIndexMoments key before log) groups.card remaining.card :=
  (expected_signWithView_newTargetEnvelopeCharge_le_mass_mul key message before log hsigned
    uniform reuse arrival queries signings groups remaining hvalid).trans
      (mul_le_of_le_one_left' (freshDigestSelectionProbability_le_one key message before))

end SphincsSecurity.Concrete
