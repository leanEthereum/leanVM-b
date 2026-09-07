import SphincsSecurity.Proof.NewTargetSigningStability
import SphincsSecurity.Proof.FreshTargetPayload

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def newTargetEnvelopeCharge (key : SecretKey) (before after : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (uniform reuse arrival : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) : ENNReal :=
  cacheMessageWeight key.parameter (fun input target => if before input = none then
    targetShapeEnvelope uniform reuse arrival queries signings (targetShapeMoments key after log (payloadOf input) target) groups remaining else 0) after

theorem signWithView_newTargetEnvelopeCharge_of_new (key : SecretKey) (message : Message)
    (before after : QueryCache HashSpec) (signature : Option Signature) (view : Option FewTimeView)
    (hresult : ((signature, view), after) ∈ support ((simulateQ romImpl (signWithView key message)).run before))
    (log : QueryLog SigningSpec) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (payload : HashInput) (output : HashOutput)
    (hfresh : before (tweakableHashInput key.parameter .message payload) = none)
    (hafter : after (tweakableHashInput key.parameter .message payload) = some output)
    (hadmissible : Admissible (truncateMessageDigest output))
    (uniform reuse arrival : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    newTargetEnvelopeCharge key before after (log ++ [⟨message, signature⟩]) uniform reuse arrival queries signings groups remaining =
      targetShapeEnvelope uniform reuse arrival queries signings (targetShapeMoments key before log payload (hashOutputFewTimeView output)) groups remaining := by
  unfold newTargetEnvelopeCharge
  rw [signWithView_cacheMessageWeight_of_new key message before after signature view hresult _ payload output hfresh hafter hadmissible,
    cacheMessageWeight_fresh_restriction, zero_add, if_pos hfresh, payloadOf_tweakableHashInput,
    signWithView_new_targetShapeMoments_eq key message before after signature view hresult log hsigned payload output _ hfresh hafter hadmissible]

theorem newTargetEnvelopeCharge_of_no_new (key : SecretKey) (before after : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (uniform reuse arrival : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (hnone : ∀ payload output, before (tweakableHashInput key.parameter .message payload) = none →
      after (tweakableHashInput key.parameter .message payload) = some output → ¬ Admissible (truncateMessageDigest output)) :
    newTargetEnvelopeCharge key before after log uniform reuse arrival queries signings groups remaining = 0 := by
  apply ENNReal.tsum_eq_zero.mpr
  intro input
  unfold cacheMessageEntryWeight
  cases houtput : after input with
  | none => rfl
  | some output =>
      simp only
      split_ifs with hgood hfresh
      · obtain ⟨payload, rfl⟩ := hgood.1
        exact (hnone payload output hfresh houtput hgood.2).elim
      · rfl
      · rfl

theorem signWithView_newTargetEnvelopeCharge_le_events (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (reference : HashInput) (hreference : before (tweakableHashInput key.parameter .message reference) = none)
    (uniform reuse arrival : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl (signWithView key message)).run before)) :
    newTargetEnvelopeCharge key before result.2 (log ++ [⟨message, result.1.1⟩]) uniform reuse arrival queries signings groups remaining ≤
      ∑' source, if NewAdmissibleSignerView before key (· = source) result then
        targetShapeEnvelope uniform reuse arrival queries signings (targetShapeMoments key before log reference source) groups remaining else 0 := by
  by_cases hnew : NewAdmissibleSignerView before key (fun _ => True) result
  · obtain ⟨payload, output, hfresh, hafter, hadmissible, _⟩ := hnew
    rw [signWithView_newTargetEnvelopeCharge_of_new key message before result.2 result.1.1 result.1.2 hresult log hsigned payload output hfresh hafter hadmissible,
      targetShapeMoments_fresh_payload_eq key before log payload reference hfresh hreference hsigned]
    have hevent : NewAdmissibleSignerView before key (· = hashOutputFewTimeView output) result :=
      ⟨payload, output, hfresh, hafter, hadmissible, rfl⟩
    exact (le_of_eq (if_pos hevent).symm).trans (ENNReal.le_tsum (hashOutputFewTimeView output))
  · rw [newTargetEnvelopeCharge_of_no_new key before result.2 _ uniform reuse arrival queries signings groups remaining
      (fun payload output hfresh hafter hadmissible => hnew ⟨payload, output, hfresh, hafter, hadmissible, trivial⟩)]
    exact bot_le

end SphincsSecurity.Concrete
