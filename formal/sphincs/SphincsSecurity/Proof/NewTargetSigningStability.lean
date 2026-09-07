import SphincsSecurity.Proof.FreshTargetEnvelope
import SphincsSecurity.Proof.SignerNewMessageUnique

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem signWithView_new_payload_eq_signature (key : SecretKey) (message : Message)
    (before after : QueryCache HashSpec) (signature : Signature) (view : Option FewTimeView)
    (hresult : ((some signature, view), after) ∈ support ((simulateQ romImpl (signWithView key message)).run before))
    (payload : HashInput) (output : HashOutput)
    (hfresh : before (tweakableHashInput key.parameter .message payload) = none)
    (hafter : after (tweakableHashInput key.parameter .message payload) = some output)
    (hadmissible : Admissible (truncateMessageDigest output)) :
    payload = messageDigestPayload key.root message signature.randomness := by
  rcases signWithView_support_decomposition key message before after (some signature) view hresult with hnone | hsome
  · cases hnone.1
  · obtain ⟨randomness, index, leaves, loopCache, hloop, hfinish, _⟩ := hsome
    rw [signAfterDigest_message_cache_eq key randomness index leaves loopCache after (some signature) hfinish payload] at hafter
    have hrandomness := signAfterDigest_support_some_randomness key randomness index leaves loopCache after signature hfinish
    rw [hrandomness]
    exact signDigestLoop_new_payload_eq_selected digestAttemptLimit key message before loopCache randomness index leaves hloop payload output hfresh hafter hadmissible

theorem signWithView_new_target_eligible_none (key : SecretKey) (message : Message)
    (before after : QueryCache HashSpec) (signature : Option Signature) (view : Option FewTimeView)
    (hresult : ((signature, view), after) ∈ support ((simulateQ romImpl (signWithView key message)).run before))
    (payload : HashInput) (output : HashOutput)
    (hfresh : before (tweakableHashInput key.parameter .message payload) = none)
    (hafter : after (tweakableHashInput key.parameter .message payload) = some output)
    (hadmissible : Admissible (truncateMessageDigest output)) :
    eligibleSigningView? (FtsProbeSimulation.messageAnswers key.parameter after) key.root payload ⟨message, signature⟩ = none := by
  cases signature with
  | none => simp [eligibleSigningView?]
  | some signature =>
      have hpayload := signWithView_new_payload_eq_signature key message before after signature view hresult payload output hfresh hafter hadmissible
      simp [eligibleSigningView?, hpayload]

theorem signWithView_new_targetShapeMoments_eq (key : SecretKey) (message : Message)
    (before after : QueryCache HashSpec) (signature : Option Signature) (view : Option FewTimeView)
    (hresult : ((signature, view), after) ∈ support ((simulateQ romImpl (signWithView key message)).run before))
    (log : QueryLog SigningSpec) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (payload : HashInput) (output : HashOutput) (target : FewTimeView)
    (hfresh : before (tweakableHashInput key.parameter .message payload) = none)
    (hafter : after (tweakableHashInput key.parameter .message payload) = some output)
    (hadmissible : Admissible (truncateMessageDigest output)) :
    targetShapeMoments key after (log ++ [⟨message, signature⟩]) payload target =
      targetShapeMoments key before log payload target := by
  have hcache := simulateQ_romImpl_cache_le (signWithView key message) before ((signature, view), after) hresult
  have heligible := signWithView_new_target_eligible_none key message before after signature view hresult payload output hfresh hafter hadmissible
  funext groups remaining
  unfold targetShapeMoments
  rw [normalizedTargetLogProduct_append_none key before after log _ payload target remaining hcache hsigned heligible]
  congr 1
  apply Finset.prod_congr rfl
  intro group _
  have h := signWithView_normalizedCachedTargetSubsetMatch_of_new key message before after signature view hresult
    (tweakableHashInput key.parameter .message payload) payload target group output hfresh hafter hadmissible
  simpa only [if_true, add_zero] using h

end SphincsSecurity.Concrete
