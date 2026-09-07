import SphincsSecurity.Proof.FreshSignerCacheView

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem signDigestLoop_new_payload_eq_selected (attempts : Nat) (key : SecretKey) (message : Message)
    (before after : QueryCache HashSpec) (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (hloop : (some (randomness, index, leaves), after) ∈ support ((simulateQ romImpl (signDigestLoop attempts key message)).run before))
    (payload : HashInput) (output : HashOutput)
    (hbefore : before (tweakableHashInput key.parameter .message payload) = none)
    (hafter : after (tweakableHashInput key.parameter .message payload) = some output)
    (hadmissible : Admissible (truncateMessageDigest output)) :
    payload = messageDigestPayload key.root message randomness := by
  obtain ⟨selected, selectedIndex, selectedLeaves, hselected, hpayload⟩ := signDigestLoop_new_admissible_selected attempts key message
    before after (some (randomness, index, leaves)) hloop payload output hbefore hafter hadmissible
  have hrandomness : randomness = selected := congrArg Prod.fst (Option.some.inj hselected)
  exact hpayload.trans (congrArg _ hrandomness.symm)

theorem signWithView_new_admissible_payload_unique (key : SecretKey) (message : Message)
    (before after : QueryCache HashSpec) (signature : Option Signature) (view : Option FewTimeView)
    (hresult : ((signature, view), after) ∈ support ((simulateQ romImpl (signWithView key message)).run before))
    (first second : HashInput) (firstOutput secondOutput : HashOutput)
    (hfirstBefore : before (tweakableHashInput key.parameter .message first) = none)
    (hfirstAfter : after (tweakableHashInput key.parameter .message first) = some firstOutput)
    (hfirstGood : Admissible (truncateMessageDigest firstOutput))
    (hsecondBefore : before (tweakableHashInput key.parameter .message second) = none)
    (hsecondAfter : after (tweakableHashInput key.parameter .message second) = some secondOutput)
    (hsecondGood : Admissible (truncateMessageDigest secondOutput)) : first = second := by
  rcases signWithView_support_decomposition key message before after signature view hresult with hnone | hsome
  · obtain ⟨randomness, index, leaves, hselected, _⟩ := signDigestLoop_new_admissible_selected digestAttemptLimit key message
      before after none hnone.2.2 first firstOutput hfirstBefore hfirstAfter hfirstGood
    contradiction
  · obtain ⟨randomness, index, leaves, loopCache, hloop, hfinish, _⟩ := hsome
    rw [signAfterDigest_message_cache_eq key randomness index leaves loopCache after signature hfinish first] at hfirstAfter
    rw [signAfterDigest_message_cache_eq key randomness index leaves loopCache after signature hfinish second] at hsecondAfter
    exact (signDigestLoop_new_payload_eq_selected digestAttemptLimit key message before loopCache randomness index leaves hloop
      first firstOutput hfirstBefore hfirstAfter hfirstGood).trans
      (signDigestLoop_new_payload_eq_selected digestAttemptLimit key message before loopCache randomness index leaves hloop
        second secondOutput hsecondBefore hsecondAfter hsecondGood).symm

theorem signWithView_new_admissible_input_unique (key : SecretKey) (message : Message)
    (before after : QueryCache HashSpec) (signature : Option Signature) (view : Option FewTimeView)
    (hresult : ((signature, view), after) ∈ support ((simulateQ romImpl (signWithView key message)).run before))
    (first second : HashInput) (firstOutput secondOutput : HashOutput)
    (hfirstBefore : before first = none) (hfirstMessage : FtsProbeSimulation.MessageHashInput key.parameter first)
    (hfirstAfter : after first = some firstOutput) (hfirstGood : Admissible (truncateMessageDigest firstOutput))
    (hsecondBefore : before second = none) (hsecondMessage : FtsProbeSimulation.MessageHashInput key.parameter second)
    (hsecondAfter : after second = some secondOutput) (hsecondGood : Admissible (truncateMessageDigest secondOutput)) : first = second := by
  obtain ⟨firstPayload, rfl⟩ := hfirstMessage
  obtain ⟨secondPayload, rfl⟩ := hsecondMessage
  exact congrArg (tweakableHashInput key.parameter .message)
    (signWithView_new_admissible_payload_unique key message before after signature view hresult firstPayload secondPayload
      firstOutput secondOutput hfirstBefore hfirstAfter hfirstGood hsecondBefore hsecondAfter hsecondGood)

end SphincsSecurity.Concrete
