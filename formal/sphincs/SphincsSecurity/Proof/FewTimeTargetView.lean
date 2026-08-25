import SphincsSecurity.Proof.FewTimeTargetCount
import SphincsSecurity.Proof.FewTimeOriginTerminal

/-!
# Verifier target views at fresh candidate intervals

An admissible message-digest answer first inserted during a signer interval is the digest-loop
answer selected by that invocation. The viewed trace therefore retains exactly the verifier target
view at the corresponding signer rank, even if later signature construction failed.
-/

namespace SphincsSecurity

open OracleComp OracleSpec

namespace Concrete

theorem ViewedFullTraceState.ValidViews.signer_interval
    {secretKey : SecretKey} {state : ViewedFullTraceState}
    (hvalid : state.ValidViews secretKey) (hconsistent : state.trace.Consistent)
    (position : Fin state.trace.intervals.length)
    (request : SignRequest) (signature : Option Signature)
    (initialCache finalCache : QueryCache HashSpec)
    (hinterval : state.trace.intervals.get position =
      ⟨.inr request, signature, initialCache, finalCache⟩) :
    let rank := signerIntervalCount (state.trace.intervals.take position.val)
    ∃ (signingPosition : Fin state.trace.signing.length)
        (viewPosition : Fin state.views.length),
      signingPosition.val = rank
        ∧ viewPosition.val = rank
        ∧ state.trace.signing.get signingPosition =
          ⟨request, signature, initialCache, finalCache⟩
        ∧ SigningCacheEntry.ValidView secretKey
          ⟨request, signature, initialCache, finalCache⟩
          (state.views.get viewPosition) := by
  let entry : SigningCacheEntry := ⟨request, signature, initialCache, finalCache⟩
  have hsigning : AdversaryCacheEntry.signingEntry?
      (state.trace.intervals.get position) = some entry := by
    rw [hinterval]
    rfl
  have hfiltered := filterMap_getElem?_at_rank AdversaryCacheEntry.signingEntry?
    state.trace.intervals position entry hsigning
  rw [hconsistent.2] at hfiltered
  let rank := signerIntervalCount (state.trace.intervals.take position.val)
  have hrankLt : rank < state.trace.signing.length :=
    (List.getElem?_eq_some_iff.mp hfiltered).1
  let signingPosition : Fin state.trace.signing.length := ⟨rank, hrankLt⟩
  have hentry : state.trace.signing.get signingPosition = entry := by
    exact (List.getElem?_eq_some_iff.mp hfiltered).2
  let viewPosition : Fin state.views.length :=
    ⟨rank, by rw [← hvalid.length_eq]; exact hrankLt⟩
  have hviewRun := hvalid.get signingPosition.isLt viewPosition.isLt
  rw [hentry] at hviewRun
  exact ⟨signingPosition, viewPosition, rfl, rfl, hentry, hviewRun⟩

theorem ViewedFullTraceState.ValidViews.signer_interval_fresh_admissible_view
    {secretKey : SecretKey} {state : ViewedFullTraceState}
    (hvalid : state.ValidViews secretKey) (hconsistent : state.trace.Consistent)
    (position : Fin state.trace.intervals.length)
    (request : SignRequest) (signature : Option Signature)
    (initialCache finalCache : QueryCache HashSpec)
    (hinterval : state.trace.intervals.get position =
      ⟨.inr request, signature, initialCache, finalCache⟩)
    (targetPayload : HashInput) (output : HashOutput) (index : Index)
    (leaves : DigestTree → FtsLeaf)
    (hbefore : initialCache
      (tweakableHashInput secretKey.parameter .message targetPayload) = none)
    (hafter : finalCache
      (tweakableHashInput secretKey.parameter .message targetPayload) = some output)
    (houtput : signAttemptResultOfOutput output = some (index, leaves)) :
    state.views[signerIntervalCount
      (state.trace.intervals.take position.val)]? =
        some (some (hashOutputFewTimeView output)) := by
  obtain ⟨signingPosition, viewPosition, hsigningRank, hviewRank, hentry,
      hviewRun⟩ := ViewedFullTraceState.ValidViews.signer_interval hvalid hconsistent
        position request signature initialCache finalCache hinterval
  obtain ⟨_, _, hview⟩ :=
    signingCacheEntry_validView_fresh_admissible_transition_view hviewRun
      targetPayload output index leaves hbefore hafter houtput
  apply List.getElem?_eq_some_iff.mpr
  refine ⟨?_, ?_⟩
  · rw [← hviewRank]
    exact viewPosition.isLt
  · let rankedViewPosition : Fin state.views.length :=
      ⟨signerIntervalCount (state.trace.intervals.take position.val), by
        rw [← hviewRank]
        exact viewPosition.isLt⟩
    have hpositionEq : rankedViewPosition = viewPosition := Fin.ext hviewRank.symm
    change state.views.get rankedViewPosition = some (hashOutputFewTimeView output)
    rw [hpositionEq]
    exact hview

end Concrete

end SphincsSecurity
