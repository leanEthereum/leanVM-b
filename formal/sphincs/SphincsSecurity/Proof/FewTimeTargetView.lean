import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.FewTimeOriginTerminal
import SphincsSecurity.Proof.FewTimeTargetCount

/-!
# Verifier target views at fresh candidate intervals

An admissible message-digest answer first inserted during a signer interval is the digest-loop
answer selected by that invocation. The viewed trace therefore retains exactly the verifier target
view at the corresponding signer rank, even if later signature construction failed.
-/

namespace SphincsSecurity

open OracleComp OracleSpec

namespace Concrete

def targetCandidateIntervalView (state : ViewedFullTraceState)
    (position : Fin state.trace.intervals.length) : FewTimeView :=
  match state.trace.intervals.get position with
  | ⟨.inl (.inl _), _, _, _⟩ => default
  | ⟨.inl (.inr _), output, _, _⟩ => hashOutputFewTimeView output
  | ⟨.inr _, _, _, _⟩ =>
      (state.views[signerIntervalCount
        (state.trace.intervals.take position.val)]?.getD none).getD default

noncomputable def freshTargetCandidateViews (secretKey : SecretKey)
    (state : ViewedFullTraceState) :
    Fin ((freshTargetCandidatePositions secretKey state.trace).card + 1) → FewTimeView :=
  Fin.lastCases (state.targetView.getD default) fun candidate =>
    targetCandidateIntervalView state
      ((freshTargetCandidatePositions secretKey state.trace).equivFin.symm candidate).1

@[simp] theorem freshTargetCandidateViews_last (secretKey : SecretKey)
    (state : ViewedFullTraceState) :
    freshTargetCandidateViews secretKey state
      (Fin.last (freshTargetCandidatePositions secretKey state.trace).card) =
        state.targetView.getD default := by
  simp [freshTargetCandidateViews]

@[simp] theorem freshTargetCandidateViews_castSucc (secretKey : SecretKey)
    (state : ViewedFullTraceState)
    (candidate : Fin (freshTargetCandidatePositions secretKey state.trace).card) :
    freshTargetCandidateViews secretKey state candidate.castSucc =
      targetCandidateIntervalView state
        ((freshTargetCandidatePositions secretKey state.trace).equivFin.symm candidate).1 := by
  simp [freshTargetCandidateViews]

theorem targetCandidateIntervalView_direct (state : ViewedFullTraceState)
    (position : Fin state.trace.intervals.length) (input : HashInput)
    (output : HashOutput) (initialCache finalCache : QueryCache HashSpec)
    (hentry : state.trace.intervals.get position =
      ⟨.inl (.inr input), output, initialCache, finalCache⟩) :
    targetCandidateIntervalView state position = hashOutputFewTimeView output := by
  have hentry' : state.trace.intervals[position.val] =
      ⟨.inl (.inr input), output, initialCache, finalCache⟩ := by
    simpa only [List.get_eq_getElem] using hentry
  simp [targetCandidateIntervalView, hentry']

theorem targetCandidateIntervalView_signer (state : ViewedFullTraceState)
    (position : Fin state.trace.intervals.length) (request : SignRequest)
    (signature : Option Signature) (initialCache finalCache : QueryCache HashSpec)
    (view : FewTimeView)
    (hentry : state.trace.intervals.get position =
      ⟨.inr request, signature, initialCache, finalCache⟩)
    (hview : state.views[signerIntervalCount
      (state.trace.intervals.take position.val)]? = some (some view)) :
    targetCandidateIntervalView state position = view := by
  have hentry' : state.trace.intervals[position.val] =
      ⟨.inr request, signature, initialCache, finalCache⟩ := by
    simpa only [List.get_eq_getElem] using hentry
  simp [targetCandidateIntervalView, hentry', hview]

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
  obtain ⟨_, _, hview, _⟩ :=
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

theorem ProperFewTimeLeak.signer_target_signature_eq_none
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {signingLog : QueryLog SigningSpec}
    {index : Index} {leaves : DigestTree → FtsLeaf}
    (hproper : ProperFewTimeLeak f cache secretKey signingLog index leaves)
    (state : ViewedFullTraceState)
    (hlog : state.trace.signing.toSigningLog = signingLog)
    (hvalidViews : state.ValidViews secretKey)
    (hconsistent : state.trace.Consistent)
    (hvalidRuns : state.trace.signing.ValidRuns secretKey)
    (hcaches : state.trace.signing.CachesLe cache) (hf : cache.AgreesWithFn f)
    (position : Fin state.trace.intervals.length)
    (request : SignRequest) (signature : Option Signature)
    (initialCache finalCache : QueryCache HashSpec)
    (hinterval : state.trace.intervals.get position =
      ⟨.inr request, signature, initialCache, finalCache⟩)
    (targetPayload : HashInput) (output : HashOutput)
    (hbefore : initialCache
      (tweakableHashInput secretKey.parameter .message targetPayload) = none)
    (hafter : finalCache
      (tweakableHashInput secretKey.parameter .message targetPayload) = some output)
    (houtput : signAttemptResultOfOutput output = some (index, leaves)) :
    signature = none := by
  obtain ⟨signingPosition, viewPosition, _, _, hentry, hviewRun⟩ :=
    ViewedFullTraceState.ValidViews.signer_interval hvalidViews hconsistent position
      request signature initialCache finalCache hinterval
  cases hsignature : signature with
  | none => rfl
  | some signed =>
      exfalso
      have hsigningMem := List.get_mem state.trace.signing signingPosition
      let signingEntry : SigningCacheEntry :=
        ⟨request, some signed, initialCache, finalCache⟩
      have hentry' : state.trace.signing.get signingPosition = signingEntry := by
        simpa only [hsignature, signingEntry] using hentry
      have hsigningEntryMem : signingEntry ∈ state.trace.signing := by
        rw [← hentry']
        exact hsigningMem
      have hlogMem : (⟨request, some signed⟩ :
          (request : SignRequest) × SigningSpec.Range request) ∈ signingLog := by
        rw [← hlog, SigningCacheTrace.toSigningLog, List.mem_map]
        exact ⟨signingEntry, hsigningEntryMem, by simp [signingEntry]⟩
      rw [hsignature] at hviewRun
      obtain ⟨randomness, hpayload, _, hrandomness⟩ :=
        signingCacheEntry_validView_fresh_admissible_transition_view hviewRun
          targetPayload output index leaves hbefore hafter houtput
      have hrandomness' : randomness = signed.randomness :=
        hrandomness signed rfl
      have hvalidRun := hvalidRuns signingEntry hsigningEntryMem
      change (some signed, finalCache) ∈ support
        ((simulateQ romImpl (scheme.sign secretKey request)).run initialCache) at hvalidRun
      rw [show scheme.sign secretKey request = sign secretKey request from rfl] at hvalidRun
      have hcacheLe : finalCache ≤ cache :=
        (hcaches signingEntry hsigningEntryMem).2
      have hfinalAgree : finalCache.AgreesWithFn f :=
        fun _ _ hcached => hf (hcacheLe hcached)
      have hreplay := replayRom_of_mem_support (sign secretKey request) initialCache
        (some signed) finalCache hvalidRun f hfinalAgree
      have hrun := successfulSignRun_of_mem_support f secretKey request signed
        initialCache finalCache cache hreplay hcacheLe hf
      have htargetCached : cache
          (tweakableHashInput secretKey.parameter .message targetPayload) = some output :=
        hcacheLe hafter
      have htargetAnswer : f
          (tweakableHashInput secretKey.parameter .message targetPayload) = output :=
        hf htargetCached
      have hevalTarget : evalWithAnswerFn f
          (signAttempt secretKey request signed.randomness) = some (index, leaves) := by
        simp only [signAttempt, messageDigest, oracleHash, evalWithAnswerFn_bind,
          evalWithAnswerFn_query]
        rw [← hrandomness', ← hpayload, htargetAnswer]
        by_cases hadmissibleOutput : Admissible (truncateMessageDigest output)
        · simpa only [if_pos hadmissibleOutput, evalWithAnswerFn_pure,
            signAttemptResultOfOutput] using houtput
        · simpa only [if_neg hadmissibleOutput, evalWithAnswerFn_pure,
            signAttemptResultOfOutput] using houtput
      obtain ⟨actualIndex, actualLeaves, hhonest⟩ := hrun.honest_fts_at
      have hpairs : (actualIndex, actualLeaves) = (index, leaves) := by
        exact Option.some.inj (hhonest.1.2.1.symm.trans hevalTarget)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpairs
      exact hproper.2 ⟨request, some signed⟩ signed hlogMem rfl hrun hhonest

end Concrete

end SphincsSecurity
