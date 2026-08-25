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

noncomputable def freshTargetCandidateOrdinal (secretKey : SecretKey)
    (state : ViewedFullTraceState) (position : Fin state.trace.intervals.length)
    (hcandidate : position ∈ freshTargetCandidatePositions secretKey state.trace) :
    Fin (freshTargetCandidatePositions secretKey state.trace).card :=
  (freshTargetCandidatePositions secretKey state.trace).equivFin ⟨position, hcandidate⟩

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

theorem freshTargetCandidateViews_ordinal (secretKey : SecretKey)
    (state : ViewedFullTraceState) (position : Fin state.trace.intervals.length)
    (hcandidate : position ∈ freshTargetCandidatePositions secretKey state.trace) :
    freshTargetCandidateViews secretKey state
      (freshTargetCandidateOrdinal secretKey state position hcandidate).castSucc =
        targetCandidateIntervalView state position := by
  rw [freshTargetCandidateViews_castSucc]
  have hinverse := Equiv.symm_apply_apply
    (freshTargetCandidatePositions secretKey state.trace).equivFin ⟨position, hcandidate⟩
  exact congrArg (targetCandidateIntervalView state ∘ Subtype.val) hinverse

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

theorem gameAfterSecretsWithViewTrace_target_in_freshCandidateViews
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState)
    (hresult : result ∈ support
      (gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret))
    (f : QueryImpl HashSpec Id) (hf : result.2.cache.AgreesWithFn f)
    (digest : MessageDigest)
    (hdigest : evalWithAnswerFn f
      (messageDigest parameter result.1.1 result.1.2.1.message
        result.1.2.1.signature.randomness) = digest)
    (hadmissible : Admissible digest) :
    let secretKey : SecretKey := ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
    ∃ candidate,
      freshTargetCandidateViews secretKey result.2 candidate =
        fewTimeTargetView (digestIndex digest) (digestLeaves digest) := by
  let secretKey : SecretKey := ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
  let targetPayload := messageDigestPayload result.1.1 result.1.2.1.message
    result.1.2.1.signature.randomness
  let input := tweakableHashInput parameter .message targetPayload
  obtain ⟨rootCache, adversaryCache, digestCache, output, _, _, houtput,
      hdigestLe, htargetView, horigin, _⟩ :=
    gameAfterSecretsWithViewTrace_target_source_kind adversary parameter otsSecret
      ftsSecret result hresult
  have hcachedDigest : digestCache input = some output :=
    randomOracle_output_cached input adversaryCache digestCache output (by
      simpa only [input, targetPayload] using houtput)
  have hcachedFinal : result.2.cache input = some output := hdigestLe hcachedDigest
  have hanswer : f input = output := hf hcachedFinal
  have hdigestOutput : truncateMessageDigest output = digest := by
    simpa only [messageDigest, oracleHash, evalWithAnswerFn_bind, evalWithAnswerFn_query,
      evalWithAnswerFn_pure, input, targetPayload, hanswer] using hdigest
  have hattempt : signAttemptResultOfOutput output =
      some (digestIndex digest, digestLeaves digest) := by
    simp [signAttemptResultOfOutput, hdigestOutput, hadmissible]
  have htargetOutput : hashOutputFewTimeView output =
      fewTimeTargetView (digestIndex digest) (digestLeaves digest) := by
    simp [hashOutputFewTimeView, fewTimeTargetView, hdigestOutput]
  rcases horigin with hverifier | ⟨source, hsourceInitial, hsourceFinal, hkind⟩
  · refine ⟨Fin.last (freshTargetCandidatePositions secretKey result.2.trace).card, ?_⟩
    rw [freshTargetCandidateViews_last, htargetView]
    simpa only [Option.getD_some] using htargetOutput
  · have hbase : (result.1, result.2.base) ∈ support
        (gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret) := by
      rw [← gameAfterSecretsWithViewTrace_projection adversary parameter otsSecret ftsSecret,
        support_map]
      exact ⟨result, hresult, rfl⟩
    have hintervals := gameAfterSecretsWithFullTrace_support_interval_invariants adversary
      parameter otsSecret ftsSecret (result.1, result.2.base) hbase
    have hvalidIntervals := gameAfterSecretsWithFullTrace_support_validIntervals adversary
      parameter otsSecret ftsSecret (result.1, result.2.base) hbase
    have hvalidViews := gameAfterSecretsWithViewTrace_support_validViews adversary parameter
      otsSecret ftsSecret result hresult
    let entry := result.2.trace.intervals.get source
    have hentry : result.2.trace.intervals.get source = entry := rfl
    have hsourceCandidate : FreshTargetCandidate secretKey entry :=
      freshTargetCandidate_of_message_transition secretKey entry targetPayload
        (hvalidIntervals entry (List.get_mem _ source))
        (by simpa only [secretKey, input] using hsourceInitial)
        (by simpa only [secretKey, input] using hsourceFinal)
        (by simpa only [secretKey, input] using hkind)
    have hcandidateMem : source ∈
        freshTargetCandidatePositions secretKey result.2.trace := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ source, by
        simpa only [entry] using hsourceCandidate⟩
    let candidate :=
      (freshTargetCandidateOrdinal secretKey result.2 source hcandidateMem).castSucc
    refine ⟨candidate, ?_⟩
    rw [show candidate =
      (freshTargetCandidateOrdinal secretKey result.2 source hcandidateMem).castSucc from rfl,
      freshTargetCandidateViews_ordinal]
    obtain ⟨sourceOutput, hsourceOutput⟩ := Option.ne_none_iff_exists'.mp hsourceFinal
    have hsourceLe : entry.finalCache ≤ result.2.cache :=
      (hintervals.2.1 entry (List.get_mem _ source)).2
    have hsourceOutputEq : sourceOutput = output := by
      have hcached := hsourceLe (by simpa only [entry, input] using hsourceOutput)
      rw [hcachedFinal] at hcached
      exact (Option.some.inj hcached).symm
    have hsourceExact : entry.finalCache input = some output := by
      simpa only [hsourceOutputEq] using hsourceOutput
    have hvalidEntry := hvalidIntervals entry (List.get_mem _ source)
    rcases hkind with hdirect | ⟨request, hsigner⟩
    · rcases entry with ⟨entryInput, entryOutput, initialCache, finalCache⟩
      change (result.2.trace.intervals.get source).input = .inl (.inr input) at hdirect
      have hentryInput := congrArg AdversaryCacheEntry.input hentry
      rw [hentryInput] at hdirect
      rcases entryInput with worldInput | sourceRequest
      · rcases worldInput with uniformInput | directInput
        · simp at hdirect
        · simp only [Sum.inl.injEq, Sum.inr.injEq] at hdirect
          subst directInput
          change finalCache input = some output at hsourceExact
          have hdirectRun : (entryOutput, finalCache) ∈ support
              ((randomOracle input).run initialCache) := by
            have hrun := hvalidEntry
            change (entryOutput, finalCache) ∈ support
              ((randomOracle input).run initialCache) at hrun
            exact hrun
          have hdirectCached : finalCache input = some entryOutput :=
            randomOracle_run_output_cached input initialCache finalCache entryOutput hdirectRun
          have hentryOutputEq : entryOutput = output := by
            rw [hsourceExact] at hdirectCached
            exact (Option.some.inj hdirectCached).symm
          rw [targetCandidateIntervalView_direct result.2 source input entryOutput
            initialCache finalCache hentry]
          rw [hentryOutputEq]
          exact htargetOutput
      · simp at hdirect
    · rcases entry with ⟨entryInput, entryOutput, initialCache, finalCache⟩
      change (result.2.trace.intervals.get source).input = .inr request at hsigner
      have hentryInput := congrArg AdversaryCacheEntry.input hentry
      rw [hentryInput] at hsigner
      rcases entryInput with worldInput | sourceRequest
      · simp at hsigner
      · simp only [Sum.inr.injEq] at hsigner
        subst sourceRequest
        rw [hentry] at hsourceInitial
        change initialCache input = none at hsourceInitial
        change finalCache input = some output at hsourceExact
        have hstored := ViewedFullTraceState.ValidViews.signer_interval_fresh_admissible_view
          hvalidViews hintervals.1 source request entryOutput initialCache finalCache
          hentry targetPayload output
          (digestIndex digest) (digestLeaves digest)
          (by simpa only [secretKey, input] using hsourceInitial)
          (by simpa only [secretKey, input] using hsourceExact) hattempt
        rw [targetCandidateIntervalView_signer result.2 source request entryOutput
          initialCache finalCache (hashOutputFewTimeView output)
          hentry hstored]
        exact htargetOutput

theorem gameAfterSecretsWithViewTrace_freshCandidateViews_count_le
    (adversary : Adversary) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (hfts : ftsSecret ∈ support sampleFtsSecrets)
    (result : (Digest × Forgery × Bool) × ViewedFullTraceState)
    (hresult : result ∈ support
      (gameAfterSecretsWithViewTrace adversary parameter otsSecret ftsSecret)) :
    (freshTargetCandidatePositions
      ⟨parameter, result.1.1, otsSecret, ftsSecret⟩ result.2.trace).card + 1 ≤ q + 1 := by
  apply Nat.succ_le_succ
  have hbound := gameAfterSecretsWithViewTrace_freshTargetCandidatePositions_card_le
    adversary q hq parameter hparameter otsSecret hots ftsSecret hfts result hresult
  exact_mod_cast hbound

end Concrete

end SphincsSecurity
