import XmssSecurity.Proof.ChainOriginProbability
import XmssSecurity.Proof.EncodingActionTrace
import XmssSecurity.Proof.EncodingPrehitProbability
import XmssSecurity.Proof.EncodingTargetMap
import XmssSecurity.Proof.SignCacheHitProbability
import XmssSecurity.Proof.SigningCacheTrace
import XmssSecurity.Proof.WinningEventReduction

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

/-- An encoding event contains two distinct cached encoding inputs with the same truncated output. -/
theorem encoding_outcomeBadEvent_has_cached_collision
    (cache : QueryCache HashSpec) (outcome : GameOutcome)
    (hevent : OutcomeBadEventOccurs cache outcome .encoding) :
    ∃ signedInput forgedInput : HashInput,
      ∃ signedOutput forgedOutput : HashOutput,
        signedInput ≠ forgedInput ∧
        cache signedInput = some signedOutput ∧
        cache forgedInput = some forgedOutput ∧
        truncateHash signedOutput = truncateHash forgedOutput := by
  rcases hevent.2 with hsame | hfresh
  · obtain ⟨request, signature, signedEncoding, forgedEncoding, hsignedDecode,
      hforgedDecode, _hreturned, hepoch, hencoding⟩ := hsame
    change (request.message, signature.randomness) ≠
        (outcome.forgery.message, outcome.forgery.signature.randomness) ∧
      Concrete.CacheView.encodingHash cache outcome.secretKey.parameter request.epoch
          (request.message, signature.randomness) =
        Concrete.CacheView.encodingHash cache outcome.secretKey.parameter request.epoch
          (outcome.forgery.message, outcome.forgery.signature.randomness) at hencoding
    obtain ⟨signedOutput, hsignedCached⟩ :=
      Concrete.CacheView.encodingInput_cached_of_decode_some cache
        outcome.secretKey.parameter request.epoch request.message signature.randomness
        signedEncoding hsignedDecode
    obtain ⟨forgedOutput, hforgedCached⟩ :=
      Concrete.CacheView.encodingInput_cached_of_decode_some cache
        outcome.secretKey.parameter request.epoch outcome.forgery.message
        outcome.forgery.signature.randomness forgedEncoding hforgedDecode
    let signedInput := Concrete.CacheView.encodingInput outcome.secretKey.parameter
      request.epoch (request.message, signature.randomness)
    let forgedInput := Concrete.CacheView.encodingInput outcome.secretKey.parameter
      request.epoch (outcome.forgery.message, outcome.forgery.signature.randomness)
    refine ⟨signedInput, forgedInput, signedOutput, forgedOutput, ?_, hsignedCached,
      hforgedCached, ?_⟩
    · intro hinput
      exact hencoding.1
        (Concrete.CacheView.encodingInput_injective outcome.secretKey.parameter request.epoch
          hinput)
    · rw [Concrete.CacheView.encodingHash,
        Concrete.CacheView.digestAt_eq_of_cache_eq_some hsignedCached,
        Concrete.CacheView.encodingHash,
        Concrete.CacheView.digestAt_eq_of_cache_eq_some hforgedCached] at hencoding
      exact hencoding.2
  · simp [Concrete.FreshEpochBadEventOccurs,
      XmssSecurity.FreshEpochBadEventOccurs] at hfresh

/-- A winning encoding event identifies a genuine returned signature and a distinct forged encoding input with the same cached 128-bit digest. Its transcript contains at most one request per epoch. -/
theorem winning_encoding_event_has_signed_collision
    (cache : QueryCache HashSpec) (outcome : GameOutcome)
    (hevent : WinningOutcomeBadEventOccurs cache outcome .encoding) :
    SigningTranscript.Valid outcome.signingLog ∧
    outcome.signingLog.length ≤ lifetime ∧
    ∃ request signature signedOutput forgedOutput,
      SigningTranscript.Returned outcome.signingLog request signature ∧
      request.epoch = outcome.forgery.epoch ∧
      Concrete.CacheView.encodingInput outcome.secretKey.parameter request.epoch
          (request.message, signature.randomness) ≠
        Concrete.CacheView.encodingInput outcome.secretKey.parameter request.epoch
          (outcome.forgery.message, outcome.forgery.signature.randomness) ∧
      cache (Concrete.CacheView.encodingInput outcome.secretKey.parameter request.epoch
          (request.message, signature.randomness)) = some signedOutput ∧
      cache (Concrete.CacheView.encodingInput outcome.secretKey.parameter request.epoch
          (outcome.forgery.message, outcome.forgery.signature.randomness)) =
        some forgedOutput ∧
      truncateHash signedOutput = truncateHash forgedOutput := by
  refine ⟨hevent.signingTranscript_valid,
    hevent.signingLog_length_le_lifetime, ?_⟩
  rcases hevent.2.2 with hsame | hfresh
  · obtain ⟨request, signature, signedEncoding, forgedEncoding, hsignedDecode,
      hforgedDecode, hreturned, hepoch, hencoding⟩ := hsame
    change (request.message, signature.randomness) ≠
        (outcome.forgery.message, outcome.forgery.signature.randomness) ∧
      Concrete.CacheView.encodingHash cache outcome.secretKey.parameter request.epoch
          (request.message, signature.randomness) =
        Concrete.CacheView.encodingHash cache outcome.secretKey.parameter request.epoch
          (outcome.forgery.message, outcome.forgery.signature.randomness) at hencoding
    obtain ⟨signedOutput, hsignedCached⟩ :=
      Concrete.CacheView.encodingInput_cached_of_decode_some cache
        outcome.secretKey.parameter request.epoch request.message signature.randomness
        signedEncoding hsignedDecode
    obtain ⟨forgedOutput, hforgedCached⟩ :=
      Concrete.CacheView.encodingInput_cached_of_decode_some cache
        outcome.secretKey.parameter request.epoch outcome.forgery.message
        outcome.forgery.signature.randomness forgedEncoding hforgedDecode
    refine ⟨request, signature, signedOutput, forgedOutput, hreturned, hepoch, ?_,
      hsignedCached, hforgedCached, ?_⟩
    · intro hinput
      exact hencoding.1
        (Concrete.CacheView.encodingInput_injective outcome.secretKey.parameter request.epoch
          hinput)
    · rw [Concrete.CacheView.encodingHash,
        Concrete.CacheView.digestAt_eq_of_cache_eq_some hsignedCached,
        Concrete.CacheView.encodingHash,
        Concrete.CacheView.digestAt_eq_of_cache_eq_some hforgedCached] at hencoding
      exact hencoding.2
  · simp [Concrete.FreshEpochBadEventOccurs,
      XmssSecurity.FreshEpochBadEventOccurs] at hfresh

/-- The signed-target map selects exactly the one same-epoch signing input relevant to the forged input. This avoids a factor for the total number of signed epochs in the post-signing collision bound. -/
theorem winning_encoding_event_has_indexed_target_collision
    (cache : QueryCache HashSpec) (outcome : GameOutcome)
    (hevent : WinningOutcomeBadEventOccurs cache outcome .encoding) :
    ∃ forgedInput signedInput signedOutput forgedOutput,
      forgedInput ≠ signedInput ∧
      signedEncodingTargetInput outcome.secretKey.parameter outcome.signingLog forgedInput =
        signedInput ∧
      cache signedInput = some signedOutput ∧
      cache forgedInput = some forgedOutput ∧
      truncateHash signedOutput = truncateHash forgedOutput := by
  obtain ⟨hvalid, _hlength, request, signature, signedOutput, forgedOutput,
    hreturned, _hepoch, hne, hsigned, hforged, hdigest⟩ :=
    winning_encoding_event_has_signed_collision cache outcome hevent
  let signedInput := Concrete.CacheView.encodingInput outcome.secretKey.parameter
    request.epoch (request.message, signature.randomness)
  let forgedInput := Concrete.CacheView.encodingInput outcome.secretKey.parameter
    request.epoch (outcome.forgery.message, outcome.forgery.signature.randomness)
  have htarget : IsSignedEncodingTarget outcome.secretKey.parameter outcome.signingLog
      forgedInput signedInput := by
    exact ⟨request, signature, hreturned, by
      simp [forgedInput], rfl⟩
  refine ⟨forgedInput, signedInput, signedOutput, forgedOutput, hne.symm, ?_,
    hsigned, hforged, hdigest⟩
  exact signedEncodingTargetInput_eq_of_target hvalid htarget

/-- A winning encoding collision is oriented at the matching signing boundary: either the forged encoding input was already cached before signing, or it was still fresh when the signer installed the honest target. -/
theorem winning_encoding_event_trace_temporal_decomposition
    (cache : QueryCache HashSpec) (outcome : GameOutcome)
    (trace : SigningCacheTrace)
    (hlog : trace.toSigningLog = outcome.signingLog)
    (hcaches : trace.CachesLe cache)
    (hcached : trace.SuccessfulEncodingsCached outcome.secretKey)
    (hevent : WinningOutcomeBadEventOccurs cache outcome .encoding) :
    ∃ entry ∈ trace,
      entry.PreexistingEncodingCollision outcome.secretKey ∨
        entry.FreshForgedEncodingCollision outcome.secretKey outcome.forgery cache := by
  obtain ⟨_hvalid, _hlength, request, signature, signedOutput, forgedOutput,
    hreturned, hepoch, hne, hsigned, hforged, hdigest⟩ :=
    winning_encoding_event_has_signed_collision cache outcome hevent
  have hreturnedTrace :
      SigningTranscript.Returned trace.toSigningLog request signature := by
    rw [hlog]
    exact hreturned
  obtain ⟨entry, hentry, hrequest, hsignature⟩ :=
    (SigningTranscript.returned_toSigningLog_iff trace request signature).mp
      hreturnedTrace
  subst request
  obtain ⟨localSignedOutput, hlocalSigned⟩ :=
    hcached entry hentry signature hsignature
  have hlocalFinal := (hcaches entry hentry).2 hlocalSigned
  have houtput : localSignedOutput = signedOutput :=
    Option.some.inj (hlocalFinal.symm.trans hsigned)
  subst localSignedOutput
  let forgedInput := Concrete.CacheView.encodingInput outcome.secretKey.parameter
    outcome.forgery.epoch
      (outcome.forgery.message, outcome.forgery.signature.randomness)
  have hforgedFinal : cache forgedInput = some forgedOutput := by
    dsimp [forgedInput]
    rw [← hepoch]
    exact hforged
  have hdistinct :
      Concrete.CacheView.encodingInput outcome.secretKey.parameter entry.request.epoch
          (entry.request.message, signature.randomness) ≠ forgedInput := by
    dsimp [forgedInput]
    rw [← hepoch]
    exact hne
  cases hinitial : entry.initialCache forgedInput with
  | none =>
      refine ⟨entry, hentry, Or.inr ?_⟩
      refine ⟨signature, signedOutput, forgedOutput, hsignature, hepoch,
        hinitial, hlocalSigned, hforgedFinal, hdistinct, hdigest⟩
  | some oldOutput =>
      have holdFinal := (hcaches entry hentry).1 hinitial
      have holdOutput : oldOutput = forgedOutput :=
        Option.some.inj (holdFinal.symm.trans hforgedFinal)
      subst oldOutput
      refine ⟨entry, hentry, Or.inl ?_⟩
      refine ⟨signature, signedOutput,
        (outcome.forgery.message, outcome.forgery.signature.randomness),
        forgedOutput, hsignature, hlocalSigned, ?_, ?_, hdigest⟩
      · rw [hepoch]
        exact hinitial
      · intro heq
        apply hdistinct
        dsimp [forgedInput]
        rw [← hepoch]
        exact congrArg
          (Concrete.CacheView.encodingInput outcome.secretKey.parameter
            entry.request.epoch) heq.symm

/-- The two budget classes are a 192-bit pre-hit on signing randomness and a 128-bit digest collision, with the latter covering both temporal orientations around signing. -/
theorem winning_encoding_event_trace_monitor_decomposition
    (cache : QueryCache HashSpec) (outcome : GameOutcome)
    (trace : SigningCacheTrace)
    (hlog : trace.toSigningLog = outcome.signingLog)
    (hcaches : trace.CachesLe cache)
    (hcached : trace.SuccessfulEncodingsCached outcome.secretKey)
    (hevent : WinningOutcomeBadEventOccurs cache outcome .encoding) :
    ∃ entry ∈ trace,
      entry.EncodingInputPrehit outcome.secretKey ∨
        entry.FreshSigningEncodingCollision outcome.secretKey ∨
          entry.FreshForgedEncodingCollision outcome.secretKey outcome.forgery cache := by
  obtain ⟨entry, hentry, hpreexisting | hfresh⟩ :=
    winning_encoding_event_trace_temporal_decomposition cache outcome trace
      hlog hcaches hcached hevent
  · rcases entry.preexistingEncodingCollision_cases outcome.secretKey hpreexisting with
      hprehit | hcollision
    · exact ⟨entry, hentry, Or.inl hprehit⟩
    · exact ⟨entry, hentry, Or.inr (Or.inl hcollision)⟩
  · exact ⟨entry, hentry, Or.inr (Or.inr hfresh)⟩

/-- In an actual supported execution, the post-signing orientation is genuinely fresh after the signer finishes. Thus the two digest-collision cases have exactly the temporal semantics of `EncodingMonitor.sign` and a later `EncodingMonitor.query`. -/
theorem winning_encoding_event_trace_postSigning_decomposition
    (adversary : Adversary Concrete.singleAttemptScheme)
    (execution : GameOutcome × (QueryCache HashSpec × SigningCacheTrace))
    (hmem : execution ∈ support (detailedGameWithSigningTrace adversary))
    (hevent : WinningOutcomeBadEventOccurs execution.2.1 execution.1 .encoding) :
    ∃ entry ∈ execution.2.2,
      entry.EncodingInputPrehit execution.1.secretKey ∨
        entry.FreshSigningEncodingCollision execution.1.secretKey ∨
          entry.PostSigningFreshForgedEncodingCollision execution.1.secretKey
            execution.1.forgery execution.2.1 := by
  obtain ⟨hlog, hcaches, hcached⟩ :=
    detailedGameWithSigningTrace_invariants adversary execution hmem
  obtain ⟨entry, hentry, hprehit | hsigning | hforged⟩ :=
    winning_encoding_event_trace_monitor_decomposition execution.2.1 execution.1
      execution.2.2 hlog hcaches hcached hevent
  · exact ⟨entry, hentry, Or.inl hprehit⟩
  · exact ⟨entry, hentry, Or.inr (Or.inl hsigning)⟩
  · have hpreserves :=
      detailedGameWithSigningTrace_preservesOtherEncodingInputs adversary execution hmem
    have hsuccessful : ∃ signature, entry.signature = some signature := by
      obtain ⟨signature, _signedOutput, _forgedOutput, hsignature, _⟩ := hforged
      exact ⟨signature, hsignature⟩
    obtain ⟨signature, hsignature⟩ := hsuccessful
    cases hsignedFresh : entry.initialCache
        (Concrete.CacheView.encodingInput execution.1.secretKey.parameter
          entry.request.epoch (entry.request.message, signature.randomness)) with
    | none =>
        exact ⟨entry, hentry, Or.inr (Or.inr
          (entry.postSigningFreshForgedEncodingCollision_of_fresh
            execution.1.secretKey execution.1.forgery execution.2.1
            (hpreserves entry hentry) hforged signature hsignature hsignedFresh))⟩
    | some output =>
        exact ⟨entry, hentry, Or.inl ⟨signature, output, hsignature, hsignedFresh⟩⟩

theorem winning_encoding_event_probability_eq_signingTrace
    (adversary : Adversary Concrete.singleAttemptScheme) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      WinningOutcomeBadEventOccurs execution.2 execution.1 .encoding |
      detailedGameWithCache Concrete.singleAttemptScheme adversary] =
    Pr[fun execution : GameOutcome × (QueryCache HashSpec × SigningCacheTrace) =>
      WinningOutcomeBadEventOccurs execution.2.1 execution.1 .encoding |
      detailedGameWithSigningTrace adversary] := by
  rw [← detailedGameWithSigningTrace_cache_projection, probEvent_map]
  rfl

theorem winning_encoding_event_probability_eq_encodingTrace
    (adversary : Adversary Concrete.singleAttemptScheme) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      WinningOutcomeBadEventOccurs execution.2 execution.1 .encoding |
      detailedGameWithCache Concrete.singleAttemptScheme adversary] =
    Pr[fun execution : GameOutcome ×
        ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) =>
      WinningOutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding |
      detailedGameWithEncodingTrace adversary] := by
  rw [winning_encoding_event_probability_eq_signingTrace,
    ← detailedGameWithEncodingTrace_projection, probEvent_map]
  rfl

/-- The concrete encoding event is reduced to a 192-bit signing-input prehit or a hit in the adaptive epoch-collision monitor. -/
theorem winning_encoding_event_probability_le_prehit_add_monitorHit
    (adversary : Adversary Concrete.singleAttemptScheme) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      WinningOutcomeBadEventOccurs execution.2 execution.1 .encoding |
      detailedGameWithCache Concrete.singleAttemptScheme adversary] ≤
    Pr[fun execution : GameOutcome ×
        ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) =>
      WinningOutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding ∧
        ∃ entry ∈ execution.2.1.2,
          entry.EncodingInputPrehit execution.1.secretKey |
      detailedGameWithEncodingTrace adversary] +
    Pr[fun execution : GameOutcome ×
        ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) =>
      WinningOutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding ∧
        EncodingMonitor.runObserved EncodingMonitor.State.empty execution.2.2 = true |
      detailedGameWithEncodingTrace adversary] := by
  rw [winning_encoding_event_probability_eq_encodingTrace]
  let win := fun execution : GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) =>
    WinningOutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding
  let prehit := fun execution : GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) =>
    ∃ entry ∈ execution.2.1.2,
      entry.EncodingInputPrehit execution.1.secretKey
  let monitorHit := fun execution : GameOutcome ×
      ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) =>
    EncodingMonitor.runObserved EncodingMonitor.State.empty execution.2.2 = true
  calc
    Pr[win | detailedGameWithEncodingTrace adversary] ≤
        Pr[fun execution =>
          (win execution ∧ prehit execution) ∨
            (win execution ∧ monitorHit execution) |
          detailedGameWithEncodingTrace adversary] := by
      apply probEvent_mono
      intro execution hmem hwin
      have hprojected : (execution.1, execution.2.1) ∈
          support (detailedGameWithSigningTrace adversary) := by
        rw [← detailedGameWithEncodingTrace_projection, support_map]
        exact ⟨execution, hmem, rfl⟩
      obtain ⟨entry, hentry, hprehit | hsigning | hpostSigning⟩ :=
        winning_encoding_event_trace_postSigning_decomposition adversary
          (execution.1, execution.2.1) hprojected hwin
      · exact Or.inl ⟨hwin, entry, hentry, hprehit⟩
      · exact Or.inr ⟨hwin,
          detailedGameWithEncodingTrace_freshSigningCollision_monitorHit adversary
            execution hmem hwin ⟨entry, hentry, hsigning⟩⟩
      · exact Or.inr ⟨hwin,
          detailedGameWithEncodingTrace_postSigningFreshForgedCollision_monitorHit
            adversary execution hmem hwin ⟨entry, hentry, hpostSigning⟩⟩
    _ ≤ Pr[fun execution => win execution ∧ prehit execution |
          detailedGameWithEncodingTrace adversary] +
        Pr[fun execution => win execution ∧ monitorHit execution |
          detailedGameWithEncodingTrace adversary] :=
      probEvent_or_le _ _ _

end XmssSecurity
