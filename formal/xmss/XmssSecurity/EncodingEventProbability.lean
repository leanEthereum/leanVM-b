import XmssSecurity.ChainOriginProbability
import XmssSecurity.EncodingActionTrace
import XmssSecurity.EncodingPrehitProbability
import XmssSecurity.EncodingTargetMap
import XmssSecurity.SignCacheHitProbability
import XmssSecurity.SigningCacheTrace
import XmssSecurity.WinningEventReduction

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

theorem TargetSum.decodeDigest_zero_eq_none :
    TargetSum.decodeDigest (0 : Digest) = none := by
  cases hdecode : TargetSum.decodeDigest (0 : Digest) with
  | none => rfl
  | some encoding =>
      exfalso
      have hview := TargetSum.decodeDigest_eq_some_iff.mp hdecode
      have hencoding : TargetSum.digestEncoding (0 : Digest) = encoding :=
        congrArg Prod.fst hview.1
      rw [← hencoding] at hview
      have hsum : TargetSum.sum (TargetSum.digestEncoding (0 : Digest)) = 0 := by
        unfold TargetSum.sum
        apply Finset.sum_eq_zero
        intro chain _
        simp [TargetSum.digestEncoding]
      unfold TargetSum.Valid at hview
      rw [hsum] at hview
      norm_num [targetSum] at hview

theorem Concrete.CacheView.encodingInput_cached_of_decode_some
    (cache : QueryCache HashSpec) (parameter : PublicParameter) (epoch : Epoch)
    (message : Message) (randomness : Randomness) (encoding : Encoding)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash cache parameter epoch (message, randomness)) =
        some encoding) :
    ∃ output, cache
      (Concrete.CacheView.encodingInput parameter epoch (message, randomness)) = some output := by
  cases hcache : cache
      (Concrete.CacheView.encodingInput parameter epoch (message, randomness)) with
  | some output => exact ⟨output, rfl⟩
  | none =>
      rw [Concrete.CacheView.encodingHash, Concrete.CacheView.digestAt, hcache,
        TargetSum.decodeDigest_zero_eq_none] at hdecode
      contradiction

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
    (adversary : Adversary Concrete.scheme)
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
    (adversary : Adversary Concrete.scheme) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      WinningOutcomeBadEventOccurs execution.2 execution.1 .encoding |
      detailedGameWithCache Concrete.scheme adversary] =
    Pr[fun execution : GameOutcome × (QueryCache HashSpec × SigningCacheTrace) =>
      WinningOutcomeBadEventOccurs execution.2.1 execution.1 .encoding |
      detailedGameWithSigningTrace adversary] := by
  rw [← detailedGameWithSigningTrace_cache_projection, probEvent_map]
  rfl

theorem winning_encoding_event_probability_eq_encodingTrace
    (adversary : Adversary Concrete.scheme) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      WinningOutcomeBadEventOccurs execution.2 execution.1 .encoding |
      detailedGameWithCache Concrete.scheme adversary] =
    Pr[fun execution : GameOutcome ×
        ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) =>
      WinningOutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding |
      detailedGameWithEncodingTrace adversary] := by
  rw [winning_encoding_event_probability_eq_signingTrace,
    ← detailedGameWithEncodingTrace_projection, probEvent_map]
  rfl

/-- The concrete encoding event is reduced to a 192-bit signing-input prehit or a hit in the adaptive epoch-collision monitor. -/
theorem winning_encoding_event_probability_le_prehit_add_monitorHit
    (adversary : Adversary Concrete.scheme) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      WinningOutcomeBadEventOccurs execution.2 execution.1 .encoding |
      detailedGameWithCache Concrete.scheme adversary] ≤
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

theorem winning_encoding_monitorHit_probability_le_sampled_external
    (adversary : Adversary Concrete.scheme) :
    Pr[fun execution : GameOutcome ×
        ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) =>
      WinningOutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding ∧
        EncodingMonitor.runObserved EncodingMonitor.State.empty execution.2.2 = true |
      detailedGameWithEncodingTrace adversary] ≤
    Pr[fun execution : (GameOutcome ×
        ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) ×
          EncodingActionTrace =>
      EncodingMonitor.runObserved EncodingMonitor.State.empty execution.2 = true |
      sampledDetailedGameWithEncodingTrace adversary] := by
  calc
    _ = Pr[fun execution : GameOutcome ×
          ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) =>
        WinningOutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding ∧
          EncodingMonitor.runObserved EncodingMonitor.State.empty execution.2.2 = true |
        splitDetailedGameWithEncodingTrace adversary] := by
      rw [probEvent_def, probEvent_def,
        splitDetailedGameWithEncodingTrace_evalDist_simulation]
    _ = Pr[fun execution : (GameOutcome ×
          ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) ×
            EncodingActionTrace =>
        WinningOutcomeBadEventOccurs execution.1.2.1.1 execution.1.1 .encoding ∧
          EncodingMonitor.runObserved EncodingMonitor.State.empty
            execution.1.2.2 = true |
        sampledDetailedGameWithEncodingTrace adversary] := by
      rw [← sampledDetailedGameWithEncodingTrace_projection, probEvent_map]
      rfl
    _ ≤ _ := by
      apply probEvent_mono
      intro execution hmem hevent
      exact sampledDetailedGameWithEncodingTrace_external_monitorHit_of_winning
        adversary execution hmem hevent.1 hevent.2

theorem sampledDetailedGame_external_collision_probability_le_of_bound
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : ∀ keyResult ∈
      support ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅),
      (splitDetailedGameAfterKeygenWithEncodingTrace adversary keyResult.1.1
        keyResult.1.2 keyResult.2).IsQueryBoundP (· matches .inr _) q) :
    Pr[fun execution : (GameOutcome ×
        ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) ×
          EncodingActionTrace =>
      EncodingMonitor.runObserved EncodingMonitor.State.empty execution.2 = true |
      sampledDetailedGameWithEncodingTrace adversary] ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  unfold sampledDetailedGameWithEncodingTrace
  refine probEvent_bind_le_of_forall_le fun keyResult hkeyResult => ?_
  exact encodingSamplingTrace_collision_probability_le
    (splitDetailedGameAfterKeygenWithEncodingTrace adversary keyResult.1.1
      keyResult.1.2 keyResult.2) q (hbound keyResult hkeyResult)

theorem sampledDetailedGame_external_collision_probability_le
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    Pr[fun execution : (GameOutcome ×
        ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)) ×
          EncodingActionTrace =>
      EncodingMonitor.runObserved EncodingMonitor.State.empty execution.2 = true |
      sampledDetailedGameWithEncodingTrace adversary] ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  exact sampledDetailedGame_external_collision_probability_le_of_bound q adversary
    (fun keyResult hkeyResult =>
      splitDetailedGameAfterKeygenWithEncodingTrace_encodingSample_bound
        q adversary hbound keyResult hkeyResult)

theorem winning_encoding_monitorHit_probability_le
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    Pr[fun execution : GameOutcome ×
        ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) =>
      WinningOutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding ∧
        EncodingMonitor.runObserved EncodingMonitor.State.empty execution.2.2 = true |
      detailedGameWithEncodingTrace adversary] ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) :=
  (winning_encoding_monitorHit_probability_le_sampled_external adversary).trans
    (sampledDetailedGame_external_collision_probability_le q adversary hbound)

theorem winning_encoding_prehit_probability_le
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    Pr[fun execution : GameOutcome ×
        ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace) =>
      WinningOutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding ∧
        ∃ entry ∈ execution.2.1.2,
          entry.EncodingInputPrehit execution.1.secretKey |
      detailedGameWithEncodingTrace adversary] ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  calc
    _ = Pr[fun execution : GameOutcome ×
          (QueryCache HashSpec × SigningCacheTrace) =>
        WinningOutcomeBadEventOccurs execution.2.1 execution.1 .encoding ∧
          execution.2.2.HasEncodingInputPrehit execution.1.secretKey |
        detailedGameWithSigningTrace adversary] := by
      rw [← detailedGameWithEncodingTrace_projection, probEvent_map]
      rfl
    _ ≤ _ := detailedGameWithSigningTrace_winning_prehit_probability_le
      q adversary hbound

theorem winning_encoding_event_probability_le_two_terms
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      WinningOutcomeBadEventOccurs execution.2 execution.1 .encoding |
      detailedGameWithCache Concrete.scheme adversary] ≤
      2 * ((q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) := by
  calc
    _ ≤
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
          detailedGameWithEncodingTrace adversary] :=
      winning_encoding_event_probability_le_prehit_add_monitorHit adversary
    _ ≤ (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) :=
      add_le_add (winning_encoding_prehit_probability_le q adversary hbound)
        (winning_encoding_monitorHit_probability_le q adversary hbound)
    _ = 2 * ((q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) := by
      rw [two_mul]

/-- The concrete winning encoding event reduces inside the actual game distribution to the two signing-boundary orientations used by the probability argument. -/
theorem winning_encoding_event_probability_le_signingTrace_orientations
    (adversary : Adversary Concrete.scheme) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      WinningOutcomeBadEventOccurs execution.2 execution.1 .encoding |
      detailedGameWithCache Concrete.scheme adversary] ≤
    Pr[fun execution : GameOutcome × (QueryCache HashSpec × SigningCacheTrace) =>
      WinningOutcomeBadEventOccurs execution.2.1 execution.1 .encoding ∧
        ∃ entry ∈ execution.2.2,
          entry.PreexistingEncodingCollision execution.1.secretKey ∨
            entry.FreshForgedEncodingCollision execution.1.secretKey
              execution.1.forgery execution.2.1 |
      detailedGameWithSigningTrace adversary] := by
  rw [winning_encoding_event_probability_eq_signingTrace]
  apply probEvent_mono
  intro execution hmem hevent
  obtain ⟨hlog, hcaches, hcached⟩ :=
    detailedGameWithSigningTrace_invariants adversary execution hmem
  exact ⟨hevent, winning_encoding_event_trace_temporal_decomposition execution.2.1
    execution.1 execution.2.2 hlog hcaches hcached hevent⟩

theorem winning_encoding_event_probability_le_preexisting_add_fresh
    (adversary : Adversary Concrete.scheme) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      WinningOutcomeBadEventOccurs execution.2 execution.1 .encoding |
      detailedGameWithCache Concrete.scheme adversary] ≤
    Pr[fun execution : GameOutcome × (QueryCache HashSpec × SigningCacheTrace) =>
      WinningOutcomeBadEventOccurs execution.2.1 execution.1 .encoding ∧
        ∃ entry ∈ execution.2.2,
          entry.PreexistingEncodingCollision execution.1.secretKey |
      detailedGameWithSigningTrace adversary] +
    Pr[fun execution : GameOutcome × (QueryCache HashSpec × SigningCacheTrace) =>
      WinningOutcomeBadEventOccurs execution.2.1 execution.1 .encoding ∧
        ∃ entry ∈ execution.2.2,
          entry.FreshForgedEncodingCollision execution.1.secretKey
            execution.1.forgery execution.2.1 |
      detailedGameWithSigningTrace adversary] := by
  refine winning_encoding_event_probability_le_signingTrace_orientations
    adversary |>.trans ?_
  let win := fun execution : GameOutcome ×
      (QueryCache HashSpec × SigningCacheTrace) =>
    WinningOutcomeBadEventOccurs execution.2.1 execution.1 .encoding
  let preexisting := fun execution : GameOutcome ×
      (QueryCache HashSpec × SigningCacheTrace) =>
    ∃ entry ∈ execution.2.2,
      entry.PreexistingEncodingCollision execution.1.secretKey
  let fresh := fun execution : GameOutcome ×
      (QueryCache HashSpec × SigningCacheTrace) =>
    ∃ entry ∈ execution.2.2,
      entry.FreshForgedEncodingCollision execution.1.secretKey
        execution.1.forgery execution.2.1
  calc
    Pr[fun execution => win execution ∧
          ∃ entry ∈ execution.2.2,
            entry.PreexistingEncodingCollision execution.1.secretKey ∨
              entry.FreshForgedEncodingCollision execution.1.secretKey
                execution.1.forgery execution.2.1 |
        detailedGameWithSigningTrace adversary] ≤
      Pr[fun execution =>
          (win execution ∧ preexisting execution) ∨
            (win execution ∧ fresh execution) |
        detailedGameWithSigningTrace adversary] := by
      apply probEvent_mono''
      intro execution hevent
      obtain ⟨hwin, entry, hentry, horientation⟩ := hevent
      rcases horientation with hpreexisting | hfresh
      · exact Or.inl ⟨hwin, entry, hentry, hpreexisting⟩
      · exact Or.inr ⟨hwin, entry, hentry, hfresh⟩
    _ ≤ Pr[fun execution => win execution ∧ preexisting execution |
          detailedGameWithSigningTrace adversary] +
        Pr[fun execution => win execution ∧ fresh execution |
          detailedGameWithSigningTrace adversary] :=
      probEvent_or_le _ _ _

theorem winning_encoding_event_probability_le_prehit_add_digestCollisions
    (adversary : Adversary Concrete.scheme) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      WinningOutcomeBadEventOccurs execution.2 execution.1 .encoding |
      detailedGameWithCache Concrete.scheme adversary] ≤
    Pr[fun execution : GameOutcome × (QueryCache HashSpec × SigningCacheTrace) =>
      WinningOutcomeBadEventOccurs execution.2.1 execution.1 .encoding ∧
        ∃ entry ∈ execution.2.2,
          entry.EncodingInputPrehit execution.1.secretKey |
      detailedGameWithSigningTrace adversary] +
    Pr[fun execution : GameOutcome × (QueryCache HashSpec × SigningCacheTrace) =>
      WinningOutcomeBadEventOccurs execution.2.1 execution.1 .encoding ∧
        ∃ entry ∈ execution.2.2,
          entry.FreshSigningEncodingCollision execution.1.secretKey ∨
            entry.FreshForgedEncodingCollision execution.1.secretKey
              execution.1.forgery execution.2.1 |
      detailedGameWithSigningTrace adversary] := by
  rw [winning_encoding_event_probability_eq_signingTrace]
  let prehit := fun execution : GameOutcome ×
      (QueryCache HashSpec × SigningCacheTrace) =>
    ∃ entry ∈ execution.2.2,
      entry.EncodingInputPrehit execution.1.secretKey
  let digestCollision := fun execution : GameOutcome ×
      (QueryCache HashSpec × SigningCacheTrace) =>
    ∃ entry ∈ execution.2.2,
      entry.FreshSigningEncodingCollision execution.1.secretKey ∨
        entry.FreshForgedEncodingCollision execution.1.secretKey
          execution.1.forgery execution.2.1
  calc
    Pr[fun execution : GameOutcome × (QueryCache HashSpec × SigningCacheTrace) =>
          WinningOutcomeBadEventOccurs execution.2.1 execution.1 .encoding |
        detailedGameWithSigningTrace adversary] ≤
      Pr[fun execution =>
          (WinningOutcomeBadEventOccurs execution.2.1 execution.1 .encoding ∧
            prehit execution) ∨
          (WinningOutcomeBadEventOccurs execution.2.1 execution.1 .encoding ∧
            digestCollision execution) |
        detailedGameWithSigningTrace adversary] := by
      apply probEvent_mono
      intro execution hmem hevent
      obtain ⟨hlog, hcaches, hcached⟩ :=
        detailedGameWithSigningTrace_invariants adversary execution hmem
      obtain ⟨entry, hentry, hprehit | hdigest⟩ :=
        winning_encoding_event_trace_monitor_decomposition execution.2.1
          execution.1 execution.2.2 hlog hcaches hcached hevent
      · exact Or.inl ⟨hevent, entry, hentry, hprehit⟩
      · exact Or.inr ⟨hevent, entry, hentry, hdigest⟩
    _ ≤ Pr[fun execution =>
          WinningOutcomeBadEventOccurs execution.2.1 execution.1 .encoding ∧
            prehit execution |
          detailedGameWithSigningTrace adversary] +
        Pr[fun execution =>
          WinningOutcomeBadEventOccurs execution.2.1 execution.1 .encoding ∧
            digestCollision execution |
          detailedGameWithSigningTrace adversary] :=
      probEvent_or_le _ _ _

theorem winning_encoding_event_trace_preexistingRisk_le
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (execution : GameOutcome × (QueryCache HashSpec × SigningCacheTrace))
    (hmem : execution ∈ support (detailedGameWithSigningTrace adversary))
    (hevent : WinningOutcomeBadEventOccurs execution.2.1 execution.1 .encoding) :
    execution.2.2.preexistingEncodingRisk execution.1.secretKey.parameter ≤
      2 * ((q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) := by
  obtain ⟨hlog, hcaches, _hcached⟩ :=
    detailedGameWithSigningTrace_invariants adversary execution hmem
  have hvalid : SigningTranscript.Valid execution.2.2.toSigningLog := by
    rw [hlog]
    exact hevent.signingTranscript_valid
  exact SigningCacheTrace.preexistingEncodingRisk_le execution.2.2
    execution.1.secretKey.parameter execution.2.1 q hvalid hcaches
    (detailedGameWithSigningTrace_cache_finite_of_mem_support
      adversary q hbound execution hmem)
    (detailedGameWithSigningTrace_cache_enncard_le_of_mem_support
      adversary q hbound execution hmem)

theorem winning_encoding_event_trace_encodingInputPrehitRisk_le
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (execution : GameOutcome × (QueryCache HashSpec × SigningCacheTrace))
    (hmem : execution ∈ support (detailedGameWithSigningTrace adversary))
    (hevent : WinningOutcomeBadEventOccurs execution.2.1 execution.1 .encoding) :
    execution.2.2.encodingInputPrehitRisk ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  obtain ⟨hlog, hcaches, _hcached⟩ :=
    detailedGameWithSigningTrace_invariants adversary execution hmem
  have hvalid : SigningTranscript.Valid execution.2.2.toSigningLog := by
    rw [hlog]
    exact hevent.signingTranscript_valid
  exact SigningCacheTrace.encodingInputPrehitRisk_le execution.2.2
    execution.2.1 q hvalid hcaches
    (detailedGameWithSigningTrace_cache_enncard_le_of_mem_support
      adversary q hbound execution hmem)

theorem winning_encoding_event_trace_freshSigningEncodingCollisionRisk_le
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (execution : GameOutcome × (QueryCache HashSpec × SigningCacheTrace))
    (hmem : execution ∈ support (detailedGameWithSigningTrace adversary))
    (hevent : WinningOutcomeBadEventOccurs execution.2.1 execution.1 .encoding) :
    execution.2.2.freshSigningEncodingCollisionRisk
        execution.1.secretKey.parameter ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  obtain ⟨hlog, hcaches, _hcached⟩ :=
    detailedGameWithSigningTrace_invariants adversary execution hmem
  have hvalid : SigningTranscript.Valid execution.2.2.toSigningLog := by
    rw [hlog]
    exact hevent.signingTranscript_valid
  exact SigningCacheTrace.freshSigningEncodingCollisionRisk_le execution.2.2
    execution.1.secretKey.parameter execution.2.1 q hvalid hcaches
    (detailedGameWithSigningTrace_cache_finite_of_mem_support
      adversary q hbound execution hmem)
    (detailedGameWithSigningTrace_cache_enncard_le_of_mem_support
      adversary q hbound execution hmem)

end XmssSecurity
