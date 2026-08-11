import XmssSecurity.ChainOriginProbability
import XmssSecurity.EncodingTargetMap
import XmssSecurity.SignCacheHitProbability
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

end XmssSecurity
