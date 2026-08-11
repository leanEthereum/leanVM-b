import XmssSecurity.FreshLeafOrientation
import XmssSecurity.SigningLogReplay

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

theorem signed_recoveredEndpoints_eq_oneTimePublicKey
    (cache : QueryCache HashSpec) (secretKey : SecretKey) (epoch : Epoch)
    (signature : Signature) (encoding : Encoding)
    (hsignature : signature = Concrete.CacheReplay.signWithEncoding cache secretKey
      epoch signature.randomness encoding) :
    recoveredEndpoints
        (fun chain => Concrete.CacheView.chainStep cache secretKey.parameter epoch chain)
        encoding signature.chainValue =
      Concrete.CacheReplay.oneTimePublicKey cache secretKey.parameter
        secretKey.chainStart epoch := by
  rw [hsignature]
  funext chain
  change Wots.recoverChain
      (Concrete.CacheView.chainStep cache secretKey.parameter epoch chain)
      (encoding chain)
      (Wots.signChain (Concrete.CacheView.chainStep cache secretKey.parameter epoch chain)
        (encoding chain) (secretKey.chainStart epoch chain)) =
    Wots.publicChain (Concrete.CacheView.chainStep cache secretKey.parameter epoch chain)
      (secretKey.chainStart epoch chain)
  exact Wots.recover_signChain_eq_publicChain _ _ _

theorem same_leaf_badEvent_is_collision
    (cache : QueryCache HashSpec) (secretKey : SecretKey) (request : SignRequest)
    (signature forgedSignature : Signature) (forgedMessage : Message)
    (signedEncoding forgedEncoding : Encoding)
    (hsignedValid : TargetSum.Valid signedEncoding)
    (hsignature : signature = Concrete.CacheReplay.signWithEncoding cache secretKey
      request.epoch signature.randomness signedEncoding)
    (hevent : Concrete.SameEpochBadEventOccurs cache secretKey.parameter request.epoch
      request.message forgedMessage signedEncoding forgedEncoding signature forgedSignature
      hsignedValid .leaf) :
    Wots.HasLeafCollision
      (Concrete.CacheView.leafHash cache secretKey.parameter request.epoch)
      (recoveredEndpoints
        (fun chain => Concrete.CacheView.chainStep cache secretKey.parameter
          request.epoch chain)
        forgedEncoding forgedSignature.chainValue)
      (Concrete.CacheReplay.oneTimePublicKey cache secretKey.parameter
        secretKey.chainStart request.epoch) := by
  change Wots.HasLeafCollision
    (Concrete.CacheView.leafHash cache secretKey.parameter request.epoch)
    (recoveredEndpoints
      (fun chain => Concrete.CacheView.chainStep cache secretKey.parameter request.epoch chain)
      forgedEncoding forgedSignature.chainValue)
    (recoveredEndpoints
      (fun chain => Concrete.CacheView.chainStep cache secretKey.parameter request.epoch chain)
      signedEncoding signature.chainValue) at hevent
  rw [signed_recoveredEndpoints_eq_oneTimePublicKey cache secretKey request.epoch
    signature signedEncoding hsignature] at hevent
  exact hevent

theorem detailed_execution_returned_signature_eq
    (adversary : Adversary Concrete.scheme)
    (execution : GameOutcome × QueryCache HashSpec)
    (hgame : execution ∈ support (detailedGameWithCache Concrete.scheme adversary))
    (request : SignRequest) (signature : Signature) (encoding : Encoding)
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        request.epoch (request.message, signature.randomness)) = some encoding)
    (hreturned : SigningTranscript.Returned execution.1.signingLog request signature) :
    signature = Concrete.CacheReplay.signWithEncoding execution.2 execution.1.secretKey
      request.epoch signature.randomness encoding := by
  obtain ⟨actualEncoding, hactualDecode, hsignature⟩ :=
    (detailed_execution_consistent adversary execution hgame).signing request signature hreturned
  have hencoding : actualEncoding = encoding := by
    rw [hdecode] at hactualDecode
    exact Option.some.inj hactualDecode.symm
  subst actualEncoding
  exact hsignature

theorem afterKeygen_execution_mem_detailedGame
    (adversary : Adversary Concrete.scheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2)) :
    execution ∈ support (detailedGameWithCache Concrete.scheme adversary) := by
  unfold detailedGameWithCache detailedGameCore
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
  exact ⟨keyResult, hkeygen, hafter⟩

theorem sameLeafCollision_afterKeygen_orientation_eq_epoch
    (adversary : Adversary Concrete.scheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (secretKey : SecretKey) (hsecret : secretKey = keyResult.1.2)
    (epoch : Epoch) (hepoch : epoch = execution.1.forgery.epoch)
    (forgedEncoding : Encoding) (forgedOutput : HashOutput)
    (hforgedCached : execution.2
      (Concrete.CacheView.leafInput secretKey.parameter execution.1.forgery.epoch
        (recoveredEndpoints
          (fun chain => Concrete.CacheView.chainStep execution.2 secretKey.parameter
            execution.1.forgery.epoch chain)
          forgedEncoding execution.1.forgery.signature.chainValue)) = some forgedOutput)
    (hleafCollision : Wots.HasLeafCollision
      (Concrete.CacheView.leafHash execution.2 secretKey.parameter epoch)
      (recoveredEndpoints
        (fun chain => Concrete.CacheView.chainStep execution.2 secretKey.parameter epoch chain)
        forgedEncoding execution.1.forgery.signature.chainValue)
      (Concrete.CacheReplay.oneTimePublicKey execution.2 secretKey.parameter
        secretKey.chainStart epoch)) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (keygenLeafTargetInput keyResult.1.2 keyResult.2) := by
  subst epoch
  apply leafCollision_afterKeygen_orientation adversary keyResult hkeygen execution hafter
    secretKey hsecret execution.1.forgery.epoch
    (recoveredEndpoints
      (fun chain => Concrete.CacheView.chainStep execution.2 secretKey.parameter
        execution.1.forgery.epoch chain)
      forgedEncoding execution.1.forgery.signature.chainValue)
    forgedOutput hforgedCached hleafCollision

theorem same_leaf_witness_afterKeygen_orientation
    (adversary : Adversary Concrete.scheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (hverified : execution.1.verified = true)
    (request : SignRequest) (signature : Signature)
    (signedEncoding forgedEncoding : Encoding)
    (hsignedDecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        request.epoch (request.message, signature.randomness)) = some signedEncoding)
    (hforgedDecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        request.epoch
        (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
        some forgedEncoding)
    (hreturned : SigningTranscript.Returned execution.1.signingLog request signature)
    (hepoch : request.epoch = execution.1.forgery.epoch)
    (hleafEvent : Concrete.SameEpochBadEventOccurs execution.2
      execution.1.secretKey.parameter request.epoch request.message
      execution.1.forgery.message signedEncoding forgedEncoding signature
      execution.1.forgery.signature
      (TargetSum.decodeDigest_eq_some_iff.mp hsignedDecode).2 .leaf) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (keygenLeafTargetInput keyResult.1.2 keyResult.2) := by
  have hkeys := detailedGameAfterKeygen_keys_eq adversary keyResult.1.1 keyResult.1.2
    keyResult.2 execution hafter
  have hgame := afterKeygen_execution_mem_detailedGame adversary keyResult hkeygen
    execution hafter
  have hsignature := detailed_execution_returned_signature_eq adversary execution hgame
    request signature signedEncoding hsignedDecode hreturned
  have hdecodeEpoch := congrArg (fun epoch => TargetSum.decodeDigest
    (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter epoch
      (execution.1.forgery.message, execution.1.forgery.signature.randomness))) hepoch
  have hforgedDecode' : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        execution.1.forgery.epoch
        (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
        some forgedEncoding := hdecodeEpoch.symm.trans hforgedDecode
  obtain ⟨forgedOutput, hforgedCached⟩ :=
    detailed_execution_verified_leaf_cached_as adversary execution hgame forgedEncoding
      hverified hforgedDecode'
  have hleafCollision := same_leaf_badEvent_is_collision execution.2
    execution.1.secretKey request signature execution.1.forgery.signature
    execution.1.forgery.message signedEncoding forgedEncoding
    (TargetSum.decodeDigest_eq_some_iff.mp hsignedDecode).2 hsignature hleafEvent
  exact sameLeafCollision_afterKeygen_orientation_eq_epoch adversary keyResult hkeygen
    execution hafter execution.1.secretKey hkeys.2 request.epoch hepoch forgedEncoding
    forgedOutput hforgedCached hleafCollision

theorem leaf_event_afterKeygen_orientation
    (adversary : Adversary Concrete.scheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (hevent : OutcomeBadEventOccurs execution.2 execution.1 .leaf) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (keygenLeafTargetInput keyResult.1.2 keyResult.2) := by
  rcases hevent.2 with hsame | hfresh
  · obtain ⟨request, signature, signedEncoding, forgedEncoding, hsignedDecode,
      hforgedDecode, hreturned, hepoch, hleafEvent⟩ := hsame
    exact same_leaf_witness_afterKeygen_orientation adversary keyResult hkeygen execution
      hafter hevent.1 request signature signedEncoding forgedEncoding hsignedDecode
      hforgedDecode hreturned hepoch hleafEvent
  · exact fresh_leaf_event_afterKeygen_orientation adversary keyResult hkeygen execution
      hafter hevent hfresh

theorem leaf_outcomeBadEvent_probability_le
    (q : Nat) (adversary : Adversary Concrete.scheme)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      OutcomeBadEventOccurs execution.2 execution.1 .leaf |
      detailedGameWithCache Concrete.scheme adversary] ≤
      (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
  apply outcomeBadEvent_probability_le_of_afterKeygen_freshCollision q adversary hbound .leaf
    (fun key cache => keygenLeafTargetInput key.2 cache)
  intro keyResult hkeygen execution hafter hevent
  exact leaf_event_afterKeygen_orientation adversary keyResult hkeygen execution hafter hevent

end XmssSecurity
