import XmssSecurity.Proof.MerkleWitnessOrientation

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

theorem same_merkle_witness_afterKeygen_orientation
    (adversary : Adversary Concrete.singleAttemptScheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.singleAttemptScheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.singleAttemptScheme adversary keyResult.1.1 keyResult.1.2)).run
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
    (level : MerkleLevel)
    (hevent : Concrete.SameEpochBadEventOccurs execution.2
      execution.1.secretKey.parameter request.epoch request.message
      execution.1.forgery.message signedEncoding forgedEncoding signature
      execution.1.forgery.signature
      (TargetSum.decodeDigest_eq_some_iff.mp hsignedDecode).2 (.merkle level)) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (keygenMerkleTargetInput keyResult.1.2 keyResult.2) := by
  have hgame := afterKeygen_execution_mem_detailedGame adversary keyResult hkeygen execution hafter
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
  change Merkle.IsXmssPathCollisionAt
    (Concrete.CacheView.nodeHash execution.2 execution.1.secretKey.parameter request.epoch)
    (Concrete.signaturePath execution.1.forgery.signature)
    (Concrete.signaturePath signature)
    (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter request.epoch
      (recoveredEndpoints
        (fun chain => Concrete.CacheView.chainStep execution.2
          execution.1.secretKey.parameter request.epoch chain)
        forgedEncoding execution.1.forgery.signature.chainValue))
    (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter request.epoch
      (recoveredEndpoints
        (fun chain => Concrete.CacheView.chainStep execution.2
          execution.1.secretKey.parameter request.epoch chain)
        signedEncoding signature.chainValue)) level at hevent
  refine merkle_witness_afterKeygen_orientation adversary keyResult hkeygen execution hafter
    (.intro hverified request.epoch hepoch forgedEncoding hforgedDecode'
      (Concrete.signaturePath signature)
      (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter request.epoch
        (recoveredEndpoints
          (fun chain => Concrete.CacheView.chainStep execution.2
            execution.1.secretKey.parameter request.epoch chain)
          signedEncoding signature.chainValue)) level
      (by unfold merkleWitnessEvent; exact hevent) ?_ ?_)
  · unfold merkleWitnessHonestCurrent
    rw [hsignature,
      Concrete.CacheReplay.leafHash_recovered_signWithEncoding]
    exact Concrete.CacheReplay.authenticationPath_ascends_to_treeNode execution.2
      execution.1.secretKey request.epoch signature.randomness signedEncoding level.val
      level.isLt.le
  · rw [hsignature]
    unfold merkleWitnessHonestSibling
    simp [Concrete.signaturePath, Concrete.CacheReplay.signWithEncoding,
      Concrete.CacheReplay.authenticationPath, level.isLt]

theorem fresh_merkle_witness_afterKeygen_orientation
    (adversary : Adversary Concrete.singleAttemptScheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.singleAttemptScheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.singleAttemptScheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (hverified : execution.1.verified = true)
    (forgedEncoding : Encoding)
    (hforgedDecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
        execution.1.forgery.epoch
        (execution.1.forgery.message, execution.1.forgery.signature.randomness)) =
        some forgedEncoding)
    (level : MerkleLevel)
    (hevent : Concrete.FreshEpochBadEventOccurs execution.2
      execution.1.secretKey.parameter execution.1.forgery.epoch forgedEncoding
      execution.1.forgery.signature
      (execution.1.secretKey.chainStart execution.1.forgery.epoch)
      (Concrete.signaturePath
        (Concrete.CacheReplay.signWithEncoding execution.2 execution.1.secretKey
          execution.1.forgery.epoch execution.1.forgery.signature.randomness forgedEncoding))
      (TargetSum.decodeDigest_eq_some_iff.mp hforgedDecode).2 (.merkle level)) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (keygenMerkleTargetInput keyResult.1.2 keyResult.2) := by
  let honestSignature := Concrete.CacheReplay.signWithEncoding execution.2
    execution.1.secretKey execution.1.forgery.epoch
    execution.1.forgery.signature.randomness forgedEncoding
  change Merkle.IsXmssPathCollisionAt
    (Concrete.CacheView.nodeHash execution.2 execution.1.secretKey.parameter
      execution.1.forgery.epoch)
    (Concrete.signaturePath execution.1.forgery.signature)
    (Concrete.signaturePath honestSignature)
    (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter
      execution.1.forgery.epoch
      (recoveredEndpoints
        (fun chain => Concrete.CacheView.chainStep execution.2
          execution.1.secretKey.parameter execution.1.forgery.epoch chain)
        forgedEncoding execution.1.forgery.signature.chainValue))
    (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter
      execution.1.forgery.epoch
      (fun chain => Wots.publicChain
        (Concrete.CacheView.chainStep execution.2 execution.1.secretKey.parameter
          execution.1.forgery.epoch chain)
        (execution.1.secretKey.chainStart execution.1.forgery.epoch chain))) level at hevent
  refine merkle_witness_afterKeygen_orientation adversary keyResult hkeygen execution hafter
    (.intro hverified execution.1.forgery.epoch rfl forgedEncoding hforgedDecode
      (Concrete.signaturePath honestSignature)
      (Concrete.CacheView.leafHash execution.2 execution.1.secretKey.parameter
        execution.1.forgery.epoch
        (fun chain => Wots.publicChain
          (Concrete.CacheView.chainStep execution.2 execution.1.secretKey.parameter
            execution.1.forgery.epoch chain)
          (execution.1.secretKey.chainStart execution.1.forgery.epoch chain))) level
      (by unfold merkleWitnessEvent; exact hevent) ?_ ?_)
  · unfold merkleWitnessHonestCurrent
    change Merkle.ascend
      (Concrete.CacheView.nodeHash execution.2 execution.1.secretKey.parameter
        execution.1.forgery.epoch)
      (Concrete.signaturePath honestSignature) 0 level.val
      (Concrete.CacheReplay.leafAt execution.2 execution.1.secretKey.parameter
        execution.1.secretKey.chainStart execution.1.forgery.epoch) = _
    exact Concrete.CacheReplay.authenticationPath_ascends_to_treeNode execution.2
      execution.1.secretKey execution.1.forgery.epoch
      execution.1.forgery.signature.randomness forgedEncoding level.val level.isLt.le
  · unfold merkleWitnessHonestSibling
    simp [honestSignature, Concrete.signaturePath,
      Concrete.CacheReplay.signWithEncoding, Concrete.CacheReplay.authenticationPath,
      level.isLt]

theorem merkle_event_afterKeygen_orientation
    (adversary : Adversary Concrete.singleAttemptScheme)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ xmssRomImpl Concrete.singleAttemptScheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ xmssRomImpl
        (detailedGameAfterKeygen Concrete.singleAttemptScheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (level : MerkleLevel)
    (hevent : OutcomeBadEventOccurs execution.2 execution.1 (.merkle level)) :
    Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
      (keygenMerkleTargetInput keyResult.1.2 keyResult.2) := by
  rcases hevent.2 with hsame | hfresh
  · obtain ⟨request, signature, signedEncoding, forgedEncoding, hsignedDecode,
      hforgedDecode, hreturned, hepoch, hmerkle⟩ := hsame
    exact same_merkle_witness_afterKeygen_orientation adversary keyResult hkeygen execution
      hafter hevent.1 request signature signedEncoding forgedEncoding hsignedDecode
      hforgedDecode hreturned hepoch level hmerkle
  · obtain ⟨forgedEncoding, hforgedValid, _hunsigned, hforgedDecode, hmerkle⟩ := hfresh
    exact fresh_merkle_witness_afterKeygen_orientation adversary keyResult hkeygen execution
      hafter hevent.1 forgedEncoding hforgedDecode level hmerkle

theorem merkle_outcomeBadEvent_probability_le
    (q : Nat) (adversary : Adversary Concrete.singleAttemptScheme)
    (hbound : HasHashQueryBound Concrete.singleAttemptScheme adversary q) (level : MerkleLevel) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      OutcomeBadEventOccurs execution.2 execution.1 (.merkle level) |
      detailedGameWithCache Concrete.singleAttemptScheme adversary] ≤
      (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
  apply outcomeBadEvent_probability_le_of_afterKeygen_freshCollision q adversary hbound
    (.merkle level) (fun key cache => keygenMerkleTargetInput key.2 cache)
  intro keyResult hkeygen execution hafter hevent
  exact merkle_event_afterKeygen_orientation adversary keyResult hkeygen execution hafter
    level hevent

end XmssSecurity
