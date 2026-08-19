import XmssSecurity.Proof.ChainInputTrace
import XmssSecurity.Proof.HashInputLemmas
import XmssSecurity.Proof.WinningEventReduction

open OracleSpec

namespace XmssSecurity

abbrev ChainValueIndex := Epoch × Digit

def chainStepDigit (step : ChainStep) : Digit :=
  ⟨step.val, step.isLt.trans (by decide)⟩

theorem Concrete.CacheView.chainInput_eq_iff
    (parameter : PublicParameter)
    (leftEpoch rightEpoch : Epoch) (leftChain rightChain : ChainIndex)
    (leftStep rightStep : ChainStep) (leftValue rightValue : Digest) :
    Concrete.CacheView.chainInput parameter leftEpoch leftChain leftStep leftValue =
        Concrete.CacheView.chainInput parameter rightEpoch rightChain rightStep rightValue ↔
      leftEpoch = rightEpoch ∧ leftChain = rightChain ∧
        leftStep = rightStep ∧ leftValue = rightValue := by
  constructor
  · intro heq
    have hdomain := domain_eq_of_tweakableHashInput_eq parameter heq
    simp only [HashDomain.chain.injEq] at hdomain
    obtain ⟨hepoch, hchain, hstep⟩ := hdomain
    subst rightEpoch
    subst rightChain
    subst rightStep
    refine ⟨rfl, rfl, rfl, ?_⟩
    exact Concrete.CacheView.chainInput_injective parameter leftEpoch leftChain
      leftStep heq
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

noncomputable def keygenChainValueTable
    (keygenCache : QueryCache HashSpec) (secretKey : SecretKey)
    (chain : ChainIndex) : ChainValueIndex → Digest := fun index =>
  Wots.walk
    (Concrete.CacheView.chainStep keygenCache secretKey.parameter index.1 chain)
    0 index.2.val (secretKey.chainStart index.1 chain)

/-- The chain coordinate used by a winning chain event precedes the coordinate returned by every successful signature at the forged epoch. -/
theorem WinningOutcomeBadEventOccurs.chain_coordinate_lt_returned
    {cache : QueryCache HashSpec} {outcome : GameOutcome} {chain : ChainIndex}
    (hevent : WinningOutcomeBadEventOccurs cache outcome (.chain chain))
    (forgedEncoding : Encoding)
    (hforgedDecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash cache outcome.secretKey.parameter
        outcome.forgery.epoch
        (outcome.forgery.message, outcome.forgery.signature.randomness)) =
      some forgedEncoding)
    (request : SignRequest) (signature : Signature) (signedEncoding : Encoding)
    (hreturned : SigningTranscript.Returned outcome.signingLog request signature)
    (hsignedDecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash cache outcome.secretKey.parameter request.epoch
        (request.message, signature.randomness)) = some signedEncoding)
    (hepoch : request.epoch = outcome.forgery.epoch) :
    forgedEncoding chain < signedEncoding chain := by
  rcases hevent.2.2 with hsame | hfresh
  · obtain ⟨eventRequest, eventSignature, eventSignedEncoding, eventForgedEncoding,
      heventSignedDecode, heventForgedDecode, heventReturned, heventEpoch,
      hchain⟩ := hsame
    have hreturnedEq := SigningTranscript.returned_eq_of_same_epoch
      hevent.signingTranscript_valid heventReturned hreturned
      (heventEpoch.trans hepoch.symm)
    obtain ⟨hrequest, hsignature⟩ := hreturnedEq
    subst request
    subst signature
    have hsignedEncoding : eventSignedEncoding = signedEncoding := by
      rw [heventSignedDecode] at hsignedDecode
      exact Option.some.inj hsignedDecode
    have hforgedEncoding : eventForgedEncoding = forgedEncoding := by
      rw [heventEpoch] at heventForgedDecode
      rw [heventForgedDecode] at hforgedDecode
      exact Option.some.inj hforgedDecode
    change Wots.IsBackwardWitnessAt
      (fun candidateChain => Concrete.CacheView.chainStep cache
        outcome.secretKey.parameter eventRequest.epoch candidateChain)
      eventSignedEncoding eventForgedEncoding eventSignature.chainValue
      outcome.forgery.signature.chainValue chain at hchain
    rw [← hsignedEncoding, ← hforgedEncoding]
    exact hchain.1
  · obtain ⟨_eventForgedEncoding, _hvalid, hunsigned, _hdecode, _hchain⟩ := hfresh
    exact (hunsigned ⟨request, signature, hreturned, hepoch⟩).elim

/-- Coordinates sent by the signer, together with every later coordinate that can be derived by walking the chain forward. -/
noncomputable def returnedChainValueIndices
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex) : Finset ChainValueIndex := by
  classical
  exact Finset.univ.filter fun index => ∃ request signature encoding,
    SigningTranscript.Returned log request signature ∧
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash cache secretKey.parameter request.epoch
          (request.message, signature.randomness)) = some encoding ∧
      index.1 = request.epoch ∧ encoding chain ≤ index.2

@[simp]
theorem mem_returnedChainValueIndices_iff
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex) (index : ChainValueIndex) :
    index ∈ returnedChainValueIndices cache secretKey log chain ↔
      ∃ request signature encoding,
        SigningTranscript.Returned log request signature ∧
          TargetSum.decodeDigest
            (Concrete.CacheView.encodingHash cache secretKey.parameter request.epoch
              (request.message, signature.randomness)) = some encoding ∧
          index.1 = request.epoch ∧ encoding chain ≤ index.2 := by
  classical
  simp only [returnedChainValueIndices, Finset.mem_filter, Finset.mem_univ, true_and]

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
theorem WinningOutcomeBadEventOccurs.forged_chain_coordinate_not_mem_returned
    {cache : QueryCache HashSpec} {outcome : GameOutcome} {chain : ChainIndex}
    (hevent : WinningOutcomeBadEventOccurs cache outcome (.chain chain))
    (forgedEncoding : Encoding)
    (hforgedDecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash cache outcome.secretKey.parameter
        outcome.forgery.epoch
        (outcome.forgery.message, outcome.forgery.signature.randomness)) =
      some forgedEncoding) :
    (outcome.forgery.epoch, forgedEncoding chain) ∉
      returnedChainValueIndices cache outcome.secretKey outcome.signingLog chain := by
  intro hmem
  rw [mem_returnedChainValueIndices_iff] at hmem
  obtain ⟨request, signature, signedEncoding, hreturned, hsignedDecode,
    hepoch, hdigit⟩ := hmem
  have hepoch : request.epoch = outcome.forgery.epoch := by
    exact hepoch.symm
  have hbackward := hevent.chain_coordinate_lt_returned forgedEncoding
    hforgedDecode request signature signedEncoding hreturned hsignedDecode hepoch
  exact (not_lt_of_ge hdigit) hbackward

end XmssSecurity
