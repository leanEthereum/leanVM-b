import XmssSecurity.Proof.ConcreteCorrectness
import XmssSecurity.Proof.DetailedExecution

open OracleComp OracleSpec ENNReal
open scoped BigOperators

namespace XmssSecurity

def SigningTranscript.Returned (log : QueryLog SigningSpec)
    (request : SignRequest) (signature : Signature) : Prop :=
  ∃ entry ∈ log, entry.1 = request ∧ entry.2 = some signature

structure ConcreteOutcomeConsistent (cache : QueryCache HashSpec)
    (outcome : GameOutcome) : Prop where
  key : outcome.publicKey =
    Concrete.CacheReplay.publicKeyFromCache cache outcome.secretKey
  verification : outcome.verified = Concrete.verifyFromCache cache outcome.publicKey
    outcome.forgery.epoch outcome.forgery.message outcome.forgery.signature
  signing : ∀ request signature, SigningTranscript.Returned outcome.signingLog request signature →
    ∃ encoding,
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash cache outcome.secretKey.parameter request.epoch
          (request.message, signature.randomness)) = some encoding ∧
      signature = Concrete.CacheReplay.signWithEncoding cache outcome.secretKey
        request.epoch signature.randomness encoding

noncomputable def OutcomeBadEventOccurs (cache : QueryCache HashSpec)
    (outcome : GameOutcome) (event : BadEvent) : Prop :=
  outcome.verified = true ∧
  ((∃ request signature signedEncoding forgedEncoding,
    ∃ hsignedEncoding : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash cache outcome.secretKey.parameter request.epoch
        (request.message, signature.randomness)) = some signedEncoding,
    TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash cache outcome.secretKey.parameter request.epoch
        (outcome.forgery.message, outcome.forgery.signature.randomness)) = some forgedEncoding ∧
    SigningTranscript.Returned outcome.signingLog request signature ∧
    request.epoch = outcome.forgery.epoch ∧
    Concrete.SameEpochBadEventOccurs cache outcome.secretKey.parameter request.epoch
      request.message outcome.forgery.message signedEncoding forgedEncoding
      signature outcome.forgery.signature
      (TargetSum.decodeDigest_eq_some_iff.mp hsignedEncoding).2 event) ∨
  (∃ forgedEncoding,
    ∃ hforgedValid : TargetSum.Valid forgedEncoding,
    (¬ ∃ request signature,
      SigningTranscript.Returned outcome.signingLog request signature ∧
        request.epoch = outcome.forgery.epoch) ∧
    TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash cache outcome.secretKey.parameter outcome.forgery.epoch
        (outcome.forgery.message, outcome.forgery.signature.randomness)) = some forgedEncoding ∧
    Concrete.FreshEpochBadEventOccurs cache outcome.secretKey.parameter
      outcome.forgery.epoch forgedEncoding outcome.forgery.signature
      (outcome.secretKey.chainStart outcome.forgery.epoch)
      (Concrete.signaturePath
        (Concrete.CacheReplay.signWithEncoding cache outcome.secretKey
          outcome.forgery.epoch outcome.forgery.signature.randomness forgedEncoding))
      hforgedValid event))

/-- Every consistent winning execution has one of the 175 concrete cache-level bad events. -/
theorem winning_outcome_has_badEvent (cache : QueryCache HashSpec)
    (outcome : GameOutcome) (hconsistent : ConcreteOutcomeConsistent cache outcome)
    (hwin : outcome.won = true) :
    ∃ event, OutcomeBadEventOccurs cache outcome event := by
  obtain ⟨hvalidLog, hnotContains, hverifed⟩ := outcome.won_eq_true_iff.mp hwin
  have hforgedVerify :
      Concrete.verifyFromCache cache outcome.publicKey outcome.forgery.epoch
        outcome.forgery.message outcome.forgery.signature = true := by
    rw [← hconsistent.verification]
    exact hverifed
  rw [hconsistent.key] at hforgedVerify
  by_cases hsigned : ∃ request signature,
      SigningTranscript.Returned outcome.signingLog request signature ∧
      request.epoch = outcome.forgery.epoch
  · obtain ⟨request, signature, hentry, hepoch⟩ := hsigned
    obtain ⟨signedEncoding, hsignedEncoding, hsignature⟩ :=
      hconsistent.signing request signature hentry
    have hsignedVerify :
        Concrete.verifyFromCache cache
          (Concrete.CacheReplay.publicKeyFromCache cache outcome.secretKey)
          request.epoch request.message signature = true := by
      rw [hsignature]
      exact Concrete.CacheReplay.verifyFromCache_signWithEncoding cache outcome.secretKey
        request.epoch request.message signature.randomness signedEncoding hsignedEncoding
    have hstrong : request.message ≠ outcome.forgery.message ∨
        signature ≠ outcome.forgery.signature := by
      by_contra hsame
      push Not at hsame
      apply hnotContains
      obtain ⟨entry, hmem, hrequest, hsignatureEntry⟩ := hentry
      refine ⟨entry, hmem, ?_, ?_⟩
      · rw [hrequest]
        exact congrArg₂ SignRequest.mk hepoch hsame.1
      · rw [hsignatureEntry]
        exact congrArg some hsame.2
    rw [← hepoch] at hforgedVerify
    obtain ⟨actualSignedEncoding, forgedEncoding, hactualSignedEncoding,
      hforgedEncoding, event, hevent⟩ :=
      Concrete.sameEpoch_badEvent_of_verifyFromCache cache
        (Concrete.CacheReplay.publicKeyFromCache cache outcome.secretKey) request.epoch
        request.message outcome.forgery.message signature outcome.forgery.signature
        hsignedVerify hforgedVerify hstrong
    have hactualSignedEncoding' : TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash cache outcome.secretKey.parameter request.epoch
          (request.message, signature.randomness)) = some actualSignedEncoding := by
      simpa only [Concrete.CacheReplay.publicKeyFromCache] using hactualSignedEncoding
    refine ⟨event, hverifed, Or.inl ⟨request, signature, actualSignedEncoding, forgedEncoding,
      hactualSignedEncoding', ?_, hentry, hepoch, ?_⟩⟩
    · simpa only [Concrete.CacheReplay.publicKeyFromCache] using hforgedEncoding
    · simpa only [Concrete.CacheReplay.publicKeyFromCache] using hevent
  · obtain ⟨forgedEncoding, hforgedEncoding, hforgedRoot⟩ :=
      (Concrete.verifyFromCache_eq_true_iff cache
        (Concrete.CacheReplay.publicKeyFromCache cache outcome.secretKey)
        outcome.forgery.epoch outcome.forgery.message outcome.forgery.signature).mp
        hforgedVerify
    have hhonestRoot := Concrete.CacheReplay.authenticationPath_ascends_to_root cache
      outcome.secretKey outcome.forgery.epoch outcome.forgery.signature.randomness forgedEncoding
    have hforgedRoot' := hforgedRoot
    simp only [Concrete.CacheReplay.publicKeyFromCache] at hforgedRoot'
    have hroot :
        Merkle.ascend
            (Concrete.CacheView.nodeHash cache outcome.secretKey.parameter outcome.forgery.epoch)
            (Concrete.signaturePath outcome.forgery.signature) 0 treeHeight
            (Concrete.CacheView.leafHash cache outcome.secretKey.parameter outcome.forgery.epoch
              (recoveredEndpoints
                (fun chain => Concrete.CacheView.chainStep cache outcome.secretKey.parameter
                  outcome.forgery.epoch chain)
                forgedEncoding outcome.forgery.signature.chainValue)) =
          Merkle.ascend
            (Concrete.CacheView.nodeHash cache outcome.secretKey.parameter outcome.forgery.epoch)
            (Concrete.signaturePath
              (Concrete.CacheReplay.signWithEncoding cache outcome.secretKey
                outcome.forgery.epoch outcome.forgery.signature.randomness forgedEncoding))
            0 treeHeight
            (Concrete.CacheView.leafHash cache outcome.secretKey.parameter outcome.forgery.epoch
              (fun chain => Wots.publicChain
                (Concrete.CacheView.chainStep cache outcome.secretKey.parameter
                  outcome.forgery.epoch chain)
                (outcome.secretKey.chainStart outcome.forgery.epoch chain))) := by
      exact hforgedRoot'.trans hhonestRoot.symm
    have hforgedValid := (TargetSum.decodeDigest_eq_some_iff.mp hforgedEncoding).2
    obtain ⟨event, hevent⟩ := Concrete.freshEpoch_forgery_has_badEvent cache
      outcome.secretKey.parameter outcome.forgery.epoch forgedEncoding
      outcome.forgery.signature (outcome.secretKey.chainStart outcome.forgery.epoch)
      (Concrete.signaturePath
        (Concrete.CacheReplay.signWithEncoding cache outcome.secretKey outcome.forgery.epoch
          outcome.forgery.signature.randomness forgedEncoding)) hforgedValid hroot
    have hforgedEncoding' : TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash cache outcome.secretKey.parameter
          outcome.forgery.epoch
          (outcome.forgery.message, outcome.forgery.signature.randomness)) =
        some forgedEncoding := by
      simpa only [Concrete.CacheReplay.publicKeyFromCache] using hforgedEncoding
    exact ⟨event, hverifed, Or.inr ⟨forgedEncoding, hforgedValid, hsigned,
      hforgedEncoding', hevent⟩⟩

end XmssSecurity
