import XmssSecurity.Proof.ConcreteForgery
import XmssSecurity.Proof.StatementLemmas

open OracleSpec

namespace XmssSecurity.Concrete

noncomputable def verifyFromCache (cache : QueryCache HashSpec)
    (publicKey : PublicKey) (epoch : Epoch) (message : Message)
    (signature : Signature) : Bool :=
  match TargetSum.decodeDigest
      (CacheView.encodingHash cache publicKey.parameter epoch
        (message, signature.randomness)) with
  | none => false
  | some encoding =>
      decide (Merkle.ascend (CacheView.nodeHash cache publicKey.parameter epoch)
        (signaturePath signature) 0 treeHeight
        (CacheView.leafHash cache publicKey.parameter epoch
          (XmssSecurity.recoveredEndpoints
            (fun chain => CacheView.chainStep cache publicKey.parameter epoch chain)
            encoding signature.chainValue)) = publicKey.root)

theorem verifyFromCache_eq_true_iff (cache : QueryCache HashSpec)
    (publicKey : PublicKey) (epoch : Epoch) (message : Message)
    (signature : Signature) :
    verifyFromCache cache publicKey epoch message signature = true ↔
      ∃ encoding,
        TargetSum.decodeDigest
          (CacheView.encodingHash cache publicKey.parameter epoch
            (message, signature.randomness)) = some encoding ∧
        Merkle.ascend (CacheView.nodeHash cache publicKey.parameter epoch)
          (signaturePath signature) 0 treeHeight
          (CacheView.leafHash cache publicKey.parameter epoch
            (XmssSecurity.recoveredEndpoints
              (fun chain => CacheView.chainStep cache publicKey.parameter epoch chain)
              encoding signature.chainValue)) = publicKey.root := by
  unfold verifyFromCache
  split <;> rename_i hdecode
  · simp only [Bool.false_eq_true, false_iff]
    rintro ⟨encoding, hencoding, _⟩
    rw [hdecode] at hencoding
    cases hencoding
  · simp only [decide_eq_true_eq]
    constructor
    · intro hroot
      exact ⟨_, hdecode, hroot⟩
    · rintro ⟨encoding, hencoding, hroot⟩
      rw [hdecode] at hencoding
      cases hencoding
      exact hroot

/-- Two distinct accepted openings at one epoch yield a concrete cache-level bad event. -/
theorem sameEpoch_badEvent_of_verifyFromCache
    (cache : QueryCache HashSpec) (publicKey : PublicKey) (epoch : Epoch)
    (signedMessage forgedMessage : Message)
    (signedSignature forgedSignature : Signature)
    (hsigned : verifyFromCache cache publicKey epoch signedMessage signedSignature = true)
    (hforged : verifyFromCache cache publicKey epoch forgedMessage forgedSignature = true)
    (hstrong : signedMessage ≠ forgedMessage ∨ signedSignature ≠ forgedSignature) :
    ∃ signedEncoding forgedEncoding,
      ∃ hsignedEncoding : TargetSum.decodeDigest
        (CacheView.encodingHash cache publicKey.parameter epoch
          (signedMessage, signedSignature.randomness)) = some signedEncoding,
      ∃ _hforgedEncoding : TargetSum.decodeDigest
        (CacheView.encodingHash cache publicKey.parameter epoch
          (forgedMessage, forgedSignature.randomness)) = some forgedEncoding,
      ∃ event, SameEpochBadEventOccurs cache publicKey.parameter epoch
        signedMessage forgedMessage signedEncoding forgedEncoding
        signedSignature forgedSignature
        (TargetSum.decodeDigest_eq_some_iff.mp hsignedEncoding).2 event := by
  obtain ⟨signedEncoding, hsignedEncoding, hsignedRoot⟩ :=
    (verifyFromCache_eq_true_iff cache publicKey epoch signedMessage signedSignature).mp hsigned
  obtain ⟨forgedEncoding, hforgedEncoding, hforgedRoot⟩ :=
    (verifyFromCache_eq_true_iff cache publicKey epoch forgedMessage forgedSignature).mp hforged
  have hroot := hforgedRoot.trans hsignedRoot.symm
  obtain ⟨event, hevent⟩ := Concrete.sameEpoch_forgery_has_badEvent
    cache publicKey.parameter epoch signedMessage forgedMessage
    signedEncoding forgedEncoding signedSignature forgedSignature
    hsignedEncoding hforgedEncoding hroot hstrong
  exact ⟨signedEncoding, forgedEncoding, hsignedEncoding, hforgedEncoding, event, hevent⟩

end XmssSecurity.Concrete
