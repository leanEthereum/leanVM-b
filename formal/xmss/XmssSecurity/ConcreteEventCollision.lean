import XmssSecurity.SigningLogReplay

open OracleSpec

namespace XmssSecurity.Concrete

/-- Two distinct concrete random-oracle inputs have the same digest in a final cache view. -/
def CacheDigestCollision (cache : QueryCache HashSpec) (left right : HashInput) : Prop :=
  left ≠ right ∧ CacheView.digestAt cache left = CacheView.digestAt cache right

theorem encodingHash_collision (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (epoch : Epoch)
    (left right : Message × Randomness) (hne : left ≠ right)
    (heq : CacheView.encodingHash cache parameter epoch left =
      CacheView.encodingHash cache parameter epoch right) :
    CacheDigestCollision cache (CacheView.encodingInput parameter epoch left)
      (CacheView.encodingInput parameter epoch right) := by
  exact ⟨fun hinput => hne (CacheView.encodingInput_injective parameter epoch hinput), heq⟩

theorem chainStep_collision (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position : Nat) (hposition : position < chainLength - 1)
    (left right : Digest) (hne : left ≠ right)
    (heq : CacheView.chainStep cache parameter epoch chain position left =
      CacheView.chainStep cache parameter epoch chain position right) :
    CacheDigestCollision cache
      (CacheView.chainInput parameter epoch chain ⟨position, hposition⟩ left)
      (CacheView.chainInput parameter epoch chain ⟨position, hposition⟩ right) := by
  constructor
  · intro hinput
    exact hne (CacheView.chainInput_injective parameter epoch chain ⟨position, hposition⟩ hinput)
  · rw [CacheView.chainStep_eq _ _ _ _ _ _ hposition,
      CacheView.chainStep_eq _ _ _ _ _ _ hposition] at heq
    exact heq

theorem leafHash_collision (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (epoch : Epoch)
    (left right : ChainIndex → Digest) (hne : left ≠ right)
    (heq : CacheView.leafHash cache parameter epoch left =
      CacheView.leafHash cache parameter epoch right) :
    CacheDigestCollision cache (CacheView.leafInput parameter epoch left)
      (CacheView.leafInput parameter epoch right) := by
  exact ⟨fun hinput => hne (CacheView.leafInput_injective parameter epoch hinput), heq⟩

theorem nodeHash_collision (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (epoch : Epoch) (level : MerkleLevel)
    (left right : Digest × Digest) (hne : left ≠ right)
    (heq : CacheView.nodeHash cache parameter epoch level.val left.1 left.2 =
      CacheView.nodeHash cache parameter epoch level.val right.1 right.2) :
    CacheDigestCollision cache
      (CacheView.nodeInput parameter epoch level left.1 left.2)
      (CacheView.nodeInput parameter epoch level right.1 right.2) := by
  constructor
  · intro hinput
    exact hne (CacheView.nodeInput_injective parameter epoch level hinput)
  · rw [CacheView.nodeHash_eq _ _ _ _ _ _ level.isLt,
      CacheView.nodeHash_eq _ _ _ _ _ _ level.isLt] at heq
    exact heq

end XmssSecurity.Concrete

namespace XmssSecurity

/-- The four event families that expose a concrete digest collision. -/
def BadEvent.IsCollision : BadEvent → Prop
  | .chain _ => False
  | _ => True

theorem sameEpoch_badEvent_has_cacheDigestCollision
    (cache : QueryCache HashSpec) (parameter : PublicParameter) (epoch : Epoch)
    (signedMessage forgedMessage : Message)
    (signedEncoding forgedEncoding : Encoding)
    (signedSignature forgedSignature : Signature)
    (hsignedValid : TargetSum.Valid signedEncoding) (event : BadEvent)
    (hevent : Concrete.SameEpochBadEventOccurs cache parameter epoch
      signedMessage forgedMessage signedEncoding forgedEncoding
      signedSignature forgedSignature hsignedValid event)
    (hcollision : event.IsCollision) :
    ∃ left right, Concrete.CacheDigestCollision cache left right := by
  cases event with
  | encoding =>
      exact ⟨_, _, Concrete.encodingHash_collision cache parameter epoch
        (signedMessage, signedSignature.randomness)
        (forgedMessage, forgedSignature.randomness) hevent.1 hevent.2⟩
  | chain chain => simp [BadEvent.IsCollision] at hcollision
  | suffixCollision slot =>
      obtain ⟨position, _hslot, hevent⟩ := hevent
      dsimp only [Wots.IsSuffixCollisionAt] at hevent
      let chain := position.1
      let offset := position.2.val
      let forgedAtSigned := Wots.walk
        (Concrete.CacheView.chainStep cache parameter epoch chain)
        (forgedEncoding chain).val
        ((signedEncoding chain).val - (forgedEncoding chain).val)
        (forgedSignature.chainValue chain)
      let left := Wots.walk (Concrete.CacheView.chainStep cache parameter epoch chain)
        (signedEncoding chain).val offset forgedAtSigned
      let right := Wots.walk (Concrete.CacheView.chainStep cache parameter epoch chain)
        (signedEncoding chain).val offset (signedSignature.chainValue chain)
      have hstep : (signedEncoding chain).val + offset < chainLength - 1 := by
        have hoffset := position.2.isLt
        change offset < chainLength - 1 - (signedEncoding chain).val at hoffset
        have hdigit := (signedEncoding chain).isLt
        omega
      exact ⟨_, _, Concrete.chainStep_collision cache parameter epoch chain
        ((signedEncoding chain).val + offset) hstep left right hevent.1 hevent.2⟩
  | leaf =>
      exact ⟨_, _, Concrete.leafHash_collision cache parameter epoch _ _ hevent.1 hevent.2⟩
  | merkle level =>
      exact ⟨_, _, Concrete.nodeHash_collision cache parameter epoch level _ _ hevent.1 hevent.2⟩

theorem freshEpoch_badEvent_has_cacheDigestCollision
    (cache : QueryCache HashSpec) (parameter : PublicParameter) (epoch : Epoch)
    (forgedEncoding : Encoding) (forgedSignature : Signature)
    (secret : ChainIndex → Digest) (honestPath : Nat → Digest)
    (hforgedValid : TargetSum.Valid forgedEncoding) (event : BadEvent)
    (hevent : Concrete.FreshEpochBadEventOccurs cache parameter epoch forgedEncoding
      forgedSignature secret honestPath hforgedValid event)
    (hcollision : event.IsCollision) :
    ∃ left right, Concrete.CacheDigestCollision cache left right := by
  cases event with
  | encoding => simp [Concrete.FreshEpochBadEventOccurs,
      XmssSecurity.FreshEpochBadEventOccurs] at hevent
  | chain chain => simp [BadEvent.IsCollision] at hcollision
  | suffixCollision slot =>
      obtain ⟨position, _hslot, hevent⟩ := hevent
      dsimp only [Wots.IsSuffixCollisionAt] at hevent
      let chain := position.1
      let offset := position.2.val
      let signedValue := fun i => Wots.signChain
        (Concrete.CacheView.chainStep cache parameter epoch i) (forgedEncoding i) (secret i)
      let forgedAtSigned := Wots.walk
        (Concrete.CacheView.chainStep cache parameter epoch chain)
        (forgedEncoding chain).val
        ((forgedEncoding chain).val - (forgedEncoding chain).val)
        (forgedSignature.chainValue chain)
      let left := Wots.walk (Concrete.CacheView.chainStep cache parameter epoch chain)
        (forgedEncoding chain).val offset forgedAtSigned
      let right := Wots.walk (Concrete.CacheView.chainStep cache parameter epoch chain)
        (forgedEncoding chain).val offset (signedValue chain)
      have hstep : (forgedEncoding chain).val + offset < chainLength - 1 := by
        have hoffset := position.2.isLt
        change offset < chainLength - 1 - (forgedEncoding chain).val at hoffset
        have hdigit := (forgedEncoding chain).isLt
        omega
      exact ⟨_, _, Concrete.chainStep_collision cache parameter epoch chain
        ((forgedEncoding chain).val + offset) hstep left right hevent.1 hevent.2⟩
  | leaf =>
      exact ⟨_, _, Concrete.leafHash_collision cache parameter epoch _ _ hevent.1 hevent.2⟩
  | merkle level =>
      exact ⟨_, _, Concrete.nodeHash_collision cache parameter epoch level _ _ hevent.1 hevent.2⟩

theorem outcomeBadEvent_has_cacheDigestCollision
    (cache : QueryCache HashSpec) (outcome : GameOutcome) (event : BadEvent)
    (hevent : OutcomeBadEventOccurs cache outcome event)
    (hcollision : event.IsCollision) :
    ∃ left right, Concrete.CacheDigestCollision cache left right := by
  rcases hevent.2 with hsame | hfresh
  · obtain ⟨request, signature, signedEncoding, forgedEncoding,
      hsignedEncoding, _hforgedEncoding, _hreturned, _hepoch, hevent⟩ := hsame
    apply sameEpoch_badEvent_has_cacheDigestCollision cache outcome.secretKey.parameter
      request.epoch request.message outcome.forgery.message signedEncoding forgedEncoding
      signature outcome.forgery.signature
      (TargetSum.decodeDigest_eq_some_iff.mp hsignedEncoding).2 event hevent hcollision
  · obtain ⟨forgedEncoding, hforgedValid, _hforgedEncoding, hevent⟩ := hfresh
    exact freshEpoch_badEvent_has_cacheDigestCollision cache outcome.secretKey.parameter
      outcome.forgery.epoch forgedEncoding outcome.forgery.signature
      (outcome.secretKey.chainStart outcome.forgery.epoch)
      (Concrete.signaturePath
        (Concrete.CacheReplay.signWithEncoding cache outcome.secretKey
          outcome.forgery.epoch outcome.forgery.signature.randomness forgedEncoding))
      hforgedValid event hevent hcollision

end XmssSecurity
