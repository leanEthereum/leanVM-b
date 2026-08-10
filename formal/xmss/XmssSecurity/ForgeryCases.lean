import XmssSecurity.Encoding
import XmssSecurity.Merkle
import XmssSecurity.SecurityBudget
import XmssSecurity.Wots

namespace XmssSecurity

def recoveredEndpoints (step : ChainIndex → Nat → Digest → Digest)
    (encoding : Encoding) (values : ChainIndex → Digest) : ChainIndex → Digest :=
  fun i => Wots.recoverChain (step i) (encoding i) (values i)

noncomputable def SameEpochBadEventOccurs {EncodingInput : Type}
    (encodingHash : EncodingInput → Digest)
    (step : ChainIndex → Nat → Digest → Digest)
    (leafHash : (ChainIndex → Digest) → Digest)
    (nodeHash : Nat → Digest → Digest → Digest)
    (signedInput forgedInput : EncodingInput)
    (signedEncoding forgedEncoding : Encoding)
    (signedValue forgedValue : ChainIndex → Digest)
    (signedPath forgedPath : Nat → Digest)
    (hsignedValid : TargetSum.Valid signedEncoding) : BadEvent → Prop
  | .encoding => signedInput ≠ forgedInput ∧ encodingHash signedInput = encodingHash forgedInput
  | .backwardChain chain =>
      Wots.IsBackwardWitnessAt step signedEncoding forgedEncoding signedValue forgedValue chain
  | .suffixCollision slot =>
      ∃ position : TargetSum.SuffixPosition signedEncoding,
        TargetSum.enumerateSuffixPositions signedEncoding hsignedValid position = slot ∧
        Wots.IsSuffixCollisionAt step signedEncoding forgedEncoding signedValue forgedValue position
  | .leaf => Wots.HasLeafCollision leafHash
      (recoveredEndpoints step forgedEncoding forgedValue)
      (recoveredEndpoints step signedEncoding signedValue)
  | .merkle level => Merkle.IsXmssPathCollisionAt nodeHash forgedPath signedPath
      (leafHash (recoveredEndpoints step forgedEncoding forgedValue))
      (leafHash (recoveredEndpoints step signedEncoding signedValue)) level

/-- The deterministic core of the same-epoch strong-forgery reduction. -/
theorem classify_sameEpoch_forgery {EncodingInput : Type}
    (encodingHash : EncodingInput → Digest)
    (step : ChainIndex → Nat → Digest → Digest)
    (leafHash : (ChainIndex → Digest) → Digest)
    (nodeHash : Nat → Digest → Digest → Digest)
    (signedInput forgedInput : EncodingInput)
    (signedEncoding forgedEncoding : Encoding)
    (signedValue forgedValue : ChainIndex → Digest)
    (signedPath forgedPath : Nat → Digest)
    (hsignedEncoding : TargetSum.decodeDigest (encodingHash signedInput) = some signedEncoding)
    (hforgedEncoding : TargetSum.decodeDigest (encodingHash forgedInput) = some forgedEncoding)
    (hroot : Merkle.ascend nodeHash forgedPath 0 treeHeight
        (leafHash (recoveredEndpoints step forgedEncoding forgedValue)) =
      Merkle.ascend nodeHash signedPath 0 treeHeight
        (leafHash (recoveredEndpoints step signedEncoding signedValue)))
    (hstrong : signedInput ≠ forgedInput ∨ signedValue ≠ forgedValue ∨
      ¬Merkle.SamePathSegment signedPath forgedPath 0 treeHeight) :
    (signedInput ≠ forgedInput ∧ encodingHash signedInput = encodingHash forgedInput) ∨
      Wots.HasBackwardWitness step signedEncoding forgedEncoding signedValue forgedValue ∨
      Wots.HasSuffixCollisionWitness step signedEncoding forgedEncoding signedValue forgedValue ∨
      Wots.HasLeafCollision leafHash
        (recoveredEndpoints step forgedEncoding forgedValue)
        (recoveredEndpoints step signedEncoding signedValue) ∨
      Merkle.HasXmssPathCollision nodeHash forgedPath signedPath
        (leafHash (recoveredEndpoints step forgedEncoding forgedValue))
        (leafHash (recoveredEndpoints step signedEncoding signedValue)) := by
  classical
  have hsignedValid := (TargetSum.decodeDigest_eq_some_iff.mp hsignedEncoding).2
  have hforgedValid := (TargetSum.decodeDigest_eq_some_iff.mp hforgedEncoding).2
  rcases Merkle.sameXmssPath_or_hasCollision nodeHash forgedPath signedPath
      (leafHash (recoveredEndpoints step forgedEncoding forgedValue))
      (leafHash (recoveredEndpoints step signedEncoding signedValue)) hroot with
    ⟨hleaf, hpath⟩ | hmerkle
  · rcases Wots.eq_or_hasLeafCollision leafHash
      (recoveredEndpoints step forgedEncoding forgedValue)
      (recoveredEndpoints step signedEncoding signedValue) hleaf with hendpoints | hleafCollision
    · have hendpoints' : ∀ i,
          Wots.recoverChain (step i) (forgedEncoding i) (forgedValue i) =
            Wots.recoverChain (step i) (signedEncoding i) (signedValue i) := by
        intro i
        exact congrFun hendpoints i
      by_cases hencoding : signedEncoding = forgedEncoding
      · subst forgedEncoding
        by_cases hvalue : signedValue = forgedValue
        · rcases Classical.em (signedInput = forgedInput) with hinput | hinput
          · exfalso
            rcases hstrong with hneInput | hneValue | hnePath
            · exact hneInput hinput
            · exact hneValue hvalue
            · exact hnePath fun offset hoffset => (hpath offset hoffset).symm
          · left
            exact TargetSum.hash_collision_of_same_decodedEncoding encodingHash hinput
              hsignedEncoding hforgedEncoding
        · exact Or.inr <| Or.inr <| Or.inl <|
            Wots.suffixCollision_of_sameEncoding_of_values_ne step signedEncoding
              signedValue forgedValue hvalue hendpoints'
      · rcases Wots.classify_distinct_valid_encodings step signedEncoding forgedEncoding
          signedValue forgedValue hsignedValid hforgedValid hencoding hendpoints' with
        hbackward | hsuffix
        · exact Or.inr <| Or.inl hbackward
        · exact Or.inr <| Or.inr <| Or.inl hsuffix
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl hleafCollision
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr hmerkle

/-- Every same-epoch strong forgery selects one of the 175 explicitly indexed bad events. -/
theorem sameEpoch_forgery_has_badEvent {EncodingInput : Type}
    (encodingHash : EncodingInput → Digest)
    (step : ChainIndex → Nat → Digest → Digest)
    (leafHash : (ChainIndex → Digest) → Digest)
    (nodeHash : Nat → Digest → Digest → Digest)
    (signedInput forgedInput : EncodingInput)
    (signedEncoding forgedEncoding : Encoding)
    (signedValue forgedValue : ChainIndex → Digest)
    (signedPath forgedPath : Nat → Digest)
    (hsignedEncoding : TargetSum.decodeDigest (encodingHash signedInput) = some signedEncoding)
    (hforgedEncoding : TargetSum.decodeDigest (encodingHash forgedInput) = some forgedEncoding)
    (hroot : Merkle.ascend nodeHash forgedPath 0 treeHeight
        (leafHash (recoveredEndpoints step forgedEncoding forgedValue)) =
      Merkle.ascend nodeHash signedPath 0 treeHeight
        (leafHash (recoveredEndpoints step signedEncoding signedValue)))
    (hstrong : signedInput ≠ forgedInput ∨ signedValue ≠ forgedValue ∨
      ¬Merkle.SamePathSegment signedPath forgedPath 0 treeHeight) :
    ∃ event, SameEpochBadEventOccurs encodingHash step leafHash nodeHash
      signedInput forgedInput signedEncoding forgedEncoding signedValue forgedValue
      signedPath forgedPath (TargetSum.decodeDigest_eq_some_iff.mp hsignedEncoding).2 event := by
  have hsignedValid := (TargetSum.decodeDigest_eq_some_iff.mp hsignedEncoding).2
  rcases classify_sameEpoch_forgery encodingHash step leafHash nodeHash
      signedInput forgedInput signedEncoding forgedEncoding signedValue forgedValue
      signedPath forgedPath hsignedEncoding hforgedEncoding hroot hstrong with
    hencoding | hbackward | hsuffix | hleaf | hmerkle
  · exact ⟨.encoding, hencoding⟩
  · obtain ⟨chain, hchain⟩ := hbackward
    exact ⟨.backwardChain chain, hchain⟩
  · obtain ⟨position, hposition⟩ := hsuffix
    exact ⟨.suffixCollision (TargetSum.enumerateSuffixPositions signedEncoding hsignedValid position),
      position, rfl, hposition⟩
  · exact ⟨.leaf, hleaf⟩
  · obtain ⟨level, hlevel⟩ := hmerkle
    exact ⟨.merkle level, hlevel⟩

end XmssSecurity
