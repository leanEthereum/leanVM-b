import SphincsSecurity.Proof.TerminalCache

/-!
# Canonical signed encoding targets

Every successful signer invocation using one one-time position computes the same layer message and
the same least admissible counter. Consequently an encoding collision at that position targets one
canonical signed payload, even when several signatures reuse the position.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

def SignedEncodingPayloadAt (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (signingLog : QueryLog SigningSpec) (lay : Layer)
    (tree : TreeIndex) (leafIdx : LeafIndex) (payload : HashInput) : Prop :=
  ∃ (entry : (request : SignRequest) × SigningSpec.Range request) (signature : Signature)
      (index : Index) (leaves : DigestTree → FtsLeaf),
    entry ∈ signingLog
      ∧ entry.2 = some signature
      ∧ SuccessfulSignRun f cache secretKey entry.1 signature
      ∧ SuccessfulDigestRun f cache secretKey entry.1 signature.randomness index leaves
      ∧ treeIndexAt index lay = tree
      ∧ leafIndexAt index lay = leafIdx
      ∧ payload = digestBytes (evalWithAnswerFn f (layerMessage secretKey index lay)) ++
        counterBytes (signature.counter lay)

theorem SignedLayerAt.signedEncodingPayload {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {signingLog : QueryLog SigningSpec}
    {lay : Layer} {tree : TreeIndex} {leafIdx : LeafIndex}
    (hsigned : SignedLayerAt f cache secretKey signingLog lay tree leafIdx) :
    ∃ payload, SignedEncodingPayloadAt f cache secretKey signingLog lay tree leafIdx payload := by
  obtain ⟨entry, signature, index, leaves, hentry, hresponse, hrun, hdigest, htree, hleaf, _⟩ :=
    hsigned
  exact ⟨_, entry, signature, index, leaves, hentry, hresponse, hrun, hdigest, htree, hleaf, rfl⟩

theorem signedEncodingPayloadAt_unique {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {signingLog : QueryLog SigningSpec}
    {lay : Layer} {tree : TreeIndex} {leafIdx : LeafIndex} {leftPayload rightPayload : HashInput}
    (left : SignedEncodingPayloadAt f cache secretKey signingLog lay tree leafIdx leftPayload)
    (right : SignedEncodingPayloadAt f cache secretKey signingLog lay tree leafIdx rightPayload) :
    leftPayload = rightPayload := by
  obtain ⟨_, leftSignature, leftIndex, leftLeaves, _, _, leftRun, leftDigest, leftTree,
    leftLeaf, rfl⟩ := left
  obtain ⟨_, rightSignature, rightIndex, rightLeaves, _, _, rightRun, rightDigest, rightTree,
    rightLeaf, rfl⟩ := right
  have htree : treeIndexAt leftIndex lay = treeIndexAt rightIndex lay :=
    leftTree.trans rightTree.symm
  have hleaf : leafIndexAt leftIndex lay = leafIndexAt rightIndex lay :=
    leftLeaf.trans rightLeaf.symm
  have hmessage : evalWithAnswerFn f (layerMessage secretKey leftIndex lay) =
      evalWithAnswerFn f (layerMessage secretKey rightIndex lay) :=
    congrArg (evalWithAnswerFn f)
      (layerMessage_eq_of_position_eq secretKey leftIndex rightIndex lay htree hleaf)
  have hots := successfulSignRun_layer_ots_eq_of_position_eq leftRun rightRun leftDigest
    rightDigest lay htree hleaf
  rw [hmessage, hots.1]

def EncodingCollisionAtSignedPayload (f : QueryImpl HashSpec Id)
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (signingLog : QueryLog SigningSpec) : Prop :=
  ∃ (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
      (signedPayload forgedPayload : HashInput) (signedAnswer forgedAnswer : HashOutput),
    SignedEncodingPayloadAt f cache secretKey signingLog lay tree leafIdx signedPayload
      ∧ signedPayload ≠ forgedPayload
      ∧ cache (tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx) signedPayload) =
        some signedAnswer
      ∧ cache (tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx) forgedPayload) =
        some forgedAnswer
      ∧ truncateHash signedAnswer = truncateHash forgedAnswer

theorem EncodingCollision.at_signed_payload {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} (hf : cache.AgreesWithFn f)
    (hcollision : EncodingCollision f cache secretKey signingLog) :
    EncodingCollisionAtSignedPayload f cache secretKey signingLog := by
  obtain ⟨lay, tree, leafIdx, forgedMessage, forgedCounter, forgedValues, _, entry, signature,
    index, leaves, hforgedRun, _, hentry, hresponse, hrun, hdigest, htree, hleaf, _, _,
    hsignedCached, hhit⟩ := hcollision
  let signedPayload := digestBytes (evalWithAnswerFn f (layerMessage secretKey index lay)) ++
    counterBytes (signature.counter lay)
  let forgedPayload := digestBytes forgedMessage ++ counterBytes forgedCounter
  let signedInput := tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx) signedPayload
  let forgedInput := tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx) forgedPayload
  obtain ⟨signedAnswer, hsignedAnswer⟩ := Option.ne_none_iff_exists'.mp hsignedCached
  have hforgedCached : cache forgedInput ≠ none :=
    CachedRun.otsLeaf_encode_cached hforgedRun
  obtain ⟨forgedAnswer, hforgedAnswer⟩ := Option.ne_none_iff_exists'.mp hforgedCached
  change signedInput ≠ forgedInput ∧ truncateHash (f signedInput) = truncateHash (f forgedInput)
    at hhit
  refine ⟨lay, tree, leafIdx, signedPayload, forgedPayload, signedAnswer, forgedAnswer,
    ⟨entry, signature, index, leaves, hentry, hresponse, hrun, hdigest, htree, hleaf, rfl⟩,
    ?_, hsignedAnswer, hforgedAnswer, ?_⟩
  · exact fun heq => hhit.1 (congrArg
      (tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx)) heq)
  · rw [← hf hsignedAnswer, ← hf hforgedAnswer]
    exact hhit.2

end SphincsSecurity.Concrete
