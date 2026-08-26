import SphincsSecurity.Proof.TerminalCache

/-!
# Canonical signed encoding targets

Every successful signer invocation using one one-time position computes the same layer message and
the same least admissible counter. Consequently an encoding collision at that position targets one
canonical signed payload, even when several signatures reuse the position.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

def layerMessagePosition (index : Index) (lay : Layer) : Position :=
  if lay = topLayer then
    .node middleLayer (treeIndexAt index middleLayer)
      ⟨layerHeight middleLayer - 1, by decide⟩ ⟨0, by positivity⟩
  else if lay = middleLayer then
    .node bottomLayer (treeIndexAt index bottomLayer)
      ⟨layerHeight bottomLayer - 1, by decide⟩ ⟨0, by positivity⟩
  else .ftsRoots index

private theorem topLayer_ne_middleLayer : topLayer ≠ middleLayer := by
  intro h
  have := congrArg Fin.val h
  norm_num [topLayer, middleLayer] at this

private theorem bottomLayer_ne_topLayer : bottomLayer ≠ topLayer := by
  intro h
  have := congrArg Fin.val h
  norm_num [bottomLayer, topLayer, numLayers] at this

private theorem bottomLayer_ne_middleLayer : bottomLayer ≠ middleLayer := by
  intro h
  have := congrArg Fin.val h
  norm_num [bottomLayer, middleLayer, numLayers] at this

@[simp] theorem layerMessagePosition_top (index : Index) :
    layerMessagePosition index topLayer =
      .node middleLayer (treeIndexAt index middleLayer)
        ⟨layerHeight middleLayer - 1, by decide⟩ ⟨0, by positivity⟩ := by
  rw [layerMessagePosition, if_pos rfl]

@[simp] theorem layerMessagePosition_middle (index : Index) :
    layerMessagePosition index middleLayer =
      .node bottomLayer (treeIndexAt index bottomLayer)
        ⟨layerHeight bottomLayer - 1, by decide⟩ ⟨0, by positivity⟩ := by
  rw [layerMessagePosition, if_neg topLayer_ne_middleLayer.symm, if_pos rfl]

@[simp] theorem layerMessagePosition_bottom (index : Index) :
    layerMessagePosition index bottomLayer = .ftsRoots index := by
  rw [layerMessagePosition, if_neg bottomLayer_ne_topLayer,
    if_neg bottomLayer_ne_middleLayer]

theorem eval_layerMessage_eq_honestValue (f : QueryImpl HashSpec Id)
    (secretKey : SecretKey) (index : Index) (lay : Layer) :
    evalWithAnswerFn f (layerMessage secretKey index lay) =
      honestValue f secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
        (layerMessagePosition index lay) := by
  have hlayer : lay = topLayer ∨ lay = middleLayer ∨ lay = bottomLayer := by
    fin_cases lay
    · exact Or.inl (Fin.ext rfl)
    · exact Or.inr (Or.inl (Fin.ext rfl))
    · exact Or.inr (Or.inr (Fin.ext rfl))
  rcases hlayer with rfl | rfl | rfl
  · rw [layerMessage_of_lt secretKey index topLayer (by decide)]
    rw [layerMessagePosition_top, honestValue_node]
    simp only [show (⟨topLayer.val + 1, by decide⟩ : Layer) = middleLayer from rfl]
    rfl
  · rw [layerMessage_of_lt secretKey index middleLayer (by decide)]
    rw [layerMessagePosition_middle, honestValue_node]
    simp only [show (⟨middleLayer.val + 1, by decide⟩ : Layer) = bottomLayer from rfl]
    rfl
  · rw [layerMessage_bottomLayer secretKey index]
    rw [layerMessagePosition_bottom, honestValue_ftsRoots]
    rfl

theorem SuccessfulSignRun.layerMessagePosition_settled {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {message : Message}
    {signature : Signature} (hf : cache.AgreesWithFn f)
    (hrun : SuccessfulSignRun f cache secretKey message signature)
    {index : Index} {leaves : DigestTree → FtsLeaf}
    (hdigest : SuccessfulDigestRun f cache secretKey message signature.randomness index leaves)
    (lay : Layer) :
    Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
      (layerMessagePosition index lay) := by
  obtain ⟨hmessage, _⟩ := hrun.honest_layer_at_of_digest hdigest lay
  have hlayer : lay = topLayer ∨ lay = middleLayer ∨ lay = bottomLayer := by
    fin_cases lay
    · exact Or.inl (Fin.ext rfl)
    · exact Or.inr (Or.inl (Fin.ext rfl))
    · exact Or.inr (Or.inr (Fin.ext rfl))
  rcases hlayer with rfl | rfl | rfl
  · rw [layerMessage_of_lt secretKey index topLayer (by decide)] at hmessage
    rw [layerMessagePosition_top]
    simpa only [
      show (⟨topLayer.val + 1, by decide⟩ : Layer) = middleLayer from rfl] using
      settled_treeRoot_of_cachedRun (ftsSecret := secretKey.ftsSecret) hf middleLayer
        (treeIndexAt index middleLayer) hmessage
  · rw [layerMessage_of_lt secretKey index middleLayer (by decide)] at hmessage
    rw [layerMessagePosition_middle]
    simpa only [
      show (⟨middleLayer.val + 1, by decide⟩ : Layer) = bottomLayer from rfl] using
      settled_treeRoot_of_cachedRun (ftsSecret := secretKey.ftsSecret) hf bottomLayer
        (treeIndexAt index bottomLayer) hmessage
  · rw [layerMessage_bottomLayer secretKey index] at hmessage
    rw [layerMessagePosition_bottom]
    exact settled_ftsRoots_of_cachedRun (otsSecret := secretKey.otsSecret) hf index hmessage

theorem layerMessagePosition_eq_of_position_eq (left right : Index) (lay : Layer)
    (htree : treeIndexAt left lay = treeIndexAt right lay)
    (hleaf : leafIndexAt left lay = leafIndexAt right lay) :
    layerMessagePosition left lay = layerMessagePosition right lay := by
  have hlayer : lay = topLayer ∨ lay = middleLayer ∨ lay = bottomLayer := by
    fin_cases lay
    · exact Or.inl (Fin.ext rfl)
    · exact Or.inr (Or.inl (Fin.ext rfl))
    · exact Or.inr (Or.inr (Fin.ext rfl))
  rcases hlayer with rfl | rfl | rfl
  · rw [layerMessagePosition_top, layerMessagePosition_top,
      middleTree_eq_of_top_position_eq left right htree hleaf]
  · rw [layerMessagePosition_middle, layerMessagePosition_middle,
      bottomTree_eq_of_middle_position_eq left right htree hleaf]
  · rw [layerMessagePosition_bottom, layerMessagePosition_bottom,
      index_eq_of_bottom_position_eq htree hleaf]

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

def CachedSignedEncodingPayloadAt (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (payload : HashInput) : Prop :=
  ∃ (index : Index) (part : LayerPart),
    treeIndexAt index lay = tree
      ∧ leafIndexAt index lay = leafIdx
      ∧ Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
        (layerMessagePosition index lay)
      ∧ CachedRun cache (fromCache cache)
        (otsSign secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
          (secretKey.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay))
          (honestValue (fromCache cache) secretKey.parameter secretKey.otsSecret
            secretKey.ftsSecret (layerMessagePosition index lay)))
      ∧ evalWithAnswerFn (fromCache cache)
        (otsSign secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
          (secretKey.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay))
          (honestValue (fromCache cache) secretKey.parameter secretKey.otsSecret
            secretKey.ftsSecret (layerMessagePosition index lay))) = some (part.1, part.2.1)
      ∧ payload = digestBytes (honestValue (fromCache cache) secretKey.parameter
          secretKey.otsSecret secretKey.ftsSecret (layerMessagePosition index lay)) ++
        counterBytes part.1

theorem SignedLayerAt.signedEncodingPayload {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {signingLog : QueryLog SigningSpec}
    {lay : Layer} {tree : TreeIndex} {leafIdx : LeafIndex}
    (hsigned : SignedLayerAt f cache secretKey signingLog lay tree leafIdx) :
    ∃ payload, SignedEncodingPayloadAt f cache secretKey signingLog lay tree leafIdx payload := by
  obtain ⟨entry, signature, index, leaves, hentry, hresponse, hrun, hdigest, htree, hleaf, _⟩ :=
    hsigned
  exact ⟨_, entry, signature, index, leaves, hentry, hresponse, hrun, hdigest, htree, hleaf, rfl⟩

theorem SignedEncodingPayloadAt.cached {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {signingLog : QueryLog SigningSpec}
    {lay : Layer} {tree : TreeIndex} {leafIdx : LeafIndex} {payload : HashInput}
    (hf : cache.AgreesWithFn f)
    (hsigned : SignedEncodingPayloadAt f cache secretKey signingLog lay tree leafIdx payload) :
    CachedSignedEncodingPayloadAt cache secretKey lay tree leafIdx payload := by
  obtain ⟨_, signature, index, leaves, _, _, hrun, hdigest, htree, hleaf, hpayload⟩ := hsigned
  obtain ⟨part, hcounter, _, hlayer⟩ := hrun.layerRun_of_digest hdigest lay
  obtain ⟨hotsEval, hotsCached⟩ := hlayer.otsSign_eval_cached
  have hsettled := hrun.layerMessagePosition_settled hf hdigest lay
  have hmessage : evalWithAnswerFn f (layerMessage secretKey index lay) =
      honestValue (fromCache cache) secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
        (layerMessagePosition index lay) := by
    rw [eval_layerMessage_eq_honestValue]
    exact honestValue_eq_of_settled hf hsettled
  rw [hmessage] at hotsEval hotsCached
  have heval := hotsCached.eval_eq hf (agreesWithFn_fromCache cache)
  refine ⟨index, part, htree, hleaf, hsettled,
    hotsCached.changeAnswerFn hf (agreesWithFn_fromCache cache), ?_, ?_⟩
  · exact heval.symm.trans hotsEval
  · rw [hpayload, hmessage, hcounter]

theorem cachedSignedEncodingPayloadAt_unique {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {lay : Layer} {tree : TreeIndex} {leafIdx : LeafIndex}
    {leftPayload rightPayload : HashInput}
    (left : CachedSignedEncodingPayloadAt cache secretKey lay tree leafIdx leftPayload)
    (right : CachedSignedEncodingPayloadAt cache secretKey lay tree leafIdx rightPayload) :
    leftPayload = rightPayload := by
  obtain ⟨leftIndex, leftPart, leftTree, leftLeaf, _, _, leftEval, rfl⟩ := left
  obtain ⟨rightIndex, rightPart, rightTree, rightLeaf, _, _, rightEval, rfl⟩ := right
  have htree : treeIndexAt leftIndex lay = treeIndexAt rightIndex lay :=
    leftTree.trans rightTree.symm
  have hleaf : leafIndexAt leftIndex lay = leafIndexAt rightIndex lay :=
    leftLeaf.trans rightLeaf.symm
  have hposition := layerMessagePosition_eq_of_position_eq leftIndex rightIndex lay htree hleaf
  rw [htree, hleaf, hposition] at leftEval
  have hpart := Option.some.inj (leftEval.symm.trans rightEval)
  have hcounter : leftPart.1 = rightPart.1 :=
    congrArg (fun value : Counter × (ChainIndex → Digest) => value.1) hpart
  rw [hposition, hcounter]

theorem CachedSignedEncodingPayloadAt.mono {cache cache' : QueryCache HashSpec}
    {secretKey : SecretKey} {lay : Layer} {tree : TreeIndex} {leafIdx : LeafIndex}
    {payload : HashInput} (hle : cache ≤ cache')
    (htarget : CachedSignedEncodingPayloadAt cache secretKey lay tree leafIdx payload) :
    CachedSignedEncodingPayloadAt cache' secretKey lay tree leafIdx payload := by
  obtain ⟨index, part, htree, hleaf, hsettled, hrun, heval, hpayload⟩ := htarget
  have hagrees : cache.AgreesWithFn (fromCache cache') := agreesWithFn_fromCache_of_le hle
  have hvalue := honestValue_eq_of_settled hagrees hsettled
  rw [← hvalue] at hrun heval
  have hevalEq := hrun.eval_eq (agreesWithFn_fromCache cache) hagrees
  have hrun' := (hrun.changeAnswerFn (agreesWithFn_fromCache cache) hagrees).mono hle
  refine ⟨index, part, htree, hleaf, hsettled.mono hle, hrun', hevalEq.symm.trans heval, ?_⟩
  rw [hpayload, hvalue]

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

def EncodingBad (cache : QueryCache HashSpec) (secretKey : SecretKey) : Prop :=
  ∃ (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
      (signedPayload otherPayload : HashInput) (signedAnswer otherAnswer : HashOutput),
    CachedSignedEncodingPayloadAt cache secretKey lay tree leafIdx signedPayload
      ∧ signedPayload ≠ otherPayload
      ∧ cache (tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx) signedPayload) =
        some signedAnswer
      ∧ cache (tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx) otherPayload) =
        some otherAnswer
      ∧ truncateHash signedAnswer = truncateHash otherAnswer

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

theorem EncodingCollisionAtSignedPayload.encodingBad {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} (hf : cache.AgreesWithFn f)
    (hcollision : EncodingCollisionAtSignedPayload f cache secretKey signingLog) :
    EncodingBad cache secretKey := by
  obtain ⟨lay, tree, leafIdx, signedPayload, otherPayload, signedAnswer, otherAnswer,
    hsigned, hne, hsignedCached, hotherCached, hvalue⟩ := hcollision
  exact ⟨lay, tree, leafIdx, signedPayload, otherPayload, signedAnswer, otherAnswer,
    hsigned.cached hf, hne, hsignedCached, hotherCached, hvalue⟩

theorem EncodingCollision.encodingBad {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} (hf : cache.AgreesWithFn f)
    (hcollision : EncodingCollision f cache secretKey signingLog) :
    EncodingBad cache secretKey :=
  (hcollision.at_signed_payload hf).encodingBad hf

theorem EncodingBad.mono {cache cache' : QueryCache HashSpec} {secretKey : SecretKey}
    (hle : cache ≤ cache') (hbad : EncodingBad cache secretKey) : EncodingBad cache' secretKey := by
  obtain ⟨lay, tree, leafIdx, signedPayload, otherPayload, signedAnswer, otherAnswer,
    hsigned, hne, hsignedCached, hotherCached, hvalue⟩ := hbad
  exact ⟨lay, tree, leafIdx, signedPayload, otherPayload, signedAnswer, otherAnswer,
    hsigned.mono hle, hne, hle hsignedCached, hle hotherCached, hvalue⟩

theorem not_encodingBad_empty (secretKey : SecretKey) : ¬ EncodingBad ∅ secretKey := by
  rintro ⟨_, _, _, _, _, _, _, _, _, hsignedCached, _⟩
  simp at hsignedCached

end SphincsSecurity.Concrete
