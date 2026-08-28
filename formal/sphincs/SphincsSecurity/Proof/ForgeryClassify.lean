import SphincsSecurity.Proof.FewTimeCompare

/-!
# Classifying an accepted forgery

Descent through the three hypertree layers stops at a bad cache, at a one-time position not covered
exactly by the signing transcript, or at an honest few-time opening.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

def LayerObstacle (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (signingLog : QueryLog SigningSpec) : Prop :=
  ∃ (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest)
      (counter : Counter) (values : ChainIndex → Digest) (path : Nat → Digest),
    HonestLayerOpening f secretKey.parameter secretKey.otsSecret lay tree leafIdx message counter
        values path
      ∧ CachedRun cache f (otsLeaf secretKey.parameter lay tree leafIdx message counter values)
      ∧ (¬ SignedLayerAt f cache secretKey signingLog lay tree leafIdx
        ∨ LayerComparisonFailure f cache secretKey signingLog lay tree leafIdx message counter)

def VerifierLayerMessage (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (leaves : DigestTree → FtsLeaf) (signature : Signature)
    (lay : Layer) (message : Digest) : Prop :=
  let ftsPublicKey := evalWithAnswerFn f
    (ftsRecover parameter index leaves signature.ftsSecret signature.ftsPath)
  ∃ bottomLeaf,
    evalWithAnswerFn f (otsLeaf parameter bottomLayer (treeIndexAt index bottomLayer)
        (leafIndexAt index bottomLayer) ftsPublicKey (signature.counter bottomLayer)
        (signature.chainValue bottomLayer)) = some bottomLeaf
      ∧ let middleMessage := foldValue f parameter bottomLayer
          (treeIndexAt index bottomLayer) (leafIndexAt index bottomLayer)
          (signaturePath signature bottomLayer) bottomLeaf (layerHeight bottomLayer)
        ∃ middleLeaf,
          evalWithAnswerFn f (otsLeaf parameter middleLayer (treeIndexAt index middleLayer)
              (leafIndexAt index middleLayer) middleMessage (signature.counter middleLayer)
              (signature.chainValue middleLayer)) = some middleLeaf
            ∧ let topMessage := foldValue f parameter middleLayer
                (treeIndexAt index middleLayer) (leafIndexAt index middleLayer)
                (signaturePath signature middleLayer) middleLeaf (layerHeight middleLayer)
              (lay = bottomLayer ∧ message = ftsPublicKey)
                ∨ (lay = middleLayer ∧ message = middleMessage)
                ∨ (lay = topLayer ∧ message = topMessage)

def ForgedLayerObstacle (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (signingLog : QueryLog SigningSpec) (index : Index)
    (leaves : DigestTree → FtsLeaf) (signature : Signature) : Prop :=
  ∃ (lay : Layer) (message : Digest),
    VerifierLayerMessage f secretKey.parameter index leaves signature lay message
      ∧ HonestLayerOpening f secretKey.parameter secretKey.otsSecret lay
        (treeIndexAt index lay) (leafIndexAt index lay) message (signature.counter lay)
        (signature.chainValue lay) (signaturePath signature lay)
      ∧ CachedRun cache f (otsLeaf secretKey.parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) message (signature.counter lay) (signature.chainValue lay))
      ∧ (¬ SignedLayerAt f cache secretKey signingLog lay
          (treeIndexAt index lay) (leafIndexAt index lay)
        ∨ LayerComparisonFailure f cache secretKey signingLog lay
          (treeIndexAt index lay) (leafIndexAt index lay) message (signature.counter lay))

def LayerRootSettled (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (lay : Layer) (tree : TreeIndex) : Prop :=
  Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
    (.node lay tree ⟨layerHeight lay - 1, by
      have hpos : 0 < layerHeight lay := by
        unfold layerHeight
        split <;> norm_num [maxLayerHeight]
      have hle := layerHeight_le lay
      omega⟩ ⟨0, by positivity⟩)

def SettledForgedLayerObstacle (f : QueryImpl HashSpec Id)
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (signingLog : QueryLog SigningSpec) (index : Index)
    (leaves : DigestTree → FtsLeaf) (signature : Signature) : Prop :=
  ∃ (lay : Layer) (message : Digest),
    LayerRootSettled cache secretKey lay (treeIndexAt index lay)
      ∧ VerifierLayerMessage f secretKey.parameter index leaves signature lay message
      ∧ HonestLayerOpening f secretKey.parameter secretKey.otsSecret lay
        (treeIndexAt index lay) (leafIndexAt index lay) message (signature.counter lay)
        (signature.chainValue lay) (signaturePath signature lay)
      ∧ CachedRun cache f (otsLeaf secretKey.parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) message (signature.counter lay) (signature.chainValue lay))
      ∧ (¬ SignedLayerAt f cache secretKey signingLog lay
          (treeIndexAt index lay) (leafIndexAt index lay)
        ∨ LayerComparisonFailure f cache secretKey signingLog lay
          (treeIndexAt index lay) (leafIndexAt index lay) message (signature.counter lay))

theorem SettledForgedLayerObstacle.toForgedLayerObstacle
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {signingLog : QueryLog SigningSpec} {index : Index}
    {leaves : DigestTree → FtsLeaf} {signature : Signature}
    (hobstacle : SettledForgedLayerObstacle f cache secretKey signingLog index leaves signature) :
    ForgedLayerObstacle f cache secretKey signingLog index leaves signature := by
  obtain ⟨lay, message, _, hverifier, hopening, hcached, hfailure⟩ := hobstacle
  exact ⟨lay, message, hverifier, hopening, hcached, hfailure⟩

theorem ForgedLayerObstacle.toLayerObstacle
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {signingLog : QueryLog SigningSpec} {index : Index}
    {leaves : DigestTree → FtsLeaf} {signature : Signature}
    (hobstacle : ForgedLayerObstacle f cache secretKey signingLog index leaves signature) :
    LayerObstacle f cache secretKey signingLog := by
  obtain ⟨lay, message, _, hopening, hcached, hfailure⟩ := hobstacle
  exact ⟨lay, treeIndexAt index lay, leafIndexAt index lay, message,
    signature.counter lay, signature.chainValue lay, signaturePath signature lay,
    hopening, hcached, hfailure⟩

def UncoveredFtsSecret (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (signingLog : QueryLog SigningSpec) (index : Index)
    (leaves : DigestTree → FtsLeaf) (secrets : FtsTree → Digest) : Prop :=
  ∃ tree, ¬ SignedFtsLeaf f cache secretKey signingLog index tree (leaves (ftsIndexOf tree))
    ∧ secrets tree = secretKey.ftsSecret index tree (leaves (ftsIndexOf tree))
    ∧ cache (tweakableHashInput secretKey.parameter
      (.ftsLeaf index tree (leaves (ftsIndexOf tree))) (digestBytes (secrets tree))) ≠ none

def FullyHonestOpening (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (index : Index) (leaves : DigestTree → FtsLeaf)
    (signature : Signature) : Prop :=
  (∀ lay, HonestLayerOpening f secretKey.parameter secretKey.otsSecret lay
        (treeIndexAt index lay) (leafIndexAt index lay)
        (evalWithAnswerFn f (layerMessage secretKey index lay)) (signature.counter lay)
        (signature.chainValue lay) (signaturePath signature lay)
      ∧ CachedRun cache f (otsLeaf secretKey.parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) (evalWithAnswerFn f (layerMessage secretKey index lay))
        (signature.counter lay) (signature.chainValue lay)))
    ∧ (∀ tree,
      signature.ftsSecret tree = secretKey.ftsSecret index tree (leaves (ftsIndexOf tree))
        ∧ ∀ level (hlevel : level < ftsTreeHeight), signature.ftsPath tree ⟨level, hlevel⟩
          = honestFtsNode f secretKey.parameter index tree (secretKey.ftsSecret index tree) level
            (Nat.xor ((leaves (ftsIndexOf tree)).val / 2 ^ level) 1))
    ∧ CachedRun cache f
      (ftsRecover secretKey.parameter index leaves signature.ftsSecret signature.ftsPath)
    ∧ ∀ lay, VerifierLayerMessage f secretKey.parameter index leaves signature lay
      (evalWithAnswerFn f (layerMessage secretKey index lay))

def SettledFullyHonestOpening (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (index : Index) (leaves : DigestTree → FtsLeaf)
    (signature : Signature) : Prop :=
  FullyHonestOpening f cache secretKey index leaves signature ∧
    ∀ lay, LayerRootSettled cache secretKey lay (treeIndexAt index lay)

theorem SettledFullyHonestOpening.settleObstacle
    {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index} {leaves : DigestTree → FtsLeaf}
    {signature : Signature}
    (hfull : SettledFullyHonestOpening f cache secretKey index leaves signature)
    (hobstacle : ForgedLayerObstacle f cache secretKey signingLog index leaves signature) :
    SettledForgedLayerObstacle f cache secretKey signingLog index leaves signature := by
  obtain ⟨lay, message, hverifier, hopening, hcached, hfailure⟩ := hobstacle
  exact ⟨lay, message, hfull.2 lay, hverifier, hopening, hcached, hfailure⟩

theorem middleTree_eq_of_top_position_eq (leftIndex rightIndex : Index)
    (htree : treeIndexAt leftIndex topLayer = treeIndexAt rightIndex topLayer)
    (hleaf : leafIndexAt leftIndex topLayer = leafIndexAt rightIndex topLayer) :
    treeIndexAt leftIndex middleLayer = treeIndexAt rightIndex middleLayer := by
  apply Fin.ext
  rw [layers_link_top leftIndex, layers_link_top rightIndex, congrArg Fin.val htree,
    congrArg Fin.val hleaf]

theorem bottomTree_eq_of_middle_position_eq (leftIndex rightIndex : Index)
    (htree : treeIndexAt leftIndex middleLayer = treeIndexAt rightIndex middleLayer)
    (hleaf : leafIndexAt leftIndex middleLayer = leafIndexAt rightIndex middleLayer) :
    treeIndexAt leftIndex bottomLayer = treeIndexAt rightIndex bottomLayer := by
  apply Fin.ext
  rw [layers_link_middle leftIndex, layers_link_middle rightIndex, congrArg Fin.val htree,
    congrArg Fin.val hleaf]

theorem exact_top_message_eq_middle_root (f : QueryImpl HashSpec Id) (secretKey : SecretKey)
    (signedIndex forgedIndex : Index) (message : Digest)
    (htree : treeIndexAt signedIndex topLayer = treeIndexAt forgedIndex topLayer)
    (hleaf : leafIndexAt signedIndex topLayer = leafIndexAt forgedIndex topLayer)
    (hmessage : evalWithAnswerFn f (layerMessage secretKey signedIndex topLayer) = message) :
    message = honestNode f secretKey.parameter middleLayer
      (treeIndexAt forgedIndex middleLayer)
      (secretKey.otsSecret middleLayer (treeIndexAt forgedIndex middleLayer))
      (layerHeight middleLayer) 0 := by
  have hnext := middleTree_eq_of_top_position_eq signedIndex forgedIndex htree hleaf
  rw [← hmessage, layerMessage_of_lt secretKey signedIndex topLayer (by decide)]
  simp only [show (⟨topLayer.val + 1, by decide⟩ : Layer) = middleLayer from rfl, hnext]
  change evalWithAnswerFn f (treeNode secretKey.parameter middleLayer
    (treeIndexAt forgedIndex middleLayer)
    (secretKey.otsSecret middleLayer (treeIndexAt forgedIndex middleLayer))
    (layerHeight middleLayer) 0) = _
  rfl

theorem exact_middle_message_eq_bottom_root (f : QueryImpl HashSpec Id) (secretKey : SecretKey)
    (signedIndex forgedIndex : Index) (message : Digest)
    (htree : treeIndexAt signedIndex middleLayer = treeIndexAt forgedIndex middleLayer)
    (hleaf : leafIndexAt signedIndex middleLayer = leafIndexAt forgedIndex middleLayer)
    (hmessage : evalWithAnswerFn f (layerMessage secretKey signedIndex middleLayer) = message) :
    message = honestNode f secretKey.parameter bottomLayer
      (treeIndexAt forgedIndex bottomLayer)
      (secretKey.otsSecret bottomLayer (treeIndexAt forgedIndex bottomLayer))
      (layerHeight bottomLayer) 0 := by
  have hnext := bottomTree_eq_of_middle_position_eq signedIndex forgedIndex htree hleaf
  rw [← hmessage, layerMessage_of_lt secretKey signedIndex middleLayer (by decide)]
  simp only [show (⟨middleLayer.val + 1, by decide⟩ : Layer) = bottomLayer from rfl, hnext]
  change evalWithAnswerFn f (treeNode secretKey.parameter bottomLayer
    (treeIndexAt forgedIndex bottomLayer)
    (secretKey.otsSecret bottomLayer (treeIndexAt forgedIndex bottomLayer))
    (layerHeight bottomLayer) 0) = _
  rfl

theorem exact_bottom_message_eq_fts_key (f : QueryImpl HashSpec Id) (secretKey : SecretKey)
    (signedIndex forgedIndex : Index) (message : Digest)
    (htree : treeIndexAt signedIndex bottomLayer = treeIndexAt forgedIndex bottomLayer)
    (hleaf : leafIndexAt signedIndex bottomLayer = leafIndexAt forgedIndex bottomLayer)
    (hmessage : evalWithAnswerFn f (layerMessage secretKey signedIndex bottomLayer) = message) :
    message = honestFtsKey f secretKey.parameter forgedIndex (secretKey.ftsSecret forgedIndex) := by
  have hindex := index_eq_of_bottom_position_eq htree hleaf
  subst signedIndex
  rw [← hmessage, layerMessage_bottomLayer]
  rfl

theorem accepted_forgery_classify (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (signingLog : QueryLog SigningSpec) (index : Index)
    (signature : Signature) (leaves : DigestTree → FtsLeaf) (ftsPublicKey root : Digest)
    (hf : cache.AgreesWithFn f)
    (hftsPublicKey : evalWithAnswerFn f
      (ftsRecover secretKey.parameter index leaves signature.ftsSecret signature.ftsPath)
        = ftsPublicKey)
    (htop : HypertreeTopOpening f cache secretKey.parameter secretKey.otsSecret index signature
      ftsPublicKey root)
    (htopSettled : LayerRootSettled cache secretKey topLayer
      (treeIndexAt index topLayer))
    (hftsRun : CachedRun cache f
      (ftsRecover secretKey.parameter index leaves signature.ftsSecret signature.ftsPath)) :
    Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
      ∨ SettledForgedLayerObstacle f cache secretKey signingLog index leaves signature
      ∨ SettledFullyHonestOpening f cache secretKey index leaves signature := by
  obtain ⟨bottomLeaf, hbottom, middleLeaf, hmiddle, htopOpening, htopRun⟩ := htop
  let middleMessage := foldValue f secretKey.parameter bottomLayer
    (treeIndexAt index bottomLayer) (leafIndexAt index bottomLayer)
    (signaturePath signature bottomLayer) bottomLeaf (layerHeight bottomLayer)
  let topMessage := foldValue f secretKey.parameter middleLayer
    (treeIndexAt index middleLayer) (leafIndexAt index middleLayer)
    (signaturePath signature middleLayer) middleLeaf (layerHeight middleLayer)
  have hverifierBottom : VerifierLayerMessage f secretKey.parameter index leaves signature
      bottomLayer ftsPublicKey := by
    simp only [VerifierLayerMessage, hftsPublicKey]
    exact ⟨bottomLeaf, hbottom.1, middleLeaf, hmiddle.1, Or.inl ⟨trivial, trivial⟩⟩
  have hverifierMiddle : VerifierLayerMessage f secretKey.parameter index leaves signature
      middleLayer middleMessage := by
    simp only [VerifierLayerMessage, hftsPublicKey]
    exact ⟨bottomLeaf, hbottom.1, middleLeaf, hmiddle.1,
      Or.inr (Or.inl ⟨trivial, rfl⟩)⟩
  have hverifierTop : VerifierLayerMessage f secretKey.parameter index leaves signature
      topLayer topMessage := by
    simp only [VerifierLayerMessage, hftsPublicKey]
    exact ⟨bottomLeaf, hbottom.1, middleLeaf, hmiddle.1,
      Or.inr (Or.inr ⟨trivial, rfl⟩)⟩
  by_cases hsignedTop : SignedLayerAt f cache secretKey signingLog topLayer
      (treeIndexAt index topLayer) (leafIndexAt index topLayer)
  · rcases hsignedTop.exact_or_failure topMessage (signature.counter topLayer)
        (signature.chainValue topLayer) (signaturePath signature topLayer) htopOpening with
      ⟨_, _, signedTopIndex, _, _, _, _, _, htopTree, htopLeaf, htopMessage, _⟩ | hfailure
    · have hmiddleRoot := exact_top_message_eq_middle_root f secretKey signedTopIndex index
        topMessage htopTree htopLeaf htopMessage
      have htopEval : evalWithAnswerFn f (layerMessage secretKey index topLayer) = topMessage := by
        rw [← htopMessage]
        congr 1
        exact (layerMessage_eq_of_position_eq secretKey signedTopIndex index topLayer htopTree
          htopLeaf).symm
      have hmiddleSettled := hsignedTop.settles_middle hf
      rcases layer_extract_from_settled_root_or_bad (ftsSecret := secretKey.ftsSecret) hf middleLayer
          (treeIndexAt index middleLayer) (leafIndexAt index middleLayer)
          (leafIndexAt_lt index middleLayer) middleMessage (signature.counter middleLayer)
          (signature.chainValue middleLayer) (signaturePath signature middleLayer) middleLeaf
          hmiddle.1 (by simpa only [topMessage] using hmiddleRoot)
          hmiddle.2.2.1 hmiddle.2.2.2.1 hmiddleSettled with hbad | hmiddleOpening
      · exact Or.inl hbad
      · by_cases hsignedMiddle : SignedLayerAt f cache secretKey signingLog middleLayer
            (treeIndexAt index middleLayer) (leafIndexAt index middleLayer)
        · rcases hsignedMiddle.exact_or_failure middleMessage (signature.counter middleLayer)
              (signature.chainValue middleLayer) (signaturePath signature middleLayer)
              hmiddleOpening with
            ⟨_, _, signedMiddleIndex, _, _, _, _, _, hmiddleTree, hmiddleLeaf, hmiddleMessage, _⟩ |
              hfailure
          · have hbottomRoot := exact_middle_message_eq_bottom_root f secretKey signedMiddleIndex index
              middleMessage hmiddleTree hmiddleLeaf hmiddleMessage
            have hmiddleEval : evalWithAnswerFn f (layerMessage secretKey index middleLayer)
                = middleMessage := by
              rw [← hmiddleMessage]
              congr 1
              exact (layerMessage_eq_of_position_eq secretKey signedMiddleIndex index middleLayer
                hmiddleTree hmiddleLeaf).symm
            have hbottomSettled := hsignedMiddle.settles_bottom hf
            rcases layer_extract_from_settled_root_or_bad (ftsSecret := secretKey.ftsSecret) hf
                bottomLayer (treeIndexAt index bottomLayer) (leafIndexAt index bottomLayer)
                (leafIndexAt_lt index bottomLayer) ftsPublicKey (signature.counter bottomLayer)
                (signature.chainValue bottomLayer) (signaturePath signature bottomLayer) bottomLeaf
                hbottom.1 (by simpa only [middleMessage] using hbottomRoot)
                hbottom.2.2.1 hbottom.2.2.2.1 hbottomSettled with hbad | hbottomOpening
            · exact Or.inl hbad
            · by_cases hsignedBottom : SignedLayerAt f cache secretKey signingLog bottomLayer
                  (treeIndexAt index bottomLayer) (leafIndexAt index bottomLayer)
              · rcases hsignedBottom.exact_or_failure ftsPublicKey (signature.counter bottomLayer)
                    (signature.chainValue bottomLayer) (signaturePath signature bottomLayer)
                    hbottomOpening with
                  ⟨_, _, signedBottomIndex, _, _, _, _, _, hbottomTree, hbottomLeaf,
                    hbottomMessage, _⟩ | hfailure
                · have hftsKey := exact_bottom_message_eq_fts_key f secretKey signedBottomIndex index
                    ftsPublicKey hbottomTree hbottomLeaf hbottomMessage
                  have hbottomEval : evalWithAnswerFn f (layerMessage secretKey index bottomLayer)
                      = ftsPublicKey := by
                    rw [← hbottomMessage]
                    congr 1
                    exact (layerMessage_eq_of_position_eq secretKey signedBottomIndex index
                      bottomLayer hbottomTree hbottomLeaf).symm
                  have hftsSettled := hsignedBottom.settles_fts hf
                  rcases ftsRecover_extract_from_settled_roots_or_bad hf index leaves
                      signature.ftsSecret signature.ftsPath (hftsPublicKey.trans hftsKey) hftsRun
                      hftsSettled with hbad | hhonest
                  · exact Or.inl hbad
                  · right
                    right
                    have htopOpening' : HonestLayerOpening f secretKey.parameter
                        secretKey.otsSecret topLayer (treeIndexAt index topLayer)
                        (leafIndexAt index topLayer)
                        (evalWithAnswerFn f (layerMessage secretKey index topLayer))
                        (signature.counter topLayer) (signature.chainValue topLayer)
                        (signaturePath signature topLayer) := by
                      rw [htopEval]
                      exact htopOpening
                    have hmiddleOpening' : HonestLayerOpening f secretKey.parameter
                        secretKey.otsSecret middleLayer (treeIndexAt index middleLayer)
                        (leafIndexAt index middleLayer)
                        (evalWithAnswerFn f (layerMessage secretKey index middleLayer))
                        (signature.counter middleLayer) (signature.chainValue middleLayer)
                        (signaturePath signature middleLayer) := by
                      rw [hmiddleEval]
                      exact hmiddleOpening
                    have hbottomOpening' : HonestLayerOpening f secretKey.parameter
                        secretKey.otsSecret bottomLayer (treeIndexAt index bottomLayer)
                        (leafIndexAt index bottomLayer)
                        (evalWithAnswerFn f (layerMessage secretKey index bottomLayer))
                        (signature.counter bottomLayer) (signature.chainValue bottomLayer)
                        (signaturePath signature bottomLayer) := by
                      rw [hbottomEval]
                      exact hbottomOpening
                    have htopRun' : CachedRun cache f (otsLeaf secretKey.parameter topLayer
                        (treeIndexAt index topLayer) (leafIndexAt index topLayer)
                        (evalWithAnswerFn f (layerMessage secretKey index topLayer))
                        (signature.counter topLayer) (signature.chainValue topLayer)) := by
                      rw [htopEval]
                      exact htopRun
                    have hmiddleRun' : CachedRun cache f (otsLeaf secretKey.parameter middleLayer
                        (treeIndexAt index middleLayer) (leafIndexAt index middleLayer)
                        (evalWithAnswerFn f (layerMessage secretKey index middleLayer))
                        (signature.counter middleLayer) (signature.chainValue middleLayer)) := by
                      rw [hmiddleEval]
                      exact hmiddle.2.2.1
                    have hbottomRun' : CachedRun cache f (otsLeaf secretKey.parameter bottomLayer
                        (treeIndexAt index bottomLayer) (leafIndexAt index bottomLayer)
                        (evalWithAnswerFn f (layerMessage secretKey index bottomLayer))
                        (signature.counter bottomLayer) (signature.chainValue bottomLayer)) := by
                      rw [hbottomEval]
                      exact hbottom.2.2.1
                    refine ⟨⟨?_, hhonest, hftsRun, ?_⟩, ?_⟩
                    · intro lay
                      fin_cases lay
                      · exact ⟨by simpa only [topLayer] using htopOpening', by
                          simpa only [topLayer] using htopRun'⟩
                      · exact ⟨by simpa only [middleLayer] using hmiddleOpening', by
                          simpa only [middleLayer] using hmiddleRun'⟩
                      · exact ⟨by simpa only [bottomLayer, numLayers] using hbottomOpening', by
                          simpa only [bottomLayer, numLayers] using hbottomRun'⟩
                    · intro lay
                      fin_cases lay
                      · rw [show (⟨0, by decide⟩ : Layer) = topLayer by rfl, htopEval]
                        exact hverifierTop
                      · rw [show (⟨1, by decide⟩ : Layer) = middleLayer by rfl, hmiddleEval]
                        exact hverifierMiddle
                      · rw [show (⟨2, by decide⟩ : Layer) = bottomLayer by rfl, hbottomEval]
                        exact hverifierBottom
                    · intro lay
                      fin_cases lay
                      · simpa only [topLayer] using htopSettled
                      · unfold LayerRootSettled
                        simpa only [middleLayer] using hmiddleSettled
                      · unfold LayerRootSettled
                        simpa only [bottomLayer, numLayers] using hbottomSettled
                · exact Or.inr (Or.inl ⟨bottomLayer, ftsPublicKey, hbottomSettled,
                    hverifierBottom, hbottomOpening, hbottom.2.2.1, Or.inr hfailure⟩)
              · exact Or.inr (Or.inl ⟨bottomLayer, ftsPublicKey, hbottomSettled,
                  hverifierBottom, hbottomOpening, hbottom.2.2.1, Or.inl hsignedBottom⟩)
          · exact Or.inr (Or.inl ⟨middleLayer, middleMessage, hmiddleSettled,
              hverifierMiddle, hmiddleOpening, hmiddle.2.2.1, Or.inr hfailure⟩)
        · exact Or.inr (Or.inl ⟨middleLayer, middleMessage, hmiddleSettled,
            hverifierMiddle, hmiddleOpening, hmiddle.2.2.1, Or.inl hsignedMiddle⟩)
    · exact Or.inr (Or.inl ⟨topLayer, topMessage, htopSettled, hverifierTop, htopOpening,
        htopRun, Or.inr hfailure⟩)
  · exact Or.inr (Or.inl ⟨topLayer, topMessage, htopSettled, hverifierTop, htopOpening,
      htopRun, Or.inl hsignedTop⟩)

theorem winning_support_classify (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (finalCache : QueryCache HashSpec)
    (hwin : (true, finalCache) ∈ support ((simulateQ romImpl
      (gameAfterSecrets adversary parameter otsSecret ftsSecret)).run ∅)) :
    Bad parameter otsSecret ftsSecret finalCache
      ∨ ∃ root forgery signingLog f digest,
        let secretKey : SecretKey := ⟨parameter, root, otsSecret, ftsSecret⟩
        finalCache.AgreesWithFn f
          ∧ SigningTranscript.Valid signingLog
          ∧ ¬ SigningTranscript.Contains signingLog forgery
          ∧ evalWithAnswerFn f
              (messageDigest parameter root forgery.message forgery.signature.randomness) = digest
          ∧ Admissible digest
          ∧ (LayerObstacle f finalCache secretKey signingLog
            ∨ FewTimeLeak f finalCache secretKey signingLog (digestIndex digest)
                (digestLeaves digest)
            ∨ UncoveredFtsSecret f finalCache secretKey signingLog (digestIndex digest)
                (digestLeaves digest) forgery.signature.ftsSecret) := by
  obtain ⟨root, _, forgery, signingLog, _, _, _, _, hvalid, hnotContains, f, hf, _, _, _, _,
      hrootSettled,
      digest, hdigest, _, hadmissible, hftsRun, hresult⟩ :=
    winning_support_extract adversary parameter otsSecret ftsSecret finalCache hwin
  rcases hresult with hbad | htop
  · exact Or.inl hbad
  ·
    let index := digestIndex digest
    let leaves := digestLeaves digest
    let ftsPublicKey := evalWithAnswerFn f
      (ftsRecover parameter index leaves forgery.signature.ftsSecret forgery.signature.ftsPath)
    have hclassified := accepted_forgery_classify f finalCache
      (⟨parameter, root, otsSecret, ftsSecret⟩ : SecretKey) signingLog index forgery.signature leaves
      ftsPublicKey root hf rfl htop (by
        have htree : treeIndexAt index topLayer = rootTree := by
          apply Fin.ext
          exact treeIndexAt_topLayer index
        unfold LayerRootSettled
        rw [htree]
        simpa using hrootSettled) hftsRun
    rcases hclassified with hbad | hobstacle | hfts
    · exact Or.inl hbad
    · exact Or.inr ⟨root, forgery, signingLog, f, digest, hf, hvalid, hnotContains, hdigest,
        hadmissible, Or.inl hobstacle.toForgedLayerObstacle.toLayerObstacle⟩
    · rcases fewTimeLeak_or_uncovered f finalCache
          (⟨parameter, root, otsSecret, ftsSecret⟩ : SecretKey) signingLog index leaves with
        hleak | ⟨tree, huncovered⟩
      · exact Or.inr ⟨root, forgery, signingLog, f, digest, hf, hvalid, hnotContains, hdigest,
          hadmissible, Or.inr (Or.inl hleak)⟩
      · exact Or.inr ⟨root, forgery, signingLog, f, digest, hf, hvalid, hnotContains, hdigest,
          hadmissible, Or.inr (Or.inr ⟨tree, huncovered, (hfts.1.2.1 tree).1, by
            apply hftsRun
            exact ftsRecover_leaf_query_mem f parameter index leaves forgery.signature.ftsSecret
              forgery.signature.ftsPath tree⟩)⟩

end SphincsSecurity.Concrete
