import SphincsSecurity.Proof.RetainedCollisionCache
import SphincsSecurity.Proof.ForgeryClassify

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

theorem LayerFrame.mono_cache
    {f : QueryImpl HashSpec Id} {cache cache' : QueryCache HashSpec}
    {parameter : PublicParameter} {index : Index} {signature : Signature}
    {lay : Layer} {message target leafValue : Digest}
    (hle : cache ≤ cache')
    (hframe : LayerFrame f cache parameter index signature lay message target leafValue) :
    LayerFrame f cache' parameter index signature lay message target leafValue :=
  ⟨hframe.1, hframe.2.1, hframe.2.2.1.mono hle,
    hframe.2.2.2.1.mono hle, hframe.2.2.2.2.mono hle⟩

theorem accepted_forgery_classify_retained (f : QueryImpl HashSpec Id) (cache retained : QueryCache HashSpec)
    (secretKey : SecretKey) (signingLog : QueryLog SigningSpec) (index : Index)
    (signature : Signature) (leaves : DigestTree → FtsLeaf) (ftsPublicKey root : Digest)
    (hf : cache.AgreesWithFn f) (hle : retained ≤ cache)
    (hpreserved : ∀ position,
      Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache position →
      Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret retained position)
    (hftsPublicKey : evalWithAnswerFn f
      (ftsRecover secretKey.parameter index leaves signature.ftsSecret signature.ftsPath)
        = ftsPublicKey)
    (htop : HypertreeTopOpening f retained secretKey.parameter secretKey.otsSecret index signature
      ftsPublicKey root)
    (htopSettled : LayerRootSettled cache secretKey topLayer
      (treeIndexAt index topLayer))
    (hftsRun : CachedRun retained f
      (ftsRecover secretKey.parameter index leaves signature.ftsSecret signature.ftsPath)) :
    Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret retained
      ∨ SettledForgedLayerObstacle f cache secretKey signingLog index leaves signature
      ∨ SettledFullyHonestOpening f cache secretKey index leaves signature := by
  obtain ⟨bottomLeaf, hbottomSmall, middleLeaf, hmiddleSmall, htopOpening, htopRunSmall⟩ := htop
  have hbottom := LayerFrame.mono_cache hle hbottomSmall
  have hmiddle := LayerFrame.mono_cache hle hmiddleSmall
  have htopRun := htopRunSmall.mono hle
  have hfSmall : retained.AgreesWithFn f := fun _ _ hcached => hf (hle hcached)
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
      rcases layer_extract_from_settled_root_or_bad (ftsSecret := secretKey.ftsSecret) hfSmall middleLayer
          (treeIndexAt index middleLayer) (leafIndexAt index middleLayer)
          (leafIndexAt_lt index middleLayer) middleMessage (signature.counter middleLayer)
          (signature.chainValue middleLayer) (signaturePath signature middleLayer) middleLeaf
          hmiddle.1 (by simpa only [topMessage] using hmiddleRoot)
          hmiddleSmall.2.2.1 hmiddleSmall.2.2.2.1 (hpreserved _ hmiddleSettled) with hbad | hmiddleOpening
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
            rcases layer_extract_from_settled_root_or_bad (ftsSecret := secretKey.ftsSecret) hfSmall
                bottomLayer (treeIndexAt index bottomLayer) (leafIndexAt index bottomLayer)
                (leafIndexAt_lt index bottomLayer) ftsPublicKey (signature.counter bottomLayer)
                (signature.chainValue bottomLayer) (signaturePath signature bottomLayer) bottomLeaf
                hbottom.1 (by simpa only [middleMessage] using hbottomRoot)
                hbottomSmall.2.2.1 hbottomSmall.2.2.2.1 (hpreserved _ hbottomSettled) with hbad | hbottomOpening
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
                  rcases ftsRecover_extract_from_settled_roots_or_bad hfSmall index leaves
                      signature.ftsSecret signature.ftsPath (hftsPublicKey.trans hftsKey) hftsRun
                      (hpreserved _ hftsSettled) with hbad | hhonest
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
                    refine ⟨⟨?_, hhonest, hftsRun.mono hle, ?_⟩, ?_⟩
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

end SphincsSecurity.Concrete
