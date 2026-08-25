import SphincsSecurity.Proof.Replay

/-!
# One-time terminal events

A layer obstacle is either an honest opening at a position the transcript never used, an encoding
collision at a used position, or a codeword that moves backward on at least one used chain.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

def FreshLayerOpening (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (signingLog : QueryLog SigningSpec) : Prop :=
  ∃ (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest)
      (counter : Counter) (values : ChainIndex → Digest) (path : Nat → Digest),
    HonestLayerOpening f secretKey.parameter secretKey.otsSecret lay tree leafIdx message counter
        values path
      ∧ CachedRun cache f (otsLeaf secretKey.parameter lay tree leafIdx message counter values)
      ∧ ¬ SignedLayerAt f cache secretKey signingLog lay tree leafIdx

def EncodingCollision (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (signingLog : QueryLog SigningSpec) : Prop :=
  ∃ (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (forgedMessage : Digest)
      (forgedCounter : Counter) (forgedValues : ChainIndex → Digest)
      (forgedPath : Nat → Digest)
      (entry : (request : SignRequest) × SigningSpec.Range request) (signature : Signature)
      (index : Index),
    CachedRun cache f (otsLeaf secretKey.parameter lay tree leafIdx forgedMessage forgedCounter
        forgedValues)
      ∧ HonestLayerOpening f secretKey.parameter secretKey.otsSecret lay tree leafIdx
          forgedMessage forgedCounter forgedValues forgedPath
      ∧ entry ∈ signingLog
      ∧ entry.2 = some signature
      ∧ SuccessfulSignRun f cache secretKey entry.1 signature
      ∧ treeIndexAt index lay = tree
      ∧ leafIndexAt index lay = leafIdx
      ∧ CachedRun cache f (layerMessage secretKey index lay)
      ∧ HonestLayerOpening f secretKey.parameter secretKey.otsSecret lay tree leafIdx
          (evalWithAnswerFn f (layerMessage secretKey index lay)) (signature.counter lay)
          (signature.chainValue lay) (signaturePath signature lay)
      ∧ cache (tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx)
        (digestBytes (evalWithAnswerFn f (layerMessage secretKey index lay)) ++
          counterBytes (signature.counter lay))) ≠ none
      ∧ EncodingHit f secretKey.parameter lay tree leafIdx
        (evalWithAnswerFn f (layerMessage secretKey index lay)) forgedMessage
        (signature.counter lay) forgedCounter

theorem EncodingCollision.reuses_values_and_path {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec}
    (hcollision : EncodingCollision f cache secretKey signingLog) :
    ∃ (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (forgedMessage : Digest)
        (forgedCounter : Counter) (forgedValues : ChainIndex → Digest)
        (forgedPath : Nat → Digest) (signature : Signature) (index : Index),
      treeIndexAt index lay = tree
        ∧ leafIndexAt index lay = leafIdx
        ∧ (evalWithAnswerFn f (layerMessage secretKey index lay) ≠ forgedMessage
          ∨ signature.counter lay ≠ forgedCounter)
        ∧ signature.chainValue lay = forgedValues
        ∧ ∀ level, level < layerHeight lay →
          signaturePath signature lay level = forgedPath level := by
  obtain ⟨lay, tree, leafIdx, forgedMessage, forgedCounter, forgedValues, forgedPath, _,
    signature, index, _, hforgedOpening, _, _, _, htree, hleaf, _, hsignedOpening, _, hhit⟩ :=
    hcollision
  have hreused := honestLayerOpening_values_path_eq_of_encodingHit f secretKey.parameter
    secretKey.otsSecret lay tree leafIdx
    (evalWithAnswerFn f (layerMessage secretKey index lay)) forgedMessage
    (signature.counter lay) forgedCounter (signature.chainValue lay) forgedValues
    (signaturePath signature lay) forgedPath hsignedOpening hforgedOpening hhit
  have hdifferent : evalWithAnswerFn f (layerMessage secretKey index lay) ≠ forgedMessage
      ∨ signature.counter lay ≠ forgedCounter := by
    by_contra hequal
    simp only [not_or, not_ne_iff] at hequal
    apply hhit.1
    rw [hequal.1, hequal.2]
  exact ⟨lay, tree, leafIdx, forgedMessage, forgedCounter, forgedValues, forgedPath, signature,
    index, htree, hleaf, hdifferent, hreused⟩

def BackwardChainOpening (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (signingLog : QueryLog SigningSpec) : Prop :=
  ∃ (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (forgedMessage : Digest)
      (forgedCounter : Counter) (forgedValues : ChainIndex → Digest) (forgedPath : Nat → Digest)
      (entry : (request : SignRequest) × SigningSpec.Range request) (signature : Signature)
      (index : Index) (signedCodeword forgedCodeword : Encoding),
    HonestLayerOpening f secretKey.parameter secretKey.otsSecret lay tree leafIdx forgedMessage
        forgedCounter forgedValues forgedPath
      ∧ CachedRun cache f (otsLeaf secretKey.parameter lay tree leafIdx forgedMessage forgedCounter
        forgedValues)
      ∧ entry ∈ signingLog
      ∧ entry.2 = some signature
      ∧ SuccessfulSignRun f cache secretKey entry.1 signature
      ∧ treeIndexAt index lay = tree
      ∧ leafIndexAt index lay = leafIdx
      ∧ CachedRun cache f (layerMessage secretKey index lay)
      ∧ HonestLayerOpening f secretKey.parameter secretKey.otsSecret lay tree leafIdx
          (evalWithAnswerFn f (layerMessage secretKey index lay)) (signature.counter lay)
          (signature.chainValue lay) (signaturePath signature lay)
      ∧ cache (tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx)
        (digestBytes (evalWithAnswerFn f (layerMessage secretKey index lay)) ++
          counterBytes (signature.counter lay))) ≠ none
      ∧ evalWithAnswerFn f (encode secretKey.parameter lay tree leafIdx
          (evalWithAnswerFn f (layerMessage secretKey index lay)) (signature.counter lay))
          = some signedCodeword
      ∧ evalWithAnswerFn f
          (encode secretKey.parameter lay tree leafIdx forgedMessage forgedCounter)
          = some forgedCodeword
      ∧ ∃ chainIdx, (forgedCodeword chainIdx).val < (signedCodeword chainIdx).val

theorem layerObstacle_classify (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (signingLog : QueryLog SigningSpec)
    (hobstacle : LayerObstacle f cache secretKey signingLog) :
    FreshLayerOpening f cache secretKey signingLog
      ∨ EncodingCollision f cache secretKey signingLog
      ∨ BackwardChainOpening f cache secretKey signingLog := by
  obtain ⟨lay, tree, leafIdx, message, counter, values, path, hopening, hforgedRun,
      hfresh | hfailure⟩ :=
    hobstacle
  · exact Or.inl ⟨lay, tree, leafIdx, message, counter, values, path, hopening, hforgedRun, hfresh⟩
  · obtain ⟨entry, signature, index, hentry, hresponse, hsignRun, htree, hleaf,
        hmessage, hsignedOpening, hsignedCached, hencoding | hearlier⟩ := hfailure
    · exact Or.inr (Or.inl ⟨lay, tree, leafIdx, message, counter, values, path, entry, signature,
        index, hforgedRun, hopening, hentry, hresponse, hsignRun, htree, hleaf,
        hmessage, hsignedOpening, hsignedCached, hencoding⟩)
    · obtain ⟨signedCodeword, forgedCodeword, hsigned, hforged, hchain⟩ := hearlier
      exact Or.inr (Or.inr ⟨lay, tree, leafIdx, message, counter, values, path, entry,
        signature, index, signedCodeword, forgedCodeword, hopening, hforgedRun, hentry, hresponse,
        hsignRun, htree, hleaf, hmessage, hsignedOpening, hsignedCached, hsigned, hforged,
        hchain⟩)

def TerminalForgeryEvent (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (signingLog : QueryLog SigningSpec) (forgery : Forgery)
    (index : Index) (leaves : DigestTree → FtsLeaf) : Prop :=
  FreshLayerOpening f cache secretKey signingLog
    ∨ EncodingCollision f cache secretKey signingLog
    ∨ BackwardChainOpening f cache secretKey signingLog
    ∨ MessageDigestCollision f cache secretKey signingLog forgery
    ∨ ProperFewTimeLeak f cache secretKey signingLog index leaves
    ∨ UncoveredFtsSecret f cache secretKey signingLog index leaves forgery.signature.ftsSecret

theorem winning_support_terminal_classify (adversary : Adversary)
    (parameter : PublicParameter)
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
          ∧ TerminalForgeryEvent f finalCache secretKey signingLog forgery
              (digestIndex digest) (digestLeaves digest) := by
  obtain ⟨root, _, forgery, signingLog, _, _, _, _, hvalid, hnotContains, f, hf, _, _, _, _, _,
      digest, hdigest, hdigestRun, hadmissible, hftsRun, hresult⟩ :=
    winning_support_extract adversary parameter otsSecret ftsSecret finalCache hwin
  rcases hresult with hbad | htop
  · exact Or.inl hbad
  · let secretKey : SecretKey := ⟨parameter, root, otsSecret, ftsSecret⟩
    let index := digestIndex digest
    let leaves := digestLeaves digest
    let ftsPublicKey := evalWithAnswerFn f
      (ftsRecover parameter index leaves forgery.signature.ftsSecret forgery.signature.ftsPath)
    have hclassified := accepted_forgery_classify f finalCache secretKey signingLog index
      forgery.signature leaves ftsPublicKey root hf rfl htop hftsRun
    rcases hclassified with hbad | hobstacle | hfull
    · exact Or.inl hbad
    · rcases layerObstacle_classify f finalCache secretKey signingLog hobstacle with
        hfresh | hencoding | hbackward
      · exact Or.inr ⟨root, forgery, signingLog, f, digest, hf, hvalid, hnotContains, hdigest,
          hadmissible, Or.inl hfresh⟩
      · exact Or.inr ⟨root, forgery, signingLog, f, digest, hf, hvalid, hnotContains, hdigest,
          hadmissible, Or.inr (Or.inl hencoding)⟩
      · exact Or.inr ⟨root, forgery, signingLog, f, digest, hf, hvalid, hnotContains, hdigest,
          hadmissible, Or.inr (Or.inr (Or.inl hbackward))⟩
    · rcases fewTimeLeak_or_uncovered f finalCache secretKey signingLog index leaves with
        hleak | ⟨tree, huncovered⟩
      · rcases fullyHonest_leak_classify f finalCache secretKey signingLog forgery digest index
            leaves hdigest hdigestRun rfl rfl hfull hnotContains hleak with
          hcollision | hobstacle | hproper
        · exact Or.inr ⟨root, forgery, signingLog, f, digest, hf, hvalid, hnotContains, hdigest,
            hadmissible, Or.inr (Or.inr (Or.inr (Or.inl hcollision)))⟩
        · rcases layerObstacle_classify f finalCache secretKey signingLog hobstacle with
            hfresh | hencoding | hbackward
          · exact Or.inr ⟨root, forgery, signingLog, f, digest, hf, hvalid, hnotContains, hdigest,
              hadmissible, Or.inl hfresh⟩
          · exact Or.inr ⟨root, forgery, signingLog, f, digest, hf, hvalid, hnotContains, hdigest,
              hadmissible, Or.inr (Or.inl hencoding)⟩
          · exact Or.inr ⟨root, forgery, signingLog, f, digest, hf, hvalid, hnotContains, hdigest,
              hadmissible, Or.inr (Or.inr (Or.inl hbackward))⟩
        · exact Or.inr ⟨root, forgery, signingLog, f, digest, hf, hvalid, hnotContains, hdigest,
            hadmissible, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hproper))))⟩
      · exact Or.inr ⟨root, forgery, signingLog, f, digest, hf, hvalid, hnotContains, hdigest,
          hadmissible, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨tree, huncovered, (hfull.2.1 tree).1, by
              apply hfull.2.2
              exact ftsRecover_leaf_query_mem f parameter index leaves forgery.signature.ftsSecret
                forgery.signature.ftsPath tree⟩))))⟩

end SphincsSecurity.Concrete
