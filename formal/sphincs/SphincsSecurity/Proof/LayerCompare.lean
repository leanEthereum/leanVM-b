import SphincsSecurity.Proof.EncodingCached

/-!
# Comparing honest layer openings

Two honest openings at the same one-time position either agree on the signed layer component, use
distinct encoding inputs with the same digest, or the forged codeword starts earlier on some chain.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

def EncodingHit (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leafIdx : LeafIndex) (leftMessage rightMessage : Digest)
    (leftCounter rightCounter : Counter) : Prop :=
  let leftInput := tweakableHashInput parameter (.encoding lay tree leafIdx)
    (digestBytes leftMessage ++ counterBytes leftCounter)
  let rightInput := tweakableHashInput parameter (.encoding lay tree leafIdx)
    (digestBytes rightMessage ++ counterBytes rightCounter)
  leftInput ≠ rightInput ∧ truncateHash (f leftInput) = truncateHash (f rightInput)

theorem decode_of_eval_encode_eq_some (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest)
    (counter : Counter) (codeword : Encoding)
    (hencode : evalWithAnswerFn f (encode parameter lay tree leafIdx message counter)
      = some codeword) :
    TargetSum.decodeDigest (truncateHash (f (tweakableHashInput parameter
      (.encoding lay tree leafIdx) (digestBytes message ++ counterBytes counter))))
        = some codeword := by
  simpa only [encode, evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_tweakableHash] using hencode

theorem valid_of_eval_encode_eq_some (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest)
    (counter : Counter) (codeword : Encoding)
    (hencode : evalWithAnswerFn f (encode parameter lay tree leafIdx message counter)
      = some codeword) : TargetSum.Valid codeword :=
  TargetSum.valid_of_decodeDigest_eq_some
    (decode_of_eval_encode_eq_some f parameter lay tree leafIdx message counter codeword hencode)

theorem honestLayerOpening_compare (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (leftMessage rightMessage : Digest)
    (leftCounter rightCounter : Counter) (leftValues rightValues : ChainIndex → Digest)
    (leftPath rightPath : Nat → Digest)
    (hleft : HonestLayerOpening f parameter otsSecret lay tree leafIdx leftMessage leftCounter
      leftValues leftPath)
    (hright : HonestLayerOpening f parameter otsSecret lay tree leafIdx rightMessage rightCounter
      rightValues rightPath) :
    (leftMessage = rightMessage ∧ leftCounter = rightCounter ∧ leftValues = rightValues
        ∧ ∀ level, level < layerHeight lay → leftPath level = rightPath level)
      ∨ EncodingHit f parameter lay tree leafIdx leftMessage rightMessage leftCounter rightCounter
      ∨ ∃ leftCodeword rightCodeword,
        evalWithAnswerFn f (encode parameter lay tree leafIdx leftMessage leftCounter)
            = some leftCodeword
          ∧ evalWithAnswerFn f (encode parameter lay tree leafIdx rightMessage rightCounter)
            = some rightCodeword
          ∧ ∃ chainIdx, (rightCodeword chainIdx).val < (leftCodeword chainIdx).val := by
  obtain ⟨leftCodeword, hleftEncode, hleftValues, hleftPath⟩ := hleft
  obtain ⟨rightCodeword, hrightEncode, hrightValues, hrightPath⟩ := hright
  by_cases hcodeword : leftCodeword = rightCodeword
  · subst rightCodeword
    let leftInput := tweakableHashInput parameter (.encoding lay tree leafIdx)
      (digestBytes leftMessage ++ counterBytes leftCounter)
    let rightInput := tweakableHashInput parameter (.encoding lay tree leafIdx)
      (digestBytes rightMessage ++ counterBytes rightCounter)
    by_cases hinput : leftInput = rightInput
    · have hpayload := (tweakableHashInput_injective parameter (by trivial) (by trivial) hinput).2
      obtain ⟨hmessageBytes, hcounterBytes⟩ :=
        List.append_inj hpayload (by simp [digestBytes_length])
      have hmessage := digestBytes_injective hmessageBytes
      have hcounter := bytesLE_injective hcounterBytes
      left
      refine ⟨hmessage, hcounter, ?_, ?_⟩
      · funext chainIdx
        rw [hleftValues chainIdx, hrightValues chainIdx]
      · intro level hlevel
        rw [hleftPath level hlevel, hrightPath level hlevel]
    · right
      left
      have hleftDecode := decode_of_eval_encode_eq_some f parameter lay tree leafIdx leftMessage
        leftCounter leftCodeword hleftEncode
      have hrightDecode := decode_of_eval_encode_eq_some f parameter lay tree leafIdx rightMessage
        rightCounter leftCodeword hrightEncode
      exact ⟨hinput, TargetSum.decodeDigest_some_injective hleftDecode hrightDecode⟩
  · right
    right
    refine ⟨leftCodeword, rightCodeword, hleftEncode, hrightEncode, ?_⟩
    by_contra hnot
    have hnot' : ∀ chainIdx,
        ¬ (rightCodeword chainIdx).val < (leftCodeword chainIdx).val :=
      not_exists.mp hnot
    have hle : ∀ chainIdx, (leftCodeword chainIdx).val ≤ (rightCodeword chainIdx).val := by
      intro chainIdx
      exact Nat.le_of_not_gt (hnot' chainIdx)
    exact hcodeword (TargetSum.eq_of_le_of_valid
      (valid_of_eval_encode_eq_some f parameter lay tree leafIdx leftMessage leftCounter leftCodeword
        hleftEncode)
      (valid_of_eval_encode_eq_some f parameter lay tree leafIdx rightMessage rightCounter rightCodeword
        hrightEncode) hle)

theorem honestLayerOpening_values_path_eq_of_encodingHit
    (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (leftMessage rightMessage : Digest) (leftCounter rightCounter : Counter)
    (leftValues rightValues : ChainIndex → Digest) (leftPath rightPath : Nat → Digest)
    (hleft : HonestLayerOpening f parameter otsSecret lay tree leafIdx leftMessage leftCounter
      leftValues leftPath)
    (hright : HonestLayerOpening f parameter otsSecret lay tree leafIdx rightMessage rightCounter
      rightValues rightPath)
    (hhit : EncodingHit f parameter lay tree leafIdx leftMessage rightMessage
      leftCounter rightCounter) :
    leftValues = rightValues ∧
      ∀ level, level < layerHeight lay → leftPath level = rightPath level := by
  obtain ⟨leftCodeword, hleftEncode, hleftValues, hleftPath⟩ := hleft
  obtain ⟨rightCodeword, hrightEncode, hrightValues, hrightPath⟩ := hright
  have hleftDecode := decode_of_eval_encode_eq_some f parameter lay tree leafIdx leftMessage
    leftCounter leftCodeword hleftEncode
  have hrightDecode := decode_of_eval_encode_eq_some f parameter lay tree leafIdx rightMessage
    rightCounter rightCodeword hrightEncode
  change _ ≠ _ ∧ truncateHash (f _) = truncateHash (f _) at hhit
  rw [hhit.2] at hleftDecode
  have hcodeword : leftCodeword = rightCodeword :=
    Option.some.inj (hleftDecode.symm.trans hrightDecode)
  constructor
  · funext chainIdx
    rw [hleftValues chainIdx, hrightValues chainIdx, hcodeword]
  · intro level hlevel
    rw [hleftPath level hlevel, hrightPath level hlevel]

def SignedLayerAt (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (signingLog : QueryLog SigningSpec) (lay : Layer)
    (tree : TreeIndex) (leafIdx : LeafIndex) : Prop :=
  ∃ (entry : (request : SignRequest) × SigningSpec.Range request) (signature : Signature)
      (index : Index),
    entry ∈ signingLog
      ∧ entry.2 = some signature
      ∧ SuccessfulSignRun f cache secretKey entry.1 signature
      ∧ treeIndexAt index lay = tree
      ∧ leafIndexAt index lay = leafIdx
      ∧ CachedRun cache f (layerMessage secretKey index lay)
      ∧ cache (tweakableHashInput secretKey.parameter
        (.encoding lay (treeIndexAt index lay) (leafIndexAt index lay))
        (digestBytes (evalWithAnswerFn f (layerMessage secretKey index lay)) ++
          counterBytes (signature.counter lay))) ≠ none
      ∧ HonestLayerOpening f secretKey.parameter secretKey.otsSecret lay
        (treeIndexAt index lay) (leafIndexAt index lay)
        (evalWithAnswerFn f (layerMessage secretKey index lay)) (signature.counter lay)
        (signature.chainValue lay) (signaturePath signature lay)

def LayerComparisonFailure (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (signingLog : QueryLog SigningSpec) (lay : Layer)
    (tree : TreeIndex) (leafIdx : LeafIndex) (forgedMessage : Digest)
    (forgedCounter : Counter) : Prop :=
  ∃ (entry : (request : SignRequest) × SigningSpec.Range request) (signature : Signature)
      (index : Index),
    entry ∈ signingLog
      ∧ entry.2 = some signature
      ∧ SuccessfulSignRun f cache secretKey entry.1 signature
      ∧ treeIndexAt index lay = tree
      ∧ leafIndexAt index lay = leafIdx
      ∧ CachedRun cache f (layerMessage secretKey index lay)
      ∧ HonestLayerOpening f secretKey.parameter secretKey.otsSecret lay tree leafIdx
          (evalWithAnswerFn f (layerMessage secretKey index lay)) (signature.counter lay)
          (signature.chainValue lay) (signaturePath signature lay)
      ∧ cache (tweakableHashInput secretKey.parameter
        (.encoding lay tree leafIdx)
        (digestBytes (evalWithAnswerFn f (layerMessage secretKey index lay)) ++
          counterBytes (signature.counter lay))) ≠ none
      ∧ (EncodingHit f secretKey.parameter lay tree leafIdx
            (evalWithAnswerFn f (layerMessage secretKey index lay)) forgedMessage
            (signature.counter lay) forgedCounter
        ∨ ∃ signedCodeword forgedCodeword,
          evalWithAnswerFn f (encode secretKey.parameter lay tree leafIdx
              (evalWithAnswerFn f (layerMessage secretKey index lay)) (signature.counter lay))
              = some signedCodeword
            ∧ evalWithAnswerFn f (encode secretKey.parameter lay tree leafIdx
              forgedMessage forgedCounter) = some forgedCodeword
            ∧ ∃ chainIdx, (forgedCodeword chainIdx).val < (signedCodeword chainIdx).val)

theorem signedLayerAt_of_signing_entry (f : QueryImpl HashSpec Id)
    (secretKey : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) alpha)
    (initialCache : QueryCache HashSpec) (value : alpha) (signingLog : QueryLog SigningSpec)
    (adversaryCache finalCache : QueryCache HashSpec)
    (hmem : ((value, signingLog), adversaryCache) ∈ support
      ((simulateQ romImpl
        ((simulateQ (forwardOracles + signingOracle scheme secretKey)
          computation).run)).run initialCache))
    (hle : adversaryCache ≤ finalCache) (hf : finalCache.AgreesWithFn f)
    (entry : (request : SignRequest) × SigningSpec.Range request) (signature : Signature)
    (hresponse : entry.2 = some signature) (hentry : entry ∈ signingLog) (lay : Layer) :
    ∃ index, SignedLayerAt f finalCache secretKey signingLog lay
      (treeIndexAt index lay) (leafIndexAt index lay) := by
  have hrun := successfulSignRun_of_signing_entry f secretKey computation initialCache value
    signingLog adversaryCache finalCache hmem hle hf entry signature hresponse hentry
  obtain ⟨index, leaves, hfts⟩ := hrun.honest_fts_at
  obtain ⟨hmessage, hopening⟩ := hrun.honest_layer_at_of_digest hfts.1 lay
  have hencoding := hrun.signed_encode_cached_of_digest hfts.1 lay
  exact ⟨index, entry, signature, index, hentry, hresponse, hrun, rfl, rfl, hmessage,
    hencoding, hopening⟩

theorem SignedLayerAt.compare_forgery {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {signingLog : QueryLog SigningSpec}
    {lay : Layer} {tree : TreeIndex} {leafIdx : LeafIndex}
    (hsigned : SignedLayerAt f cache secretKey signingLog lay tree leafIdx)
    (forgedMessage : Digest) (forgedCounter : Counter)
    (forgedValues : ChainIndex → Digest) (forgedPath : Nat → Digest)
    (hforged : HonestLayerOpening f secretKey.parameter secretKey.otsSecret lay tree leafIdx
      forgedMessage forgedCounter forgedValues forgedPath) :
    ∃ (entry : (request : SignRequest) × SigningSpec.Range request) (signature : Signature)
        (index : Index),
      entry ∈ signingLog
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
        ∧ ((evalWithAnswerFn f (layerMessage secretKey index lay) = forgedMessage
              ∧ signature.counter lay = forgedCounter
              ∧ signature.chainValue lay = forgedValues
              ∧ ∀ level, level < layerHeight lay →
                signaturePath signature lay level = forgedPath level)
          ∨ EncodingHit f secretKey.parameter lay tree leafIdx
              (evalWithAnswerFn f (layerMessage secretKey index lay)) forgedMessage
              (signature.counter lay) forgedCounter
          ∨ ∃ signedCodeword forgedCodeword,
            evalWithAnswerFn f (encode secretKey.parameter lay tree leafIdx
                (evalWithAnswerFn f (layerMessage secretKey index lay)) (signature.counter lay))
                = some signedCodeword
              ∧ evalWithAnswerFn f (encode secretKey.parameter lay tree leafIdx
                forgedMessage forgedCounter) = some forgedCodeword
              ∧ ∃ chainIdx, (forgedCodeword chainIdx).val < (signedCodeword chainIdx).val) := by
  obtain ⟨entry, signature, index, hentry, hresponse, hrun, htree, hleaf, hmessage, hencoding,
    hopening⟩ := hsigned
  have hopening' : HonestLayerOpening f secretKey.parameter secretKey.otsSecret lay tree leafIdx
      (evalWithAnswerFn f (layerMessage secretKey index lay)) (signature.counter lay)
      (signature.chainValue lay) (signaturePath signature lay) := by
    simpa only [htree, hleaf] using hopening
  rw [htree, hleaf] at hencoding
  exact ⟨entry, signature, index, hentry, hresponse, hrun, htree, hleaf, hmessage, hopening',
    hencoding,
    honestLayerOpening_compare f secretKey.parameter secretKey.otsSecret lay tree leafIdx
      (evalWithAnswerFn f (layerMessage secretKey index lay)) forgedMessage
      (signature.counter lay) forgedCounter (signature.chainValue lay) forgedValues
      (signaturePath signature lay) forgedPath hopening' hforged⟩

theorem SignedLayerAt.exact_or_failure {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {signingLog : QueryLog SigningSpec}
    {lay : Layer} {tree : TreeIndex} {leafIdx : LeafIndex}
    (hsigned : SignedLayerAt f cache secretKey signingLog lay tree leafIdx)
    (forgedMessage : Digest) (forgedCounter : Counter)
    (forgedValues : ChainIndex → Digest) (forgedPath : Nat → Digest)
    (hforged : HonestLayerOpening f secretKey.parameter secretKey.otsSecret lay tree leafIdx
      forgedMessage forgedCounter forgedValues forgedPath) :
    (∃ (entry : (request : SignRequest) × SigningSpec.Range request)
        (signature : Signature) (index : Index),
      entry ∈ signingLog
        ∧ entry.2 = some signature
        ∧ SuccessfulSignRun f cache secretKey entry.1 signature
        ∧ treeIndexAt index lay = tree
        ∧ leafIndexAt index lay = leafIdx
        ∧ evalWithAnswerFn f (layerMessage secretKey index lay) = forgedMessage
        ∧ signature.counter lay = forgedCounter
        ∧ signature.chainValue lay = forgedValues
        ∧ ∀ level, level < layerHeight lay →
          signaturePath signature lay level = forgedPath level)
      ∨ LayerComparisonFailure f cache secretKey signingLog lay tree leafIdx
        forgedMessage forgedCounter := by
  obtain ⟨entry, signature, index, hentry, hresponse, hrun, htree, hleaf, hmessage,
    hopening, hcached, hresult⟩ :=
    hsigned.compare_forgery forgedMessage forgedCounter forgedValues forgedPath hforged
  rcases hresult with hexact | hencoding | hearlier
  · exact Or.inl ⟨entry, signature, index, hentry, hresponse, hrun, htree, hleaf, hexact⟩
  · exact Or.inr ⟨entry, signature, index, hentry, hresponse, hrun,
      htree, hleaf, hmessage, hopening, hcached, Or.inl hencoding⟩
  · exact Or.inr ⟨entry, signature, index, hentry, hresponse, hrun,
      htree, hleaf, hmessage, hopening, hcached, Or.inr hearlier⟩

theorem SignedLayerAt.settles_middle {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {signingLog : QueryLog SigningSpec}
    {forgedIndex : Index}
    (hf : cache.AgreesWithFn f)
    (hsigned : SignedLayerAt f cache secretKey signingLog topLayer
      (treeIndexAt forgedIndex topLayer) (leafIndexAt forgedIndex topLayer)) :
    Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
      (.node middleLayer (treeIndexAt forgedIndex middleLayer)
        ⟨layerHeight middleLayer - 1, by decide⟩ ⟨0, by positivity⟩) := by
  obtain ⟨_, _, signedIndex, _, _, _, htree, hleaf, hcached, _⟩ := hsigned
  have hnext : treeIndexAt signedIndex middleLayer = treeIndexAt forgedIndex middleLayer := by
    apply Fin.ext
    rw [layers_link_top signedIndex, layers_link_top forgedIndex]
    rw [congrArg Fin.val htree, congrArg Fin.val hleaf]
  rw [layerMessage_of_lt secretKey signedIndex topLayer (by decide)] at hcached
  have hsettled := settled_treeRoot_of_cachedRun (ftsSecret := secretKey.ftsSecret) hf middleLayer
    (treeIndexAt signedIndex middleLayer) (by
      simpa only [show (⟨topLayer.val + 1, by decide⟩ : Layer) = middleLayer from rfl] using hcached)
  simpa only [hnext] using hsettled

theorem SignedLayerAt.settles_bottom {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {signingLog : QueryLog SigningSpec}
    {forgedIndex : Index}
    (hf : cache.AgreesWithFn f)
    (hsigned : SignedLayerAt f cache secretKey signingLog middleLayer
      (treeIndexAt forgedIndex middleLayer) (leafIndexAt forgedIndex middleLayer)) :
    Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
      (.node bottomLayer (treeIndexAt forgedIndex bottomLayer)
        ⟨layerHeight bottomLayer - 1, by decide⟩ ⟨0, by positivity⟩) := by
  obtain ⟨_, _, signedIndex, _, _, _, htree, hleaf, hcached, _⟩ := hsigned
  have hnext : treeIndexAt signedIndex bottomLayer = treeIndexAt forgedIndex bottomLayer := by
    apply Fin.ext
    rw [layers_link_middle signedIndex, layers_link_middle forgedIndex]
    rw [congrArg Fin.val htree, congrArg Fin.val hleaf]
  rw [layerMessage_of_lt secretKey signedIndex middleLayer (by decide)] at hcached
  have hsettled := settled_treeRoot_of_cachedRun (ftsSecret := secretKey.ftsSecret) hf bottomLayer
    (treeIndexAt signedIndex bottomLayer) (by
      simpa only [show (⟨middleLayer.val + 1, by decide⟩ : Layer) = bottomLayer from rfl] using hcached)
  simpa only [hnext] using hsettled

theorem SignedLayerAt.settles_fts {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey} {signingLog : QueryLog SigningSpec}
    {forgedIndex : Index}
    (hf : cache.AgreesWithFn f)
    (hsigned : SignedLayerAt f cache secretKey signingLog bottomLayer
      (treeIndexAt forgedIndex bottomLayer) (leafIndexAt forgedIndex bottomLayer)) :
    Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
      (.ftsRoots forgedIndex) := by
  obtain ⟨_, _, signedIndex, _, _, _, htree, hleaf, hcached, _⟩ := hsigned
  have hindex := index_eq_of_bottom_position_eq htree hleaf
  subst signedIndex
  rw [layerMessage_bottomLayer secretKey forgedIndex] at hcached
  exact settled_ftsRoots_of_cachedRun (otsSecret := secretKey.otsSecret) hf forgedIndex hcached

end SphincsSecurity.Concrete
