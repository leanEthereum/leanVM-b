import SphincsSecurity.Proof.OneTimeEvents

/-!
# Cache witnesses for terminal events

Terminal classifications retain the executions that produced their oracle values. This module turns
those executions into concrete cache events for the probability bounds.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

def EncodingCacheCollision (parameter : PublicParameter) (cache : QueryCache HashSpec) : Prop :=
  ∃ (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
      (leftPayload rightPayload : HashInput) (leftAnswer rightAnswer : HashOutput),
    leftPayload ≠ rightPayload
      ∧ cache (tweakableHashInput parameter (.encoding lay tree leafIdx) leftPayload)
          = some leftAnswer
      ∧ cache (tweakableHashInput parameter (.encoding lay tree leafIdx) rightPayload)
          = some rightAnswer
      ∧ truncateHash leftAnswer = truncateHash rightAnswer

def MessageCacheCollision (parameter : PublicParameter) (cache : QueryCache HashSpec) : Prop :=
  ∃ (leftPayload rightPayload : HashInput) (leftAnswer rightAnswer : HashOutput),
    leftPayload ≠ rightPayload
      ∧ cache (tweakableHashInput parameter .message leftPayload) = some leftAnswer
      ∧ cache (tweakableHashInput parameter .message rightPayload) = some rightAnswer
      ∧ truncateMessageDigest leftAnswer = truncateMessageDigest rightAnswer

theorem encodingCollision_cacheCollision {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} (hf : cache.AgreesWithFn f)
    (hcollision : EncodingCollision f cache secretKey signingLog) :
    EncodingCacheCollision secretKey.parameter cache := by
  obtain ⟨lay, tree, leafIdx, forgedMessage, forgedCounter, _, _, entry, signature, index, _,
    hforgedCached, _, _, _, _, _, _, _, _, _, hsignedCached, hhit⟩ := hcollision
  let signedPayload := digestBytes (evalWithAnswerFn f (layerMessage secretKey index lay)) ++
    counterBytes (signature.counter lay)
  let forgedPayload := digestBytes forgedMessage ++ counterBytes forgedCounter
  let signedInput := tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx) signedPayload
  let forgedInput := tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx) forgedPayload
  obtain ⟨signedAnswer, hsignedAnswer⟩ := Option.ne_none_iff_exists'.mp hsignedCached
  have hforgedCached' : cache forgedInput ≠ none := by
    exact CachedRun.otsLeaf_encode_cached hforgedCached
  obtain ⟨forgedAnswer, hforgedAnswer⟩ := Option.ne_none_iff_exists'.mp hforgedCached'
  change signedInput ≠ forgedInput ∧ truncateHash (f signedInput) = truncateHash (f forgedInput)
    at hhit
  refine ⟨lay, tree, leafIdx, signedPayload, forgedPayload, signedAnswer, forgedAnswer, ?_,
    hsignedAnswer, hforgedAnswer, ?_⟩
  · exact fun heq => hhit.1 (congrArg
      (tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx)) heq)
  · rw [← hf hsignedAnswer, ← hf hforgedAnswer]
    exact hhit.2

theorem CachedRun.messageDigest_cached {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {parameter : PublicParameter} {root : Digest}
    {message : Message} {randomness : Randomness}
    (hrun : CachedRun cache f (messageDigest parameter root message randomness)) :
    cache (tweakableHashInput parameter .message
      (messageDigestPayload root message randomness)) ≠ none := by
  apply hrun
  rw [messageDigest]
  apply queriedInputs_mono_bind_left
  change tweakableHashInput parameter .message
      (messageDigestPayload root message randomness) ∈
    [tweakableHashInput parameter .message (messageDigestPayload root message randomness)]
  simp

theorem messageDigestCollision_cacheCollision {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {forgery : Forgery}
    (hf : cache.AgreesWithFn f)
    (hcollision : MessageDigestCollision f cache secretKey signingLog forgery) :
    MessageCacheCollision secretKey.parameter cache := by
  obtain ⟨entry, signature, _, _, hsignRun, hforgedRun, hinput, hvalue⟩ := hcollision
  obtain ⟨_, _, _, hsignedDigest, _, _, _, _, _, _, _⟩ := hsignRun.indexed
  obtain ⟨_, _, _, _, _, _, hsignedRun⟩ := hsignedDigest.extract
  let signedPayload := messageDigestPayload secretKey.root entry.1 signature.randomness
  let forgedPayload := messageDigestPayload secretKey.root forgery.message
    forgery.signature.randomness
  let signedInput := tweakableHashInput secretKey.parameter .message signedPayload
  let forgedInput := tweakableHashInput secretKey.parameter .message forgedPayload
  have hsignedCached : cache signedInput ≠ none := by
    exact CachedRun.messageDigest_cached hsignedRun
  have hforgedCached : cache forgedInput ≠ none := by
    exact CachedRun.messageDigest_cached hforgedRun
  obtain ⟨signedAnswer, hsignedAnswer⟩ := Option.ne_none_iff_exists'.mp hsignedCached
  obtain ⟨forgedAnswer, hforgedAnswer⟩ := Option.ne_none_iff_exists'.mp hforgedCached
  refine ⟨signedPayload, forgedPayload, signedAnswer, forgedAnswer, ?_, hsignedAnswer,
    hforgedAnswer, ?_⟩
  · exact fun heq => hinput (congrArg
      (tweakableHashInput secretKey.parameter HashDomain.message) heq)
  · change truncateMessageDigest (f signedInput) = truncateMessageDigest (f forgedInput) at hvalue
    rw [← hf hsignedAnswer, ← hf hforgedAnswer]
    exact hvalue

end SphincsSecurity.Concrete
