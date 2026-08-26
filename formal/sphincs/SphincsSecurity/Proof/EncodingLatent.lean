import SphincsSecurity.Proof.EncodingRetryCharge

/-!
# Latent encoding collisions

A fully cached encoding search can become canonical when a missing earlier retry receives an
inadmissible answer. The collision itself is older: its target is already the least admissible
cached counter for the settled layer message. This cache event records that older witness without
requiring every smaller counter to be cached.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

def LatentEncodingBad (cache : QueryCache HashSpec) (secretKey : SecretKey) : Prop :=
  ∃ (position : EncodingPosition) (index : Index) (counter : Counter)
      (targetPayload otherPayload : HashInput) (targetAnswer otherAnswer : HashOutput),
    treeIndexAt index position.lay = position.tree
      ∧ leafIndexAt index position.lay = position.leafIdx
      ∧ Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
        (layerMessagePosition index position.lay)
      ∧ targetPayload = digestBytes (honestValue (fromCache cache) secretKey.parameter
          secretKey.otsSecret secretKey.ftsSecret
          (layerMessagePosition index position.lay)) ++ counterBytes counter
      ∧ cache (tweakableHashInput secretKey.parameter position.domain targetPayload) =
          some targetAnswer
      ∧ TargetSum.ValidDigest (truncateHash targetAnswer)
      ∧ (∀ candidate : Counter, candidate.toNat < counter.toNat →
        ∀ answer : HashOutput,
          cache (tweakableHashInput secretKey.parameter position.domain
            (digestBytes (honestValue (fromCache cache) secretKey.parameter
              secretKey.otsSecret secretKey.ftsSecret
              (layerMessagePosition index position.lay)) ++ counterBytes candidate)) =
              some answer →
            ¬ TargetSum.ValidDigest (truncateHash answer))
      ∧ targetPayload ≠ otherPayload
      ∧ cache (tweakableHashInput secretKey.parameter position.domain otherPayload) =
          some otherAnswer
      ∧ truncateHash targetAnswer = truncateHash otherAnswer

theorem EncodingBad.latent {cache : QueryCache HashSpec} {secretKey : SecretKey}
    (hbad : EncodingBad cache secretKey) : LatentEncodingBad cache secretKey := by
  obtain ⟨lay, tree, leafIdx, targetPayload, otherPayload, targetAnswer, otherAnswer,
    htarget, hpayloadNe, htargetAnswer, hotherAnswer, hcollision⟩ := hbad
  obtain ⟨index, counter, htree, hleaf, hsettled, _hrun, heval, hpayload,
    _htargetCached⟩ := htarget
  let position : EncodingPosition := ⟨lay, tree, leafIdx⟩
  have hselected := encodingSearch_selected_encode_ne_none (fromCache cache)
    secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
    (honestValue (fromCache cache) secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret (layerMessagePosition index lay)) counter heval
  have hvalid := (eval_encode_ne_none_iff_validDigest (fromCache cache)
    secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
    (honestValue (fromCache cache) secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret (layerMessagePosition index lay)) counter).mp hselected
  refine ⟨position, index, counter, targetPayload, otherPayload, targetAnswer,
    otherAnswer, htree, hleaf, hsettled, hpayload, ?_, ?_, ?_, hpayloadNe, ?_,
    hcollision⟩
  · simpa only [position, EncodingPosition.domain] using htargetAnswer
  · have hfromCache : fromCache cache
        (tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx)
          targetPayload) =
          targetAnswer := by
      simp [fromCache, htargetAnswer]
    rw [htree, hleaf, ← hpayload] at hvalid
    rwa [hfromCache] at hvalid
  · intro candidate hcandidate answer hanswer
    have hrejected := encodingSearch_rejected_before (fromCache cache)
      secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
      (honestValue (fromCache cache) secretKey.parameter secretKey.otsSecret
        secretKey.ftsSecret (layerMessagePosition index lay)) counter candidate heval
      hcandidate
    have hinvalid : ¬ TargetSum.ValidDigest (truncateHash (fromCache cache
        (tweakableHashInput secretKey.parameter
          (.encoding lay (treeIndexAt index lay) (leafIndexAt index lay))
          (digestBytes (honestValue (fromCache cache) secretKey.parameter
            secretKey.otsSecret secretKey.ftsSecret
            (layerMessagePosition index lay)) ++ counterBytes candidate)))) := by
      intro hvalidCandidate
      exact ((eval_encode_ne_none_iff_validDigest (fromCache cache)
        secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
        (honestValue (fromCache cache) secretKey.parameter secretKey.otsSecret
          secretKey.ftsSecret (layerMessagePosition index lay)) candidate).mpr
          hvalidCandidate) hrejected
    have hfromCache : fromCache cache
        (tweakableHashInput secretKey.parameter (.encoding lay tree leafIdx)
          (digestBytes (honestValue (fromCache cache) secretKey.parameter
            secretKey.otsSecret secretKey.ftsSecret
            (layerMessagePosition index lay)) ++ counterBytes candidate)) =
          answer := by
      have hanswer' : cache (tweakableHashInput secretKey.parameter
          (.encoding lay tree leafIdx)
          (digestBytes (honestValue (fromCache cache) secretKey.parameter
            secretKey.otsSecret secretKey.ftsSecret
            (layerMessagePosition index lay)) ++ counterBytes candidate)) =
          some answer := by
        simpa only [position, EncodingPosition.domain] using hanswer
      simp [fromCache, hanswer']
    rw [htree, hleaf] at hinvalid
    rwa [hfromCache] at hinvalid
  · simpa only [position, EncodingPosition.domain] using hotherAnswer

theorem LatentEncodingBad.of_cacheQuery_of_invalid_encoding
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {input : HashInput} {answer : HashOutput} {queriedPosition : EncodingPosition}
    (huncached : cache input = none)
    (hqueried : AtEncodingPosition secretKey.parameter input queriedPosition)
    (hinvalid : ¬ TargetSum.ValidDigest (truncateHash answer))
    (hbad : LatentEncodingBad (cache.cacheQuery input answer) secretKey) :
    LatentEncodingBad cache secretKey := by
  obtain ⟨position, index, counter, targetPayload, otherPayload, targetAnswer,
    otherAnswer, htree, hleaf, hsettledAfter, hpayload, htargetAnswer,
    htargetValid, hbefore, hpayloadNe, hotherAnswer, hcollision⟩ := hbad
  have hle := le_cacheQuery (cache := cache) (input := input) (answer := answer) huncached
  have hsettled : Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
      (layerMessagePosition index position.lay) := by
    exact settled_of_settled_cacheQuery secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret huncached (p₀ := none)
      (fun structuralPosition hposition =>
        absurd hposition (hqueried.not_atPosition structuralPosition))
      (by simp) ((layerMessagePosition index position.lay).depth + 1)
      (layerMessagePosition index position.lay) (by omega) (by simp) hsettledAfter
  have hmessage := honestValue_eq_of_settled
    (agreesWithFn_fromCache_of_le hle) hsettled
  have htargetInputNe :
      tweakableHashInput secretKey.parameter position.domain targetPayload ≠ input := by
    intro heq
    have hanswerEq : targetAnswer = answer := by
      rw [heq, QueryCache.cacheQuery_self] at htargetAnswer
      exact Option.some.inj htargetAnswer.symm
    exact hinvalid (hanswerEq ▸ htargetValid)
  have hotherValid : TargetSum.ValidDigest (truncateHash otherAnswer) := by
    rwa [← hcollision]
  have hotherInputNe :
      tweakableHashInput secretKey.parameter position.domain otherPayload ≠ input := by
    intro heq
    have hanswerEq : otherAnswer = answer := by
      rw [heq, QueryCache.cacheQuery_self] at hotherAnswer
      exact Option.some.inj hotherAnswer.symm
    exact hinvalid (hanswerEq ▸ hotherValid)
  have htargetOld : cache
      (tweakableHashInput secretKey.parameter position.domain targetPayload) =
        some targetAnswer := by
    rwa [QueryCache.cacheQuery_of_ne _ _ htargetInputNe] at htargetAnswer
  have hotherOld : cache
      (tweakableHashInput secretKey.parameter position.domain otherPayload) =
        some otherAnswer := by
    rwa [QueryCache.cacheQuery_of_ne _ _ hotherInputNe] at hotherAnswer
  refine ⟨position, index, counter, targetPayload, otherPayload, targetAnswer,
    otherAnswer, htree, hleaf, hsettled, ?_, htargetOld, htargetValid, ?_,
    hpayloadNe, hotherOld, hcollision⟩
  · rw [hmessage] at hpayload
    exact hpayload
  · intro candidate hcandidate candidateAnswer hcandidateAnswer
    have hcandidateInputNe : tweakableHashInput secretKey.parameter position.domain
        (digestBytes (honestValue (fromCache cache) secretKey.parameter
          secretKey.otsSecret secretKey.ftsSecret
          (layerMessagePosition index position.lay)) ++ counterBytes candidate) ≠ input := by
      intro heq
      rw [heq, huncached] at hcandidateAnswer
      simp at hcandidateAnswer
    have hcandidateAfter : (cache.cacheQuery input answer)
        (tweakableHashInput secretKey.parameter position.domain
          (digestBytes (honestValue (fromCache (cache.cacheQuery input answer))
            secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
            (layerMessagePosition index position.lay)) ++ counterBytes candidate)) =
          some candidateAnswer := by
      rw [hmessage]
      rwa [QueryCache.cacheQuery_of_ne _ _ hcandidateInputNe]
    exact hbefore candidate hcandidate candidateAnswer hcandidateAfter

theorem latentEncodingBad_of_encodingBad_cacheQuery_of_invalid_encoding
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {input : HashInput} {answer : HashOutput} {queriedPosition : EncodingPosition}
    (huncached : cache input = none)
    (hqueried : AtEncodingPosition secretKey.parameter input queriedPosition)
    (hinvalid : ¬ TargetSum.ValidDigest (truncateHash answer))
    (hbad : EncodingBad (cache.cacheQuery input answer) secretKey) :
    LatentEncodingBad cache secretKey :=
  hbad.latent.of_cacheQuery_of_invalid_encoding huncached hqueried hinvalid

theorem not_latentEncodingBad_empty (secretKey : SecretKey) :
    ¬ LatentEncodingBad ∅ secretKey := by
  rintro ⟨position, index, counter, targetPayload, otherPayload, targetAnswer,
    otherAnswer, htree, hleaf, hsettled, hpayload, htargetAnswer, hrest⟩
  simp at htargetAnswer

theorem latentEncodingBad_answer_hit_of_encoding_query
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {answer : HashOutput}
    {queriedPosition : EncodingPosition}
    (hclean : ¬ LatentEncodingBad cache secretKey)
    (huncached : cache input = none)
    (hqueried : AtEncodingPosition secretKey.parameter input queriedPosition)
    (hbad : LatentEncodingBad (cache.cacheQuery input answer) secretKey) :
    truncateHash answer ∈
      encodingAnswerTargets secretKey.parameter cache hfinite queriedPosition := by
  obtain ⟨position, index, counter, targetPayload, otherPayload, targetAnswer,
    otherAnswer, htree, hleaf, hsettledAfter, hpayload, htargetAnswer,
    htargetValid, hbefore, hpayloadNe, hotherAnswer, hcollision⟩ := hbad
  let targetInput := tweakableHashInput secretKey.parameter position.domain targetPayload
  let otherInput := tweakableHashInput secretKey.parameter position.domain otherPayload
  have htargetAt : AtEncodingPosition secretKey.parameter targetInput position :=
    ⟨targetPayload, rfl⟩
  have hotherAt : AtEncodingPosition secretKey.parameter otherInput position :=
    ⟨otherPayload, rfl⟩
  by_cases htargetQuery : targetInput = input
  · have hposition : position = queriedPosition :=
      atEncodingPosition_unique htargetAt (htargetQuery ▸ hqueried)
    subst position
    have htargetAnswerEq : targetAnswer = answer := by
      have htargetQuery' : tweakableHashInput secretKey.parameter queriedPosition.domain
          targetPayload = input := by
        simpa only [targetInput] using htargetQuery
      rw [htargetQuery', QueryCache.cacheQuery_self] at htargetAnswer
      exact Option.some.inj htargetAnswer.symm
    have hotherQuery : otherInput ≠ input := by
      intro heq
      apply hpayloadNe
      exact (tweakableHashInput_injective secretKey.parameter (by trivial) (by trivial)
        (htargetQuery.trans heq.symm)).2
    have hotherOld : cache otherInput = some otherAnswer := by
      rwa [QueryCache.cacheQuery_of_ne _ _ hotherQuery] at hotherAnswer
    have hmem := cachedAnswer_mem_encodingAnswerTargets hfinite hotherOld hotherAt
    rwa [← hcollision, htargetAnswerEq] at hmem
  · by_cases hotherQuery : otherInput = input
    · have hposition : position = queriedPosition :=
        atEncodingPosition_unique hotherAt (hotherQuery ▸ hqueried)
      subst position
      have hotherAnswerEq : otherAnswer = answer := by
        have hotherQuery' : tweakableHashInput secretKey.parameter queriedPosition.domain
            otherPayload = input := by
          simpa only [otherInput] using hotherQuery
        rw [hotherQuery', QueryCache.cacheQuery_self] at hotherAnswer
        exact Option.some.inj hotherAnswer.symm
      have htargetOld : cache targetInput = some targetAnswer := by
        rwa [QueryCache.cacheQuery_of_ne _ _ htargetQuery] at htargetAnswer
      have hmem := cachedAnswer_mem_encodingAnswerTargets hfinite htargetOld htargetAt
      rwa [hcollision, hotherAnswerEq] at hmem
    · exfalso
      apply hclean
      have hle := le_cacheQuery (cache := cache) (input := input) (answer := answer)
        huncached
      have hsettled : Settled secretKey.parameter secretKey.otsSecret
          secretKey.ftsSecret cache (layerMessagePosition index position.lay) := by
        exact settled_of_settled_cacheQuery secretKey.parameter secretKey.otsSecret
          secretKey.ftsSecret huncached (p₀ := none)
          (fun structuralPosition hposition =>
            absurd hposition (hqueried.not_atPosition structuralPosition))
          (by simp) ((layerMessagePosition index position.lay).depth + 1)
          (layerMessagePosition index position.lay) (by omega) (by simp) hsettledAfter
      have hmessage := honestValue_eq_of_settled
        (agreesWithFn_fromCache_of_le hle) hsettled
      have htargetOld : cache targetInput = some targetAnswer := by
        rwa [QueryCache.cacheQuery_of_ne _ _ htargetQuery] at htargetAnswer
      have hotherOld : cache otherInput = some otherAnswer := by
        rwa [QueryCache.cacheQuery_of_ne _ _ hotherQuery] at hotherAnswer
      refine ⟨position, index, counter, targetPayload, otherPayload, targetAnswer,
        otherAnswer, htree, hleaf, hsettled, ?_, htargetOld, htargetValid, ?_,
        hpayloadNe, hotherOld, hcollision⟩
      · rw [hmessage] at hpayload
        exact hpayload
      · intro candidate hcandidate candidateAnswer hcandidateAnswer
        have hcandidateInputNe : tweakableHashInput secretKey.parameter position.domain
            (digestBytes (honestValue (fromCache cache) secretKey.parameter
              secretKey.otsSecret secretKey.ftsSecret
              (layerMessagePosition index position.lay)) ++ counterBytes candidate) ≠ input := by
          intro heq
          rw [heq, huncached] at hcandidateAnswer
          simp at hcandidateAnswer
        have hcandidateAfter : (cache.cacheQuery input answer)
            (tweakableHashInput secretKey.parameter position.domain
              (digestBytes (honestValue (fromCache (cache.cacheQuery input answer))
                secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
                (layerMessagePosition index position.lay)) ++ counterBytes candidate)) =
              some candidateAnswer := by
          rw [hmessage]
          rwa [QueryCache.cacheQuery_of_ne _ _ hcandidateInputNe]
        exact hbefore candidate hcandidate candidateAnswer hcandidateAfter

end SphincsSecurity.Concrete
