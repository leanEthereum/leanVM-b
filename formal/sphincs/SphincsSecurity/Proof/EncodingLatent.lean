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

set_option maxRecDepth 100000

def EncodingMessageSettledAt (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (position : EncodingPosition) : Prop :=
  ∃ index : Index,
    treeIndexAt index position.lay = position.tree
      ∧ leafIndexAt index position.lay = position.leafIdx
      ∧ Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
        (layerMessagePosition index position.lay)

theorem EncodingMessageSettledAt.mono {cache cache' : QueryCache HashSpec}
    {secretKey : SecretKey} {position : EncodingPosition} (hle : cache ≤ cache')
    (hsettled : EncodingMessageSettledAt cache secretKey position) :
    EncodingMessageSettledAt cache' secretKey position := by
  obtain ⟨index, htree, hleaf, hposition⟩ := hsettled
  exact ⟨index, htree, hleaf, hposition.mono hle⟩

def LatentEncodingBadAt (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (position : EncodingPosition) : Prop :=
  ∃ (index : Index) (counter : Counter)
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

def LatentEncodingBad (cache : QueryCache HashSpec) (secretKey : SecretKey) : Prop :=
  ∃ position, LatentEncodingBadAt cache secretKey position

theorem encodingAnswerTargets_card_le_encodingPotential
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {position : EncodingPosition}
    (hnotTarget : ¬ HasEncodingTarget cache secretKey position) :
    (encodingAnswerTargets secretKey.parameter cache hfinite position).card ≤
      encodingPotential cache secretKey := by
  calc
    (encodingAnswerTargets secretKey.parameter cache hfinite position).card ≤
        (encodingCachedAt secretKey.parameter cache position).ncard :=
      encodingAnswerTargets_card_le hfinite position
    _ = encodingContribution cache secretKey position := by
      rw [encodingContribution, if_neg hnotTarget]
    _ ≤ ∑ candidate : EncodingPosition,
        encodingContribution cache secretKey candidate := by
      rw [Fintype.sum_eq_add_sum_subtype_ne _ position]
      exact Nat.le_add_right _ _
    _ = encodingPotential cache secretKey := rfl

theorem encodingMessageTargets_card_le_encodingPotential
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {position : EncodingPosition}
    (hnotTarget : ¬ HasEncodingTarget cache secretKey position) :
    (encodingMessageTargets secretKey.parameter cache hfinite position).card ≤
      encodingPotential cache secretKey := by
  calc
    (encodingMessageTargets secretKey.parameter cache hfinite position).card ≤
        (encodingCachedAt secretKey.parameter cache position).ncard :=
      encodingMessageTargets_card_le hfinite position
    _ = encodingContribution cache secretKey position := by
      rw [encodingContribution, if_neg hnotTarget]
    _ ≤ ∑ candidate : EncodingPosition,
        encodingContribution cache secretKey candidate := by
      rw [Fintype.sum_eq_add_sum_subtype_ne _ position]
      exact Nat.le_add_right _ _
    _ = encodingPotential cache secretKey := rfl

theorem EncodingBad.latent_with_target
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    (hbad : EncodingBad cache secretKey) :
    ∃ position : EncodingPosition,
      HasEncodingTarget cache secretKey position ∧
        LatentEncodingBadAt cache secretKey position := by
  obtain ⟨lay, tree, leafIdx, targetPayload, otherPayload, targetAnswer, otherAnswer,
    htarget, hpayloadNe, htargetAnswer, hotherAnswer, hcollision⟩ := hbad
  have htargetData := htarget
  obtain ⟨index, counter, htree, hleaf, hsettled, _hrun, heval, hpayload,
    _htargetCached⟩ := htargetData
  let position : EncodingPosition := ⟨lay, tree, leafIdx⟩
  have hselected := encodingSearch_selected_encode_ne_none (fromCache cache)
    secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
    (honestValue (fromCache cache) secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret (layerMessagePosition index lay)) counter heval
  have hvalid := (eval_encode_ne_none_iff_validDigest (fromCache cache)
    secretKey.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
    (honestValue (fromCache cache) secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret (layerMessagePosition index lay)) counter).mp hselected
  refine ⟨position, ⟨targetPayload, htarget⟩, index, counter, targetPayload,
    otherPayload, targetAnswer, otherAnswer, htree, hleaf, hsettled, hpayload,
    ?_, ?_, ?_, hpayloadNe, ?_, hcollision⟩
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

theorem EncodingBad.latent {cache : QueryCache HashSpec} {secretKey : SecretKey}
    (hbad : EncodingBad cache secretKey) : LatentEncodingBad cache secretKey := by
  obtain ⟨position, htarget, hlatent⟩ := hbad.latent_with_target
  exact ⟨position, hlatent⟩

theorem LatentEncodingBadAt.encodingBad_of_hasTarget
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {position : EncodingPosition}
    (hlatent : LatentEncodingBadAt cache secretKey position)
    (htarget : HasEncodingTarget cache secretKey position) :
    EncodingBad cache secretKey := by
  obtain ⟨index, counter, targetPayload, otherPayload, targetAnswer, otherAnswer,
    htree, hleaf, hsettled, hpayload, htargetAnswer, htargetValid, hbefore,
    hpayloadNe, hotherAnswer, hcollision⟩ := hlatent
  obtain ⟨signedPayload, hsigned⟩ := htarget
  have hsignedData := hsigned
  obtain ⟨_, _, _, _, _, _, _, _, signedCached⟩ := hsignedData
  obtain ⟨signedAnswer, hsignedAnswer⟩ :=
    Option.ne_none_iff_exists'.mp signedCached
  obtain ⟨signedIndex, signedCounter, signedTree, signedLeaf, signedPayloadEq,
    signedValid, signedBefore⟩ := hsigned.target_least_valid
  have hmessagePosition : layerMessagePosition index position.lay =
      layerMessagePosition signedIndex position.lay :=
    layerMessagePosition_eq_of_position_eq index signedIndex position.lay
      (htree.trans signedTree.symm) (hleaf.trans signedLeaf.symm)
  have htargetFromCache : fromCache cache
      (tweakableHashInput secretKey.parameter position.domain targetPayload) =
        targetAnswer := by
    simp [fromCache, htargetAnswer]
  have hsignedFromCache : fromCache cache
      (tweakableHashInput secretKey.parameter
        (.encoding position.lay position.tree position.leafIdx) signedPayload) =
        signedAnswer := by
    simp only [fromCache, hsignedAnswer, Option.getD_some]
  have hcounter : counter = signedCounter := by
    apply BitVec.eq_of_toNat_eq
    by_contra hne
    have hcases : counter.toNat < signedCounter.toNat ∨
        signedCounter.toNat < counter.toNat := by omega
    rcases hcases with hcounterLt | hsignedLt
    · apply signedBefore counter hcounterLt
      have hvalid := htargetValid
      rw [← htargetFromCache] at hvalid
      rw [hpayload, hmessagePosition, EncodingPosition.domain, ← signedTree,
        ← signedLeaf] at hvalid
      exact hvalid
    · have hsignedCachedAtLatent : cache
          (tweakableHashInput secretKey.parameter position.domain
            (digestBytes (honestValue (fromCache cache) secretKey.parameter
              secretKey.otsSecret secretKey.ftsSecret
              (layerMessagePosition index position.lay)) ++
              counterBytes signedCounter)) = some signedAnswer := by
        rw [hmessagePosition, ← signedPayloadEq]
        simpa only [EncodingPosition.domain] using hsignedAnswer
      have hinvalid := hbefore signedCounter hsignedLt signedAnswer
        hsignedCachedAtLatent
      apply hinvalid
      rw [hsignedFromCache] at signedValid
      exact signedValid
  have hpayloadEq : targetPayload = signedPayload := by
    rw [hpayload, signedPayloadEq, hmessagePosition, hcounter]
  rw [hpayloadEq] at hpayloadNe htargetAnswer
  exact ⟨position.lay, position.tree, position.leafIdx, signedPayload,
    otherPayload, targetAnswer, otherAnswer, hsigned, hpayloadNe,
    by simpa only [EncodingPosition.domain] using htargetAnswer,
    by simpa only [EncodingPosition.domain] using hotherAnswer, hcollision⟩

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

theorem not_latentEncodingBad_of_encoding_none
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    (hnone : ∀ (position : EncodingPosition) (payload : HashInput),
      cache (tweakableHashInput secretKey.parameter position.domain payload) = none) :
    ¬ LatentEncodingBad cache secretKey := by
  rintro ⟨position, index, counter, targetPayload, otherPayload, targetAnswer,
    otherAnswer, htree, hleaf, hsettled, hpayload, htargetAnswer, hrest⟩
  rw [hnone position targetPayload] at htargetAnswer
  simp at htargetAnswer

inductive LatentEncodingFreshOrientation
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (input : HashInput) (answer : HashOutput) (position : EncodingPosition) : Prop where
  | targetFresh (targetPayload otherPayload : HashInput)
      (targetAnswer otherAnswer : HashOutput)
      (payloadNe : targetPayload ≠ otherPayload)
      (collision : truncateHash targetAnswer = truncateHash otherAnswer)
      (targetInput : tweakableHashInput secretKey.parameter position.domain targetPayload = input)
      (targetAnswerEq : targetAnswer = answer)
      (otherCached : cache
        (tweakableHashInput secretKey.parameter position.domain otherPayload) = some otherAnswer)
  | otherFresh (targetPayload otherPayload : HashInput)
      (targetAnswer otherAnswer : HashOutput)
      (payloadNe : targetPayload ≠ otherPayload)
      (collision : truncateHash targetAnswer = truncateHash otherAnswer)
      (targetCached : cache
        (tweakableHashInput secretKey.parameter position.domain targetPayload) = some targetAnswer)
      (otherInput : tweakableHashInput secretKey.parameter position.domain otherPayload = input)
      (otherAnswerEq : otherAnswer = answer)

theorem latentEncodingBadAt_fresh_orientation
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {input : HashInput} {answer : HashOutput} {position : EncodingPosition}
    (hclean : ¬ LatentEncodingBadAt cache secretKey position)
    (huncached : cache input = none)
    (hqueried : AtEncodingPosition secretKey.parameter input position)
    (hbad : LatentEncodingBadAt
      (cache.cacheQuery input answer) secretKey position) :
    LatentEncodingFreshOrientation cache secretKey input answer position := by
  obtain ⟨index, counter, targetPayload, otherPayload, targetAnswer,
    otherAnswer, htree, hleaf, hsettledAfter, hpayload, htargetAnswer,
    htargetValid, hbefore, hpayloadNe, hotherAnswer, hcollision⟩ := hbad
  let targetInput := tweakableHashInput secretKey.parameter position.domain targetPayload
  let otherInput := tweakableHashInput secretKey.parameter position.domain otherPayload
  by_cases htargetQuery : targetInput = input
  · have htargetAnswerEq : targetAnswer = answer := by
      have htargetQuery' : tweakableHashInput secretKey.parameter position.domain
          targetPayload = input := by simpa only [targetInput] using htargetQuery
      rw [htargetQuery', QueryCache.cacheQuery_self] at htargetAnswer
      exact Option.some.inj htargetAnswer.symm
    have hotherQuery : otherInput ≠ input := by
      intro heq
      apply hpayloadNe
      exact (tweakableHashInput_injective secretKey.parameter (by trivial) (by trivial)
        (htargetQuery.trans heq.symm)).2
    have hotherOld : cache otherInput = some otherAnswer := by
      rwa [QueryCache.cacheQuery_of_ne _ _ hotherQuery] at hotherAnswer
    exact .targetFresh targetPayload otherPayload targetAnswer otherAnswer
      hpayloadNe hcollision htargetQuery htargetAnswerEq hotherOld
  · by_cases hotherQuery : otherInput = input
    · have hotherAnswerEq : otherAnswer = answer := by
        have hotherQuery' : tweakableHashInput secretKey.parameter position.domain
            otherPayload = input := by simpa only [otherInput] using hotherQuery
        rw [hotherQuery', QueryCache.cacheQuery_self] at hotherAnswer
        exact Option.some.inj hotherAnswer.symm
      have htargetOld : cache targetInput = some targetAnswer := by
        rwa [QueryCache.cacheQuery_of_ne _ _ htargetQuery] at htargetAnswer
      exact .otherFresh targetPayload otherPayload targetAnswer otherAnswer
        hpayloadNe hcollision htargetOld hotherQuery hotherAnswerEq
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
      refine ⟨index, counter, targetPayload, otherPayload, targetAnswer,
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

theorem latentEncodingBad_validAnswer_hit_of_encoding_query
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {answer : HashOutput}
    {queriedPosition : EncodingPosition}
    (hclean : ¬ LatentEncodingBad cache secretKey)
    (huncached : cache input = none)
    (hqueried : AtEncodingPosition secretKey.parameter input queriedPosition)
    (hbad : LatentEncodingBad (cache.cacheQuery input answer) secretKey) :
    truncateHash answer ∈
      encodingValidAnswerTargets secretKey.parameter cache hfinite queriedPosition := by
  have hhit := latentEncodingBad_answer_hit_of_encoding_query hfinite hclean huncached
    hqueried hbad
  have hvalid : TargetSum.ValidDigest (truncateHash answer) := by
    by_contra hinvalid
    exact hclean (hbad.of_cacheQuery_of_invalid_encoding huncached hqueried hinvalid)
  exact Finset.mem_filter.mpr ⟨hhit, hvalid⟩

theorem latentEncodingBadAt_answer_hit_of_encoding_query
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {answer : HashOutput}
    {position : EncodingPosition}
    (hclean : ¬ LatentEncodingBadAt cache secretKey position)
    (huncached : cache input = none)
    (hqueried : AtEncodingPosition secretKey.parameter input position)
    (hbad : LatentEncodingBadAt (cache.cacheQuery input answer) secretKey position) :
    truncateHash answer ∈
      encodingValidAnswerTargets secretKey.parameter cache hfinite position := by
  obtain ⟨index, counter, targetPayload, otherPayload, targetAnswer,
    otherAnswer, htree, hleaf, hsettledAfter, hpayload, htargetAnswer,
    htargetValid, hbefore, hpayloadNe, hotherAnswer, hcollision⟩ := hbad
  let targetInput := tweakableHashInput secretKey.parameter position.domain targetPayload
  let otherInput := tweakableHashInput secretKey.parameter position.domain otherPayload
  have htargetAt : AtEncodingPosition secretKey.parameter targetInput position :=
    ⟨targetPayload, rfl⟩
  have hotherAt : AtEncodingPosition secretKey.parameter otherInput position :=
    ⟨otherPayload, rfl⟩
  have hhit : truncateHash answer ∈
        encodingAnswerTargets secretKey.parameter cache hfinite position
      ∧ TargetSum.ValidDigest (truncateHash answer) := by
    by_cases htargetQuery : targetInput = input
    · have htargetAnswerEq : targetAnswer = answer := by
        have htargetQuery' : tweakableHashInput secretKey.parameter position.domain
            targetPayload = input := by simpa only [targetInput] using htargetQuery
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
      constructor
      · rwa [← hcollision, htargetAnswerEq] at hmem
      · rwa [← htargetAnswerEq]
    · by_cases hotherQuery : otherInput = input
      · have hotherAnswerEq : otherAnswer = answer := by
          have hotherQuery' : tweakableHashInput secretKey.parameter position.domain
              otherPayload = input := by simpa only [otherInput] using hotherQuery
          rw [hotherQuery', QueryCache.cacheQuery_self] at hotherAnswer
          exact Option.some.inj hotherAnswer.symm
        have htargetOld : cache targetInput = some targetAnswer := by
          rwa [QueryCache.cacheQuery_of_ne _ _ htargetQuery] at htargetAnswer
        have hmem := cachedAnswer_mem_encodingAnswerTargets hfinite htargetOld htargetAt
        constructor
        · rwa [hcollision, hotherAnswerEq] at hmem
        · have hotherValid := htargetValid.of_eq hcollision
          rwa [hotherAnswerEq] at hotherValid
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
        refine ⟨index, counter, targetPayload, otherPayload, targetAnswer,
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
  exact Finset.mem_filter.mpr hhit

theorem latentEncodingBadAt_message_hit_of_settling_query
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {answer : HashOutput}
    {position : EncodingPosition} {queryIndex : Index}
    (huncached : cache input = none)
    (htree : treeIndexAt queryIndex position.lay = position.tree)
    (hleaf : leafIndexAt queryIndex position.lay = position.leafIdx)
    (hposition : AtPosition secretKey.parameter input
      (layerMessagePosition queryIndex position.lay))
    (hunsettled : ¬ Settled secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret cache (layerMessagePosition queryIndex position.lay))
    (hbad : LatentEncodingBadAt (cache.cacheQuery input answer) secretKey position) :
    truncateHash answer ∈
      encodingMessageTargets secretKey.parameter cache hfinite position := by
  obtain ⟨targetIndex, counter, targetPayload, otherPayload, targetAnswer,
    otherAnswer, htargetTree, htargetLeaf, hsettledAfter, hpayload,
    htargetAnswer, htargetValid, hbefore, hpayloadNe, hotherAnswer,
    hcollision⟩ := hbad
  have hmessagePosition : layerMessagePosition queryIndex position.lay =
      layerMessagePosition targetIndex position.lay :=
    layerMessagePosition_eq_of_position_eq queryIndex targetIndex position.lay
      (htree.trans htargetTree.symm) (hleaf.trans htargetLeaf.symm)
  have htargetPosition : AtPosition secretKey.parameter input
      (layerMessagePosition targetIndex position.lay) := by
    rwa [← hmessagePosition]
  have htargetUnsettled : ¬ Settled secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret cache (layerMessagePosition targetIndex position.lay) := by
    rwa [← hmessagePosition]
  have hmessage := honestValue_cacheQuery_self_of_settled secretKey.parameter
    secretKey.otsSecret secretKey.ftsSecret huncached htargetPosition
    htargetUnsettled hsettledAfter
  let targetInput := tweakableHashInput secretKey.parameter position.domain targetPayload
  have htargetInputNe : targetInput ≠ input := by
    intro heq
    exact (show AtEncodingPosition secretKey.parameter targetInput position from
      ⟨targetPayload, rfl⟩).not_atPosition
        (layerMessagePosition targetIndex position.lay) (heq ▸ htargetPosition)
  have htargetOld : cache targetInput ≠ none := by
    have htargetAfter : cache.cacheQuery input answer targetInput ≠ none := by
      simp [targetInput, htargetAnswer]
    rwa [QueryCache.cacheQuery_of_ne _ _ htargetInputNe] at htargetAfter
  have hmem := slotDigest_mem_encodingMessageTargets hfinite htargetOld
    (show AtEncodingPosition secretKey.parameter targetInput position from
      ⟨targetPayload, rfl⟩)
  have hslot : slotDigest 0 targetInput =
      honestValue (fromCache (cache.cacheQuery input answer)) secretKey.parameter
        secretKey.otsSecret secretKey.ftsSecret
        (layerMessagePosition targetIndex position.lay) := by
    dsimp only [targetInput]
    rw [hpayload]
    exact slotDigest_zero_encodingInput secretKey.parameter position
      (honestValue (fromCache (cache.cacheQuery input answer)) secretKey.parameter
        secretKey.otsSecret secretKey.ftsSecret
        (layerMessagePosition targetIndex position.lay)) counter
  rw [hslot, hmessage] at hmem
  exact hmem

theorem LatentEncodingBadAt.of_cacheQuery_of_settled_of_not_atEncoding
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {input : HashInput} {answer : HashOutput} {position : EncodingPosition}
    (huncached : cache input = none)
    (hsettledAt : ∀ index : Index,
      treeIndexAt index position.lay = position.tree →
      leafIndexAt index position.lay = position.leafIdx →
        Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
          (layerMessagePosition index position.lay))
    (hnotAt : ¬ AtEncodingPosition secretKey.parameter input position)
    (hbad : LatentEncodingBadAt (cache.cacheQuery input answer) secretKey position) :
    LatentEncodingBadAt cache secretKey position := by
  obtain ⟨index, counter, targetPayload, otherPayload, targetAnswer, otherAnswer,
    htree, hleaf, hsettledAfter, hpayload, htargetAnswer, htargetValid,
    hbefore, hpayloadNe, hotherAnswer, hcollision⟩ := hbad
  have hsettled := hsettledAt index htree hleaf
  have hle := le_cacheQuery (cache := cache) (input := input) (answer := answer) huncached
  have hmessage := honestValue_eq_of_settled
    (agreesWithFn_fromCache_of_le hle) hsettled
  let targetInput := tweakableHashInput secretKey.parameter position.domain targetPayload
  let otherInput := tweakableHashInput secretKey.parameter position.domain otherPayload
  have htargetInputNe : targetInput ≠ input := by
    intro heq
    exact hnotAt ⟨targetPayload, heq.symm⟩
  have hotherInputNe : otherInput ≠ input := by
    intro heq
    exact hnotAt ⟨otherPayload, heq.symm⟩
  have htargetOld : cache targetInput = some targetAnswer := by
    have htargetAnswer' : cache.cacheQuery input answer targetInput =
        some targetAnswer := by
      simpa only [targetInput] using htargetAnswer
    rwa [QueryCache.cacheQuery_of_ne _ _ htargetInputNe] at htargetAnswer'
  have hotherOld : cache otherInput = some otherAnswer := by
    have hotherAnswer' : cache.cacheQuery input answer otherInput = some otherAnswer := by
      simpa only [otherInput] using hotherAnswer
    rwa [QueryCache.cacheQuery_of_ne _ _ hotherInputNe] at hotherAnswer'
  refine ⟨index, counter, targetPayload, otherPayload, targetAnswer, otherAnswer,
    htree, hleaf, hsettled, ?_, htargetOld, htargetValid, ?_, hpayloadNe,
    hotherOld, hcollision⟩
  · rw [hmessage] at hpayload
    exact hpayload
  · intro candidate hcandidate candidateAnswer hcandidateAnswer
    have hcandidateInputNe : tweakableHashInput secretKey.parameter position.domain
        (digestBytes (honestValue (fromCache cache) secretKey.parameter
          secretKey.otsSecret secretKey.ftsSecret
          (layerMessagePosition index position.lay)) ++ counterBytes candidate) ≠ input := by
      intro heq
      exact hnotAt ⟨_, heq.symm⟩
    have hcandidateAfter : (cache.cacheQuery input answer)
        (tweakableHashInput secretKey.parameter position.domain
          (digestBytes (honestValue (fromCache (cache.cacheQuery input answer))
            secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
            (layerMessagePosition index position.lay)) ++ counterBytes candidate)) =
          some candidateAnswer := by
      rw [hmessage]
      rwa [QueryCache.cacheQuery_of_ne _ _ hcandidateInputNe]
    exact hbefore candidate hcandidate candidateAnswer hcandidateAfter

def PrematureLayerMessageSettlement (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (input : HashInput) (answer : HashOutput) : Prop :=
  ∃ (position : EncodingPosition) (index : Index),
    treeIndexAt index position.lay = position.tree
      ∧ leafIndexAt index position.lay = position.leafIdx
      ∧ ¬ Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
        (layerMessagePosition index position.lay)
      ∧ Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
        (cache.cacheQuery input answer) (layerMessagePosition index position.lay)
      ∧ ¬ AtPosition secretKey.parameter input
        (layerMessagePosition index position.lay)

theorem latentEncodingBad_step_classify
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {answer : HashOutput}
    (hclean : ¬ LatentEncodingBad cache secretKey)
    (huncached : cache input = none)
    (hbad : LatentEncodingBad (cache.cacheQuery input answer) secretKey) :
    (∃ position : EncodingPosition,
      AtEncodingPosition secretKey.parameter input position ∧
        truncateHash answer ∈
          encodingValidAnswerTargets secretKey.parameter cache hfinite position)
      ∨ (∃ (position : EncodingPosition) (index : Index),
        treeIndexAt index position.lay = position.tree ∧
          leafIndexAt index position.lay = position.leafIdx ∧
          ¬ Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
            (layerMessagePosition index position.lay) ∧
          Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
            (cache.cacheQuery input answer) (layerMessagePosition index position.lay) ∧
          AtPosition secretKey.parameter input
            (layerMessagePosition index position.lay) ∧
          truncateHash answer ∈
            encodingMessageTargets secretKey.parameter cache hfinite position)
      ∨ PrematureLayerMessageSettlement cache secretKey input answer := by
  classical
  by_cases hencoding : ∃ position,
      AtEncodingPosition secretKey.parameter input position
  · obtain ⟨position, hposition⟩ := hencoding
    exact Or.inl ⟨position, hposition,
      latentEncodingBad_validAnswer_hit_of_encoding_query hfinite hclean huncached
        hposition hbad⟩
  · right
    obtain ⟨position, index, counter, targetPayload, otherPayload, targetAnswer,
      otherAnswer, htree, hleaf, hsettledAfter, hpayload, htargetAnswer,
      htargetValid, hbefore, hpayloadNe, hotherAnswer, hcollision⟩ := hbad
    by_cases hsettled : Settled secretKey.parameter secretKey.otsSecret
        secretKey.ftsSecret cache (layerMessagePosition index position.lay)
    · exfalso
      apply hclean
      refine ⟨position, ?_⟩
      apply LatentEncodingBadAt.of_cacheQuery_of_settled_of_not_atEncoding
        huncached
      · intro candidate hcandidateTree hcandidateLeaf
        have hpositionEq := layerMessagePosition_eq_of_position_eq index candidate
          position.lay (htree.trans hcandidateTree.symm)
          (hleaf.trans hcandidateLeaf.symm)
        rwa [← hpositionEq]
      · exact fun hposition => hencoding ⟨position, hposition⟩
      · exact ⟨index, counter, targetPayload, otherPayload, targetAnswer,
          otherAnswer, htree, hleaf, hsettledAfter, hpayload, htargetAnswer,
          htargetValid, hbefore, hpayloadNe, hotherAnswer, hcollision⟩
    · by_cases hposition : AtPosition secretKey.parameter input
          (layerMessagePosition index position.lay)
      · left
        refine ⟨position, index, htree, hleaf, hsettled, hsettledAfter,
          hposition, ?_⟩
        apply latentEncodingBadAt_message_hit_of_settling_query hfinite huncached
          htree hleaf hposition hsettled
        exact ⟨index, counter, targetPayload, otherPayload, targetAnswer,
          otherAnswer, htree, hleaf, hsettledAfter, hpayload, htargetAnswer,
          htargetValid, hbefore, hpayloadNe, hotherAnswer, hcollision⟩
      · right
        exact ⟨position, index, htree, hleaf, hsettled, hsettledAfter, hposition⟩

theorem latentEncodingBadAt_step_classify
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {answer : HashOutput}
    {position : EncodingPosition}
    (hclean : ¬ LatentEncodingBadAt cache secretKey position)
    (huncached : cache input = none)
    (hbad : LatentEncodingBadAt (cache.cacheQuery input answer) secretKey position) :
    (AtEncodingPosition secretKey.parameter input position ∧
      truncateHash answer ∈
        encodingValidAnswerTargets secretKey.parameter cache hfinite position)
      ∨ (∃ index : Index,
        treeIndexAt index position.lay = position.tree ∧
          leafIndexAt index position.lay = position.leafIdx ∧
          ¬ Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
            (layerMessagePosition index position.lay) ∧
          Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
            (cache.cacheQuery input answer) (layerMessagePosition index position.lay) ∧
          AtPosition secretKey.parameter input
            (layerMessagePosition index position.lay) ∧
          truncateHash answer ∈
            encodingMessageTargets secretKey.parameter cache hfinite position)
      ∨ PrematureLayerMessageSettlement cache secretKey input answer := by
  classical
  by_cases hencoding : AtEncodingPosition secretKey.parameter input position
  · exact Or.inl ⟨hencoding,
      latentEncodingBadAt_answer_hit_of_encoding_query hfinite hclean huncached
        hencoding hbad⟩
  · right
    obtain ⟨index, counter, targetPayload, otherPayload, targetAnswer,
      otherAnswer, htree, hleaf, hsettledAfter, hpayload, htargetAnswer,
      htargetValid, hbefore, hpayloadNe, hotherAnswer, hcollision⟩ := hbad
    by_cases hsettled : Settled secretKey.parameter secretKey.otsSecret
        secretKey.ftsSecret cache (layerMessagePosition index position.lay)
    · exfalso
      apply hclean
      apply LatentEncodingBadAt.of_cacheQuery_of_settled_of_not_atEncoding
        huncached
      · intro candidate hcandidateTree hcandidateLeaf
        have hpositionEq := layerMessagePosition_eq_of_position_eq index candidate
          position.lay (htree.trans hcandidateTree.symm)
          (hleaf.trans hcandidateLeaf.symm)
        rwa [← hpositionEq]
      · exact hencoding
      · exact ⟨index, counter, targetPayload, otherPayload, targetAnswer,
          otherAnswer, htree, hleaf, hsettledAfter, hpayload, htargetAnswer,
          htargetValid, hbefore, hpayloadNe, hotherAnswer, hcollision⟩
    · by_cases hposition : AtPosition secretKey.parameter input
          (layerMessagePosition index position.lay)
      · left
        refine ⟨index, htree, hleaf, hsettled, hsettledAfter, hposition, ?_⟩
        apply latentEncodingBadAt_message_hit_of_settling_query hfinite huncached
          htree hleaf hposition hsettled
        exact ⟨index, counter, targetPayload, otherPayload, targetAnswer,
          otherAnswer, htree, hleaf, hsettledAfter, hpayload, htargetAnswer,
          htargetValid, hbefore, hpayloadNe, hotherAnswer, hcollision⟩
      · right
        exact ⟨position, index, htree, hleaf, hsettled, hsettledAfter, hposition⟩

theorem PrematureLayerMessageSettlement.mem_settlingTargets
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {answer : HashOutput}
    (huncached : cache input = none)
    (hpremature : PrematureLayerMessageSettlement cache secretKey input answer) :
    ∃ queriedPosition : Position,
      AtPosition secretKey.parameter input queriedPosition ∧
        ¬ Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
          cache queriedPosition ∧
        Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
          (cache.cacheQuery input answer) queriedPosition ∧
        truncateHash answer ∈
          settlingTargets secretKey.parameter cache hfinite queriedPosition := by
  obtain ⟨encodingPosition, index, htree, hleaf, htargetUnsettled,
    htargetSettled, hnotTarget⟩ := hpremature
  let targetPosition := layerMessagePosition index encodingPosition.lay
  have htargetUnsettled' : ¬ Settled secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret cache targetPosition := by
    simpa only [targetPosition] using htargetUnsettled
  have htargetSettled' : Settled secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret (cache.cacheQuery input answer) targetPosition := by
    simpa only [targetPosition] using htargetSettled
  have hnotTarget' : ¬ AtPosition secretKey.parameter input targetPosition := by
    simpa only [targetPosition] using hnotTarget
  have hat : ∃ queriedPosition, AtPosition secretKey.parameter input queriedPosition := by
    by_contra hnone
    apply htargetUnsettled'
    exact settled_of_settled_cacheQuery secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret huncached (p₀ := none)
      (fun position hposition => (hnone ⟨position, hposition⟩).elim)
      (by simp) (targetPosition.depth + 1) targetPosition (by omega) (by simp)
      htargetSettled'
  obtain ⟨queriedPosition, hqueried⟩ := hat
  have hqueriedNe : queriedPosition ≠ targetPosition := by
    intro heq
    exact hnotTarget' (heq ▸ hqueried)
  have hqueriedUnsettled : ¬ Settled secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret cache queriedPosition := by
    intro hsettled
    apply htargetUnsettled'
    exact settled_of_cacheQuery_at_settled secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret huncached hqueried hsettled
      (targetPosition.depth + 1) targetPosition (by omega) htargetSettled'
  have hpositionRule : ∀ position,
      AtPosition secretKey.parameter input position →
        some queriedPosition = some position := by
    intro position hposition
    exact congrArg some (atPosition_unique secretKey.parameter hqueried hposition)
  obtain ⟨parent, hparent, hparentSettled⟩ : ∃ parent,
      queriedPosition.parentOf = some parent ∧
        Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
          (cache.cacheQuery input answer) parent := by
    cases hparent : queriedPosition.parentOf with
    | none =>
        exfalso
        apply htargetUnsettled'
        exact settled_of_settled_cacheQuery secretKey.parameter secretKey.otsSecret
          secretKey.ftsSecret huncached (p₀ := some queriedPosition) hpositionRule
          (by
            intro position parent heq hparent'
            have hpositionEq : position = queriedPosition := Option.some.inj heq.symm
            subst position
            rw [hparent] at hparent'
            simp at hparent')
          (targetPosition.depth + 1) targetPosition (by omega)
          (by
            intro heq
            exact hqueriedNe (Option.some.inj heq)) htargetSettled'
    | some parent =>
        by_cases hsettledParent : Settled secretKey.parameter secretKey.otsSecret
            secretKey.ftsSecret (cache.cacheQuery input answer) parent
        · exact ⟨parent, rfl, hsettledParent⟩
        · exfalso
          apply htargetUnsettled'
          exact settled_of_settled_cacheQuery secretKey.parameter secretKey.otsSecret
            secretKey.ftsSecret huncached (p₀ := some queriedPosition) hpositionRule
            (by
              intro position candidateParent heq hparent'
              have hpositionEq : position = queriedPosition := Option.some.inj heq.symm
              subst position
              rw [hparent] at hparent'
              have : candidateParent = parent := Option.some.inj hparent'.symm
              subst candidateParent
              exact hsettledParent)
            (targetPosition.depth + 1) targetPosition (by omega)
            (by
              intro heq
              exact hqueriedNe (Option.some.inj heq)) htargetSettled'
  have hchild : queriedPosition ∈ parent.children :=
    Position.mem_children_iff.mpr hparent
  have hqueriedSettled : Settled secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret (cache.cacheQuery input answer) queriedPosition :=
    hparentSettled.children queriedPosition hchild
  have hslot : truncateHash answer ∈ slotTargets secretKey.parameter cache hfinite
      queriedPosition parent := by
    by_contra havoid
    exact (not_settled_parent_of_avoids_slotTargets secretKey.parameter
      secretKey.otsSecret secretKey.ftsSecret hfinite huncached hqueried
      hqueriedUnsettled hqueriedSettled hchild havoid) hparentSettled
  refine ⟨queriedPosition, hqueried, hqueriedUnsettled, hqueriedSettled, ?_⟩
  rw [settlingTargets, hparent]
  exact Finset.mem_union_right _ hslot

theorem latentEncodingBad_step_targets
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {answer : HashOutput}
    (hclean : ¬ LatentEncodingBad cache secretKey)
    (huncached : cache input = none)
    (hbad : LatentEncodingBad (cache.cacheQuery input answer) secretKey) :
    (∃ position : EncodingPosition,
      AtEncodingPosition secretKey.parameter input position ∧
        truncateHash answer ∈
          encodingValidAnswerTargets secretKey.parameter cache hfinite position)
      ∨ (∃ position : EncodingPosition,
        truncateHash answer ∈
          encodingMessageTargets secretKey.parameter cache hfinite position)
      ∨ ∃ position : Position,
        AtPosition secretKey.parameter input position ∧
          truncateHash answer ∈
            settlingTargets secretKey.parameter cache hfinite position := by
  rcases latentEncodingBad_step_classify hfinite hclean huncached hbad with
    hencoding | hmessage | hpremature
  · exact Or.inl hencoding
  · obtain ⟨position, index, htree, hleaf, hunsettled, hsettled,
      hposition, hmem⟩ := hmessage
    exact Or.inr (Or.inl ⟨position, hmem⟩)
  · obtain ⟨position, hposition, hunsettled, hsettled, hmem⟩ :=
      PrematureLayerMessageSettlement.mem_settlingTargets hfinite huncached hpremature
    exact Or.inr (Or.inr ⟨position, hposition, hmem⟩)

end SphincsSecurity.Concrete
