import SphincsSecurity.Proof.EncodingSelectionPotential

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] instFintypePosition
set_option backward.isDefEq.respectTransparency false

noncomputable def encodingCollisionPairs (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (position : EncodingPosition) : Finset ((HashInput × Digest) × (HashInput × Digest)) :=
  let candidates := encodingSelectionCandidates parameter cache hfinite position
  (candidates ×ˢ candidates).filter fun pair => pair.1.1 ≠ pair.2.1 ∧ pair.1.2 = pair.2.2

noncomputable def encodingCollisionMessageTargets (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (position : EncodingPosition) : Finset Digest :=
  (encodingCollisionPairs parameter cache hfinite position).image fun pair => slotDigest 0 pair.1.1

theorem encodingCollisionMessageTargets_card_le_pairs (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (position : EncodingPosition) :
    (encodingCollisionMessageTargets parameter cache hfinite position).card ≤
      (encodingCollisionPairs parameter cache hfinite position).card := Finset.card_image_le

theorem encodingCollisionMessageTargets_subset (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (position : EncodingPosition) :
    encodingCollisionMessageTargets parameter cache hfinite position ⊆ encodingMessageTargets parameter cache hfinite position := by
  intro message hmessage
  rw [encodingCollisionMessageTargets, Finset.mem_image] at hmessage
  obtain ⟨pair, hpair, rfl⟩ := hmessage
  rw [encodingCollisionPairs, Finset.mem_filter, Finset.mem_product] at hpair
  have hfirst := (mem_encodingSelectionCandidates_iff hfinite).mp hpair.1.1
  exact slotDigest_mem_encodingMessageTargets hfinite hfirst.1 hfirst.2.1

theorem encodingCollisionMessageTargets_card_le_cached (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (position : EncodingPosition) :
    (encodingCollisionMessageTargets parameter cache hfinite position).card ≤
      (encodingCachedAt parameter cache position).ncard :=
  (Finset.card_le_card (encodingCollisionMessageTargets_subset parameter cache hfinite position)).trans
    (encodingMessageTargets_card_le hfinite position)

theorem cached_encoding_collision_mem_messageTargets
    {parameter : PublicParameter} {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {position : EncodingPosition} {first second : HashInput} {left right : HashOutput}
    (hfirst : cache first = some left) (hsecond : cache second = some right)
    (hatFirst : AtEncodingPosition parameter first position) (hatSecond : AtEncodingPosition parameter second position)
    (hne : first ≠ second) (hvalid : TargetSum.ValidDigest (truncateHash left))
    (heq : truncateHash left = truncateHash right) :
    slotDigest 0 first ∈ encodingCollisionMessageTargets parameter cache hfinite position := by
  have hl : fromCache cache first = left := by simp [fromCache, hfirst]
  have hr : fromCache cache second = right := by simp [fromCache, hsecond]
  have hcFirst : (first, truncateHash left) ∈ encodingSelectionCandidates parameter cache hfinite position :=
    (mem_encodingSelectionCandidates_iff hfinite).mpr ⟨by simp [hfirst], hatFirst, hl ▸ hvalid, congrArg truncateHash hl.symm⟩
  have hcSecond : (second, truncateHash right) ∈ encodingSelectionCandidates parameter cache hfinite position :=
    (mem_encodingSelectionCandidates_iff hfinite).mpr ⟨by simp [hsecond], hatSecond, by simpa only [hr, ← heq] using hvalid,
      congrArg truncateHash hr.symm⟩
  rw [encodingCollisionMessageTargets, Finset.mem_image]
  refine ⟨((first, truncateHash left), (second, truncateHash right)), ?_, rfl⟩
  rw [encodingCollisionPairs, Finset.mem_filter, Finset.mem_product]
  exact ⟨⟨hcFirst, hcSecond⟩, hne, heq⟩

theorem latentEncodingBadAt_collisionMessage_hit_of_settling_query
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
      encodingCollisionMessageTargets secretKey.parameter cache hfinite position := by
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
  have htargetOld : cache targetInput = some targetAnswer := by
    change cache.cacheQuery input answer targetInput = some targetAnswer at htargetAnswer
    simpa only [QueryCache.cacheQuery_of_ne _ _ htargetInputNe] using htargetAnswer
  let otherInput := tweakableHashInput secretKey.parameter position.domain otherPayload
  have hotherInputNe : otherInput ≠ input := by
    intro heq
    exact (show AtEncodingPosition secretKey.parameter otherInput position from
      ⟨otherPayload, rfl⟩).not_atPosition
        (layerMessagePosition targetIndex position.lay) (heq ▸ htargetPosition)
  have hotherOld : cache otherInput = some otherAnswer := by
    change cache.cacheQuery input answer otherInput = some otherAnswer at hotherAnswer
    simpa only [QueryCache.cacheQuery_of_ne _ _ hotherInputNe] using hotherAnswer
  have hinputsNe : targetInput ≠ otherInput := by
    intro heq
    exact hpayloadNe (tweakableHashInput_injective secretKey.parameter
      (by trivial) (by trivial) heq).2
  have hmem := cached_encoding_collision_mem_messageTargets hfinite htargetOld hotherOld
    (show AtEncodingPosition secretKey.parameter targetInput position from ⟨targetPayload, rfl⟩)
    (show AtEncodingPosition secretKey.parameter otherInput position from ⟨otherPayload, rfl⟩)
    hinputsNe htargetValid hcollision
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

theorem encodingSelection_hasCachedHit_mem_collisionMessageTargets_of_newlySettled
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {answer : HashOutput}
    {position : EncodingPosition} {index : Index}
    (huncached : cache input = none)
    (htree : treeIndexAt index position.lay = position.tree)
    (hleaf : leafIndexAt index position.lay = position.leafIdx)
    (hunsettled : ¬ Settled secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret cache (layerMessagePosition index position.lay))
    (hsettled : Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
      (cache.cacheQuery input answer) (layerMessagePosition index position.lay))
    (hposition : AtPosition secretKey.parameter input
      (layerMessagePosition index position.lay))
    (hhit : EncodingSelection.HasCachedHit
      (encodingRetrySchedule secretKey.parameter (cache.cacheQuery input answer)
        position (encodingSettledMessage (cache.cacheQuery input answer) secretKey position))
      (encodingSelectionCandidates secretKey.parameter (cache.cacheQuery input answer)
        (finite_cacheQuery hfinite input answer) position)) :
    truncateHash answer ∈
      encodingCollisionMessageTargets secretKey.parameter cache hfinite position := by
  have hbad := latentEncodingBadAt_of_newlySettled_of_encodingSelection_hasCachedHit
    hfinite (show EncodingMessageSettledAt
      (cache.cacheQuery input answer) secretKey position from
        ⟨index, htree, hleaf, hsettled⟩) hhit
  exact latentEncodingBadAt_collisionMessage_hit_of_settling_query hfinite huncached
    htree hleaf hposition hunsettled hbad

end SphincsSecurity.Concrete
