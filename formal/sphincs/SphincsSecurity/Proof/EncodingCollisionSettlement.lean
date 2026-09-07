import SphincsSecurity.Proof.EncodingCollisionMessageTargets
import SphincsSecurity.Proof.EncodingWithoutParent

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem encodingSelectionContribution_cacheQuery_le_add_collisionMessageBonus
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {answer : HashOutput}
    {position : EncodingPosition} {index : Index}
    (huncached : cache input = none)
    (htree : treeIndexAt index position.lay = position.tree)
    (hleaf : leafIndexAt index position.lay = position.leafIdx)
    (hunsettled : ¬ Settled secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret cache (layerMessagePosition index position.lay))
    (hposition : AtPosition secretKey.parameter input
      (layerMessagePosition index position.lay)) :
    encodingSelectionContribution (cache.cacheQuery input answer)
        (finite_cacheQuery hfinite input answer) secretKey position ≤
      encodingSelectionContribution cache hfinite secretKey position +
        if truncateHash answer ∈
          encodingCollisionMessageTargets secretKey.parameter cache hfinite position then 1 else 0 := by
  have hnotAt : ¬ AtEncodingPosition secretKey.parameter input position :=
    fun hencoding => hencoding.not_atPosition
      (layerMessagePosition index position.lay) hposition
  have hmessageUnsettled : ¬ EncodingMessageSettledAt cache secretKey position := by
    rintro ⟨candidate, hcandidateTree, hcandidateLeaf, hcandidateSettled⟩
    have hpositionEq := layerMessagePosition_eq_of_position_eq index candidate
      position.lay (htree.trans hcandidateTree.symm)
      (hleaf.trans hcandidateLeaf.symm)
    apply hunsettled
    rwa [hpositionEq]
  by_cases hmessageSettled : EncodingMessageSettledAt
      (cache.cacheQuery input answer) secretKey position
  · by_cases hhit : EncodingSelection.HasCachedHit
        (encodingRetrySchedule secretKey.parameter (cache.cacheQuery input answer)
          position (encodingSettledMessage (cache.cacheQuery input answer) secretKey position))
        (encodingSelectionCandidates secretKey.parameter (cache.cacheQuery input answer)
          (finite_cacheQuery hfinite input answer) position)
    · obtain ⟨candidate, hcandidateTree, hcandidateLeaf, hcandidateSettled⟩ :=
        (show EncodingMessageSettledAt
          (cache.cacheQuery input answer) secretKey position from hmessageSettled)
      have hpositionEq := layerMessagePosition_eq_of_position_eq index candidate
        position.lay (htree.trans hcandidateTree.symm)
        (hleaf.trans hcandidateLeaf.symm)
      have hsettled : Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
          (cache.cacheQuery input answer) (layerMessagePosition index position.lay) := by
        rwa [hpositionEq]
      have hmem := encodingSelection_hasCachedHit_mem_collisionMessageTargets_of_newlySettled
        hfinite huncached htree hleaf hunsettled hsettled hposition hhit
      rw [if_pos hmem, encodingSelectionContribution_eq_conditional _ hmessageSettled]
      exact (encodingConditionalRiskAtMessage_le_one _).trans (le_add_left le_rfl)
    · exact (encodingSelectionContribution_cacheQuery_le_of_newlySettled_of_not_hasCachedHit
        hfinite hmessageUnsettled hmessageSettled hnotAt hhit).trans
          (le_add_right le_rfl)
  · exact
      (encodingSelectionContribution_cacheQuery_le_of_unsettled_of_stillUnsettled_of_not_atPosition
        hfinite huncached hmessageUnsettled hmessageSettled hnotAt).trans
          (le_add_right le_rfl)

theorem uniform_encodingSelectionContribution_cacheQuery_add_collisionMessageTargets_sum_le
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput}
    {position : EncodingPosition} {index : Index}
    (huncached : cache input = none)
    (htree : treeIndexAt index position.lay = position.tree)
    (hleaf : leafIndexAt index position.lay = position.leafIdx)
    (hunsettled : ¬ Settled secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret cache (layerMessagePosition index position.lay))
    (hposition : AtPosition secretKey.parameter input
      (layerMessagePosition index position.lay)) :
    (∑' answer : HashOutput,
      Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
        encodingSelectionContribution (cache.cacheQuery input answer)
          (finite_cacheQuery hfinite input answer) secretKey position) ≤
      encodingSelectionContribution cache hfinite secretKey position +
        (encodingCollisionMessageTargets secretKey.parameter cache hfinite position).card *
          (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  calc
    _ ≤ ∑' answer : HashOutput,
        Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (encodingSelectionContribution cache hfinite secretKey position +
            if truncateHash answer ∈
              encodingCollisionMessageTargets secretKey.parameter cache hfinite position then 1 else 0) := by
        apply ENNReal.tsum_le_tsum
        intro answer
        exact mul_le_mul_right
          (encodingSelectionContribution_cacheQuery_le_add_collisionMessageBonus hfinite
            huncached htree hleaf hunsettled hposition) _
    _ = encodingSelectionContribution cache hfinite secretKey position +
        ∑' answer : HashOutput,
          Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
            (if truncateHash answer ∈
              encodingCollisionMessageTargets secretKey.parameter cache hfinite position then 1 else 0) := by
        simp_rw [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right,
          tsum_probOutput_of_liftM_PMF, one_mul]
    _ = _ := by rw [uniformHashOutput_mem_bonus_sum_eq]

theorem encodingSelectionPotential_cacheQuery_le_without_parent_collisionTargets
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {answer : HashOutput} {queried : Position}
    (hfresh : cache input = none) (hat : AtPosition secretKey.parameter input queried)
    (hnoParent : ¬ ParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache input answer)
    (havoid : ∀ (position : EncodingPosition) (index : Index),
      treeIndexAt index position.lay = position.tree → leafIndexAt index position.lay = position.leafIdx →
      AtPosition secretKey.parameter input (layerMessagePosition index position.lay) →
      truncateHash answer ∉ encodingCollisionMessageTargets secretKey.parameter cache hfinite position) :
    encodingSelectionPotential (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) secretKey ≤
      encodingSelectionPotential cache hfinite secretKey := by
  classical
  rw [encodingSelectionPotential, encodingSelectionPotential]
  apply Finset.sum_le_sum
  intro position _
  have hnotAt : ¬ AtEncodingPosition secretKey.parameter input position := fun h => h.not_atPosition queried hat
  by_cases hbefore : EncodingMessageSettledAt cache secretKey position
  · exact le_of_eq (encodingSelectionContribution_cacheQuery_eq_of_settled_of_not_atPosition hfinite hfresh hbefore hnotAt)
  · by_cases hafter : EncodingMessageSettledAt (cache.cacheQuery input answer) secretKey position
    · apply encodingSelectionContribution_cacheQuery_le_of_newlySettled_of_not_hasCachedHit hfinite hbefore hafter hnotAt
      intro hhit
      obtain ⟨index, htree, hleaf, hsettled⟩ := hafter
      have hunsettled : ¬ Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache
          (layerMessagePosition index position.lay) := fun h => hbefore ⟨index, htree, hleaf, h⟩
      have hmessage : AtPosition secretKey.parameter input (layerMessagePosition index position.lay) := by
        by_contra hnot
        exact hunsettled (settled_of_cacheQuery_without_parent secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
          hfresh hat hnoParent (fun heq => hnot (heq ▸ hat)) hsettled)
      exact havoid position index htree hleaf hmessage
        (encodingSelection_hasCachedHit_mem_collisionMessageTargets_of_newlySettled hfinite hfresh htree hleaf hunsettled hsettled hmessage hhit)
    · exact encodingSelectionContribution_cacheQuery_le_of_unsettled_of_stillUnsettled_of_not_atPosition
        hfinite hfresh hbefore hafter hnotAt

end SphincsSecurity.Concrete
