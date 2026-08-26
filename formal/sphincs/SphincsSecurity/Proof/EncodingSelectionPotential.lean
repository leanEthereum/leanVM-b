import SphincsSecurity.Proof.EncodingSelectionCache
import SphincsSecurity.Proof.EncodingStageCharge

/-!
# Conditional encoding collision potential

Before an honest layer message is settled, the existing normalized valid-answer contribution
retains the risk of every cached encoding answer. Once the message is settled, the exact
cache-derived retry schedule replaces that coarse contribution.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

set_option maxRecDepth 100000

noncomputable def encodingSettledMessage
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (position : EncodingPosition) : Digest :=
  open Classical in
  if hsettled : EncodingMessageSettledAt cache secretKey position then
    honestValue (fromCache cache) secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret
      (layerMessagePosition (Classical.choose hsettled) position.lay)
  else
    0

theorem encodingSettledMessage_eq_of_witness
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {position : EncodingPosition} {index : Index}
    (htree : treeIndexAt index position.lay = position.tree)
    (hleaf : leafIndexAt index position.lay = position.leafIdx)
    (hsettled : Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
      cache (layerMessagePosition index position.lay)) :
    encodingSettledMessage cache secretKey position =
      honestValue (fromCache cache) secretKey.parameter secretKey.otsSecret
        secretKey.ftsSecret (layerMessagePosition index position.lay) := by
  classical
  rw [encodingSettledMessage, dif_pos ⟨index, htree, hleaf, hsettled⟩]
  have hchosen := Classical.choose_spec
    (show EncodingMessageSettledAt cache secretKey position from
      ⟨index, htree, hleaf, hsettled⟩)
  have hposition := layerMessagePosition_eq_of_position_eq
    (Classical.choose
      (show EncodingMessageSettledAt cache secretKey position from
        ⟨index, htree, hleaf, hsettled⟩))
    index position.lay (hchosen.1.trans htree.symm)
      (hchosen.2.1.trans hleaf.symm)
  rw [hposition]

theorem encodingSettledMessage_eq_of_le
    {cache cache' : QueryCache HashSpec} {secretKey : SecretKey}
    {position : EncodingPosition} (hle : cache ≤ cache')
    (hsettled : EncodingMessageSettledAt cache secretKey position) :
    encodingSettledMessage cache' secretKey position =
      encodingSettledMessage cache secretKey position := by
  obtain ⟨index, htree, hleaf, hposition⟩ := hsettled
  rw [encodingSettledMessage_eq_of_witness htree hleaf hposition,
    encodingSettledMessage_eq_of_witness htree hleaf (hposition.mono hle)]
  exact honestValue_eq_of_settled (agreesWithFn_fromCache_of_le hle) hposition

theorem encodingPosition_eq_of_layerMessagePosition_eq
    {left right : EncodingPosition} {leftIndex rightIndex : Index}
    (hleftTree : treeIndexAt leftIndex left.lay = left.tree)
    (hleftLeaf : leafIndexAt leftIndex left.lay = left.leafIdx)
    (hrightTree : treeIndexAt rightIndex right.lay = right.tree)
    (hrightLeaf : leafIndexAt rightIndex right.lay = right.leafIdx)
    (heq : layerMessagePosition leftIndex left.lay =
      layerMessagePosition rightIndex right.lay) :
    left = right := by
  obtain ⟨leftLay, leftTree, leftLeaf⟩ := left
  obtain ⟨rightLay, rightTree, rightLeaf⟩ := right
  have hlay : leftLay = rightLay := by
    fin_cases leftLay <;> fin_cases rightLay
    all_goals try rfl
    all_goals norm_num [layerMessagePosition, topLayer, middleLayer, bottomLayer,
      numLayers] at heq
    all_goals try { cases heq }
  subst rightLay
  fin_cases leftLay
  · have hnext : treeIndexAt leftIndex middleLayer =
        treeIndexAt rightIndex middleLayer := by
      change layerMessagePosition leftIndex topLayer =
        layerMessagePosition rightIndex topLayer at heq
      simp only [layerMessagePosition_top, Position.node.injEq] at heq
      exact heq.2.1
    change treeIndexAt leftIndex topLayer = leftTree at hleftTree
    change leafIndexAt leftIndex topLayer = leftLeaf at hleftLeaf
    change treeIndexAt rightIndex topLayer = rightTree at hrightTree
    change leafIndexAt rightIndex topLayer = rightLeaf at hrightLeaf
    have hnextVal := congrArg Fin.val hnext
    have hleftLink := layers_link_top leftIndex
    have hrightLink := layers_link_top rightIndex
    have hleftTreeVal := congrArg Fin.val hleftTree
    have hrightTreeVal := congrArg Fin.val hrightTree
    have hleftLeafVal := congrArg Fin.val hleftLeaf
    have hrightLeafVal := congrArg Fin.val hrightLeaf
    have hleftTop := treeIndexAt_topLayer leftIndex
    have hrightTop := treeIndexAt_topLayer rightIndex
    have htreeEq : leftTree = rightTree := by
      rw [← hleftTree, ← hrightTree]
      apply Fin.ext
      rw [treeIndexAt_topLayer, treeIndexAt_topLayer]
    have hleafEq : leftLeaf = rightLeaf := by
      rw [← hleftLeaf, ← hrightLeaf]
      apply Fin.ext
      norm_num [layerHeight] at hleftLink hrightLink
      rw [hleftTop] at hleftLink
      rw [hrightTop] at hrightLink
      omega
    cases htreeEq
    cases hleafEq
    rfl
  · have hnext : treeIndexAt leftIndex bottomLayer =
        treeIndexAt rightIndex bottomLayer := by
      change layerMessagePosition leftIndex middleLayer =
        layerMessagePosition rightIndex middleLayer at heq
      simp only [layerMessagePosition_middle, Position.node.injEq] at heq
      exact heq.2.1
    change treeIndexAt leftIndex middleLayer = leftTree at hleftTree
    change leafIndexAt leftIndex middleLayer = leftLeaf at hleftLeaf
    change treeIndexAt rightIndex middleLayer = rightTree at hrightTree
    change leafIndexAt rightIndex middleLayer = rightLeaf at hrightLeaf
    have hnextVal := congrArg Fin.val hnext
    have hleftLink := layers_link_middle leftIndex
    have hrightLink := layers_link_middle rightIndex
    norm_num [show layerHeight middleLayer = 7 by decide] at hleftLink hrightLink
    have hleftLeafLt : (leafIndexAt leftIndex middleLayer).val < 128 := by
      simpa [layerHeight, middleLayer] using leafIndexAt_lt leftIndex middleLayer
    have hrightLeafLt : (leafIndexAt rightIndex middleLayer).val < 128 := by
      simpa [layerHeight, middleLayer] using leafIndexAt_lt rightIndex middleLayer
    have hleftTreeFormula : (treeIndexAt leftIndex middleLayer).val =
        (treeIndexAt leftIndex bottomLayer).val / 128 := by
      rw [Nat.mul_comm (treeIndexAt leftIndex middleLayer).val 128] at hleftLink
      rw [hleftLink]
      rw [Nat.mul_add_div (by norm_num), Nat.div_eq_of_lt hleftLeafLt, Nat.add_zero]
    have hrightTreeFormula : (treeIndexAt rightIndex middleLayer).val =
        (treeIndexAt rightIndex bottomLayer).val / 128 := by
      rw [Nat.mul_comm (treeIndexAt rightIndex middleLayer).val 128] at hrightLink
      rw [hrightLink]
      rw [Nat.mul_add_div (by norm_num), Nat.div_eq_of_lt hrightLeafLt, Nat.add_zero]
    have hleftLeafFormula : (leafIndexAt leftIndex middleLayer).val =
        (treeIndexAt leftIndex bottomLayer).val % 128 := by
      rw [hleftLink]
      rw [Nat.mul_comm (treeIndexAt leftIndex middleLayer).val 128]
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hleftLeafLt]
    have hrightLeafFormula : (leafIndexAt rightIndex middleLayer).val =
        (treeIndexAt rightIndex bottomLayer).val % 128 := by
      rw [hrightLink]
      rw [Nat.mul_comm (treeIndexAt rightIndex middleLayer).val 128]
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hrightLeafLt]
    have htreeEq : leftTree = rightTree := by
      rw [← hleftTree, ← hrightTree]
      apply Fin.ext
      rw [hleftTreeFormula, hrightTreeFormula, hnextVal]
    have hleafEq : leftLeaf = rightLeaf := by
      rw [← hleftLeaf, ← hrightLeaf]
      apply Fin.ext
      rw [hleftLeafFormula, hrightLeafFormula, hnextVal]
    cases htreeEq
    cases hleafEq
    rfl
  · have hindex : leftIndex = rightIndex := by
      change layerMessagePosition leftIndex bottomLayer =
        layerMessagePosition rightIndex bottomLayer at heq
      simpa only [layerMessagePosition_bottom, Position.ftsRoots.injEq] using heq
    subst rightIndex
    change treeIndexAt leftIndex bottomLayer = leftTree at hleftTree
    change leafIndexAt leftIndex bottomLayer = leftLeaf at hleftLeaf
    change treeIndexAt leftIndex bottomLayer = rightTree at hrightTree
    change leafIndexAt leftIndex bottomLayer = rightLeaf at hrightLeaf
    have htreeEq : leftTree = rightTree := hleftTree.symm.trans hrightTree
    have hleafEq : leftLeaf = rightLeaf := hleftLeaf.symm.trans hrightLeaf
    cases htreeEq
    cases hleafEq
    rfl

theorem EncodingMessageSettledAt.of_cacheQuery_of_atEncoding
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {input : HashInput} {answer : HashOutput} {queriedPosition : EncodingPosition}
    (huncached : cache input = none)
    (hqueried : AtEncodingPosition secretKey.parameter input queriedPosition)
    {position : EncodingPosition}
    (hsettled : EncodingMessageSettledAt
      (cache.cacheQuery input answer) secretKey position) :
    EncodingMessageSettledAt cache secretKey position := by
  obtain ⟨index, htree, hleaf, hposition⟩ := hsettled
  refine ⟨index, htree, hleaf, ?_⟩
  exact settled_of_settled_cacheQuery secretKey.parameter secretKey.otsSecret
    secretKey.ftsSecret huncached (p₀ := none)
    (fun structuralPosition hat =>
      (hqueried.not_atPosition structuralPosition hat).elim)
    (by simp) ((layerMessagePosition index position.lay).depth + 1)
    (layerMessagePosition index position.lay) (by omega) (by simp) hposition

noncomputable def encodingSelectionContribution
    (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (secretKey : SecretKey) (position : EncodingPosition) : ℝ≥0∞ :=
  open Classical in
  if EncodingMessageSettledAt cache secretKey position then
    encodingConditionalRiskAtMessage secretKey.parameter cache hfinite position
      (encodingSettledMessage cache secretKey position)
  else
    encodingRetryContribution cache secretKey position

noncomputable def encodingSelectionPotential
    (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (secretKey : SecretKey) : ℝ≥0∞ :=
  ∑ position : EncodingPosition,
    encodingSelectionContribution cache hfinite secretKey position

noncomputable def encodingSelectionTotalPotential
    (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (secretKey : SecretKey) : ℝ≥0∞ :=
  open Classical in
  if Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache then 0
  else if LatentEncodingBad cache secretKey then 1
  else min 1 ((encodingStructuralPotential cache secretKey : ℝ≥0∞) *
      (Fintype.card Digest : ℝ≥0∞)⁻¹ +
    encodingSelectionPotential cache hfinite secretKey)

theorem encodingSelectionContribution_eq_conditional
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {position : EncodingPosition}
    (hsettled : EncodingMessageSettledAt cache secretKey position) :
    encodingSelectionContribution cache hfinite secretKey position =
      encodingConditionalRiskAtMessage secretKey.parameter cache hfinite position
        (encodingSettledMessage cache secretKey position) := by
  rw [encodingSelectionContribution, if_pos hsettled]

theorem encodingSelectionContribution_eq_retry
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {position : EncodingPosition}
    (hunsettled : ¬ EncodingMessageSettledAt cache secretKey position) :
    encodingSelectionContribution cache hfinite secretKey position =
      encodingRetryContribution cache secretKey position := by
  rw [encodingSelectionContribution, if_neg hunsettled]

theorem encodingSelectionContribution_cacheQuery_eq_of_settled_of_not_atPosition
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {answer : HashOutput}
    {position : EncodingPosition} (huncached : cache input = none)
    (hsettled : EncodingMessageSettledAt cache secretKey position)
    (hnotAt : ¬ AtEncodingPosition secretKey.parameter input position) :
    encodingSelectionContribution (cache.cacheQuery input answer)
        (finite_cacheQuery hfinite input answer) secretKey position =
      encodingSelectionContribution cache hfinite secretKey position := by
  have hle := le_cacheQuery (cache := cache) (input := input) (answer := answer) huncached
  rw [encodingSelectionContribution_eq_conditional _ (hsettled.mono hle),
    encodingSelectionContribution_eq_conditional hfinite hsettled,
    encodingSettledMessage_eq_of_le hle hsettled,
    encodingConditionalRiskAtMessage_cacheQuery_eq_of_not_atPosition hfinite hnotAt]

theorem encodingSelectionContribution_cacheQuery_le_of_unsettled_of_stillUnsettled_of_not_atPosition
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {answer : HashOutput}
    {position : EncodingPosition} (huncached : cache input = none)
    (hunsettled : ¬ EncodingMessageSettledAt cache secretKey position)
    (hstillUnsettled : ¬ EncodingMessageSettledAt
      (cache.cacheQuery input answer) secretKey position)
    (hnotAt : ¬ AtEncodingPosition secretKey.parameter input position) :
    encodingSelectionContribution (cache.cacheQuery input answer)
        (finite_cacheQuery hfinite input answer) secretKey position ≤
      encodingSelectionContribution cache hfinite secretKey position := by
  rw [encodingSelectionContribution_eq_retry _ hstillUnsettled,
    encodingSelectionContribution_eq_retry hfinite hunsettled]
  exact encodingRetryContribution_cacheQuery_le_of_not_atPosition
    huncached position hnotAt

theorem encodingSelectionContribution_cacheQuery_le_of_newlySettled_of_not_hasCachedHit
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {answer : HashOutput}
    {position : EncodingPosition}
    (hunsettled : ¬ EncodingMessageSettledAt cache secretKey position)
    (hsettled : EncodingMessageSettledAt
      (cache.cacheQuery input answer) secretKey position)
    (hnotAt : ¬ AtEncodingPosition secretKey.parameter input position)
    (hclean : ¬ EncodingSelection.HasCachedHit
      (encodingRetrySchedule secretKey.parameter (cache.cacheQuery input answer)
        position (encodingSettledMessage (cache.cacheQuery input answer) secretKey position))
      (encodingSelectionCandidates secretKey.parameter (cache.cacheQuery input answer)
        (finite_cacheQuery hfinite input answer) position)) :
    encodingSelectionContribution (cache.cacheQuery input answer)
        (finite_cacheQuery hfinite input answer) secretKey position ≤
      encodingSelectionContribution cache hfinite secretKey position := by
  have hnotTarget : ¬ HasEncodingTarget cache secretKey position :=
    fun htarget => hunsettled htarget.messageSettled
  rw [encodingSelectionContribution_eq_conditional _ hsettled,
    encodingSelectionContribution_eq_retry hfinite hunsettled,
    encodingConditionalRiskAtMessage]
  calc
    EncodingSelection.selectionRisk
        (encodingRetrySchedule secretKey.parameter (cache.cacheQuery input answer)
          position (encodingSettledMessage (cache.cacheQuery input answer) secretKey position))
        (encodingSelectionCandidates secretKey.parameter (cache.cacheQuery input answer)
          (finite_cacheQuery hfinite input answer) position) ≤
      EncodingRetry.pendingRisk
        (EncodingSelection.targetDigests
          (encodingSelectionCandidates secretKey.parameter (cache.cacheQuery input answer)
            (finite_cacheQuery hfinite input answer) position)) :=
      EncodingSelection.selectionRisk_le_pendingRisk_of_not_hasCachedHit _ _ hclean
    _ = EncodingRetry.pendingRisk
        (EncodingSelection.targetDigests
          (encodingSelectionCandidates secretKey.parameter cache hfinite position)) := by
      rw [encodingSelectionCandidates_cacheQuery_of_not_atPosition hfinite hnotAt]
    _ = EncodingRetry.pendingRisk
        (encodingValidAnswerTargets secretKey.parameter cache hfinite position) := by
      rw [targetDigests_encodingSelectionCandidates]
    _ = encodingRetryContribution cache secretKey position :=
      (encodingRetryContribution_eq_pendingRisk hfinite hnotTarget).symm

theorem latentEncodingBadAt_of_newlySettled_of_encodingSelection_hasCachedHit
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {answer : HashOutput}
    {position : EncodingPosition}
    (hsettled : EncodingMessageSettledAt
      (cache.cacheQuery input answer) secretKey position)
    (hhit : EncodingSelection.HasCachedHit
      (encodingRetrySchedule secretKey.parameter (cache.cacheQuery input answer)
        position (encodingSettledMessage (cache.cacheQuery input answer) secretKey position))
      (encodingSelectionCandidates secretKey.parameter (cache.cacheQuery input answer)
        (finite_cacheQuery hfinite input answer) position)) :
    LatentEncodingBadAt (cache.cacheQuery input answer) secretKey position := by
  obtain ⟨index, htree, hleaf, hposition⟩ := hsettled
  exact latentEncodingBadAt_of_encodingSelection_hasCachedHit
    (finite_cacheQuery hfinite input answer) htree hleaf hposition
    (encodingSettledMessage_eq_of_witness htree hleaf hposition) hhit

theorem encodingConditionalRiskAtMessage_le_one
    {parameter : PublicParameter} {cache : QueryCache HashSpec}
    (hfinite : Finite cache) {position : EncodingPosition} {message : Digest} :
    encodingConditionalRiskAtMessage parameter cache hfinite position message ≤ 1 := by
  rw [encodingConditionalRiskAtMessage]
  exact probEvent_le_one

theorem encodingSelection_hasCachedHit_mem_messageTargets_of_newlySettled
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
      encodingMessageTargets secretKey.parameter cache hfinite position := by
  have hbad := latentEncodingBadAt_of_newlySettled_of_encodingSelection_hasCachedHit
    hfinite (show EncodingMessageSettledAt
      (cache.cacheQuery input answer) secretKey position from
        ⟨index, htree, hleaf, hsettled⟩) hhit
  exact latentEncodingBadAt_message_hit_of_settling_query hfinite huncached
    htree hleaf hposition hunsettled hbad

theorem encodingSelection_hasCachedHit_mem_settlingTargets_of_prematureSettlement
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {answer : HashOutput}
    {position : EncodingPosition} {index : Index} {queriedPosition : Position}
    (huncached : cache input = none)
    (htree : treeIndexAt index position.lay = position.tree)
    (hleaf : leafIndexAt index position.lay = position.leafIdx)
    (hunsettled : ¬ Settled secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret cache (layerMessagePosition index position.lay))
    (hsettled : Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
      (cache.cacheQuery input answer) (layerMessagePosition index position.lay))
    (hnotMessage : ¬ AtPosition secretKey.parameter input
      (layerMessagePosition index position.lay))
    (hqueried : AtPosition secretKey.parameter input queriedPosition)
    (hhit : EncodingSelection.HasCachedHit
      (encodingRetrySchedule secretKey.parameter (cache.cacheQuery input answer)
        position (encodingSettledMessage (cache.cacheQuery input answer) secretKey position))
      (encodingSelectionCandidates secretKey.parameter (cache.cacheQuery input answer)
        (finite_cacheQuery hfinite input answer) position)) :
    truncateHash answer ∈
      settlingTargets secretKey.parameter cache hfinite queriedPosition := by
  have hbad := latentEncodingBadAt_of_newlySettled_of_encodingSelection_hasCachedHit
    hfinite (show EncodingMessageSettledAt
      (cache.cacheQuery input answer) secretKey position from
        ⟨index, htree, hleaf, hsettled⟩) hhit
  obtain ⟨targetIndex, counter, targetPayload, otherPayload, targetAnswer,
    otherAnswer, htargetTree, htargetLeaf, htargetSettled, hpayload,
    htargetAnswer, htargetValid, hbefore, hpayloadNe, hotherAnswer,
    hcollision⟩ := hbad
  have hmessagePosition : layerMessagePosition index position.lay =
      layerMessagePosition targetIndex position.lay :=
    layerMessagePosition_eq_of_position_eq index targetIndex position.lay
      (htree.trans htargetTree.symm) (hleaf.trans htargetLeaf.symm)
  have hpremature : PrematureLayerMessageSettlement cache secretKey input answer :=
    ⟨position, targetIndex, htargetTree, htargetLeaf,
      by rwa [← hmessagePosition], htargetSettled,
      by rwa [← hmessagePosition]⟩
  obtain ⟨candidate, hcandidate, _, _, hmem⟩ :=
      hpremature.mem_settlingTargets hfinite huncached
  have heq : candidate = queriedPosition :=
    atPosition_unique secretKey.parameter hcandidate hqueried
  simpa only [heq] using hmem

theorem encodingSelectionContribution_cacheQuery_le_add_messageBonus
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
          encodingMessageTargets secretKey.parameter cache hfinite position then 1 else 0 := by
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
      have hmem := encodingSelection_hasCachedHit_mem_messageTargets_of_newlySettled
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

theorem uniform_encodingSelectionContribution_cacheQuery_add_messageTargets_sum_le
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
        (encodingMessageTargets secretKey.parameter cache hfinite position).card *
          (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  calc
    _ ≤ ∑' answer : HashOutput,
        Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (encodingSelectionContribution cache hfinite secretKey position +
            if truncateHash answer ∈
              encodingMessageTargets secretKey.parameter cache hfinite position then 1 else 0) := by
        apply ENNReal.tsum_le_tsum
        intro answer
        exact mul_le_mul_right
          (encodingSelectionContribution_cacheQuery_le_add_messageBonus hfinite
            huncached htree hleaf hunsettled hposition) _
    _ = encodingSelectionContribution cache hfinite secretKey position +
        ∑' answer : HashOutput,
          Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
            (if truncateHash answer ∈
              encodingMessageTargets secretKey.parameter cache hfinite position then 1 else 0) := by
        simp_rw [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right,
          tsum_probOutput_of_liftM_PMF, one_mul]
    _ = _ := by rw [uniformHashOutput_mem_bonus_sum_eq]

theorem encodingSelectionContribution_cacheQuery_le_add_settlingBonus
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {answer : HashOutput}
    {position : EncodingPosition} {index : Index} {queriedPosition : Position}
    (huncached : cache input = none)
    (htree : treeIndexAt index position.lay = position.tree)
    (hleaf : leafIndexAt index position.lay = position.leafIdx)
    (hunsettled : ¬ Settled secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret cache (layerMessagePosition index position.lay))
    (hnotMessage : ¬ AtPosition secretKey.parameter input
      (layerMessagePosition index position.lay))
    (hqueried : AtPosition secretKey.parameter input queriedPosition) :
    encodingSelectionContribution (cache.cacheQuery input answer)
        (finite_cacheQuery hfinite input answer) secretKey position ≤
      encodingSelectionContribution cache hfinite secretKey position +
        if truncateHash answer ∈
          settlingTargets secretKey.parameter cache hfinite queriedPosition then 1 else 0 := by
  have hnotAt : ¬ AtEncodingPosition secretKey.parameter input position :=
    fun hencoding => hencoding.not_atPosition queriedPosition hqueried
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
      have hmem :=
        encodingSelection_hasCachedHit_mem_settlingTargets_of_prematureSettlement
          hfinite huncached htree hleaf hunsettled hsettled hnotMessage hqueried hhit
      rw [if_pos hmem, encodingSelectionContribution_eq_conditional _ hmessageSettled]
      exact (encodingConditionalRiskAtMessage_le_one _).trans (le_add_left le_rfl)
    · exact (encodingSelectionContribution_cacheQuery_le_of_newlySettled_of_not_hasCachedHit
        hfinite hmessageUnsettled hmessageSettled hnotAt hhit).trans
          (le_add_right le_rfl)
  · exact
      (encodingSelectionContribution_cacheQuery_le_of_unsettled_of_stillUnsettled_of_not_atPosition
        hfinite huncached hmessageUnsettled hmessageSettled hnotAt).trans
          (le_add_right le_rfl)

theorem uniform_encodingSelectionContribution_cacheQuery_add_settlingTargets_sum_le
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput}
    {position : EncodingPosition} {index : Index} {queriedPosition : Position}
    (huncached : cache input = none)
    (htree : treeIndexAt index position.lay = position.tree)
    (hleaf : leafIndexAt index position.lay = position.leafIdx)
    (hunsettled : ¬ Settled secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret cache (layerMessagePosition index position.lay))
    (hnotMessage : ¬ AtPosition secretKey.parameter input
      (layerMessagePosition index position.lay))
    (hqueried : AtPosition secretKey.parameter input queriedPosition) :
    (∑' answer : HashOutput,
      Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
        encodingSelectionContribution (cache.cacheQuery input answer)
          (finite_cacheQuery hfinite input answer) secretKey position) ≤
      encodingSelectionContribution cache hfinite secretKey position +
        (settlingTargets secretKey.parameter cache hfinite queriedPosition).card *
          (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  calc
    _ ≤ ∑' answer : HashOutput,
        Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (encodingSelectionContribution cache hfinite secretKey position +
            if truncateHash answer ∈
              settlingTargets secretKey.parameter cache hfinite queriedPosition then 1 else 0) := by
        apply ENNReal.tsum_le_tsum
        intro answer
        exact mul_le_mul_right
          (encodingSelectionContribution_cacheQuery_le_add_settlingBonus hfinite
            huncached htree hleaf hunsettled hnotMessage hqueried) _
    _ = encodingSelectionContribution cache hfinite secretKey position +
        ∑' answer : HashOutput,
          Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
            (if truncateHash answer ∈
              settlingTargets secretKey.parameter cache hfinite queriedPosition then 1 else 0) := by
        simp_rw [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right,
          tsum_probOutput_of_liftM_PMF, one_mul]
    _ = _ := by rw [uniformHashOutput_mem_bonus_sum_eq]

theorem uniform_encodingSelectionContribution_cacheQuery_atPosition_sum_le
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {position : EncodingPosition}
    (huncached : cache input = none)
    (hposition : AtEncodingPosition secretKey.parameter input position) :
    (∑' answer : HashOutput,
      Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
        encodingSelectionContribution (cache.cacheQuery input answer)
          (finite_cacheQuery hfinite input answer) secretKey position) ≤
      encodingSelectionContribution cache hfinite secretKey position +
        (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  have hle (answer : HashOutput) :=
    le_cacheQuery (cache := cache) (input := input) (answer := answer) huncached
  by_cases hsettled : EncodingMessageSettledAt cache secretKey position
  · simp_rw [encodingSelectionContribution_eq_conditional _ (hsettled.mono (hle _)),
      encodingSettledMessage_eq_of_le (hle _) hsettled]
    rw [encodingSelectionContribution_eq_conditional hfinite hsettled]
    exact uniform_encodingConditionalRiskAtMessage_cacheQuery_sum_le
      hfinite huncached hposition
  · have hstillUnsettled : ∀ answer : HashOutput,
        ¬ EncodingMessageSettledAt (cache.cacheQuery input answer) secretKey position := by
      intro answer hafter
      exact hsettled (hafter.of_cacheQuery_of_atEncoding huncached hposition)
    simp_rw [encodingSelectionContribution_eq_retry _ (hstillUnsettled _)]
    rw [encodingSelectionContribution_eq_retry hfinite hsettled]
    calc
      _ ≤ ∑' answer : HashOutput,
          Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
            (encodingRetryContribution cache secretKey position +
              if TargetSum.ValidDigest (truncateHash answer) then
                (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ else 0) := by
          apply ENNReal.tsum_le_tsum
          intro answer
          gcongr
          exact encodingRetryContribution_cacheQuery_le hfinite huncached position
      _ = encodingRetryContribution cache secretKey position +
          ∑' answer : HashOutput,
            Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
              (if TargetSum.ValidDigest (truncateHash answer) then
                (TargetSum.validDigests.card : ℝ≥0∞)⁻¹ else 0) := by
          simp_rw [mul_add]
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right,
            tsum_probOutput_of_liftM_PMF, one_mul]
      _ = _ := by rw [uniformHashOutput_valid_bonus_sum_eq]

theorem encodingSelectionContribution_cacheQuery_le_of_other_encodingPosition
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {answer : HashOutput}
    {queriedPosition position : EncodingPosition}
    (huncached : cache input = none)
    (hqueried : AtEncodingPosition secretKey.parameter input queriedPosition)
    (hne : position ≠ queriedPosition) :
    encodingSelectionContribution (cache.cacheQuery input answer)
        (finite_cacheQuery hfinite input answer) secretKey position ≤
      encodingSelectionContribution cache hfinite secretKey position := by
  have hnotAt : ¬ AtEncodingPosition secretKey.parameter input position := by
    intro hposition
    exact hne (atEncodingPosition_unique hposition hqueried)
  by_cases hsettled : EncodingMessageSettledAt cache secretKey position
  · exact le_of_eq
      (encodingSelectionContribution_cacheQuery_eq_of_settled_of_not_atPosition
        hfinite huncached hsettled hnotAt)
  · have hstillUnsettled : ¬ EncodingMessageSettledAt
        (cache.cacheQuery input answer) secretKey position := by
      intro hafter
      exact hsettled (hafter.of_cacheQuery_of_atEncoding huncached hqueried)
    exact
      encodingSelectionContribution_cacheQuery_le_of_unsettled_of_stillUnsettled_of_not_atPosition
        hfinite huncached hsettled hstillUnsettled hnotAt

theorem uniform_encodingSelectionPotential_cacheQuery_atPosition_sum_le
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {position : EncodingPosition}
    (huncached : cache input = none)
    (hposition : AtEncodingPosition secretKey.parameter input position) :
    (∑' answer : HashOutput,
      Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
        encodingSelectionPotential (cache.cacheQuery input answer)
          (finite_cacheQuery hfinite input answer) secretKey) ≤
      encodingSelectionPotential cache hfinite secretKey +
        (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  simp only [encodingSelectionPotential]
  calc
    _ = ∑ candidate : EncodingPosition,
        ∑' answer : HashOutput,
          Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
            encodingSelectionContribution (cache.cacheQuery input answer)
              (finite_cacheQuery hfinite input answer) secretKey candidate := by
        simp_rw [Finset.mul_sum]
        exact Summable.tsum_finsetSum fun _ _ => ENNReal.summable
    _ ≤ ∑ candidate : EncodingPosition,
        (encodingSelectionContribution cache hfinite secretKey candidate +
          if candidate = position then
            (Fintype.card Digest : ℝ≥0∞)⁻¹ else 0) := by
        apply Finset.sum_le_sum
        intro candidate _
        by_cases heq : candidate = position
        · rw [if_pos heq]
          simpa only [heq] using
            uniform_encodingSelectionContribution_cacheQuery_atPosition_sum_le
              hfinite huncached hposition
        · rw [if_neg heq, add_zero]
          calc
            _ ≤ ∑' answer : HashOutput,
                Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                  encodingSelectionContribution cache hfinite secretKey candidate := by
                    apply ENNReal.tsum_le_tsum
                    intro answer
                    exact mul_le_mul_right
                      (encodingSelectionContribution_cacheQuery_le_of_other_encodingPosition
                        hfinite huncached hposition heq) _
            _ = _ := by
              rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
    _ = (∑ candidate : EncodingPosition,
          encodingSelectionContribution cache hfinite secretKey candidate) +
        (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
          rw [Finset.sum_add_distrib, Fintype.sum_ite_eq']

theorem encodingSelectionContribution_eq_one_of_collision
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {position : EncodingPosition}
    {signedPayload otherPayload : HashInput}
    {signedAnswer otherAnswer : HashOutput}
    (htarget : CachedSignedEncodingPayloadAt cache secretKey position.lay
      position.tree position.leafIdx signedPayload)
    (hpayloadNe : signedPayload ≠ otherPayload)
    (hsignedAnswer : cache (tweakableHashInput secretKey.parameter
      position.domain signedPayload) = some signedAnswer)
    (hotherAnswer : cache (tweakableHashInput secretKey.parameter
      position.domain otherPayload) = some otherAnswer)
    (hcollision : truncateHash signedAnswer = truncateHash otherAnswer) :
    encodingSelectionContribution cache hfinite secretKey position = 1 := by
  have htargetData := htarget
  obtain ⟨index, selected, htree, hleaf, hsettled, hrun, hselected,
    hpayload, _⟩ := htargetData
  let message := honestValue (fromCache cache) secretKey.parameter
    secretKey.otsSecret secretKey.ftsSecret (layerMessagePosition index position.lay)
  have hmessageSettled : EncodingMessageSettledAt cache secretKey position :=
    ⟨index, htree, hleaf, hsettled⟩
  have hmessage : encodingSettledMessage cache secretKey position = message :=
    encodingSettledMessage_eq_of_witness htree hleaf hsettled
  rw [encodingSelectionContribution_eq_conditional hfinite hmessageSettled, hmessage]
  rw [htree, hleaf] at hselected hrun
  apply encodingConditionalRiskAtMessage_eq_one_of_encodingSearch_hit
    (parameter := secretKey.parameter) (cache := cache) (position := position)
    (message := message) (selected := selected) hfinite hselected hrun
  have hofNat : BitVec.ofNat counterBits selected.toNat = selected := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  let signedInput := tweakableHashInput secretKey.parameter position.domain signedPayload
  let otherInput := tweakableHashInput secretKey.parameter position.domain otherPayload
  change signedPayload = digestBytes message ++ counterBytes selected at hpayload
  have hselectedInput : encodingRetryInput secretKey.parameter position message selected.toNat =
      signedInput := by
    rw [encodingRetryInput, hofNat, ← hpayload]
  have hsignedFromCache : fromCache cache signedInput = signedAnswer := by
    simp [signedInput, fromCache, hsignedAnswer]
  have hotherFromCache : fromCache cache otherInput = otherAnswer := by
    simp [otherInput, fromCache, hotherAnswer]
  have hvalid : TargetSum.ValidDigest (truncateHash signedAnswer) := by
    have hvalid := htarget.target_valid
    change TargetSum.ValidDigest (truncateHash (fromCache cache signedInput)) at hvalid
    rwa [hsignedFromCache] at hvalid
  refine ⟨(otherInput, truncateHash otherAnswer), ?_, ?_, ?_⟩
  · rw [mem_encodingSelectionCandidates_iff hfinite]
    exact ⟨by simp [hotherAnswer, otherInput], ⟨otherPayload, rfl⟩,
      hvalid.of_eq (hcollision.trans (congrArg truncateHash hotherFromCache).symm),
      by rw [hotherFromCache]⟩
  · rw [hselectedInput]
    intro hinput
    apply hpayloadNe
    exact (tweakableHashInput_injective secretKey.parameter (by trivial) (by trivial)
      hinput.symm).2
  · rw [hselectedInput, hsignedFromCache]
    exact hcollision.symm

theorem one_le_encodingSelectionPotential_of_encodingBad
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} (hbad : EncodingBad cache secretKey) :
    1 ≤ encodingSelectionPotential cache hfinite secretKey := by
  obtain ⟨lay, tree, leafIdx, signedPayload, otherPayload, signedAnswer,
    otherAnswer, htarget, hpayloadNe, hsignedAnswer, hotherAnswer, hcollision⟩ := hbad
  let position : EncodingPosition := ⟨lay, tree, leafIdx⟩
  have hone : encodingSelectionContribution cache hfinite secretKey position = 1 := by
    exact encodingSelectionContribution_eq_one_of_collision
      (cache := cache) (secretKey := secretKey) (position := position)
      (signedPayload := signedPayload) (otherPayload := otherPayload)
      (signedAnswer := signedAnswer) (otherAnswer := otherAnswer)
      hfinite (by simpa only [position] using htarget) hpayloadNe
      (by simpa only [position, EncodingPosition.domain] using hsignedAnswer)
      (by simpa only [position, EncodingPosition.domain] using hotherAnswer) hcollision
  rw [encodingSelectionPotential, Fintype.sum_eq_add_sum_subtype_ne _ position,
    hone]
  exact le_add_right le_rfl

theorem encodingSelectionTotalPotential_eq_one_of_clean_of_encodingBad
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey}
    (hclean : ¬ Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache)
    (hbad : EncodingBad cache secretKey) :
    encodingSelectionTotalPotential cache hfinite secretKey = 1 := by
  obtain ⟨position, _, hlatent⟩ := hbad.latent_with_target
  rw [encodingSelectionTotalPotential, if_neg hclean, if_pos ⟨position, hlatent⟩]

theorem encodingSelectionTotalPotential_le_one
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    (secretKey : SecretKey) :
    encodingSelectionTotalPotential cache hfinite secretKey ≤ 1 := by
  rw [encodingSelectionTotalPotential]
  split
  · exact bot_le
  · split
    · exact le_rfl
    · exact min_le_left _ _

theorem encodingSelectionTotalPotential_cacheQuery_le_of_bad
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {answer : HashOutput}
    (huncached : cache input = none)
    (hbad : Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache) :
    encodingSelectionTotalPotential (cache.cacheQuery input answer)
        (finite_cacheQuery hfinite input answer) secretKey ≤
      encodingSelectionTotalPotential cache hfinite secretKey := by
  have hbadAfter := Bad.mono secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
    (le_cacheQuery (cache := cache) (input := input) (answer := answer) huncached) hbad
  have hbefore : encodingSelectionTotalPotential cache hfinite secretKey = 0 := by
    rw [encodingSelectionTotalPotential, if_pos hbad]
  have hafter : encodingSelectionTotalPotential (cache.cacheQuery input answer)
      (finite_cacheQuery hfinite input answer) secretKey = 0 := by
    rw [encodingSelectionTotalPotential, if_pos hbadAfter]
  rw [hbefore, hafter]

theorem encodingSelectionTotalPotential_cacheQuery_le_of_latent
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {answer : HashOutput}
    (hclean : ¬ Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache)
    (hlatent : LatentEncodingBad cache secretKey) :
    encodingSelectionTotalPotential (cache.cacheQuery input answer)
        (finite_cacheQuery hfinite input answer) secretKey ≤
      encodingSelectionTotalPotential cache hfinite secretKey := by
  have hbefore : encodingSelectionTotalPotential cache hfinite secretKey = 1 := by
    rw [encodingSelectionTotalPotential, if_neg hclean, if_pos hlatent]
  rw [hbefore]
  exact encodingSelectionTotalPotential_le_one _ secretKey

theorem encodingSelectionTotalPotential_cacheQuery_le_of_one_le_uncapped
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {answer : HashOutput}
    (hclean : ¬ Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache)
    (hlatent : ¬ LatentEncodingBad cache secretKey)
    (hone : 1 ≤ (encodingStructuralPotential cache secretKey : ℝ≥0∞) *
        (Fintype.card Digest : ℝ≥0∞)⁻¹ +
      encodingSelectionPotential cache hfinite secretKey) :
    encodingSelectionTotalPotential (cache.cacheQuery input answer)
        (finite_cacheQuery hfinite input answer) secretKey ≤
      encodingSelectionTotalPotential cache hfinite secretKey := by
  have hbefore : encodingSelectionTotalPotential cache hfinite secretKey = 1 := by
    rw [encodingSelectionTotalPotential, if_neg hclean, if_neg hlatent,
      min_eq_left hone]
  rw [hbefore]
  exact encodingSelectionTotalPotential_le_one _ secretKey

@[simp] theorem encodingSelectionContribution_empty
    (secretKey : SecretKey) (position : EncodingPosition) :
    encodingSelectionContribution ∅ finite_empty secretKey position = 0 := by
  rw [encodingSelectionContribution, if_neg]
  · exact encodingRetryContribution_empty secretKey position
  · rintro ⟨index, _, _, hsettled⟩
    exact hsettled.cached (by simp)

@[simp] theorem encodingSelectionPotential_empty (secretKey : SecretKey) :
    encodingSelectionPotential ∅ finite_empty secretKey = 0 := by
  rw [encodingSelectionPotential]
  apply Fintype.sum_eq_zero
  exact encodingSelectionContribution_empty secretKey

@[simp] theorem encodingSelectionTotalPotential_empty (secretKey : SecretKey) :
    encodingSelectionTotalPotential ∅ finite_empty secretKey = 0 := by
  rw [encodingSelectionTotalPotential,
    if_neg (not_bad_empty secretKey.parameter secretKey.otsSecret secretKey.ftsSecret),
    if_neg (not_latentEncodingBad_empty secretKey), encodingStructuralPotential_empty,
    encodingSelectionPotential_empty]
  simp

end SphincsSecurity.Concrete
