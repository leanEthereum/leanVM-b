import SphincsSecurity.Proof.EncodingCollisionReserve
import SphincsSecurity.Proof.EncodingCollisionSettlement

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal
attribute [local irreducible] instFintypePosition instFintypeEncodingPosition answerPotential
set_option backward.isDefEq.respectTransparency false

noncomputable def collisionAnswerEncodingPotential (cache : QueryCache HashSpec) (hfinite : Finite cache) (key : SecretKey) : Nat :=
  answerPotential key.parameter key.otsSecret key.ftsSecret cache + encodingCollisionReserve cache hfinite key

@[simp] theorem collisionAnswerEncodingPotential_empty (key : SecretKey) :
    collisionAnswerEncodingPotential ∅ finite_empty key = 0 := by
  rw [collisionAnswerEncodingPotential, answerPotential_empty, encodingCollisionReserve_empty, Nat.zero_add]

private theorem add_empty_card_le (n : Nat) : n + (∅ : Finset Digest).card ≤ n := by simp

theorem encodingCollisionTargets_for_settling_query
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {secretKey : SecretKey}
    {input : HashInput} {queried : Position}
    (hfresh : cache input = none) (hat : AtPosition secretKey.parameter input queried)
    (hbefore : ¬ Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache queried)
    (hsettles : ∀ answer : HashOutput,
      Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret (cache.cacheQuery input answer) queried) :
    ∃ targets : Finset Digest,
      (∀ (position : EncodingPosition) (index : Index),
        treeIndexAt index position.lay = position.tree → leafIndexAt index position.lay = position.leafIdx →
        layerMessagePosition index position.lay = queried →
        encodingCollisionMessageTargets secretKey.parameter cache hfinite position ⊆ targets) ∧
      ∀ answer : HashOutput, encodingCollisionReserve (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) secretKey + targets.card ≤
        encodingCollisionReserve cache hfinite secretKey := by
  classical
  have hnotEncoding : ∀ position : EncodingPosition, ¬ AtEncodingPosition secretKey.parameter input position :=
    fun position h => h.not_atPosition queried hat
  by_cases hdirect : ∃ (position : EncodingPosition) (index : Index),
      treeIndexAt index position.lay = position.tree ∧ leafIndexAt index position.lay = position.leafIdx ∧
      layerMessagePosition index position.lay = queried
  · obtain ⟨position, index, htree, hleaf, heq⟩ := hdirect
    refine ⟨encodingCollisionMessageTargets secretKey.parameter cache hfinite position, ?_, ?_⟩
    · intro candidate candidateIndex hcTree hcLeaf hcEq
      have hc : candidate = position := encodingPosition_eq_of_layerMessagePosition_eq hcTree hcLeaf htree hleaf
        (hcEq.trans heq.symm)
      subst candidate
      exact Finset.Subset.rfl
    · intro answer
      apply encodingCollisionReserve_add_targets_le_of_new_message hfinite hfresh hnotEncoding ?_ ?_
      · rintro ⟨other, hoTree, hoLeaf, hoSettled⟩
        have ho := layerMessagePosition_eq_of_position_eq index other position.lay
          (htree.trans hoTree.symm) (hleaf.trans hoLeaf.symm)
        apply hbefore
        rwa [← heq, ho]
      · exact ⟨index, htree, hleaf, heq ▸ hsettles answer⟩
  · refine ⟨∅, ?_, ?_⟩
    · intro position index htree hleaf heq
      exact (hdirect ⟨position, index, htree, hleaf, heq⟩).elim
    · intro answer
      exact (Nat.add_le_add
        (encodingCollisionReserve_cacheQuery_le_of_not_atEncoding hfinite (answer := answer) hfresh hnotEncoding)
        (Nat.le_refl _)).trans (add_empty_card_le (encodingCollisionReserve cache hfinite secretKey))

theorem collisionAnswerEncoding_step_of_settling
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {secretKey : SecretKey}
    {input : HashInput} {queried : Position}
    (hclean : ¬ Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache)
    (hfresh : cache input = none) (hat : AtPosition secretKey.parameter input queried)
    (hbefore : ¬ Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache queried)
    (hsettles : ∀ answer : HashOutput,
      Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret (cache.cacheQuery input answer) queried) :
    ∃ targets : Finset Digest, targets.card ≤ collisionAnswerEncodingPotential cache hfinite secretKey ∧
      ∀ answer : HashOutput,
        ¬ ParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache input answer →
        truncateHash answer ∉ targets →
        ¬ Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret (cache.cacheQuery input answer) ∧
          collisionAnswerEncodingPotential (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) secretKey + targets.card ≤ collisionAnswerEncodingPotential cache hfinite secretKey ∧
          encodingSelectionPotential (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) secretKey ≤
            encodingSelectionPotential cache hfinite secretKey := by
  classical
  obtain ⟨messageTargets, hdirect, hstage⟩ := encodingCollisionTargets_for_settling_query hfinite hfresh hat hbefore hsettles
  let targets := answerTargets secretKey.parameter cache hfinite queried ∪ messageTargets
  have hdrop (answer : HashOutput) :
      collisionAnswerEncodingPotential (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) secretKey + targets.card ≤ collisionAnswerEncodingPotential cache hfinite secretKey := by
    have ha := answerPotential_add_answerTargets_card_le secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
      hfinite hfresh hat hbefore (hsettles answer)
    have he := hstage answer
    have hu : targets.card ≤ (answerTargets secretKey.parameter cache hfinite queried).card + messageTargets.card :=
      Finset.card_union_le _ _
    rw [collisionAnswerEncodingPotential, collisionAnswerEncodingPotential]
    omega
  refine ⟨targets, (Nat.le_add_left _ _).trans (hdrop 0), ?_⟩
  intro answer hnoParent havoid
  refine ⟨clean_cacheQuery_of_settling_without_parent secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
    hfinite hclean hfresh hat hbefore (hsettles answer) hnoParent
    (fun h => havoid (Finset.mem_union_left _ h)), hdrop answer, ?_⟩
  apply encodingSelectionPotential_cacheQuery_le_without_parent_collisionTargets hfinite hfresh hat hnoParent
  intro position index htree hleaf hmessage hmem
  exact havoid (Finset.mem_union_right _ (hdirect position index htree hleaf
    (atPosition_unique secretKey.parameter hmessage hat) hmem))

theorem collisionAnswerEncoding_step_of_no_new_messages
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {secretKey : SecretKey} {input : HashInput}
    (hclean : ¬ Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache)
    (hfresh : cache input = none)
    (hnotEncoding : ∀ position : EncodingPosition, ¬ AtEncodingPosition secretKey.parameter input position)
    (hnoNew : ∀ (answer : HashOutput) (position : EncodingPosition),
      EncodingMessageSettledAt (cache.cacheQuery input answer) secretKey position → EncodingMessageSettledAt cache secretKey position) :
    ∃ targets : Finset Digest, targets.card ≤ collisionAnswerEncodingPotential cache hfinite secretKey + 1 ∧
      ∀ answer : HashOutput,
        ¬ ParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache input answer →
        truncateHash answer ∉ targets →
        ¬ Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret (cache.cacheQuery input answer) ∧
          collisionAnswerEncodingPotential (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) secretKey + targets.card ≤ collisionAnswerEncodingPotential cache hfinite secretKey + 1 ∧
          encodingSelectionPotential (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) secretKey ≤
            encodingSelectionPotential cache hfinite secretKey := by
  obtain ⟨targets, hcard, hsafe⟩ := answerCharge_step secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
    hfinite hclean input hfresh
  refine ⟨targets, ?_, ?_⟩
  · rw [collisionAnswerEncodingPotential]
    omega
  · intro answer hnoParent havoid
    obtain ⟨hcleanAfter, ha⟩ := hsafe answer hnoParent havoid
    refine ⟨hcleanAfter, ?_, encodingSelectionPotential_cacheQuery_le_of_no_new_messages
      hfinite hfresh hnotEncoding (hnoNew answer)⟩
    have he := encodingCollisionReserve_cacheQuery_le_of_not_atEncoding hfinite (key := secretKey) (answer := answer) hfresh hnotEncoding
    rw [collisionAnswerEncodingPotential, collisionAnswerEncodingPotential]
    omega

theorem collisionAnswerEncoding_step_of_structural
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {secretKey : SecretKey} {input : HashInput} {queried : Position}
    (hclean : ¬ Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache)
    (hfresh : cache input = none) (hat : AtPosition secretKey.parameter input queried) :
    ∃ targets : Finset Digest, targets.card ≤ collisionAnswerEncodingPotential cache hfinite secretKey + 1 ∧
      ∀ answer : HashOutput,
        ¬ ParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache input answer →
        truncateHash answer ∉ targets →
        ¬ Bad secretKey.parameter secretKey.otsSecret secretKey.ftsSecret (cache.cacheQuery input answer) ∧
          collisionAnswerEncodingPotential (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) secretKey + targets.card ≤ collisionAnswerEncodingPotential cache hfinite secretKey + 1 ∧
          encodingSelectionPotential (cache.cacheQuery input answer) (finite_cacheQuery hfinite input answer) secretKey ≤
            encodingSelectionPotential cache hfinite secretKey := by
  have hnotEncoding : ∀ position : EncodingPosition, ¬ AtEncodingPosition secretKey.parameter input position :=
    fun position h => h.not_atPosition queried hat
  by_cases hbefore : Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache queried
  · exact collisionAnswerEncoding_step_of_no_new_messages hfinite hclean hfresh hnotEncoding
      (fun _ _ h => h.of_cacheQuery_of_at_settled hfresh hat hbefore)
  · by_cases hnever : ∀ answer : HashOutput,
        ¬ Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret (cache.cacheQuery input answer) queried
    · exact collisionAnswerEncoding_step_of_no_new_messages hfinite hclean hfresh hnotEncoding
        (fun answer _ h => h.of_cacheQuery_of_at_unsettledAfter hfresh hat (hnever answer))
    · push Not at hnever
      obtain ⟨answer, hsettled⟩ := hnever
      have hsettles := settled_cacheQuery_of_settled_cacheQuery secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
        hfresh hat hbefore hsettled
      obtain ⟨targets, hcard, hsafe⟩ := collisionAnswerEncoding_step_of_settling hfinite hclean hfresh hat hbefore hsettles
      refine ⟨targets, hcard.trans (Nat.le_add_right _ 1), ?_⟩
      intro answer hnoParent havoid
      obtain ⟨hcleanAfter, hp, hs⟩ := hsafe answer hnoParent havoid
      exact ⟨hcleanAfter, hp.trans (Nat.le_add_right _ 1), hs⟩

end SphincsSecurity.Concrete
