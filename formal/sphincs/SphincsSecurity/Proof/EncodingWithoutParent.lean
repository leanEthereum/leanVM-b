import SphincsSecurity.Proof.AnswerChargeStep
import SphincsSecurity.Proof.TightEncodingSelectionPotential

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

attribute [local irreducible] instFintypePosition answerPotential

theorem settled_of_cacheQuery_without_parent
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    {cache : QueryCache HashSpec} {input : HashInput} {answer : HashOutput} {queried position : Position}
    (hfresh : cache input = none) (hat : AtPosition parameter input queried)
    (hnoParent : ¬ ParentSettlement parameter otsSecret ftsSecret cache input answer)
    (hne : position ≠ queried)
    (hsettled : Settled parameter otsSecret ftsSecret (cache.cacheQuery input answer) position) :
    Settled parameter otsSecret ftsSecret cache position := by
  by_cases hbefore : Settled parameter otsSecret ftsSecret cache queried
  · exact settled_of_cacheQuery_at_settled parameter otsSecret ftsSecret hfresh hat hbefore
      (position.depth + 1) position (by omega) hsettled
  · apply settled_of_settled_cacheQuery parameter otsSecret ftsSecret hfresh
      (p₀ := some queried) (fun candidate hc => congrArg some (atPosition_unique parameter hat hc))
      ?_ (position.depth + 1) position (by omega) (fun heq => hne (Option.some.inj heq).symm) hsettled
    intro child parent heq hparent hafter
    have he : child = queried := (Option.some.inj heq).symm
    subst child
    exact hnoParent ⟨hfresh, queried, parent, hat, hbefore,
      hafter.children queried (Position.mem_children_iff.mpr hparent), hparent, hafter⟩

namespace Concrete

theorem encodingSelectionPotential_cacheQuery_le_without_parent
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {answer : HashOutput} {queried : Position}
    (hfresh : cache input = none) (hat : AtPosition secretKey.parameter input queried)
    (hnoParent : ¬ ParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache input answer)
    (havoid : ∀ (position : EncodingPosition) (index : Index),
      treeIndexAt index position.lay = position.tree → leafIndexAt index position.lay = position.leafIdx →
      AtPosition secretKey.parameter input (layerMessagePosition index position.lay) →
      truncateHash answer ∉ encodingMessageTargets secretKey.parameter cache hfinite position) :
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
        (encodingSelection_hasCachedHit_mem_messageTargets_of_newlySettled hfinite hfresh htree hleaf hunsettled hsettled hmessage hhit)
    · exact encodingSelectionContribution_cacheQuery_le_of_unsettled_of_stillUnsettled_of_not_atPosition
        hfinite hfresh hbefore hafter hnotAt

theorem EncodingMessagePrehit.mem_directTargets_without_parent
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {answer : HashOutput} {queried : Position}
    (hfresh : cache input = none) (hat : AtPosition secretKey.parameter input queried)
    (hnoParent : ¬ ParentSettlement secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache input answer)
    (targets : Finset Digest)
    (hdirect : ∀ (position : EncodingPosition) (index : Index),
      treeIndexAt index position.lay = position.tree → leafIndexAt index position.lay = position.leafIdx →
      layerMessagePosition index position.lay = queried →
      encodingMessageTargets secretKey.parameter cache hfinite position ⊆ targets)
    (hhit : EncodingMessagePrehit cache secretKey input answer) : truncateHash answer ∈ targets := by
  obtain ⟨position, index, previous, htree, hleaf, hbefore, hafter, hencoding, hcached, hvalue⟩ := hhit
  have heq : layerMessagePosition index position.lay = queried := by
    by_contra hne
    exact hbefore (settled_of_cacheQuery_without_parent secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
      hfresh hat hnoParent hne hafter)
  have hmessage : AtPosition secretKey.parameter input (layerMessagePosition index position.lay) := heq ▸ hat
  apply hdirect position index htree hleaf heq
  have hmem := slotDigest_mem_encodingMessageTargets hfinite hcached hencoding
  have hanswer := honestValue_cacheQuery_self_of_settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
    hfresh hmessage hbefore hafter
  rwa [hvalue, hanswer] at hmem

end Concrete
end SphincsSecurity
