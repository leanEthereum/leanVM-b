import SphincsSecurity.Proof.TightEncodingSettlement

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

def EncodingMessagePrehit (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (input : HashInput) (answer : HashOutput) : Prop :=
  ∃ (position : EncodingPosition) (index : Index) (previous : HashInput),
    treeIndexAt index position.lay = position.tree ∧
    leafIndexAt index position.lay = position.leafIdx ∧
    ¬ Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache (layerMessagePosition index position.lay) ∧
    Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
      (cache.cacheQuery input answer) (layerMessagePosition index position.lay) ∧
    AtEncodingPosition secretKey.parameter previous position ∧ cache previous ≠ none ∧
    slotDigest 0 previous = honestValue (fromCache (cache.cacheQuery input answer))
      secretKey.parameter secretKey.otsSecret secretKey.ftsSecret (layerMessagePosition index position.lay)

theorem EncodingMessagePrehit.mem_settlementTargets
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {answer : HashOutput} {queriedPosition : Position}
    (hfresh : cache input = none) (hat : AtPosition secretKey.parameter input queriedPosition)
    (messageTargets : Finset Digest)
    (hdirect : ∀ (position : EncodingPosition) (index : Index),
      treeIndexAt index position.lay = position.tree →
      leafIndexAt index position.lay = position.leafIdx →
      layerMessagePosition index position.lay = queriedPosition →
      encodingMessageTargets secretKey.parameter cache hfinite position ⊆ messageTargets)
    (hhit : EncodingMessagePrehit cache secretKey input answer) :
    truncateHash answer ∈ messageTargets ∪
      tightSettlingTargets secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache hfinite queriedPosition := by
  obtain ⟨position, index, previous, htree, hleaf, hbefore, hafter, hencoding, hcached, hvalue⟩ := hhit
  by_cases hmessage : AtPosition secretKey.parameter input (layerMessagePosition index position.lay)
  · have hanswer := honestValue_cacheQuery_self_of_settled secretKey.parameter secretKey.otsSecret
      secretKey.ftsSecret hfresh hmessage hbefore hafter
    apply Finset.mem_union_left
    apply hdirect position index htree hleaf (atPosition_unique secretKey.parameter hmessage hat)
    have hmem := slotDigest_mem_encodingMessageTargets hfinite hcached hencoding
    rwa [hvalue, hanswer] at hmem
  · have hpremature : PrematureLayerMessageSettlement cache secretKey input answer :=
      ⟨position, index, htree, hleaf, hbefore, hafter, hmessage⟩
    obtain ⟨other, hother, _, _, hmem⟩ := hpremature.mem_tightSettlingTargets hfinite hfresh
    have heq := atPosition_unique secretKey.parameter hother hat
    subst other
    exact Finset.mem_union_right _ hmem

theorem EncodingMessagePrehit.queried_settles
    {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {secretKey : SecretKey} {input : HashInput} {answer : HashOutput}
    (hfresh : cache input = none) (hhit : EncodingMessagePrehit cache secretKey input answer) :
    ∃ position : Position, AtPosition secretKey.parameter input position ∧
      ¬ Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret cache position ∧
      Settled secretKey.parameter secretKey.otsSecret secretKey.ftsSecret (cache.cacheQuery input answer) position := by
  obtain ⟨position, index, previous, htree, hleaf, hbefore, hafter, _⟩ := hhit
  by_cases hmessage : AtPosition secretKey.parameter input (layerMessagePosition index position.lay)
  · exact ⟨_, hmessage, hbefore, hafter⟩
  · have hpremature : PrematureLayerMessageSettlement cache secretKey input answer :=
      ⟨position, index, htree, hleaf, hbefore, hafter, hmessage⟩
    obtain ⟨other, hat, hunsettled, hsettled, _⟩ := hpremature.mem_tightSettlingTargets hfinite hfresh
    exact ⟨other, hat, hunsettled, hsettled⟩

end SphincsSecurity.Concrete
