import SphincsSecurity.Proof.AnswerCharge

namespace SphincsSecurity

open OracleComp OracleSpec

attribute [local irreducible] instFintypePosition

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)

theorem ParentSettlement.exists_full_parent_input {cache finalCache : QueryCache HashSpec}
    {input : HashInput} {answer : HashOutput}
    (h : ParentSettlement parameter otsSecret ftsSecret cache input answer)
    (hle : cache.cacheQuery input answer ≤ finalCache) :
    ∃ child parent,
      AtPosition parameter input child ∧ child.parentOf = some parent ∧
      ¬ Settled parameter otsSecret ftsSecret cache child ∧
      OtherChildrenSettled parameter otsSecret ftsSecret cache child parent ∧
      Settled parameter otsSecret ftsSecret finalCache child ∧
      Settled parameter otsSecret ftsSecret finalCache parent ∧
      cache (cachedInput parameter otsSecret ftsSecret finalCache parent) ≠ none ∧
      slotDigest (parent.children.idxOf child) (cachedInput parameter otsSecret ftsSecret finalCache parent) =
        honestValue (fromCache finalCache) parameter otsSecret ftsSecret child ∧
      honestValue (fromCache finalCache) parameter otsSecret ftsSecret child = truncateHash answer := by
  obtain ⟨hfresh, child, parent, hat, hbefore, hafter, hparent, hs⟩ := h
  have hmem := Position.mem_children_iff.mpr hparent
  have hne : parent ≠ child := by
    intro heq
    subst parent
    have := Position.depth_lt_of_mem_children hmem
    omega
  have hinputne : cachedInput parameter otsSecret ftsSecret
      (cache.cacheQuery input answer) parent ≠ input :=
    atPosition_ne parameter
      (atPosition_cachedInput parameter otsSecret ftsSecret (cache.cacheQuery input answer) parent) hat hne
  have hcached := hs.cached
  rw [QueryCache.cacheQuery_of_ne _ _ hinputne] at hcached
  refine ⟨child, parent, hat, hparent, hbefore, ?_, hafter.mono hle, hs.mono hle, ?_, ?_, ?_⟩
  · exact otherChildrenSettled_of_parent_settled_cacheQuery parameter otsSecret ftsSecret hfresh hat hmem hs
  · rwa [cachedInput_eq_of_settled hle hs]
  · exact slotDigest_honestInput_child (fromCache finalCache) parameter otsSecret ftsSecret hs.valid hmem
  · rw [honestValue_eq_of_settled (agreesWithFn_fromCache_of_le hle) hafter]
    exact honestValue_cacheQuery_self_of_settled parameter otsSecret ftsSecret hfresh hat hbefore hafter

end SphincsSecurity
