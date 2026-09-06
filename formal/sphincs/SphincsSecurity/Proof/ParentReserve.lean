import SphincsSecurity.Proof.AnswerCharge
import SphincsSecurity.Proof.TightEncodingChildrenCharge

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

attribute [local irreducible] instFintypePosition

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
  (eligible : Position → Prop)

noncomputable def parentReserveContribution (cache : QueryCache HashSpec) (position : Position) : Nat :=
  open Classical in
  if eligible position ∧ ¬ ∀ child ∈ position.children, Settled parameter otsSecret ftsSecret cache child
  then (cachedAt parameter cache position).ncard else 0

noncomputable def parentReserve (cache : QueryCache HashSpec) : Nat :=
  ∑ position : Position, parentReserveContribution parameter otsSecret ftsSecret eligible cache position

noncomputable def parentReserveCharge (cache : QueryCache HashSpec) (input : HashInput) : Nat :=
  open Classical in
  if ∃ position, AtPosition parameter input position ∧ eligible position ∧
      ¬ ∀ child ∈ position.children, Settled parameter otsSecret ftsSecret cache child then 1 else 0

def EligibleParentSettlement (cache : QueryCache HashSpec) (input : HashInput) (answer : HashOutput) : Prop :=
  ParentSettlement parameter otsSecret ftsSecret cache input answer ∧
    ∃ child parent, AtPosition parameter input child ∧ child.parentOf = some parent ∧ eligible parent

theorem parentReserve_empty : parentReserve parameter otsSecret ftsSecret eligible (∅ : QueryCache HashSpec) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro position _
  have hc : cachedAt parameter (∅ : QueryCache HashSpec) position = ∅ := by
    ext input
    simp [cachedAt]
  simp [parentReserveContribution, hc]

theorem parentReserveContribution_le_of_cachedAt_eq {cache cache' : QueryCache HashSpec}
    (hle : cache ≤ cache') (position : Position)
    (hcached : cachedAt parameter cache' position = cachedAt parameter cache position) :
    parentReserveContribution parameter otsSecret ftsSecret eligible cache' position ≤
      parentReserveContribution parameter otsSecret ftsSecret eligible cache position := by
  classical
  by_cases he : eligible position
  · by_cases hc : ∀ child ∈ position.children, Settled parameter otsSecret ftsSecret cache child
    · have hc' : ∀ child ∈ position.children, Settled parameter otsSecret ftsSecret cache' child :=
        fun child hchild => (hc child hchild).mono hle
      rw [parentReserveContribution, if_neg (fun h => h.2 hc')]
      exact Nat.zero_le _
    · simp only [parentReserveContribution, he, hc, not_false_eq_true, and_self, if_true, hcached]
      split_ifs <;> omega
  · simp [parentReserveContribution, he]

theorem parentReserve_cacheQuery_le_charge {cache : QueryCache HashSpec}
    {input : HashInput} {answer : HashOutput} (hfresh : cache input = none) :
    parentReserve parameter otsSecret ftsSecret eligible (cache.cacheQuery input answer) ≤
      parentReserve parameter otsSecret ftsSecret eligible cache +
        parentReserveCharge parameter otsSecret ftsSecret eligible cache input := by
  classical
  have hle := le_cacheQuery (answer := answer) hfresh
  by_cases hat : ∃ queried, AtPosition parameter input queried
  · obtain ⟨queried, hat⟩ := hat
    have hlocal : parentReserveContribution parameter otsSecret ftsSecret eligible
        (cache.cacheQuery input answer) queried ≤
        parentReserveContribution parameter otsSecret ftsSecret eligible cache queried +
          parentReserveCharge parameter otsSecret ftsSecret eligible cache input := by
      by_cases hc : eligible queried ∧ ¬ ∀ child ∈ queried.children,
          Settled parameter otsSecret ftsSecret cache child
      · have hcharge : parentReserveCharge parameter otsSecret ftsSecret eligible cache input = 1 := by
          unfold parentReserveCharge
          rw [if_pos ⟨queried, hat, hc⟩]
        have hcard : (cachedAt parameter (cache.cacheQuery input answer) queried).ncard ≤
            (cachedAt parameter cache queried).ncard + 1 := by
          rw [cachedAt_cacheQuery_self parameter hat]
          exact Set.ncard_insert_le _ _
        rw [parentReserveContribution, parentReserveContribution, if_pos hc, hcharge]
        split_ifs <;> omega
      · have hc' : ¬ (eligible queried ∧ ¬ ∀ child ∈ queried.children,
            Settled parameter otsSecret ftsSecret (cache.cacheQuery input answer) child) := by
          rintro ⟨he, hnot⟩
          apply hc
          exact ⟨he, fun hall => hnot (fun child hchild => (hall child hchild).mono hle)⟩
        rw [parentReserveContribution, if_neg hc']
        exact Nat.zero_le _
    calc
      _ ≤ ∑ position : Position,
          (parentReserveContribution parameter otsSecret ftsSecret eligible cache position +
            if position = queried then parentReserveCharge parameter otsSecret ftsSecret eligible cache input else 0) := by
        apply Finset.sum_le_sum
        intro position _
        by_cases heq : position = queried
        · simpa only [heq, if_true] using hlocal
        · simp only [heq, if_false, Nat.add_zero]
          exact parentReserveContribution_le_of_cachedAt_eq parameter otsSecret ftsSecret eligible hle position
            (cachedAt_cacheQuery_of_not_atPosition parameter (fun h => heq (atPosition_unique parameter h hat)))
      _ = _ := by rw [Finset.sum_add_distrib, Fintype.sum_ite_eq']; rfl
  · have hsum : parentReserve parameter otsSecret ftsSecret eligible (cache.cacheQuery input answer) ≤
        parentReserve parameter otsSecret ftsSecret eligible cache := by
      apply Finset.sum_le_sum
      intro position _
      exact parentReserveContribution_le_of_cachedAt_eq parameter otsSecret ftsSecret eligible hle position
        (cachedAt_cacheQuery_of_not_atPosition parameter (fun h => hat ⟨position, h⟩))
    exact hsum.trans (Nat.le_add_right _ _)

theorem parentReserve_add_slotTargets_card_le {cache : QueryCache HashSpec} (hfinite : Finite cache)
    {input : HashInput} {answer : HashOutput} {child parent : Position}
    (hfresh : cache input = none) (hat : AtPosition parameter input child)
    (hbefore : ¬ Settled parameter otsSecret ftsSecret cache child)
    (hafter : Settled parameter otsSecret ftsSecret (cache.cacheQuery input answer) child)
    (hmem : child ∈ parent.children) (he : eligible parent)
    (hother : OtherChildrenSettled parameter otsSecret ftsSecret cache child parent) :
    parentReserve parameter otsSecret ftsSecret eligible (cache.cacheQuery input answer) +
        (slotTargets parameter cache hfinite child parent).card ≤
      parentReserve parameter otsSecret ftsSecret eligible cache := by
  classical
  have hle := le_cacheQuery (answer := answer) hfresh
  have hparentBefore : ¬ ∀ sibling ∈ parent.children, Settled parameter otsSecret ftsSecret cache sibling :=
    fun h => hbefore (h child hmem)
  have hparentAfter : ∀ sibling ∈ parent.children,
      Settled parameter otsSecret ftsSecret (cache.cacheQuery input answer) sibling := by
    intro sibling hsibling
    by_cases heq : sibling = child
    · simpa only [heq] using hafter
    · exact (hother sibling hsibling heq).mono hle
  have hchildren := (eq_cachedInput_and_children_of_settled_cacheQuery
    parameter otsSecret ftsSecret hfresh hat hbefore hafter).2
  have hsum : (∑ position : Position,
      (parentReserveContribution parameter otsSecret ftsSecret eligible (cache.cacheQuery input answer) position +
        if position = parent then (cachedAt parameter cache parent).ncard else 0)) ≤
      ∑ position : Position, parentReserveContribution parameter otsSecret ftsSecret eligible cache position := by
    apply Finset.sum_le_sum
    intro position _
    by_cases hp : position = parent
    · subst position
      rw [parentReserveContribution, if_neg (fun h => h.2 hparentAfter),
        parentReserveContribution, if_pos rfl, if_pos ⟨he, hparentBefore⟩, Nat.zero_add]
    · simp only [hp, if_false, Nat.add_zero]
      by_cases hc : position = child
      · subst position
        have hchildren' : ∀ sibling ∈ child.children,
            Settled parameter otsSecret ftsSecret (cache.cacheQuery input answer) sibling :=
          fun sibling hsibling => (hchildren sibling hsibling).mono hle
        rw [parentReserveContribution, if_neg (fun h => h.2 hchildren')]
        exact Nat.zero_le _
      · exact parentReserveContribution_le_of_cachedAt_eq parameter otsSecret ftsSecret eligible hle position
          (cachedAt_cacheQuery_of_not_atPosition parameter (fun h => hc (atPosition_unique parameter h hat)))
  rw [Finset.sum_add_distrib, Fintype.sum_ite_eq'] at hsum
  exact (Nat.add_le_add_left (slotTargets_card_le parameter cache hfinite child parent) _).trans hsum

theorem parentReserve_step {cache : QueryCache HashSpec} (hfinite : Finite cache)
    (input : HashInput) (hfresh : cache input = none) :
    ∃ targets : Finset Digest, ∀ answer,
      (EligibleParentSettlement parameter otsSecret ftsSecret eligible cache input answer →
        truncateHash answer ∈ targets) ∧
      parentReserve parameter otsSecret ftsSecret eligible (cache.cacheQuery input answer) + targets.card ≤
        parentReserve parameter otsSecret ftsSecret eligible cache +
          parentReserveCharge parameter otsSecret ftsSecret eligible cache input := by
  classical
  by_cases hex : ∃ answer, EligibleParentSettlement parameter otsSecret ftsSecret eligible cache input answer
  · obtain ⟨answer₀, ⟨_, child, parent, hat, hbefore, hafter, hparent, hsettled⟩,
      child', parent', hat', hparent', he⟩ := hex
    have hc : child' = child := atPosition_unique parameter hat' hat
    subst child'
    have hp : parent' = parent := Option.some.inj (hparent'.symm.trans hparent)
    subst parent'
    have hmem := Position.mem_children_iff.mpr hparent
    have hother := otherChildrenSettled_of_parent_settled_cacheQuery parameter otsSecret ftsSecret
      hfresh hat hmem hsettled
    refine ⟨slotTargets parameter cache hfinite child parent, fun answer => ⟨?_, ?_⟩⟩
    · rintro ⟨⟨_, candidate, ancestor, hcandidate, _, _, hancestor, hsettled'⟩, _⟩
      have hc : candidate = child := atPosition_unique parameter hcandidate hat
      subst candidate
      have hp : ancestor = parent := Option.some.inj (hancestor.symm.trans hparent)
      subst ancestor
      by_contra havoid
      exact not_settled_parent_of_avoids_slotTargets parameter otsSecret ftsSecret hfinite hfresh hat hbefore
        (settled_cacheQuery_of_settled_cacheQuery parameter otsSecret ftsSecret hfresh hat hbefore hafter answer)
        hmem havoid hsettled'
    · exact (parentReserve_add_slotTargets_card_le parameter otsSecret ftsSecret eligible hfinite hfresh hat
        hbefore (settled_cacheQuery_of_settled_cacheQuery parameter otsSecret ftsSecret hfresh hat hbefore hafter answer)
        hmem he hother).trans (Nat.le_add_right _ _)
  · refine ⟨∅, fun answer => ⟨fun h => (hex ⟨answer, h⟩).elim, ?_⟩⟩
    simpa using parentReserve_cacheQuery_le_charge parameter otsSecret ftsSecret eligible (answer := answer) hfresh

end SphincsSecurity
