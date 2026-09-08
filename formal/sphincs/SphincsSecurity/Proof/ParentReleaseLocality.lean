import SphincsSecurity.Proof.ParentReserveQueryConservation
import SphincsSecurity.Proof.EncodingWithoutParent

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] instFintypePosition
set_option backward.isDefEq.respectTransparency false

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
  (eligible : Position → Prop)

theorem releasedParentReserveAt_le_contribution
    (before after : QueryCache HashSpec) (position : Position) :
    releasedParentReserveAt parameter otsSecret ftsSecret eligible before after position ≤
      parentReserveContribution parameter otsSecret ftsSecret eligible before position := by
  unfold releasedParentReserveAt
  split_ifs with hrelease
  · rw [parentReserveContribution, if_pos ⟨hrelease.1, hrelease.2.1⟩]
  · exact Nat.zero_le _

theorem releasedParentReserve_le_before (before after : QueryCache HashSpec) :
    releasedParentReserve parameter otsSecret ftsSecret eligible before after ≤
      parentReserve parameter otsSecret ftsSecret eligible before := by
  exact Finset.sum_le_sum (fun position _ => releasedParentReserveAt_le_contribution parameter otsSecret ftsSecret eligible before after position)

theorem newly_settled_at_queried_without_parent
    {cache : QueryCache HashSpec} {input : HashInput} {answer : HashOutput} {position : Position}
    (hfresh : cache input = none)
    (hnoParent : ¬ ParentSettlement parameter otsSecret ftsSecret cache input answer)
    (hbefore : ¬ Settled parameter otsSecret ftsSecret cache position)
    (hafter : Settled parameter otsSecret ftsSecret (cache.cacheQuery input answer) position) :
    AtPosition parameter input position := by
  by_cases hex : ∃ queried, AtPosition parameter input queried
  · obtain ⟨queried, hat⟩ := hex
    by_cases heq : position = queried
    · exact heq ▸ hat
    · exact (hbefore (settled_of_cacheQuery_without_parent parameter otsSecret ftsSecret hfresh hat hnoParent heq hafter)).elim
  · exact (hbefore (settled_of_settled_cacheQuery parameter otsSecret ftsSecret hfresh (p₀ := none)
      (fun queried hat => (hex ⟨queried, hat⟩).elim) (by simp) (position.depth + 1) position
      (Nat.lt_succ_self _) (by simp) hafter)).elim

def ReadyParentRelease (cache : QueryCache HashSpec) (input : HashInput) (parent : Position) : Prop :=
  ∃ child, AtPosition parameter input child ∧ child.parentOf = some parent ∧
    ¬ Settled parameter otsSecret ftsSecret cache child ∧
    (∃ answer, Settled parameter otsSecret ftsSecret (cache.cacheQuery input answer) child) ∧
    OtherChildrenSettled parameter otsSecret ftsSecret cache child parent

theorem ParentSettlement.exists_ready_release
    {cache : QueryCache HashSpec} {input : HashInput} {answer : HashOutput}
    (hparent : ParentSettlement parameter otsSecret ftsSecret cache input answer) :
    ∃ parent, ReadyParentRelease parameter otsSecret ftsSecret cache input parent := by
  obtain ⟨hfresh, child, parent, hat, hb, ha, hp, hs⟩ := hparent
  exact ⟨parent, child, hat, hp, hb, ⟨answer, ha⟩,
    otherChildrenSettled_of_parent_settled_cacheQuery parameter otsSecret ftsSecret hfresh hat (Position.mem_children_iff.mpr hp) hs⟩

theorem ReadyParentRelease.honest_input
    {cache : QueryCache HashSpec} {input : HashInput} {parent : Position} (hfresh : cache input = none)
    (hready : ReadyParentRelease parameter otsSecret ftsSecret cache input parent) :
    ∃ child, AtPosition parameter input child ∧ child.parentOf = some parent ∧
      input = cachedInput parameter otsSecret ftsSecret cache child ∧
      (∀ descendant ∈ child.children, Settled parameter otsSecret ftsSecret cache descendant) := by
  obtain ⟨child, hat, hp, hb, ⟨answer, ha⟩, _⟩ := hready
  exact ⟨child, hat, hp, eq_cachedInput_and_children_of_settled_cacheQuery parameter otsSecret ftsSecret hfresh hat hb ha⟩

theorem ReadyParentRelease.newly_settled_children
    {cache : QueryCache HashSpec} {input : HashInput} {answer : HashOutput} {parent : Position}
    (hfresh : cache input = none) (hready : ReadyParentRelease parameter otsSecret ftsSecret cache input parent) :
    (¬ ∀ child ∈ parent.children, Settled parameter otsSecret ftsSecret cache child) ∧
      (∀ child ∈ parent.children, Settled parameter otsSecret ftsSecret (cache.cacheQuery input answer) child) := by
  obtain ⟨child, hat, hp, hb, ⟨otherAnswer, ha⟩, hother⟩ := hready
  refine ⟨fun hall => hb (hall child (Position.mem_children_iff.mpr hp)), ?_⟩
  intro sibling hs
  by_cases heq : sibling = child
  · subst sibling
    exact settled_cacheQuery_of_settled_cacheQuery parameter otsSecret ftsSecret hfresh hat hb ha answer
  · exact (hother sibling hs heq).mono (le_cacheQuery (answer := answer) hfresh)

theorem readyParentRelease_iff_newly_settled_children
    {cache : QueryCache HashSpec} {input : HashInput} {answer : HashOutput} (hfresh : cache input = none)
    (hnoParent : ¬ ParentSettlement parameter otsSecret ftsSecret cache input answer) (parent : Position) :
    ReadyParentRelease parameter otsSecret ftsSecret cache input parent ↔
      (¬ ∀ child ∈ parent.children, Settled parameter otsSecret ftsSecret cache child) ∧
        (∀ child ∈ parent.children, Settled parameter otsSecret ftsSecret (cache.cacheQuery input answer) child) := by
  constructor
  · exact ReadyParentRelease.newly_settled_children parameter otsSecret ftsSecret hfresh
  · rintro ⟨hb, ha⟩
    push Not at hb
    obtain ⟨child, hc, hb⟩ := hb
    have hat := newly_settled_at_queried_without_parent parameter otsSecret ftsSecret hfresh hnoParent hb (ha child hc)
    refine ⟨child, hat, Position.mem_children_iff.mp hc, hb, ⟨answer, ha child hc⟩, ?_⟩
    intro sibling hs hne
    exact settled_of_cacheQuery_without_parent parameter otsSecret ftsSecret hfresh hat hnoParent hne (ha sibling hs)

noncomputable def directParentRelease (cache : QueryCache HashSpec) (input : HashInput) : Nat :=
  ∑ parent : Position, if ReadyParentRelease parameter otsSecret ftsSecret cache input parent then
    parentReserveContribution parameter otsSecret ftsSecret eligible cache parent else 0

theorem ReadyParentRelease.unique
    {cache : QueryCache HashSpec} {input : HashInput} {left right : Position}
    (hl : ReadyParentRelease parameter otsSecret ftsSecret cache input left)
    (hr : ReadyParentRelease parameter otsSecret ftsSecret cache input right) : left = right := by
  obtain ⟨child, hat, hp, _⟩ := hl
  obtain ⟨other, hat', hp', _⟩ := hr
  have heq := atPosition_unique parameter hat hat'
  subst other
  exact Option.some.inj (hp.symm.trans hp')

theorem directParentRelease_eq_contribution_of_ready
    {cache : QueryCache HashSpec} {input : HashInput} {parent : Position}
    (hready : ReadyParentRelease parameter otsSecret ftsSecret cache input parent) :
    directParentRelease parameter otsSecret ftsSecret eligible cache input =
      parentReserveContribution parameter otsSecret ftsSecret eligible cache parent := by
  unfold directParentRelease
  rw [Finset.sum_eq_single parent]
  · rw [if_pos hready]
  · intro other _ hne
    exact if_neg (fun h => hne (ReadyParentRelease.unique parameter otsSecret ftsSecret h hready))
  · simp

theorem directParentRelease_eq_zero_of_not_atPosition
    {cache : QueryCache HashSpec} {input : HashInput}
    (hnot : ¬ ∃ child, AtPosition parameter input child) :
    directParentRelease parameter otsSecret ftsSecret eligible cache input = 0 := by
  apply Finset.sum_eq_zero
  intro parent _
  exact if_neg (by rintro ⟨child, hat, _⟩; exact hnot ⟨child, hat⟩)

theorem freshParentReserveCharge_eq_zero_of_ready
    {cache : QueryCache HashSpec} {input : HashInput} {parent : Position}
    (hready : ReadyParentRelease parameter otsSecret ftsSecret cache input parent) :
    freshParentReserveCharge parameter otsSecret ftsSecret eligible cache input = 0 := by
  unfold freshParentReserveCharge
  split_ifs with hfresh
  · obtain ⟨child, hat, _, _, hchildren⟩ := ReadyParentRelease.honest_input parameter otsSecret ftsSecret hfresh hready
    have hzero : parentReserveCharge parameter otsSecret ftsSecret eligible cache input = 0 := by
      unfold parentReserveCharge
      apply if_neg
      rintro ⟨queried, hq, _, hnot⟩
      have heq := atPosition_unique parameter hq hat
      exact hnot (heq ▸ hchildren)
    rw [hzero, Nat.cast_zero]
  · rfl

theorem directParentRelease_le_before (cache : QueryCache HashSpec) (input : HashInput) :
    directParentRelease parameter otsSecret ftsSecret eligible cache input ≤
      parentReserve parameter otsSecret ftsSecret eligible cache := by
  apply Finset.sum_le_sum
  intro parent _
  split_ifs <;> omega

theorem releasedParentReserve_eq_direct_without_parent
    {cache : QueryCache HashSpec} {input : HashInput} {answer : HashOutput} (hfresh : cache input = none)
    (hnoParent : ¬ ParentSettlement parameter otsSecret ftsSecret cache input answer) :
    releasedParentReserve parameter otsSecret ftsSecret eligible cache (cache.cacheQuery input answer) =
      directParentRelease parameter otsSecret ftsSecret eligible cache input := by
  apply Finset.sum_congr rfl
  intro parent _
  have heq := readyParentRelease_iff_newly_settled_children parameter otsSecret ftsSecret hfresh hnoParent parent
  unfold releasedParentReserveAt parentReserveContribution
  by_cases hr : ReadyParentRelease parameter otsSecret ftsSecret cache input parent
  · obtain ⟨hb, ha⟩ := heq.mp hr
    rw [if_pos hr]
    by_cases he : eligible parent
    · rw [if_pos ⟨he, hb, ha⟩, if_pos ⟨he, hb⟩]
    · rw [if_neg (fun h => he h.1), if_neg (fun h => he h.1)]
  · have hn := fun h => hr (heq.mpr h)
    rw [if_neg (fun h => hn ⟨h.2.1, h.2.2⟩), if_neg hr]

theorem releasedParentReserve_le_direct_add_exception
    {cache : QueryCache HashSpec} {input : HashInput} {answer : HashOutput} (hfresh : cache input = none) :
    releasedParentReserve parameter otsSecret ftsSecret eligible cache (cache.cacheQuery input answer) ≤
      directParentRelease parameter otsSecret ftsSecret eligible cache input +
        if ParentSettlement parameter otsSecret ftsSecret cache input answer then
          parentReserve parameter otsSecret ftsSecret eligible cache else 0 := by
  by_cases hp : ParentSettlement parameter otsSecret ftsSecret cache input answer
  · rw [if_pos hp]
    exact (releasedParentReserve_le_before parameter otsSecret ftsSecret eligible cache _).trans (Nat.le_add_left _ _)
  · rw [if_neg hp, Nat.add_zero, releasedParentReserve_eq_direct_without_parent parameter otsSecret ftsSecret eligible hfresh hp]

theorem releasedParentReserve_add_discard_le_direct_add_exception
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (hsub : ∀ cache input answer, exception cache input answer → ParentSettlement parameter otsSecret ftsSecret cache input answer)
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {input : HashInput} {answer : HashOutput} (hfresh : cache input = none) :
    releasedParentReserve parameter otsSecret ftsSecret eligible cache (cache.cacheQuery input answer) +
      (if exception cache input answer then parentReserve parameter otsSecret ftsSecret eligible (cache.cacheQuery input answer) else 0) ≤
      directParentRelease parameter otsSecret ftsSecret eligible cache input +
        if ParentSettlement parameter otsSecret ftsSecret cache input answer then
          parentReserve parameter otsSecret ftsSecret eligible cache else 0 := by
  by_cases he : exception cache input answer
  · have hp := hsub cache input answer he
    obtain ⟨parent, hr⟩ := ParentSettlement.exists_ready_release parameter otsSecret ftsSecret hp
    have hz := freshParentReserveCharge_eq_zero_of_ready parameter otsSecret ftsSecret eligible hr
    rw [freshParentReserveCharge, if_pos hfresh, Nat.cast_eq_zero] at hz
    have hbalance := parentReserve_cacheQuery_add_released_eq parameter otsSecret ftsSecret eligible (answer := answer) hfinite hfresh
    rw [hz, Nat.add_zero] at hbalance
    rw [if_pos he, if_pos hp, Nat.add_comm, hbalance]
    exact Nat.le_add_left _ _
  · rw [if_neg he, Nat.add_zero]
    exact releasedParentReserve_le_direct_add_exception parameter otsSecret ftsSecret eligible hfresh

end SphincsSecurity
