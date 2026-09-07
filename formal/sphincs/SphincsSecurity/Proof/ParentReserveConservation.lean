import SphincsSecurity.Proof.StructuralCacheCount

namespace SphincsSecurity

open OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
attribute [local irreducible] instFintypePosition
set_option backward.isDefEq.respectTransparency false

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
  (eligible : Position → Prop)

noncomputable def releasedParentReserveAt (before after : QueryCache HashSpec) (position : Position) : Nat :=
  if eligible position ∧ ¬ (∀ child ∈ position.children, Settled parameter otsSecret ftsSecret before child) ∧
      (∀ child ∈ position.children, Settled parameter otsSecret ftsSecret after child) then
    (cachedAt parameter before position).ncard else 0

noncomputable def releasedParentReserve (before after : QueryCache HashSpec) : Nat :=
  ∑ position : Position, releasedParentReserveAt parameter otsSecret ftsSecret eligible before after position

theorem parentReserveContribution_add_released_of_cachedAt_eq
    {before after : QueryCache HashSpec} (hle : before ≤ after) (position : Position)
    (hcached : cachedAt parameter after position = cachedAt parameter before position) :
    parentReserveContribution parameter otsSecret ftsSecret eligible after position +
      releasedParentReserveAt parameter otsSecret ftsSecret eligible before after position =
      parentReserveContribution parameter otsSecret ftsSecret eligible before position := by
  have hm : (∀ child ∈ position.children, Settled parameter otsSecret ftsSecret before child) →
      (∀ child ∈ position.children, Settled parameter otsSecret ftsSecret after child) := fun h child hc => (h child hc).mono hle
  unfold parentReserveContribution releasedParentReserveAt
  rw [hcached]
  by_cases he : eligible position
  · by_cases hb : ∀ child ∈ position.children, Settled parameter otsSecret ftsSecret before child
    · rw [if_neg (fun h => h.2 (hm hb)), if_neg (fun h => h.2.1 hb), if_neg (fun h => h.2 hb), Nat.zero_add]
    · by_cases ha : ∀ child ∈ position.children, Settled parameter otsSecret ftsSecret after child
      · rw [if_neg (fun h => h.2 ha), if_pos ⟨he, hb, ha⟩, if_pos ⟨he, hb⟩, Nat.zero_add]
      · rw [if_pos ⟨he, ha⟩, if_neg (fun h => ha h.2.2), if_pos ⟨he, hb⟩, Nat.add_zero]
  · simp only [he, false_and, if_false, Nat.zero_add]

theorem parentReserveContribution_cacheQuery_self_eq
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {input : HashInput} {answer : HashOutput} {queried : Position}
    (hfresh : cache input = none) (hat : AtPosition parameter input queried) :
    parentReserveContribution parameter otsSecret ftsSecret eligible (cache.cacheQuery input answer) queried +
      releasedParentReserveAt parameter otsSecret ftsSecret eligible cache (cache.cacheQuery input answer) queried =
      parentReserveContribution parameter otsSecret ftsSecret eligible cache queried +
        parentReserveCharge parameter otsSecret ftsSecret eligible cache input := by
  have hchildren : (∀ child ∈ queried.children, Settled parameter otsSecret ftsSecret (cache.cacheQuery input answer) child) ↔
      (∀ child ∈ queried.children, Settled parameter otsSecret ftsSecret cache child) := by
    constructor
    · intro h child hc
      exact settled_of_cacheQuery_below parameter otsSecret ftsSecret hfresh hat (child.depth + 1) child
        (Nat.lt_succ_self _) (Position.depth_lt_of_mem_children hc) (h child hc)
    · intro h child hc
      exact (h child hc).mono (le_cacheQuery (answer := answer) hfresh)
  have hcharge : parentReserveCharge parameter otsSecret ftsSecret eligible cache input =
      if eligible queried ∧ ¬ (∀ child ∈ queried.children, Settled parameter otsSecret ftsSecret cache child) then 1 else 0 := by
    unfold parentReserveCharge
    congr 1
    apply propext
    constructor
    · rintro ⟨position, hp, he, hs⟩
      have heq := atPosition_unique parameter hp hat
      exact heq ▸ ⟨he, hs⟩
    · intro h
      exact ⟨queried, hat, h⟩
  have hcard : (cachedAt parameter (cache.cacheQuery input answer) queried).ncard = (cachedAt parameter cache queried).ncard + 1 := by
    rw [cachedAt_cacheQuery_self parameter hat]
    apply Set.ncard_insert_of_notMem _ (cachedAt_finite parameter hfinite queried)
    intro hm
    exact hm.1 hfresh
  simp only [parentReserveContribution, releasedParentReserveAt, hchildren, hcharge, hcard]
  simp only [not_and_self, and_false, if_false, Nat.add_zero]
  split_ifs <;> rfl

theorem parentReserve_cacheQuery_add_released_eq
    {cache : QueryCache HashSpec} (hfinite : Finite cache) {input : HashInput} {answer : HashOutput}
    (hfresh : cache input = none) :
    parentReserve parameter otsSecret ftsSecret eligible (cache.cacheQuery input answer) +
      releasedParentReserve parameter otsSecret ftsSecret eligible cache (cache.cacheQuery input answer) =
      parentReserve parameter otsSecret ftsSecret eligible cache + parentReserveCharge parameter otsSecret ftsSecret eligible cache input := by
  by_cases hex : ∃ queried : Position, AtPosition parameter input queried
  · obtain ⟨queried, hat⟩ := hex
    have hpoint (position : Position) :
        parentReserveContribution parameter otsSecret ftsSecret eligible (cache.cacheQuery input answer) position +
          releasedParentReserveAt parameter otsSecret ftsSecret eligible cache (cache.cacheQuery input answer) position =
          parentReserveContribution parameter otsSecret ftsSecret eligible cache position +
            if position = queried then parentReserveCharge parameter otsSecret ftsSecret eligible cache input else 0 := by
      by_cases heq : position = queried
      · subst position
        rw [if_pos rfl]
        exact parentReserveContribution_cacheQuery_self_eq parameter otsSecret ftsSecret eligible hfinite hfresh hat
      · rw [if_neg heq, Nat.add_zero]
        exact parentReserveContribution_add_released_of_cachedAt_eq parameter otsSecret ftsSecret eligible
          (le_cacheQuery (answer := answer) hfresh) position
          (cachedAt_cacheQuery_of_not_atPosition parameter (fun h => heq (atPosition_unique parameter h hat)))
    rw [parentReserve, releasedParentReserve, ← Finset.sum_add_distrib]
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib, Fintype.sum_ite_eq']
    rfl
  · have hz : parentReserveCharge parameter otsSecret ftsSecret eligible cache input = 0 := by
      unfold parentReserveCharge
      rw [if_neg (by rintro ⟨position, hat, _⟩; exact hex ⟨position, hat⟩)]
    rw [hz, Nat.add_zero, parentReserve, releasedParentReserve, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro position _
    exact parentReserveContribution_add_released_of_cachedAt_eq parameter otsSecret ftsSecret eligible
      (le_cacheQuery (answer := answer) hfresh) position
      (cachedAt_cacheQuery_of_not_atPosition parameter (fun h => hex ⟨position, h⟩))

end SphincsSecurity
