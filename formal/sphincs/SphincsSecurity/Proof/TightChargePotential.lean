import SphincsSecurity.Proof.TightCharge

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)

theorem tightPotential_add_settlingTargets_card_le {cache : QueryCache HashSpec}
    (hfinite : Finite cache) {input₀ : HashInput} {answer : HashOutput} {p₀ : Position}
    (huncached : cache input₀ = none) (hposition : AtPosition parameter input₀ p₀)
    (hunsettled : ¬ Settled parameter otsSecret ftsSecret cache p₀)
    (hsettled : Settled parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer) p₀) :
    tightPotential parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer)
        + (tightSettlingTargets parameter otsSecret ftsSecret cache hfinite p₀).card
      ≤ tightPotential parameter otsSecret ftsSecret cache := by
  classical
  let cache' := cache.cacheQuery input₀ answer
  have hle : cache ≤ cache' := le_cacheQuery huncached
  have hrelease₀ : tightContribution parameter otsSecret ftsSecret cache' p₀
        + (cachedAt parameter cache p₀).ncard
      ≤ tightContribution parameter otsSecret ftsSecret cache p₀ :=
    tightContribution_add_cachedAt_le_of_settled parameter otsSecret ftsSecret hunsettled
      hsettled
  have hcard := tightSettlingTargets_card_le parameter otsSecret ftsSecret cache hfinite p₀
  cases hparent : p₀.parentOf with
  | none =>
      simp only [hparent] at hcard
      have hsum : ∑ p : Position, (tightContribution parameter otsSecret ftsSecret cache' p
            + if p = p₀ then (cachedAt parameter cache p₀).ncard else 0)
          ≤ ∑ p : Position, tightContribution parameter otsSecret ftsSecret cache p := by
        refine Finset.sum_le_sum fun p _ => ?_
        by_cases hp : p = p₀
        · subst hp
          simpa using hrelease₀
        · simp only [hp, if_false, Nat.add_zero]
          have hnotAt : ¬ AtPosition parameter input₀ p := by
            intro hat
            exact hp (atPosition_unique parameter hat hposition)
          exact tightContribution_le_of_cachedAt_eq parameter otsSecret ftsSecret hle p
            (cachedAt_cacheQuery_of_not_atPosition parameter hnotAt)
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq'] at hsum
      simp only [Finset.mem_univ, if_true] at hsum
      change tightPotential parameter otsSecret ftsSecret cache'
          + (tightSettlingTargets parameter otsSecret ftsSecret cache hfinite p₀).card
        ≤ tightPotential parameter otsSecret ftsSecret cache
      rw [tightPotential, tightPotential]
      omega
  | some parent =>
      have hmem : p₀ ∈ parent.children := Position.mem_children_iff.mpr hparent
      have hpne : parent ≠ p₀ := by
        intro heq
        subst heq
        have := Position.depth_lt_of_mem_children hmem
        omega
      have hcachedAt : cachedAt parameter cache' parent = cachedAt parameter cache parent :=
        cachedAt_cacheQuery_of_not_atPosition parameter (by
          intro hat
          exact hpne (atPosition_unique parameter hat hposition))
      have hreleaseParent : tightContribution parameter otsSecret ftsSecret cache' parent
            + tightParentCharge parameter otsSecret ftsSecret cache p₀ parent
          ≤ tightContribution parameter otsSecret ftsSecret cache parent :=
        tightContribution_add_parentCharge_le parameter otsSecret ftsSecret hle hmem
          hunsettled hsettled hcachedAt
      simp only [hparent] at hcard
      have hsum : ∑ p : Position, ((tightContribution parameter otsSecret ftsSecret cache' p
              + if p = p₀ then (cachedAt parameter cache p₀).ncard else 0)
            + if p = parent then tightParentCharge parameter otsSecret ftsSecret cache p₀ parent else 0)
          ≤ ∑ p : Position, tightContribution parameter otsSecret ftsSecret cache p := by
        refine Finset.sum_le_sum fun p _ => ?_
        by_cases hq : p = p₀
        · subst hq
          simp only [if_pos, hpne.symm, if_false, Nat.add_zero]
          exact hrelease₀
        · by_cases hp : p = parent
          · subst hp
            simp only [hpne, if_false, if_pos, Nat.add_zero]
            exact hreleaseParent
          · simp only [hq, hp, if_false, Nat.add_zero]
            have hnotAt : ¬ AtPosition parameter input₀ p := by
              intro hat
              exact hq (atPosition_unique parameter hat hposition)
            exact tightContribution_le_of_cachedAt_eq parameter otsSecret ftsSecret hle p
              (cachedAt_cacheQuery_of_not_atPosition parameter hnotAt)
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
        Finset.sum_ite_eq'] at hsum
      simp only [Finset.mem_univ, if_true] at hsum
      change tightPotential parameter otsSecret ftsSecret cache'
          + (tightSettlingTargets parameter otsSecret ftsSecret cache hfinite p₀).card
        ≤ tightPotential parameter otsSecret ftsSecret cache
      rw [tightPotential, tightPotential]
      omega

theorem tightPotential_cacheQuery_le_of_unsettled
    {cache : QueryCache HashSpec} {input : HashInput} {answer : HashOutput} {queried : Position}
    (hfresh : cache input = none) (hat : AtPosition parameter input queried)
    (hunsettled : ¬ Settled parameter otsSecret ftsSecret (cache.cacheQuery input answer) queried) :
    tightPotential parameter otsSecret ftsSecret (cache.cacheQuery input answer) ≤
      tightPotential parameter otsSecret ftsSecret cache + 2 := by
  classical
  let cache' := cache.cacheQuery input answer
  have hle : cache ≤ cache' := le_cacheQuery hfresh
  have hunsettledBefore : ¬ Settled parameter otsSecret ftsSecret cache queried :=
    fun h => hunsettled (h.mono hle)
  have hcard : (cachedAt parameter cache' queried).ncard ≤ (cachedAt parameter cache queried).ncard + 1 := by
    rw [show cachedAt parameter cache' queried = insert input (cachedAt parameter cache queried) from
      cachedAt_cacheQuery_self parameter hat]
    exact Set.ncard_insert_le _ _
  have hlocal : tightContribution parameter otsSecret ftsSecret cache' queried ≤
      tightContribution parameter otsSecret ftsSecret cache queried + 2 := by
    change ¬ Settled parameter otsSecret ftsSecret cache' queried at hunsettled
    simp only [tightContribution, hunsettled, hunsettledBefore, if_false]
    by_cases hc : ∀ child ∈ queried.children, Settled parameter otsSecret ftsSecret cache child
    · have hc' : ∀ child ∈ queried.children, Settled parameter otsSecret ftsSecret cache' child :=
        fun child hchild => (hc child hchild).mono hle
      rw [if_pos hc', if_pos hc]
      omega
    · rw [if_neg hc]
      split_ifs <;> omega
  calc
    _ ≤ ∑ position : Position,
        (tightContribution parameter otsSecret ftsSecret cache position +
          if position = queried then 2 else 0) := by
      apply Finset.sum_le_sum
      intro position _
      by_cases heq : position = queried
      · simpa only [heq, if_true] using hlocal
      · simp only [heq, if_false, Nat.add_zero]
        exact tightContribution_le_of_cachedAt_eq parameter otsSecret ftsSecret hle position
          (cachedAt_cacheQuery_of_not_atPosition parameter (fun h =>
            heq (atPosition_unique parameter h hat)))
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp only [Finset.mem_univ, if_true]
      rfl

theorem tightPotential_cacheQuery_le_of_settled {cache : QueryCache HashSpec} {input₀ : HashInput}
    {answer : HashOutput} {p₀ : Position} (huncached : cache input₀ = none)
    (hposition : AtPosition parameter input₀ p₀)
    (hsettled : Settled parameter otsSecret ftsSecret cache p₀) :
    tightPotential parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer)
      ≤ tightPotential parameter otsSecret ftsSecret cache := by
  classical
  have hle : cache ≤ cache.cacheQuery input₀ answer := le_cacheQuery huncached
  have hsettled' : Settled parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer) p₀ :=
    hsettled.mono hle
  rw [tightPotential, tightPotential]
  refine Finset.sum_le_sum fun p _ => ?_
  by_cases hp : p = p₀
  · subst hp
    simp [tightContribution, hsettled, hsettled']
  · have hnotAt : ¬ AtPosition parameter input₀ p := by
      intro hat
      exact hp (atPosition_unique parameter hat hposition)
    exact tightContribution_le_of_cachedAt_eq parameter otsSecret ftsSecret hle p
      (cachedAt_cacheQuery_of_not_atPosition parameter hnotAt)

theorem clean_and_tightPotential_cacheQuery_of_not_atPosition
    {cache : QueryCache HashSpec} {input : HashInput} {answer : HashOutput}
    (hclean : ¬ Bad parameter otsSecret ftsSecret cache) (hfresh : cache input = none)
    (hnotAt : ∀ position, ¬ AtPosition parameter input position) :
    ¬ Bad parameter otsSecret ftsSecret (cache.cacheQuery input answer) ∧
      tightPotential parameter otsSecret ftsSecret (cache.cacheQuery input answer) ≤
        tightPotential parameter otsSecret ftsSecret cache := by
  constructor
  · exact (clean_and_potential_cacheQuery_of_not_atPosition parameter otsSecret ftsSecret
      hclean hfresh hnotAt).1
  · apply Finset.sum_le_sum
    intro position _
    exact tightContribution_le_of_cachedAt_eq parameter otsSecret ftsSecret (le_cacheQuery hfresh)
      position (cachedAt_cacheQuery_of_not_atPosition parameter (hnotAt position))

end SphincsSecurity
