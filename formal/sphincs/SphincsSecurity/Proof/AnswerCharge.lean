import SphincsSecurity.Proof.TightChargePotential

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

attribute [local irreducible] instFintypePosition

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)

def ParentSettlement (cache : QueryCache HashSpec) (input : HashInput) (answer : HashOutput) : Prop :=
  cache input = none ∧ ∃ child parent : Position,
    AtPosition parameter input child ∧
      ¬ Settled parameter otsSecret ftsSecret cache child ∧
      Settled parameter otsSecret ftsSecret (cache.cacheQuery input answer) child ∧
      child.parentOf = some parent ∧
      Settled parameter otsSecret ftsSecret (cache.cacheQuery input answer) parent

def CleanParentSettlement (cache : QueryCache HashSpec) (input : HashInput) (answer : HashOutput) : Prop :=
  ¬ Bad parameter otsSecret ftsSecret cache ∧ ParentSettlement parameter otsSecret ftsSecret cache input answer

noncomputable def answerContribution (cache : QueryCache HashSpec) (position : Position) : Nat :=
  open Classical in
  if Settled parameter otsSecret ftsSecret cache position then 0
  else (cachedAt parameter cache position).ncard

noncomputable def answerPotential (cache : QueryCache HashSpec) : Nat :=
  ∑ position : Position, answerContribution parameter otsSecret ftsSecret cache position

theorem answerPotential_empty : answerPotential parameter otsSecret ftsSecret (∅ : QueryCache HashSpec) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro position _
  have hcached : cachedAt parameter (∅ : QueryCache HashSpec) position = ∅ := by
    ext input
    simp [cachedAt]
  simp [answerContribution, hcached]

theorem answerContribution_le_of_cachedAt_eq {cache cache' : QueryCache HashSpec}
    (hle : cache ≤ cache') (position : Position)
    (hcached : cachedAt parameter cache' position = cachedAt parameter cache position) :
    answerContribution parameter otsSecret ftsSecret cache' position ≤
      answerContribution parameter otsSecret ftsSecret cache position := by
  classical
  by_cases hs : Settled parameter otsSecret ftsSecret cache position
  · simp [answerContribution, hs, hs.mono hle]
  · simp only [answerContribution, hs, if_false]
    split_ifs <;> simp [hcached]

theorem answerPotential_add_answerTargets_card_le {cache : QueryCache HashSpec}
    (hfinite : Finite cache) {input : HashInput} {answer : HashOutput} {queried : Position}
    (hfresh : cache input = none) (hat : AtPosition parameter input queried)
    (hbefore : ¬ Settled parameter otsSecret ftsSecret cache queried)
    (hafter : Settled parameter otsSecret ftsSecret (cache.cacheQuery input answer) queried) :
    answerPotential parameter otsSecret ftsSecret (cache.cacheQuery input answer) +
        (answerTargets parameter cache hfinite queried).card ≤ answerPotential parameter otsSecret ftsSecret cache := by
  classical
  have hle := le_cacheQuery (answer := answer) hfresh
  have hsum : (∑ position : Position,
      (answerContribution parameter otsSecret ftsSecret (cache.cacheQuery input answer) position +
        if position = queried then (cachedAt parameter cache queried).ncard else 0)) ≤
      ∑ position : Position, answerContribution parameter otsSecret ftsSecret cache position := by
    apply Finset.sum_le_sum
    intro position _
    by_cases heq : position = queried
    · subst position
      simp [answerContribution, hbefore, hafter]
    · simp only [heq, if_false, Nat.add_zero]
      exact answerContribution_le_of_cachedAt_eq parameter otsSecret ftsSecret hle position
        (cachedAt_cacheQuery_of_not_atPosition parameter (fun h => heq (atPosition_unique parameter h hat)))
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq'] at hsum
  simp only [Finset.mem_univ, if_true] at hsum
  exact (Nat.add_le_add_left (answerTargets_card_le parameter cache hfinite queried) _).trans hsum

theorem answerPotential_cacheQuery_le_one {cache : QueryCache HashSpec}
    {input : HashInput} {answer : HashOutput} {queried : Position}
    (hfresh : cache input = none) (hat : AtPosition parameter input queried) :
    answerPotential parameter otsSecret ftsSecret (cache.cacheQuery input answer) ≤
      answerPotential parameter otsSecret ftsSecret cache + 1 := by
  classical
  have hle := le_cacheQuery (answer := answer) hfresh
  have hcard : (cachedAt parameter (cache.cacheQuery input answer) queried).ncard ≤
      (cachedAt parameter cache queried).ncard + 1 := by
    rw [cachedAt_cacheQuery_self parameter hat]
    exact Set.ncard_insert_le _ _
  have hlocal : answerContribution parameter otsSecret ftsSecret (cache.cacheQuery input answer) queried ≤
      answerContribution parameter otsSecret ftsSecret cache queried + 1 := by
    by_cases hs : Settled parameter otsSecret ftsSecret cache queried
    · simp [answerContribution, hs, hs.mono hle]
    · simp only [answerContribution, hs, if_false]
      split_ifs <;> omega
  calc
    _ ≤ ∑ position : Position,
        (answerContribution parameter otsSecret ftsSecret cache position + if position = queried then 1 else 0) := by
      apply Finset.sum_le_sum
      intro position _
      by_cases heq : position = queried
      · simpa only [heq, if_true] using hlocal
      · simp only [heq, if_false, Nat.add_zero]
        exact answerContribution_le_of_cachedAt_eq parameter otsSecret ftsSecret hle position
          (cachedAt_cacheQuery_of_not_atPosition parameter (fun h => heq (atPosition_unique parameter h hat)))
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp only [Finset.mem_univ, if_true]
      rfl

theorem answerPotential_cacheQuery_le_of_settled {cache : QueryCache HashSpec}
    {input : HashInput} {answer : HashOutput} {queried : Position}
    (hfresh : cache input = none) (hat : AtPosition parameter input queried)
    (hs : Settled parameter otsSecret ftsSecret cache queried) :
    answerPotential parameter otsSecret ftsSecret (cache.cacheQuery input answer) ≤
      answerPotential parameter otsSecret ftsSecret cache := by
  classical
  have hle := le_cacheQuery (answer := answer) hfresh
  apply Finset.sum_le_sum
  intro position _
  by_cases heq : position = queried
  · subst position
    simp [answerContribution, hs, hs.mono hle]
  · exact answerContribution_le_of_cachedAt_eq parameter otsSecret ftsSecret hle position
      (cachedAt_cacheQuery_of_not_atPosition parameter (fun h => heq (atPosition_unique parameter h hat)))

theorem answerPotential_cacheQuery_le_of_not_atPosition {cache : QueryCache HashSpec}
    {input : HashInput} {answer : HashOutput}
    (hfresh : cache input = none) (hnot : ∀ position, ¬ AtPosition parameter input position) :
    answerPotential parameter otsSecret ftsSecret (cache.cacheQuery input answer) ≤
      answerPotential parameter otsSecret ftsSecret cache := by
  apply Finset.sum_le_sum
  intro position _
  exact answerContribution_le_of_cachedAt_eq parameter otsSecret ftsSecret (le_cacheQuery hfresh) position
    (cachedAt_cacheQuery_of_not_atPosition parameter (hnot position))

theorem ParentSettlement.exists_prior_guess {cache : QueryCache HashSpec}
    (hfinite : Finite cache) {input : HashInput} {answer : HashOutput}
    (hevent : ParentSettlement parameter otsSecret ftsSecret cache input answer) :
    ∃ child parent : Position, ∃ priorInput : HashInput,
      AtPosition parameter input child ∧ child.parentOf = some parent ∧
        ¬ Settled parameter otsSecret ftsSecret cache child ∧
        OtherChildrenSettled parameter otsSecret ftsSecret cache child parent ∧
        priorInput ∈ cachedAt parameter cache parent ∧
        slotDigest (parent.children.idxOf child) priorInput = truncateHash answer := by
  classical
  obtain ⟨hfresh, child, parent, hat, hbefore, hafter, hparent, hs⟩ := hevent
  have hmem := Position.mem_children_iff.mpr hparent
  have hslot : truncateHash answer ∈ slotTargets parameter cache hfinite child parent := by
    by_contra hnot
    exact not_settled_parent_of_avoids_slotTargets parameter otsSecret ftsSecret hfinite
      hfresh hat hbefore hafter hmem hnot hs
  rw [slotTargets, Finset.mem_image] at hslot
  obtain ⟨priorInput, hprior, hvalue⟩ := hslot
  exact ⟨child, parent, priorInput, hat, hparent, hbefore,
    otherChildrenSettled_of_parent_settled_cacheQuery parameter otsSecret ftsSecret hfresh hat hmem hs,
    (cachedAt_finite parameter hfinite parent).mem_toFinset.mp hprior, hvalue⟩

end SphincsSecurity
