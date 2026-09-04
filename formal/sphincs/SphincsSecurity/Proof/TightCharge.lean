import SphincsSecurity.Proof.Charge

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

theorem Position.depth_eq_of_mem_children {left right parent : Position}
    (hl : left ∈ parent.children) (hr : right ∈ parent.children) : left.depth = right.depth := by
  cases parent with
  | chain lay tree leafIdx chainIdx step =>
      rw [Position.children] at hl hr
      split at hl
      · simp_all
      · simp_all
  | leaf lay tree leafIdx =>
      simp only [Position.children, List.mem_ofFn] at hl hr
      obtain ⟨_, rfl⟩ := hl
      obtain ⟨_, rfl⟩ := hr
      rfl
  | node lay tree level nodeIdx =>
      rw [Position.children] at hl hr
      split at hl
      · split at hl <;> simp_all <;>
          rcases hl with rfl | rfl <;> rcases hr with rfl | rfl <;> rfl
      · simp_all
  | ftsLeaf => simp [Position.children] at hl
  | ftsNode index tree level nodeIdx =>
      rw [Position.children] at hl hr
      split at hl
      · split at hl <;> simp_all <;>
          rcases hl with rfl | rfl <;> rcases hr with rfl | rfl <;> rfl
      · simp_all
  | ftsRoots index =>
      simp only [Position.children, List.mem_ofFn] at hl hr
      obtain ⟨_, rfl⟩ := hl
      obtain ⟨_, rfl⟩ := hr
      rfl

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)

theorem settled_of_cacheQuery_other_depth_le
    {cache : QueryCache HashSpec} {input : HashInput} {answer : HashOutput}
    {queried position : Position} (hfresh : cache input = none)
    (hat : AtPosition parameter input queried) (hne : position ≠ queried)
    (hdepth : position.depth ≤ queried.depth)
    (hsettled : Settled parameter otsSecret ftsSecret (cache.cacheQuery input answer) position) :
    Settled parameter otsSecret ftsSecret cache position := by
  have hle : cache ≤ cache.cacheQuery input answer := le_cacheQuery hfresh
  have hchildren : ∀ child ∈ position.children, Settled parameter otsSecret ftsSecret cache child := by
    intro child hchild
    exact settled_of_cacheQuery_below parameter otsSecret ftsSecret hfresh hat
      (child.depth + 1) child (by omega)
      (lt_of_lt_of_le (Position.depth_lt_of_mem_children hchild) hdepth)
      (hsettled.children child hchild)
  have hpinned := honestInput_congr (fromCache (cache.cacheQuery input answer)) (fromCache cache)
    parameter otsSecret ftsSecret hsettled.valid (fun child hchild =>
      honestValue_eq_of_settled (agreesWithFn_fromCache_of_le hle) (hchildren child hchild))
  change cachedInput parameter otsSecret ftsSecret (cache.cacheQuery input answer) position =
    cachedInput parameter otsSecret ftsSecret cache position at hpinned
  have hinputne : cachedInput parameter otsSecret ftsSecret cache position ≠ input :=
    atPosition_ne parameter (atPosition_cachedInput parameter otsSecret ftsSecret cache position) hat hne
  rw [settled_iff]
  refine ⟨hsettled.valid, ?_, hchildren⟩
  have hcached := hsettled.cached
  rw [hpinned, QueryCache.cacheQuery_of_ne _ _ hinputne] at hcached
  exact hcached

def OtherChildrenSettled (cache : QueryCache HashSpec) (child parent : Position) : Prop :=
  ∀ sibling ∈ parent.children, sibling ≠ child → Settled parameter otsSecret ftsSecret cache sibling

theorem otherChildrenSettled_of_parent_settled_cacheQuery
    {cache : QueryCache HashSpec} {input : HashInput} {answer : HashOutput}
    {child parent : Position} (hfresh : cache input = none)
    (hat : AtPosition parameter input child) (hchild : child ∈ parent.children)
    (hparent : Settled parameter otsSecret ftsSecret (cache.cacheQuery input answer) parent) :
    OtherChildrenSettled parameter otsSecret ftsSecret cache child parent := by
  intro sibling hsibling hne
  exact settled_of_cacheQuery_other_depth_le parameter otsSecret ftsSecret hfresh hat hne
    (Position.depth_eq_of_mem_children hsibling hchild).le (hparent.children sibling hsibling)

noncomputable def tightSettlingTargets (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (child : Position) : Finset Digest :=
  open Classical in
  match child.parentOf with
  | none => answerTargets parameter cache hfinite child
  | some parent => answerTargets parameter cache hfinite child ∪
      if OtherChildrenSettled parameter otsSecret ftsSecret cache child parent then
        slotTargets parameter cache hfinite child parent else ∅

noncomputable def tightContribution (cache : QueryCache HashSpec) (position : Position) : Nat :=
  open Classical in
  if Settled parameter otsSecret ftsSecret cache position then 0 else
    (cachedAt parameter cache position).ncard *
      (1 + if ∀ child ∈ position.children, Settled parameter otsSecret ftsSecret cache child then 0 else 1)

noncomputable def tightPotential (cache : QueryCache HashSpec) : Nat :=
  ∑ position : Position, tightContribution parameter otsSecret ftsSecret cache position

theorem tightPotential_empty :
    tightPotential parameter otsSecret ftsSecret (∅ : QueryCache HashSpec) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro position _
  have hcached : cachedAt parameter (∅ : QueryCache HashSpec) position = ∅ := by
    ext input
    simp [cachedAt]
  simp [tightContribution, hcached]

theorem tightContribution_le_of_cachedAt_eq {cache cache' : QueryCache HashSpec}
    (hle : cache ≤ cache') (position : Position)
    (hcached : cachedAt parameter cache' position = cachedAt parameter cache position) :
    tightContribution parameter otsSecret ftsSecret cache' position ≤
      tightContribution parameter otsSecret ftsSecret cache position := by
  classical
  by_cases hs : Settled parameter otsSecret ftsSecret cache position
  · simp [tightContribution, hs, hs.mono hle]
  · by_cases hs' : Settled parameter otsSecret ftsSecret cache' position
    · simp [tightContribution, hs, hs']
    · by_cases hc : ∀ child ∈ position.children, Settled parameter otsSecret ftsSecret cache child
      · have hc' : ∀ child ∈ position.children, Settled parameter otsSecret ftsSecret cache' child :=
          fun child hchild => (hc child hchild).mono hle
        simp only [tightContribution, hs, hs', if_false, hcached]
        rw [if_pos hc', if_pos hc]
      · simp only [tightContribution, hs, hs', if_false, hcached]
        rw [if_neg hc]
        split_ifs <;> omega

theorem tightContribution_add_cachedAt_le_of_settled {cache cache' : QueryCache HashSpec}
    {position : Position} (hunsettled : ¬ Settled parameter otsSecret ftsSecret cache position)
    (hsettled : Settled parameter otsSecret ftsSecret cache' position) :
    tightContribution parameter otsSecret ftsSecret cache' position +
      (cachedAt parameter cache position).ncard ≤
        tightContribution parameter otsSecret ftsSecret cache position := by
  classical
  simp only [tightContribution, hunsettled, hsettled, if_false, if_true, zero_add]
  split_ifs <;> omega

noncomputable def tightParentCharge (cache : QueryCache HashSpec) (child parent : Position) : Nat :=
  open Classical in
  if OtherChildrenSettled parameter otsSecret ftsSecret cache child parent then
    (cachedAt parameter cache parent).ncard else 0

theorem tightContribution_add_parentCharge_le {cache cache' : QueryCache HashSpec}
    (hle : cache ≤ cache') {parent child : Position} (hmem : child ∈ parent.children)
    (hunsettled : ¬ Settled parameter otsSecret ftsSecret cache child)
    (hsettled : Settled parameter otsSecret ftsSecret cache' child)
    (hcached : cachedAt parameter cache' parent = cachedAt parameter cache parent) :
    tightContribution parameter otsSecret ftsSecret cache' parent +
      tightParentCharge parameter otsSecret ftsSecret cache child parent ≤
        tightContribution parameter otsSecret ftsSecret cache parent := by
  classical
  by_cases hother : OtherChildrenSettled parameter otsSecret ftsSecret cache child parent
  · have hbefore : ¬ ∀ sibling ∈ parent.children, Settled parameter otsSecret ftsSecret cache sibling :=
      fun h => hunsettled (h child hmem)
    have hafter : ∀ sibling ∈ parent.children, Settled parameter otsSecret ftsSecret cache' sibling := by
      intro sibling hsibling
      by_cases heq : sibling = child
      · simpa only [heq] using hsettled
      · exact (hother sibling hsibling heq).mono hle
    have hparent : ¬ Settled parameter otsSecret ftsSecret cache parent :=
      fun h => hunsettled (h.children child hmem)
    rw [tightParentCharge, if_pos hother]
    simp only [tightContribution, hparent, if_false]
    rw [if_neg hbefore]
    by_cases hparentAfter : Settled parameter otsSecret ftsSecret cache' parent
    · rw [if_pos hparentAfter]
      omega
    · rw [if_neg hparentAfter, if_pos hafter, hcached]
      omega
  · rw [tightParentCharge, if_neg hother, Nat.add_zero]
    exact tightContribution_le_of_cachedAt_eq parameter otsSecret ftsSecret hle parent hcached

theorem tightSettlingTargets_card_le (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (child : Position) :
    (tightSettlingTargets parameter otsSecret ftsSecret cache hfinite child).card ≤
      (cachedAt parameter cache child).ncard +
        match child.parentOf with
        | none => 0
        | some parent => tightParentCharge parameter otsSecret ftsSecret cache child parent := by
  classical
  rw [tightSettlingTargets]
  split
  · simpa using answerTargets_card_le parameter cache hfinite child
  · rename_i parent hparent
    by_cases hother : OtherChildrenSettled parameter otsSecret ftsSecret cache child parent
    · simp only [hother, if_true, tightParentCharge]
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add
        (answerTargets_card_le parameter cache hfinite child)
        (slotTargets_card_le parameter cache hfinite child parent))
    · simp only [hother, if_false, tightParentCharge, Finset.union_empty, Nat.add_zero]
      exact answerTargets_card_le parameter cache hfinite child

theorem clean_cacheQuery_of_settling_of_avoids_tight {cache : QueryCache HashSpec}
    (hfinite : Finite cache) {input₀ : HashInput} {answer : HashOutput} {p₀ : Position}
    (hclean : ¬ Bad parameter otsSecret ftsSecret cache) (huncached : cache input₀ = none)
    (hposition : AtPosition parameter input₀ p₀)
    (hunsettled : ¬ Settled parameter otsSecret ftsSecret cache p₀)
    (hsettled : Settled parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer) p₀)
    (havoid : truncateHash answer ∉ tightSettlingTargets parameter otsSecret ftsSecret cache hfinite p₀) :
    ¬ Bad parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer) := by
  have hle : cache ≤ cache.cacheQuery input₀ answer := le_cacheQuery huncached
  obtain ⟨hinput₀, hchildren⟩ := eq_cachedInput_and_children_of_settled_cacheQuery
    parameter otsSecret ftsSecret huncached hposition hunsettled hsettled
  have hvalues : ∀ c ∈ p₀.children,
      honestValue (fromCache (cache.cacheQuery input₀ answer)) parameter otsSecret ftsSecret c
        = honestValue (fromCache cache) parameter otsSecret ftsSecret c := fun c hc =>
    honestValue_eq_of_settled (agreesWithFn_fromCache_of_le hle) (hchildren c hc)
  have hpinned₀ : cachedInput parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer) p₀
      = cachedInput parameter otsSecret ftsSecret cache p₀ :=
    honestInput_congr _ _ parameter otsSecret ftsSecret hsettled.valid hvalues
  have hinputNew : cachedInput parameter otsSecret ftsSecret
      (cache.cacheQuery input₀ answer) p₀ = input₀ := hpinned₀.trans hinput₀.symm
  have hparentClean : ∀ q parent, some p₀ = some q → q.parentOf = some parent →
      ¬ Settled parameter otsSecret ftsSecret (cache.cacheQuery input₀ answer) parent := by
    intro q parent hq hparent
    rw [Option.some.injEq] at hq
    subst hq
    have hmem : p₀ ∈ parent.children := Position.mem_children_iff.mpr hparent
    by_cases hother : OtherChildrenSettled parameter otsSecret ftsSecret cache p₀ parent
    · have hslotAvoid : truncateHash answer ∉ slotTargets parameter cache hfinite p₀ parent := by
        intro hmemTarget
        apply havoid
        simp [tightSettlingTargets, hparent, hother, hmemTarget]
      exact not_settled_parent_of_avoids_slotTargets parameter otsSecret ftsSecret hfinite
        huncached hposition hunsettled hsettled hmem hslotAvoid
    · intro hparentSettled
      exact hother (otherChildrenSettled_of_parent_settled_cacheQuery parameter otsSecret ftsSecret
        huncached hposition hmem hparentSettled)
  rintro ⟨p, hsettled', input, ax, ay, hat, hne, hinput, hhonest, heq⟩
  by_cases hp : p = p₀
  · subst hp
    have hinputne : input ≠ input₀ := by rwa [hinputNew] at hne
    have hinputOld : cache input = some ax := by
      rwa [QueryCache.cacheQuery_of_ne _ _ hinputne] at hinput
    have hcachedAt : input ∈ cachedAt parameter cache p :=
      ⟨by simp [hinputOld], hat⟩
    have htarget : truncateHash ax ∈ answerTargets parameter cache hfinite p := by
      simpa [hinputOld] using mem_answerTargets parameter hfinite hcachedAt
    rw [hinputNew, QueryCache.cacheQuery_self] at hhonest
    have hanswer : answer = ay := Option.some.inj hhonest
    apply havoid
    have heqAnswer : truncateHash answer = truncateHash ax := by rw [hanswer, ← heq]
    rw [heqAnswer]
    rw [tightSettlingTargets]
    split
    · exact htarget
    · exact Finset.mem_union_left _ htarget
  · have hsettledOld : Settled parameter otsSecret ftsSecret cache p :=
      settled_of_settled_cacheQuery parameter otsSecret ftsSecret huncached
        (p₀ := some p₀) (fun q hq => by
          rw [atPosition_unique parameter hposition hq]) hparentClean
        (p.depth + 1) p (by omega) (by
          intro heq
          exact hp (Option.some.inj heq).symm) hsettled'
    have hpinned := cachedInput_eq_of_settled hle hsettledOld
    have hinputne : input ≠ input₀ := atPosition_ne parameter hat hposition hp
    have hhonestne : cachedInput parameter otsSecret ftsSecret cache p ≠ input₀ :=
      atPosition_ne parameter (atPosition_cachedInput parameter otsSecret ftsSecret cache p)
        hposition hp
    have hinputOld : cache input = some ax := by
      rwa [QueryCache.cacheQuery_of_ne _ _ hinputne] at hinput
    rw [hpinned, QueryCache.cacheQuery_of_ne _ _ hhonestne] at hhonest
    apply hclean
    refine ⟨p, hsettledOld, input, ax, ay, hat, ?_, hinputOld, hhonest, heq⟩
    rwa [hpinned] at hne

end SphincsSecurity
