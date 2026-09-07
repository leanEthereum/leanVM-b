import SphincsSecurity.Proof.TargetShapeEnvelope

namespace SphincsSecurity.Concrete

open ENNReal

def TargetRankZero (bound : Nat) (f : TargetShapeVector) : Prop :=
  ∀ groups remaining, TargetShapeValid groups remaining → targetShapeRank groups remaining < bound → f groups remaining = 0

theorem targetCacheLower_rank_zero {bound : Nat} {f : TargetShapeVector} (hzero : TargetRankZero bound f) :
    TargetRankZero (bound + 1) (targetCacheLower f) := by
  intro groups remaining hvalid hrank
  apply Finset.sum_eq_zero
  intro kept hkept
  have hsub := Finset.mem_powerset.mp (Finset.mem_erase.mp hkept).2
  have hproper : kept ⊂ groups := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, (Finset.mem_erase.mp hkept).1⟩
  have hdrop := targetShapeRank_drop_groups hproper (Finset.Subset.refl remaining)
  exact hzero kept remaining (hvalid.subsets hsub (Finset.Subset.refl _)) (by omega)

theorem targetTreeLower_rank_zero {bound : Nat} {f : TargetShapeVector} (hzero : TargetRankZero bound f) :
    TargetRankZero (bound + 1) (targetTreeLower f) := by
  intro groups remaining hvalid hrank
  apply Finset.sum_eq_zero
  intro selected hselected
  have hsub := Finset.mem_powerset.mp (Finset.mem_erase.mp hselected).2
  have hnonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hselected).1
  have hproper : remaining \ selected ⊂ remaining := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, ?_⟩
    intro heq
    obtain ⟨tree, htree⟩ := hnonempty
    have hmem : tree ∈ remaining \ selected := by rw [heq]; exact hsub htree
    exact (Finset.mem_sdiff.mp hmem).2 htree
  have hdrop := targetShapeRank_drop_trees groups hproper
  exact hzero groups _ (hvalid.subsets (Finset.Subset.refl _) Finset.sdiff_subset) (by omega)

theorem targetReuseStep_rank_zero {bound : Nat} {f : TargetShapeVector} (hzero : TargetRankZero bound f) :
    TargetRankZero (bound + 1) (targetReuseStep f) := by
  intro groups remaining hvalid hrank
  apply Finset.sum_eq_zero
  intro selected hselected
  have hsub := Finset.mem_powerset.mp (Finset.mem_erase.mp hselected).2
  have hnonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hselected).1
  have hdrop := targetShapeRank_reuse hvalid hnonempty hsub
  exact hzero _ _ (hvalid.reuse hnonempty hsub) (by omega)

noncomputable def targetShapeQueryIncrement (arrival : ENNReal) (f : TargetShapeVector)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) : ENNReal := arrival * targetCacheLower f groups remaining

noncomputable def targetShapeSigningIncrement (uniform reuse : ENNReal) (f : TargetShapeVector)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) : ENNReal :=
  uniform * (targetCacheLower f groups remaining + targetTreeLower f groups remaining + targetCacheLower (targetTreeLower f) groups remaining) +
    reuse * targetReuseStep f groups remaining

theorem targetShapeQueryIncrement_rank_zero (arrival : ENNReal) {bound : Nat} {f : TargetShapeVector} (hzero : TargetRankZero bound f) :
    TargetRankZero (bound + 1) (targetShapeQueryIncrement arrival f) := by
  intro groups remaining hvalid hrank
  rw [targetShapeQueryIncrement, targetCacheLower_rank_zero hzero groups remaining hvalid hrank, mul_zero]

theorem targetShapeSigningIncrement_rank_zero (uniform reuse : ENNReal) {bound : Nat} {f : TargetShapeVector} (hzero : TargetRankZero bound f) :
    TargetRankZero (bound + 1) (targetShapeSigningIncrement uniform reuse f) := by
  intro groups remaining hvalid hrank
  rw [targetShapeSigningIncrement, targetCacheLower_rank_zero hzero groups remaining hvalid hrank,
    targetTreeLower_rank_zero hzero groups remaining hvalid hrank,
    targetCacheLower_rank_zero (targetTreeLower_rank_zero hzero) groups remaining hvalid (by omega),
    targetReuseStep_rank_zero hzero groups remaining hvalid hrank]
  simp only [add_zero, mul_zero]

theorem targetShapeQueryIncrement_iterate_rank_zero (arrival : ENNReal) (steps : Nat) (f : TargetShapeVector) :
    TargetRankZero steps ((targetShapeQueryIncrement arrival)^[steps] f) := by
  induction steps with
  | zero => intro _ _ _ h; omega
  | succ steps ih =>
      rw [Function.iterate_succ_apply']
      exact targetShapeQueryIncrement_rank_zero arrival ih

theorem targetShapeSigningIncrement_iterate_rank_zero (uniform reuse : ENNReal) (steps : Nat) (f : TargetShapeVector) :
    TargetRankZero steps ((targetShapeSigningIncrement uniform reuse)^[steps] f) := by
  induction steps with
  | zero => intro _ _ _ h; omega
  | succ steps ih =>
      rw [Function.iterate_succ_apply']
      exact targetShapeSigningIncrement_rank_zero uniform reuse ih

theorem targetShapeQueryIncrement_iterate_zero (arrival : ENNReal) (steps : Nat) (f : TargetShapeVector)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) (hsteps : 29 ≤ steps) :
    (targetShapeQueryIncrement arrival)^[steps] f groups remaining = 0 :=
  targetShapeQueryIncrement_iterate_rank_zero arrival steps f groups remaining hvalid (lt_of_le_of_lt hvalid.rank_le (by omega))

theorem targetShapeSigningIncrement_iterate_zero (uniform reuse : ENNReal) (steps : Nat) (f : TargetShapeVector)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) (hsteps : 29 ≤ steps) :
    (targetShapeSigningIncrement uniform reuse)^[steps] f groups remaining = 0 :=
  targetShapeSigningIncrement_iterate_rank_zero uniform reuse steps f groups remaining hvalid (lt_of_le_of_lt hvalid.rank_le (by omega))

end SphincsSecurity.Concrete
