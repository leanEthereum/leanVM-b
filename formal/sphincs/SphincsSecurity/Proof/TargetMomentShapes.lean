import SphincsSecurity.Proof.ClosedTargetMixedSigning

namespace SphincsSecurity.Concrete

attribute [local instance] Classical.propDecidable

structure TargetShapeValid (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) : Prop where
  nonempty : ∀ group ∈ groups, group.Nonempty
  disjoint : ∀ first ∈ groups, ∀ second ∈ groups, first ≠ second → Disjoint first second
  remaining : ∀ group ∈ groups, Disjoint group remaining

theorem TargetShapeValid.subsets {groups kept : Finset (Finset FtsTree)} {remaining trees : Finset FtsTree}
    (hvalid : TargetShapeValid groups remaining) (hgroups : kept ⊆ groups) (htrees : trees ⊆ remaining) :
    TargetShapeValid kept trees where
  nonempty group hgroup := hvalid.nonempty group (hgroups hgroup)
  disjoint first hfirst second hsecond hne := hvalid.disjoint first (hgroups hfirst) second (hgroups hsecond) hne
  remaining group hgroup := (hvalid.remaining group (hgroups hgroup)).mono_right htrees

theorem TargetShapeValid.new_group {groups : Finset (Finset FtsTree)} {remaining selected : Finset FtsTree}
    (hvalid : TargetShapeValid groups remaining) (hselected : selected.Nonempty) (hsub : selected ⊆ remaining) : selected ∉ groups := by
  intro hmem
  obtain ⟨tree, htree⟩ := hselected
  exact Finset.disjoint_left.mp (hvalid.remaining selected hmem) htree (hsub htree)

theorem TargetShapeValid.reuse {groups : Finset (Finset FtsTree)} {remaining selected : Finset FtsTree}
    (hvalid : TargetShapeValid groups remaining) (hselected : selected.Nonempty) (hsub : selected ⊆ remaining) :
    TargetShapeValid (insert selected groups) (remaining \ selected) := by
  constructor
  · intro group hgroup
    rcases Finset.mem_insert.mp hgroup with rfl | hgroup
    · exact hselected
    · exact hvalid.nonempty group hgroup
  · intro first hfirst second hsecond hne
    rcases Finset.mem_insert.mp hfirst with rfl | hfirstOld
    · rcases Finset.mem_insert.mp hsecond with rfl | hsecond
      · exact (hne rfl).elim
      · exact ((hvalid.remaining second hsecond).mono_right hsub).symm
    · rcases Finset.mem_insert.mp hsecond with rfl | hsecond
      · exact (hvalid.remaining first hfirstOld).mono_right hsub
      · exact hvalid.disjoint first hfirstOld second hsecond hne
  · intro group hgroup
    rcases Finset.mem_insert.mp hgroup with rfl | hgroup
    · exact Finset.disjoint_left.mpr (fun tree htree hrest => (Finset.mem_sdiff.mp hrest).2 htree)
    · exact (hvalid.remaining group hgroup).mono_right Finset.sdiff_subset

def targetShapeRank (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) : Nat := groups.card + 2 * remaining.card

theorem TargetShapeValid.degree_le {groups : Finset (Finset FtsTree)} {remaining : Finset FtsTree}
    (hvalid : TargetShapeValid groups remaining) : groups.card + remaining.card ≤ Fintype.card FtsTree := by
  have hpair : (groups : Set (Finset FtsTree)).PairwiseDisjoint id := hvalid.disjoint
  have hdisjoint : Disjoint (groups.biUnion id) remaining :=
    (Finset.disjoint_biUnion_left _ _ _).mpr hvalid.remaining
  calc
    groups.card + remaining.card ≤ (∑ group ∈ groups, group.card) + remaining.card := by
      apply Nat.add_le_add_right
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum (fun group hgroup => Finset.card_pos.mpr (hvalid.nonempty group hgroup))
    _ = (groups.biUnion id ∪ remaining).card := by rw [Finset.card_union_of_disjoint hdisjoint, Finset.card_biUnion hpair]; rfl
    _ ≤ _ := Finset.card_le_univ _

theorem TargetShapeValid.rank_le {groups : Finset (Finset FtsTree)} {remaining : Finset FtsTree}
    (hvalid : TargetShapeValid groups remaining) : targetShapeRank groups remaining ≤ 28 := by
  have hdegree := hvalid.degree_le
  have hcard : Fintype.card FtsTree = 14 := by decide
  unfold targetShapeRank
  omega

theorem targetShapeRank_drop_groups {groups kept : Finset (Finset FtsTree)} {remaining trees : Finset FtsTree}
    (hgroups : kept ⊂ groups) (htrees : trees ⊆ remaining) : targetShapeRank kept trees < targetShapeRank groups remaining := by
  have hg := Finset.card_lt_card hgroups
  have ht := Finset.card_le_card htrees
  unfold targetShapeRank
  omega

theorem targetShapeRank_drop_trees (groups : Finset (Finset FtsTree)) {remaining trees : Finset FtsTree}
    (htrees : trees ⊂ remaining) : targetShapeRank groups trees < targetShapeRank groups remaining := by
  have ht := Finset.card_lt_card htrees
  unfold targetShapeRank
  omega

theorem targetShapeRank_reuse {groups : Finset (Finset FtsTree)} {remaining selected : Finset FtsTree}
    (hvalid : TargetShapeValid groups remaining) (hselected : selected.Nonempty) (hsub : selected ⊆ remaining) :
    targetShapeRank (insert selected groups) (remaining \ selected) < targetShapeRank groups remaining := by
  have hp := Finset.card_pos.mpr hselected
  have hs := Finset.card_le_card hsub
  simp only [targetShapeRank, Finset.card_insert_of_notMem (hvalid.new_group hselected hsub), Finset.card_sdiff_of_subset hsub]
  omega

end SphincsSecurity.Concrete
