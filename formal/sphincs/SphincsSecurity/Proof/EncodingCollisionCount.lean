import SphincsSecurity.Proof.EncodingCollisionMessageTargets
import SphincsSecurity.Proof.ValidCacheCollisionBound

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] instFintypePosition instFintypeEncodingPosition validCacheEntries digestCollisionCount
set_option backward.isDefEq.respectTransparency false

theorem encodingSelectionCandidates_subset_validCacheEntries (parameter : PublicParameter)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (position : EncodingPosition) :
    encodingSelectionCandidates parameter cache hfinite position ⊆ validCacheEntries cache := by
  rintro ⟨input, digest⟩ hmem
  obtain ⟨hc, _, hv, hd⟩ := (mem_encodingSelectionCandidates_iff hfinite).mp hmem
  exact (mem_validCacheEntries_iff hfinite).mpr ⟨hc, hv, hd⟩

theorem encodingCollisionPairs_disjoint (parameter : PublicParameter)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) {left right : EncodingPosition}
    (hne : left ≠ right) :
    Disjoint (encodingCollisionPairs parameter cache hfinite left)
      (encodingCollisionPairs parameter cache hfinite right) := by
  apply Finset.disjoint_left.mpr
  intro pair hl hr
  have hleft := (Finset.mem_product.mp (Finset.mem_filter.mp hl).1).1
  have hright := (Finset.mem_product.mp (Finset.mem_filter.mp hr).1).1
  exact hne (atEncodingPosition_unique ((mem_encodingSelectionCandidates_iff hfinite).mp hleft).2.1
    ((mem_encodingSelectionCandidates_iff hfinite).mp hright).2.1)

theorem encodingCollisionPairs_card_eq (parameter : PublicParameter)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (position : EncodingPosition) :
    (encodingCollisionPairs parameter cache hfinite position).card =
      digestCollisionCount (encodingSelectionCandidates parameter cache hfinite position) := by
  simp only [encodingCollisionPairs, Finset.card_filter, Finset.sum_product, digestCollisionCount]

theorem encodingCollisionPairs_sum_card_le_validCache_count (parameter : PublicParameter)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    (∑ position : EncodingPosition, (encodingCollisionPairs parameter cache hfinite position).card) ≤
      digestCollisionCount (validCacheEntries cache) := by
  have hdisjoint : (↑(Finset.univ : Finset EncodingPosition) : Set EncodingPosition).PairwiseDisjoint
      (encodingCollisionPairs parameter cache hfinite) := by
    intro left _ right _ hne
    exact encodingCollisionPairs_disjoint parameter cache hfinite hne
  rw [← Finset.card_biUnion hdisjoint]
  let allPairs := ((validCacheEntries cache) ×ˢ (validCacheEntries cache)).filter
    fun pair => pair.1.1 ≠ pair.2.1 ∧ pair.1.2 = pair.2.2
  have hsubset : (Finset.univ.biUnion (encodingCollisionPairs parameter cache hfinite)) ⊆ allPairs := by
    intro pair hmem
    obtain ⟨position, _, hp⟩ := Finset.mem_biUnion.mp hmem
    obtain ⟨⟨hl, hr⟩, hcollision⟩ := (Finset.mem_filter.mp hp).imp_left Finset.mem_product.mp
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨encodingSelectionCandidates_subset_validCacheEntries parameter cache hfinite position hl,
        encodingSelectionCandidates_subset_validCacheEntries parameter cache hfinite position hr⟩, hcollision⟩
  apply (Finset.card_le_card hsubset).trans_eq
  simp only [allPairs, Finset.card_filter, Finset.sum_product, digestCollisionCount]

theorem encodingCollisionMessageTargets_sum_card_le_validCache_count (parameter : PublicParameter)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    (∑ position : EncodingPosition, (encodingCollisionMessageTargets parameter cache hfinite position).card) ≤
      digestCollisionCount (validCacheEntries cache) :=
  (Finset.sum_le_sum fun position _ => encodingCollisionMessageTargets_card_le_pairs parameter cache hfinite position).trans
    (encodingCollisionPairs_sum_card_le_validCache_count parameter cache hfinite)

theorem encodingSelectionCandidates_mono (parameter : PublicParameter)
    {before after : QueryCache HashSpec} (hb : Finite before) (ha : Finite after)
    (hle : before ≤ after) (position : EncodingPosition) :
    encodingSelectionCandidates parameter before hb position ⊆ encodingSelectionCandidates parameter after ha position := by
  rintro ⟨input, digest⟩ hmem
  obtain ⟨hc, hp, hv, hd⟩ := (mem_encodingSelectionCandidates_iff hb).mp hmem
  obtain ⟨output, ho⟩ := Option.ne_none_iff_exists'.mp hc
  have hafter := hle ho
  have hf : fromCache before input = fromCache after input := by simp only [fromCache, ho, hafter]
  exact (mem_encodingSelectionCandidates_iff ha).mpr ⟨by simp only [hafter, ne_eq, reduceCtorEq, not_false_eq_true],
    hp, hf ▸ hv, hd.trans (congrArg truncateHash hf)⟩

theorem encodingCollisionPairs_mono (parameter : PublicParameter)
    {before after : QueryCache HashSpec} (hb : Finite before) (ha : Finite after)
    (hle : before ≤ after) (position : EncodingPosition) :
    encodingCollisionPairs parameter before hb position ⊆ encodingCollisionPairs parameter after ha position := by
  intro pair hmem
  obtain ⟨⟨hl, hr⟩, heq⟩ := (Finset.mem_filter.mp hmem).imp_left Finset.mem_product.mp
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨encodingSelectionCandidates_mono parameter hb ha hle position hl,
      encodingSelectionCandidates_mono parameter hb ha hle position hr⟩, heq⟩

theorem encodingCollisionMessageTargets_mono (parameter : PublicParameter)
    {before after : QueryCache HashSpec} (hb : Finite before) (ha : Finite after)
    (hle : before ≤ after) (position : EncodingPosition) :
    encodingCollisionMessageTargets parameter before hb position ⊆
      encodingCollisionMessageTargets parameter after ha position :=
  Finset.image_subset_image (encodingCollisionPairs_mono parameter hb ha hle position)

theorem encodingCollisionMessageTargets_snapshots_le_terminal_count (parameter : PublicParameter)
    (positions : Finset EncodingPosition) (snapshots : EncodingPosition → QueryCache HashSpec)
    (hfinite : ∀ position, Finite (snapshots position)) (terminal : QueryCache HashSpec)
    (ht : Finite terminal) (hle : ∀ position ∈ positions, snapshots position ≤ terminal) :
    (∑ position ∈ positions, (encodingCollisionMessageTargets parameter (snapshots position)
      (hfinite position) position).card) ≤ digestCollisionCount (validCacheEntries terminal) := by
  calc
    _ ≤ ∑ position ∈ positions, (encodingCollisionMessageTargets parameter terminal ht position).card :=
      Finset.sum_le_sum fun position hp => Finset.card_le_card
        (encodingCollisionMessageTargets_mono parameter (hfinite position) ht (hle position hp) position)
    _ ≤ ∑ position : EncodingPosition, (encodingCollisionMessageTargets parameter terminal ht position).card :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ positions)
    _ ≤ _ := encodingCollisionMessageTargets_sum_card_le_validCache_count parameter terminal ht

noncomputable def encodingCollisionTargetCount (parameter : PublicParameter) (cache : QueryCache HashSpec) : Nat :=
  if hfinite : Finite cache then
    ∑ position : EncodingPosition, (encodingCollisionMessageTargets parameter cache hfinite position).card
  else 0

theorem encodingCollisionTargetCount_le_validCache_count (parameter : PublicParameter) (cache : QueryCache HashSpec) :
    encodingCollisionTargetCount parameter cache ≤ digestCollisionCount (validCacheEntries cache) := by
  unfold encodingCollisionTargetCount
  split_ifs with hfinite
  · exact encodingCollisionMessageTargets_sum_card_le_validCache_count parameter cache hfinite
  · exact Nat.zero_le _

theorem expected_encodingCollisionTargetCount_scaled_le_127 {α : Type}
    (computation : OracleComp OracleWorld α) (parameter : PublicParameter)
    (q : Nat) (hbound : computation.IsQueryBoundP (· matches Sum.inr _) q) (hq : q ≤ 2 ^ 127) :
    (∑' result, Pr[= result | (simulateQ romImpl computation).run ∅] *
      (encodingCollisionTargetCount parameter result.2 : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ ≤
      (q : ENNReal) * (1 / 64) * (Fintype.card Digest : ENNReal)⁻¹ := by
  apply le_trans ?_ (expected_validCache_pairs_scaled_le_127 computation q hbound hq)
  apply mul_le_mul' ?_ le_rfl
  apply ENNReal.tsum_le_tsum
  intro result
  exact mul_le_mul' le_rfl (Nat.cast_le.mpr (encodingCollisionTargetCount_le_validCache_count parameter result.2))

end SphincsSecurity.Concrete
