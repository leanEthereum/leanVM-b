import SphincsSecurity.Proof.SubsetTargetExpectation

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem sourceSubsetMatch_symm (target source : FewTimeView) (required : Finset FtsTree) :
    sourceSubsetMatch target source required = sourceSubsetMatch source target required := by
  unfold sourceSubsetMatch
  apply Finset.prod_congr rfl
  intro tree _
  simp only [sourceTreeMatch, eq_comm]

theorem sourceSubsetMatch_index_leaf (source : FewTimeView) (required : Finset FtsTree) (hne : required.Nonempty)
    (index : Index) (leaves : FtsTree → FtsLeaf) :
    sourceSubsetMatch (index, leaves) source required =
      (if source.1 = index then 1 else 0) * ∏ tree ∈ required, (if leaves tree = source.2 tree then 1 else 0) := by
  rw [sourceSubsetMatch_symm, sourceSubsetMatch_index source required hne]
  by_cases hi : index = source.1 <;> simp only [hi, eq_comm, if_true, if_false, one_mul, zero_mul]

theorem prod_block_leafMatch (required : Finset FtsTree) (owner : FtsTree → Fin m)
    (sources : Fin m → FewTimeView) (leaves : FtsTree → FtsLeaf) :
    (∏ block : Fin m, ∏ tree ∈ required.filter (owner · = block), if leaves tree = (sources block).2 tree then 1 else 0) =
      ∏ tree ∈ required, if leaves tree = (sources (owner tree)).2 tree then 1 else 0 := by
  calc
    _ = ∏ block : Fin m, ∏ tree ∈ required.filter (owner · = block),
        if leaves tree = (sources (owner tree)).2 tree then 1 else 0 := by
      apply Finset.prod_congr rfl
      intro block _
      apply Finset.prod_congr rfl
      intro tree htree
      rw [(Finset.mem_filter.mp htree).2]
    _ = _ := Finset.prod_fiberwise required owner _

theorem sum_leaf_sourceBlockMatches (required : Finset FtsTree) (owner : FtsTree → Fin m)
    (hne : ∀ block, (required.filter (owner · = block)).Nonempty) (sources : Fin m → FewTimeView) (index : Index) :
    (∑ leaves : FtsTree → FtsLeaf, ∏ block : Fin m, sourceSubsetMatch (index, leaves) (sources block) (required.filter (owner · = block))) =
      Fintype.card FtsLeaf ^ (Fintype.card FtsTree - required.card) *
        ∏ block : Fin m, if (sources block).1 = index then 1 else 0 := by
  simp only [sourceSubsetMatch_index_leaf _ _ (hne _), Finset.prod_mul_distrib, prod_block_leafMatch, ← Finset.mul_sum]
  rw [sum_leaf_partial_product required (fun tree leaf => if leaf = (sources (owner tree)).2 tree then 1 else 0)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.prod_const_one, mul_one]
  exact mul_comm _ _

noncomputable def targetBlockMatchProduct (required : Finset FtsTree) (owner : FtsTree → Fin m)
    (sizes : Fin m → Nat) (views : (block : Fin m) → Fin (sizes block) → FewTimeView) (target : FewTimeView) : Nat :=
  ∏ block : Fin m, ∑ slot : Fin (sizes block), sourceSubsetMatch target (views block slot) (required.filter (owner · = block))

theorem sum_targetBlockMatchProduct (required : Finset FtsTree) (owner : FtsTree → Fin m)
    (hne : ∀ block, (required.filter (owner · = block)).Nonempty) (sizes : Fin m → Nat)
    (views : (block : Fin m) → Fin (sizes block) → FewTimeView) :
    (∑ target : FewTimeView, targetBlockMatchProduct required owner sizes views target) =
      Fintype.card FtsLeaf ^ (Fintype.card FtsTree - required.card) *
        ∑ index : Index, ∏ block : Fin m, ∑ slot : Fin (sizes block), if (views block slot).1 = index then 1 else 0 := by
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  simp only [targetBlockMatchProduct, Fintype.prod_sum]
  rw [Finset.sum_comm]
  simp only [sum_leaf_sourceBlockMatches required owner hne, ← Finset.mul_sum]

theorem normalized_expected_targetBlockMatchProduct (required : Finset FtsTree) (owner : FtsTree → Fin m)
    (hne : ∀ block, (required.filter (owner · = block)).Nonempty) (sizes : Fin m → Nat)
    (views : (block : Fin m) → Fin (sizes block) → FewTimeView) :
    (Fintype.card FtsLeaf ^ required.card : Nat) *
      (∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
        (targetBlockMatchProduct required owner sizes views target : ENNReal)) =
      (∑ index : Index, ∏ block : Fin m, ∑ slot : Fin (sizes block),
        if (views block slot).1 = index then 1 else 0 : Nat) / (Fintype.card Index : ENNReal) := by
  have hrequired : required.Nonempty := (hne (owner ⟨0, by decide⟩)).mono (Finset.filter_subset _ _)
  have hrate := normalized_expected_sourceSubsetMatch (default : FewTimeView) required hrequired
  rw [expected_sourceSubsetMatch _ required hrequired] at hrate
  simp only [probOutput_uniformSample, tsum_fintype]
  rw [← Finset.mul_sum, ← Nat.cast_sum, sum_targetBlockMatchProduct required owner hne sizes views, Nat.cast_mul]
  calc
    _ = ((Fintype.card FtsLeaf ^ required.card : Nat) *
        ((Fintype.card FtsLeaf ^ (Fintype.card FtsTree - required.card) : Nat) / (Fintype.card FewTimeView : ENNReal))) *
        (∑ index : Index, ∏ block : Fin m, ∑ slot : Fin (sizes block), if (views block slot).1 = index then 1 else 0 : Nat) := by
      simp only [div_eq_mul_inv]
      ring
    _ = _ := by rw [hrate]; exact mul_comm _ _

end SphincsSecurity.Concrete
