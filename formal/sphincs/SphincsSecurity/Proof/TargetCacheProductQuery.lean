import SphincsSecurity.Proof.CachedTargetSubsetMatch

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem sourceSubsetMatch_prod (target source : FewTimeView) (groups : Fin m → Finset FtsTree) (selected : Finset (Fin m)) :
    (∏ slot ∈ selected, sourceSubsetMatch target source (groups slot)) =
      sourceSubsetMatch target source (selected.biUnion groups) := by
  induction selected using Finset.induction_on with
  | empty => simp [sourceSubsetMatch]
  | @insert slot selected hnot ih =>
      rw [Finset.prod_insert hnot, Finset.biUnion_insert, ih, sourceSubsetMatch_mul]

noncomputable def targetCacheProduct (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (targetInput : HashInput) (target : FewTimeView) (groups : Fin m → Finset FtsTree) : ENNReal :=
  ∏ slot : Fin m, cachedTargetSubsetMatch parameter cache targetInput target (groups slot)

theorem targetCacheProduct_cacheQuery (parameter : PublicParameter) (before : QueryCache HashSpec)
    (targetInput : HashInput) (target : FewTimeView) (groups : Fin m → Finset FtsTree) (input : HashInput) (output : HashOutput)
    (hfresh : before input = none) (hmessage : FtsProbeSimulation.MessageHashInput parameter input) (hne : input ≠ targetInput) :
    targetCacheProduct parameter (before.cacheQuery input output) targetInput target groups =
      targetCacheProduct parameter before targetInput target groups +
        ∑ selected ∈ (Finset.univ : Finset (Fin m)).powerset.erase ∅,
          (if Admissible (truncateMessageDigest output) then
            (sourceSubsetMatch target (hashOutputFewTimeView output) (selected.biUnion groups) : ENNReal) else 0) *
              ∏ slot ∈ (Finset.univ : Finset (Fin m)) \ selected, cachedTargetSubsetMatch parameter before targetInput target (groups slot) := by
  unfold targetCacheProduct
  simp only [cachedTargetSubsetMatch_cacheQuery parameter before targetInput target _ input output hfresh,
    hmessage, true_and, if_neg hne]
  rw [show (∏ slot : Fin m, (cachedTargetSubsetMatch parameter before targetInput target (groups slot) +
      if Admissible (truncateMessageDigest output) then (sourceSubsetMatch target (hashOutputFewTimeView output) (groups slot) : ENNReal) else 0)) =
      ∏ slot : Fin m, ((if Admissible (truncateMessageDigest output) then (sourceSubsetMatch target (hashOutputFewTimeView output) (groups slot) : ENNReal) else 0) +
        cachedTargetSubsetMatch parameter before targetInput target (groups slot)) by simp only [add_comm]]
  rw [Finset.prod_add, ← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset _)]
  simp only [Finset.prod_empty, Finset.sdiff_empty, one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro selected hselected
  congr 1
  by_cases hadmissible : Admissible (truncateMessageDigest output)
  · simp only [hadmissible, if_true, ← Nat.cast_prod, sourceSubsetMatch_prod]
  · simp only [hadmissible, if_false]
    obtain ⟨slot, hslot⟩ := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hselected).1
    exact Finset.prod_eq_zero hslot rfl

theorem expected_targetCacheProduct_cacheQuery (parameter : PublicParameter) (before : QueryCache HashSpec)
    (targetInput : HashInput) (target : FewTimeView) (groups : Fin m → Finset FtsTree)
    (hgroups : ∀ slot, (groups slot).Nonempty) (input : HashInput)
    (hfresh : before input = none) (hmessage : FtsProbeSimulation.MessageHashInput parameter input) (hne : input ≠ targetInput) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      targetCacheProduct parameter (before.cacheQuery input output) targetInput target groups) =
      targetCacheProduct parameter before targetInput target groups +
        ∑ selected ∈ (Finset.univ : Finset (Fin m)).powerset.erase ∅,
          (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ *
            ((Fintype.card FtsLeaf ^ (Fintype.card FtsTree - (selected.biUnion groups).card) : Nat) / (Fintype.card FewTimeView : ENNReal))) *
              ∏ slot ∈ (Finset.univ : Finset (Fin m)) \ selected, cachedTargetSubsetMatch parameter before targetInput target (groups slot) := by
  have hmass : (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)]) = 1 := tsum_probOutput_eq_one' (by simp)
  simp only [targetCacheProduct_cacheQuery parameter before targetInput target groups input _ hfresh hmessage hne,
    mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  congr 1
  apply Finset.sum_congr rfl
  intro selected hselected
  simp only [← mul_assoc, ENNReal.tsum_mul_right]
  congr 1
  have hselectedNonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hselected).1
  obtain ⟨slot, hslot⟩ := hselectedNonempty
  obtain ⟨tree, htree⟩ := hgroups slot
  have hunion : (selected.biUnion groups).Nonempty := ⟨tree, Finset.mem_biUnion.mpr ⟨slot, hslot, htree⟩⟩
  rw [expected_uniformHashOutput_admissible_weight
    (fun source => (sourceSubsetMatch target source (selected.biUnion groups) : ENNReal)),
    expected_sourceSubsetMatch target _ hunion]

theorem targetCacheProduct_cacheQuery_self (parameter : PublicParameter) (before : QueryCache HashSpec)
    (targetInput : HashInput) (target : FewTimeView) (groups : Fin m → Finset FtsTree) (output : HashOutput)
    (hfresh : before targetInput = none) :
    targetCacheProduct parameter (before.cacheQuery targetInput output) targetInput target groups =
      targetCacheProduct parameter before targetInput target groups := by
  simp only [targetCacheProduct, cachedTargetSubsetMatch_cacheQuery_self parameter before targetInput target _ output hfresh]

end SphincsSecurity.Concrete
