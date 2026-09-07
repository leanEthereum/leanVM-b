import SphincsSecurity.Proof.FewTimeCoverageGrowth

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem signingSlotsAtIndex_insert_card {n : Nat} (views : Fin n → Option FewTimeView)
    (source : FewTimeView) (index : Index) :
    (signingSlotsAtIndex (insertFewTimeView views source) index).card =
      (signingSlotsAtIndex views index).card + if source.1 = index then 1 else 0 := by
  unfold signingSlotsAtIndex
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_succ]
  simp only [insertFewTimeView, Fin.cons_zero, Fin.cons_succ, Option.some.injEq, exists_eq_left']
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact add_comm _ _

noncomputable def occupancyIncrementAtIndex {n : Nat} (views : Fin n → Option FewTimeView) (index : Index) : Nat :=
  ((signingSlotsAtIndex views index).card + 1) ^ (ftsTrees - 1) - (signingSlotsAtIndex views index).card ^ (ftsTrees - 1)

theorem coverageOccupancyMoment_insert_eq {n : Nat} (views : Fin n → Option FewTimeView) (source : FewTimeView) :
    coverageOccupancyMoment (insertFewTimeView views source) = coverageOccupancyMoment views + occupancyIncrementAtIndex views source.1 := by
  have hpoint (index : Index) :
      ((signingSlotsAtIndex views index).card + if source.1 = index then 1 else 0) ^ (ftsTrees - 1) =
        (signingSlotsAtIndex views index).card ^ (ftsTrees - 1) + if source.1 = index then occupancyIncrementAtIndex views source.1 else 0 := by
    by_cases heq : source.1 = index
    · subst index
      simp only [if_true, occupancyIncrementAtIndex]
      have hle : (signingSlotsAtIndex views source.1).card ^ (ftsTrees - 1) ≤
          ((signingSlotsAtIndex views source.1).card + 1) ^ (ftsTrees - 1) := Nat.pow_le_pow_left (Nat.le_succ _) _
      omega
    · simp only [heq, if_false, add_zero]
  simp_rw [coverageOccupancyMoment, signingSlotsAtIndex_insert_card, hpoint]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem coverageOccupancyMoment_insert_le {n : Nat} (views : Fin n → Option FewTimeView) (source : FewTimeView)
    (increment : Nat) (hbound : ∀ index, occupancyIncrementAtIndex views index ≤ increment) :
    coverageOccupancyMoment (insertFewTimeView views source) ≤ coverageOccupancyMoment views + increment := by
  rw [coverageOccupancyMoment_insert_eq]
  exact Nat.add_le_add_left (hbound source.1) _

theorem expected_coverageOccupancyMoment_insert_eq {n : Nat} (views : Fin n → Option FewTimeView) :
    (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
      (coverageOccupancyMoment (insertFewTimeView views source) : ENNReal)) =
        (coverageOccupancyMoment views : ENNReal) +
          ∑' index, Pr[= index | ($ᵗ Index : ProbComp Index)] * (occupancyIncrementAtIndex views index : ENNReal) := by
  have hmarginal : ∀ index, Pr[= index | (Prod.fst <$> ($ᵗ FewTimeView : ProbComp FewTimeView))] =
      Pr[= index | ($ᵗ Index : ProbComp Index)] := by
    intro index
    exact congrArg (fun distribution => distribution index)
      (evalDist_map_fst_uniformSample_prod (α := Index) (β := FtsTree → FtsLeaf))
  have hmass : (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)]) = 1 := by
    exact tsum_probOutput_eq_one' (by simp)
  simp_rw [coverageOccupancyMoment_insert_eq, Nat.cast_add, mul_add]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul]
  congr 1
  rw [← tsum_probOutput_map_mul (mx := ($ᵗ FewTimeView : ProbComp FewTimeView))
    (f := fun source : FewTimeView => source.1) (g := fun index : Index => (occupancyIncrementAtIndex views index : ENNReal))]
  simp_rw [hmarginal]

theorem expected_successfulSignerView_weight_le (weight : FewTimeView → ENNReal)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    (∑' source, Pr[SuccessfulSignerViewSatisfies (· = source) |
      (simulateQ romImpl (signWithView key message)).run cache] * weight source) ≤
        (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] * weight source) +
          (∑' source, cachedMessageEntryCountWhere cache key.parameter key.root message (· = source) * weight source) * digestReuseWeight q := by
  calc
    _ ≤ ∑' source, (Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] +
        cachedMessageEntryCountWhere cache key.parameter key.root message (· = source) * digestReuseWeight q) * weight source := by
      apply ENNReal.tsum_le_tsum
      intro source
      apply mul_le_mul' _ le_rfl
      simpa only [probEvent_eq_eq_probOutput] using
        probEvent_successfulSignerViewSatisfies_le_uniform_add_reuse key message cache (· = source) q hq hcache
    _ = _ := by
      simp only [add_mul, ENNReal.tsum_add, ENNReal.tsum_mul_right, mul_right_comm]

theorem expected_successfulSigner_occupancyIncrement_le {n : Nat} (views : Fin n → Option FewTimeView)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    (∑' source, Pr[SuccessfulSignerViewSatisfies (· = source) |
      (simulateQ romImpl (signWithView key message)).run cache] * (occupancyIncrementAtIndex views source.1 : ENNReal)) ≤
        (∑' index, Pr[= index | ($ᵗ Index : ProbComp Index)] * (occupancyIncrementAtIndex views index : ENNReal)) +
          (∑' source, cachedMessageEntryCountWhere cache key.parameter key.root message (· = source) *
            (occupancyIncrementAtIndex views source.1 : ENNReal)) * digestReuseWeight q := by
  have hmarginal : ∀ index, Pr[= index | (Prod.fst <$> ($ᵗ FewTimeView : ProbComp FewTimeView))] =
      Pr[= index | ($ᵗ Index : ProbComp Index)] := by
    intro index
    exact congrArg (fun distribution => distribution index)
      (evalDist_map_fst_uniformSample_prod (α := Index) (β := FtsTree → FtsLeaf))
  have hbound := expected_successfulSignerView_weight_le
    (fun source => (occupancyIncrementAtIndex views source.1 : ENNReal)) key message cache q hq hcache
  rw [← tsum_probOutput_map_mul (mx := ($ᵗ FewTimeView : ProbComp FewTimeView))
    (f := fun source : FewTimeView => source.1) (g := fun index : Index => (occupancyIncrementAtIndex views index : ENNReal))] at hbound
  simpa only [hmarginal] using hbound

end SphincsSecurity.Concrete
