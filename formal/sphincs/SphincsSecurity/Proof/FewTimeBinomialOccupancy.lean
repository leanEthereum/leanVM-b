import SphincsSecurity.Proof.ObservedSignerOccupancy

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def binomialOccupancyMoment {n : Nat} (views : Fin n → Option FewTimeView) (degree : Nat) : Nat :=
  ∑ index : Index, (signingSlotsAtIndex views index).card.choose degree

theorem binomialOccupancyMoment_zero {n : Nat} (views : Fin n → Option FewTimeView) :
    binomialOccupancyMoment views 0 = Fintype.card Index := by
  simp only [binomialOccupancyMoment, Nat.choose_zero_right]
  exact (Finset.card_eq_sum_ones (Finset.univ : Finset Index)).symm

theorem binomialOccupancyMoment_empty (views : Fin 0 → Option FewTimeView) (degree : Nat) :
    binomialOccupancyMoment views (degree + 1) = 0 := by
  simp only [binomialOccupancyMoment, signingSlotsAtIndex, Finset.univ_eq_empty,
    Finset.filter_empty, Finset.card_empty, Nat.choose_zero_succ, Finset.sum_const_zero]

theorem binomialOccupancyMoment_insert {n : Nat} (views : Fin n → Option FewTimeView) (source : FewTimeView) (degree : Nat) :
    binomialOccupancyMoment (insertFewTimeView views source) (degree + 1) =
      binomialOccupancyMoment views (degree + 1) + (signingSlotsAtIndex views source.1).card.choose degree := by
  have hpoint (index : Index) :
      ((signingSlotsAtIndex views index).card + if source.1 = index then 1 else 0).choose (degree + 1) =
        (signingSlotsAtIndex views index).card.choose (degree + 1) +
          if source.1 = index then (signingSlotsAtIndex views source.1).card.choose degree else 0 := by
    by_cases heq : source.1 = index
    · subst index
      simp only [if_true, Nat.choose_succ_succ]
      exact add_comm _ _
    · simp only [heq, if_false, add_zero]
  simp_rw [binomialOccupancyMoment, signingSlotsAtIndex_insert_card, hpoint]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem uniform_index_choose_expectation {n : Nat} (views : Fin n → Option FewTimeView) (degree : Nat) :
    (∑' index, Pr[= index | ($ᵗ Index : ProbComp Index)] * ((signingSlotsAtIndex views index).card.choose degree : ENNReal)) =
      (binomialOccupancyMoment views degree : ENNReal) / (Fintype.card Index : ENNReal) := by
  simp only [probOutput_uniformSample, tsum_fintype, binomialOccupancyMoment, Nat.cast_sum, div_eq_mul_inv]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro index _
  exact mul_comm _ _

theorem uniform_view_choose_expectation {n : Nat} (views : Fin n → Option FewTimeView) (degree : Nat) :
    (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
      ((signingSlotsAtIndex views source.1).card.choose degree : ENNReal)) =
        (binomialOccupancyMoment views degree : ENNReal) / (Fintype.card Index : ENNReal) := by
  have hmarginal : ∀ index, Pr[= index | (Prod.fst <$> ($ᵗ FewTimeView : ProbComp FewTimeView))] =
      Pr[= index | ($ᵗ Index : ProbComp Index)] := by
    intro index
    exact congrArg (fun distribution => distribution index)
      (evalDist_map_fst_uniformSample_prod (α := Index) (β := FtsTree → FtsLeaf))
  rw [← tsum_probOutput_map_mul (mx := ($ᵗ FewTimeView : ProbComp FewTimeView))
    (f := fun source : FewTimeView => source.1) (g := fun index : Index => ((signingSlotsAtIndex views index).card.choose degree : ENNReal))]
  simp_rw [hmarginal]
  exact uniform_index_choose_expectation views degree

theorem expected_binomialOccupancyMoment_insert {n : Nat} (views : Fin n → Option FewTimeView) (degree : Nat) :
    (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
      (binomialOccupancyMoment (insertFewTimeView views source) (degree + 1) : ENNReal)) =
        (binomialOccupancyMoment views (degree + 1) : ENNReal) +
          (binomialOccupancyMoment views degree : ENNReal) / (Fintype.card Index : ENNReal) := by
  simp_rw [binomialOccupancyMoment_insert, Nat.cast_add, mul_add]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp), one_mul,
    uniform_view_choose_expectation]

theorem expected_successfulSigner_choose_le {n : Nat} (views : Fin n → Option FewTimeView) (degree : Nat)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    (∑' source, Pr[SuccessfulSignerViewSatisfies (· = source) |
      (simulateQ romImpl (signWithView key message)).run cache] * ((signingSlotsAtIndex views source.1).card.choose degree : ENNReal)) ≤
        (binomialOccupancyMoment views degree : ENNReal) / (Fintype.card Index : ENNReal) +
          (∑' source, cachedMessageEntryCountWhere cache key.parameter key.root message (· = source) *
            ((signingSlotsAtIndex views source.1).card.choose degree : ENNReal)) * digestReuseWeight q := by
  have hbound := expected_successfulSignerView_weight_le
    (fun source => ((signingSlotsAtIndex views source.1).card.choose degree : ENNReal)) key message cache q hq hcache
  rwa [uniform_view_choose_expectation] at hbound

end SphincsSecurity.Concrete
