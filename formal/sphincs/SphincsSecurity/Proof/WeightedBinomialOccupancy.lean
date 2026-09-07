import SphincsSecurity.Proof.AllMessageBinomialReuse

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def weightedBinomialOccupancyMoment {n : Nat} (weights : Index → ENNReal)
    (views : Fin n → Option FewTimeView) (degree : Nat) : ENNReal :=
  ∑ index : Index, weights index * ((signingSlotsAtIndex views index).card.choose degree : ENNReal)

theorem weightedBinomialOccupancyMoment_zero {n : Nat} (weights : Index → ENNReal) (views : Fin n → Option FewTimeView) :
    weightedBinomialOccupancyMoment weights views 0 = ∑ index : Index, weights index := by
  simp only [weightedBinomialOccupancyMoment, Nat.choose_zero_right, Nat.cast_one, mul_one]

theorem weightedBinomialOccupancyMoment_one {n : Nat} (views : Fin n → Option FewTimeView) (degree : Nat) :
    weightedBinomialOccupancyMoment (fun _ => 1) views degree = (binomialOccupancyMoment views degree : ENNReal) := by
  simp only [weightedBinomialOccupancyMoment, one_mul, binomialOccupancyMoment, Nat.cast_sum]

theorem weightedBinomialOccupancyMoment_insert {n : Nat} (weights : Index → ENNReal)
    (views : Fin n → Option FewTimeView) (source : FewTimeView) (degree : Nat) :
    weightedBinomialOccupancyMoment weights (insertFewTimeView views source) (degree + 1) =
      weightedBinomialOccupancyMoment weights views (degree + 1) +
        weights source.1 * ((signingSlotsAtIndex views source.1).card.choose degree : ENNReal) := by
  have hpoint (index : Index) :
      ((signingSlotsAtIndex views index).card + if source.1 = index then 1 else 0).choose (degree + 1) =
        (signingSlotsAtIndex views index).card.choose (degree + 1) +
          if source.1 = index then (signingSlotsAtIndex views source.1).card.choose degree else 0 := by
    by_cases heq : source.1 = index
    · subst index
      simp only [if_true, Nat.choose_succ_succ]
      exact add_comm _ _
    · simp only [heq, if_false, add_zero]
  simp_rw [weightedBinomialOccupancyMoment, signingSlotsAtIndex_insert_card, hpoint, Nat.cast_add, mul_add]
  rw [Finset.sum_add_distrib]
  simp only [Nat.cast_ite, Nat.cast_zero, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem uniform_view_index_weight_expectation (weight : Index → ENNReal) :
    (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] * weight source.1) =
      (∑ index : Index, weight index) / (Fintype.card Index : ENNReal) := by
  have hmarginal : ∀ index, Pr[= index | (Prod.fst <$> ($ᵗ FewTimeView : ProbComp FewTimeView))] =
      Pr[= index | ($ᵗ Index : ProbComp Index)] := by
    intro index
    exact congrArg (fun distribution => distribution index)
      (evalDist_map_fst_uniformSample_prod (α := Index) (β := FtsTree → FtsLeaf))
  rw [← tsum_probOutput_map_mul (mx := ($ᵗ FewTimeView : ProbComp FewTimeView))
    (f := fun source : FewTimeView => source.1) (g := weight)]
  simp only [hmarginal, probOutput_uniformSample, tsum_fintype, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro index _
  exact mul_comm _ _

theorem observed_weightedBinomial_append_none (weights : Index → ENNReal) (answers : HashInput → Option HashOutput)
    (root : Digest) (log : QueryLog SigningSpec) (entry : SigningEntry) (degree : Nat)
    (hnone : observedSigningView? answers root entry = none) :
    weightedBinomialOccupancyMoment weights (observedOptionalSigningViews answers root (log ++ [entry])) degree =
      weightedBinomialOccupancyMoment weights (observedOptionalSigningViews answers root log) degree := by
  unfold weightedBinomialOccupancyMoment observedOptionalSigningViews
  simp only [signingSlotsAtIndex_log_append_card, hnone, reduceCtorEq, false_and, exists_false, if_false, add_zero]

theorem observed_weightedBinomial_append_some (weights : Index → ENNReal) (answers : HashInput → Option HashOutput)
    (root : Digest) (log : QueryLog SigningSpec) (entry : SigningEntry) (source : FewTimeView) (degree : Nat)
    (hsome : observedSigningView? answers root entry = some source) :
    weightedBinomialOccupancyMoment weights (observedOptionalSigningViews answers root (log ++ [entry])) (degree + 1) =
      weightedBinomialOccupancyMoment weights (observedOptionalSigningViews answers root log) (degree + 1) +
        weights source.1 * ((signingSlotsAtIndex (observedOptionalSigningViews answers root log) source.1).card.choose degree : ENNReal) := by
  rw [← weightedBinomialOccupancyMoment_insert]
  unfold weightedBinomialOccupancyMoment observedOptionalSigningViews
  simp only [signingSlotsAtIndex_log_append_card, signingSlotsAtIndex_insert_card, hsome, Option.some.injEq, exists_eq_left']

end SphincsSecurity.Concrete
