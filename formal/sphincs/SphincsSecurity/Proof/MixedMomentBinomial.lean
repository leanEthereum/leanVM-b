import SphincsSecurity.Proof.MixedMomentIncrements
namespace SphincsSecurity.Concrete
open ENNReal
set_option backward.isDefEq.respectTransparency false
private theorem mixedEnd_sum_apply {α : Type} [DecidableEq α] (indices : Finset α) (operations : α → AddMonoid.End MixedMomentVector) (moments : MixedMomentVector) :
    (∑ index ∈ indices, operations index) moments = ∑ index ∈ indices, operations index moments := by
  induction indices using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; rfl
  | @insert index indices hnot ih =>
      simp only [Finset.sum_insert hnot]
      change operations index moments + (∑ i ∈ indices, operations i) moments = _
      rw [ih]
theorem mixedAdditiveIterate_binomial (increment : AddMonoid.End MixedMomentVector) (steps : Nat) (moments : MixedMomentVector) (power order : Nat) :
    (fun v => v + increment v)^[steps] moments power order =
      ∑ degree ∈ Finset.range (steps + 1), (steps.choose degree : ENNReal) * increment^[degree] moments power order := by
  have hfun : (fun v => v + increment v) = ⇑(increment + 1) := by
    funext v
    change v + increment v = increment v + v
    exact add_comm _ _
  have hvector : (fun v => v + increment v)^[steps] moments =
      ∑ degree ∈ Finset.range (steps + 1), steps.choose degree • increment^[degree] moments := by
    rw [hfun, ← AddMonoid.End.coe_pow, (Commute.one_right increment).add_pow]
    simp only [one_pow, mul_one]
    rw [mixedEnd_sum_apply]
    apply Finset.sum_congr rfl
    intro degree _
    change (increment ^ degree) ((steps.choose degree : AddMonoid.End MixedMomentVector) moments) = _
    rw [AddMonoid.End.natCast_apply, map_nsmul]
    rfl
  simpa only [Finset.sum_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply] using congrArg (fun v => v power order) hvector

theorem mixedBinomial_sum_truncate (values : Nat → ENNReal) (steps cutoff : Nat)
    (hzero : ∀ degree, cutoff < degree → values degree = 0) :
    (∑ degree ∈ Finset.range (steps + 1), (steps.choose degree : ENNReal) * values degree) =
      ∑ degree ∈ Finset.range (cutoff + 1), (steps.choose degree : ENNReal) * values degree := by
  by_cases hle : cutoff ≤ steps
  · symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro degree _ hout
    rw [hzero degree (by simp only [Finset.mem_range] at hout; omega), mul_zero]
  · apply Finset.sum_subset (Finset.range_mono (by omega))
    intro degree _ hout
    rw [Nat.choose_eq_zero_of_lt (by simp only [Finset.mem_range] at hout; omega), Nat.cast_zero, zero_mul]

theorem mixedQueryEnvelope_iterate_eq_binomial (arrival : ENNReal) (steps : Nat) (moments : MixedMomentVector) (power order : Nat) :
    (mixedQueryEnvelope arrival)^[steps] moments power order =
      ∑ degree ∈ Finset.range (power + 1), (steps.choose degree : ENNReal) * (mixedQueryIncrement arrival)^[degree] moments power order := by
  have hfun : mixedQueryEnvelope arrival = fun v => v + mixedQueryIncrementHom arrival v := rfl
  rw [hfun, mixedAdditiveIterate_binomial]
  apply mixedBinomial_sum_truncate
  intro degree hdegree
  exact mixedQueryIncrement_iterate_zero arrival moments degree power order hdegree

theorem mixedSigningEnvelope_iterate_eq_binomial (uniform reuse : ENNReal) (steps : Nat) (moments : MixedMomentVector)
    (hzero : ∀ power order, 15 ≤ order → moments power order = 0) (power order : Nat) (horder : order < 15) :
    (mixedSigningEnvelope uniform reuse)^[steps] moments power order =
      ∑ degree ∈ Finset.range (power + 2 * (14 - order) + 1),
        (steps.choose degree : ENNReal) * (mixedSigningIncrement uniform reuse)^[degree] moments power order := by
  have hfun : mixedSigningEnvelope uniform reuse = fun v => v + mixedSigningIncrementHom uniform reuse v := by
    funext v
    exact mixedSigningEnvelope_eq_add_increment uniform reuse v
  rw [hfun, mixedAdditiveIterate_binomial]
  apply mixedBinomial_sum_truncate
  intro degree hdegree
  exact mixedSigningIncrement_iterate_zero uniform reuse moments hzero degree power order (by omega)

noncomputable def finiteMixedQueryEnvelope (arrival : ENNReal) (queries : Nat) (moments : MixedMomentVector) : MixedMomentVector :=
  fun power order => ∑ degree ∈ Finset.range (power + 1),
    (queries.choose degree : ENNReal) * (mixedQueryIncrement arrival)^[degree] moments power order

theorem mixedQueryEnvelope_iterate_eq_finite (arrival : ENNReal) (queries : Nat) (moments : MixedMomentVector) :
    (mixedQueryEnvelope arrival)^[queries] moments = finiteMixedQueryEnvelope arrival queries moments := by
  funext power order
  exact mixedQueryEnvelope_iterate_eq_binomial arrival queries moments power order

theorem mixedRemainingEnvelope_zero_zero_eq_finite (uniform reuse arrival : ENNReal) (queries signatures : Nat)
    (moments : MixedMomentVector) (hzero : ∀ power order, 15 ≤ order → moments power order = 0) :
    mixedRemainingEnvelope uniform reuse arrival queries signatures moments 0 0 =
      ∑ degree ∈ Finset.range 29, (signatures.choose degree : ENNReal) *
        (mixedSigningIncrement uniform reuse)^[degree] (finiteMixedQueryEnvelope arrival queries moments) 0 0 := by
  unfold mixedRemainingEnvelope
  rw [mixedSigningEnvelope_iterate_eq_binomial uniform reuse signatures _
    (fun p o ho => mixedQueryEnvelope_order_zero arrival moments hzero queries p o ho) 0 0 (by omega),
    mixedQueryEnvelope_iterate_eq_finite]

end SphincsSecurity.Concrete
