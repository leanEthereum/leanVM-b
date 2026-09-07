import SphincsSecurity.Proof.TargetShapeNilpotence
import SphincsSecurity.Proof.MixedMomentBinomial

namespace SphincsSecurity.Concrete
open ENNReal
set_option backward.isDefEq.respectTransparency false

noncomputable def targetShapeQueryIncrementHom (arrival : ENNReal) : AddMonoid.End TargetShapeVector where
  toFun := targetShapeQueryIncrement arrival
  map_zero' := by
    funext groups remaining
    simp only [targetShapeQueryIncrement, targetCacheLower, Pi.zero_apply, Finset.sum_const_zero, mul_zero]
  map_add' f g := by
    funext groups remaining
    change arrival * targetCacheLower (fun G R => f G R + g G R) groups remaining = _
    rw [targetCacheLower_add, mul_add]
    rfl

noncomputable def targetShapeSigningIncrementHom (uniform reuse : ENNReal) : AddMonoid.End TargetShapeVector where
  toFun := targetShapeSigningIncrement uniform reuse
  map_zero' := by
    funext groups remaining
    simp only [targetShapeSigningIncrement, targetCacheLower, targetTreeLower, targetReuseStep,
      Pi.zero_apply, Finset.sum_const_zero, add_zero, mul_zero]
  map_add' f g := by
    funext groups remaining
    change targetShapeSigningIncrement uniform reuse (fun G R => f G R + g G R) groups remaining = _
    have htree : targetTreeLower (fun G R => f G R + g G R) = fun G R => targetTreeLower f G R + targetTreeLower g G R := by
      funext G R
      exact targetTreeLower_add f g G R
    simp only [targetShapeSigningIncrement, htree, targetCacheLower_add, targetTreeLower_add, targetReuseStep_add, Pi.add_apply]
    ring

private theorem targetEnd_sum_apply {α : Type} [DecidableEq α] (indices : Finset α) (operations : α → AddMonoid.End TargetShapeVector) (moments : TargetShapeVector) :
    (∑ index ∈ indices, operations index) moments = ∑ index ∈ indices, operations index moments := by
  induction indices using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; rfl
  | @insert index indices hnot ih =>
      simp only [Finset.sum_insert hnot]
      change operations index moments + (∑ i ∈ indices, operations i) moments = _
      rw [ih]
theorem targetAdditiveIterate_binomial (increment : AddMonoid.End TargetShapeVector) (steps : Nat) (moments : TargetShapeVector) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    (fun v => v + increment v)^[steps] moments groups remaining =
      ∑ degree ∈ Finset.range (steps + 1), (steps.choose degree : ENNReal) * increment^[degree] moments groups remaining := by
  have hfun : (fun v => v + increment v) = ⇑(increment + 1) := by
    funext v
    change v + increment v = increment v + v
    exact add_comm _ _
  have hvector : (fun v => v + increment v)^[steps] moments =
      ∑ degree ∈ Finset.range (steps + 1), steps.choose degree • increment^[degree] moments := by
    rw [hfun, ← AddMonoid.End.coe_pow, (Commute.one_right increment).add_pow]
    simp only [one_pow, mul_one]
    rw [targetEnd_sum_apply]
    apply Finset.sum_congr rfl
    intro degree _
    change (increment ^ degree) ((steps.choose degree : AddMonoid.End TargetShapeVector) moments) = _
    rw [AddMonoid.End.natCast_apply, map_nsmul]
    rfl
  simpa only [Finset.sum_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply] using congrArg (fun v => v groups remaining) hvector

theorem targetShapeQuery_iterate_eq_binomial (arrival : ENNReal) (steps : Nat) (f : TargetShapeVector)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (targetShapeQuery arrival)^[steps] f groups remaining =
      ∑ degree ∈ Finset.range 29, (steps.choose degree : ENNReal) * (targetShapeQueryIncrement arrival)^[degree] f groups remaining := by
  have hfun : targetShapeQuery arrival = fun v => v + targetShapeQueryIncrementHom arrival v := rfl
  rw [hfun, targetAdditiveIterate_binomial]
  apply mixedBinomial_sum_truncate
  intro degree hdegree
  exact targetShapeQueryIncrement_iterate_zero arrival degree f groups remaining hvalid (by omega)

theorem targetShapeSigning_iterate_eq_binomial (uniform reuse : ENNReal) (steps : Nat) (f : TargetShapeVector)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (targetShapeSigning uniform reuse)^[steps] f groups remaining =
      ∑ degree ∈ Finset.range 29, (steps.choose degree : ENNReal) * (targetShapeSigningIncrement uniform reuse)^[degree] f groups remaining := by
  have hfun : targetShapeSigning uniform reuse = fun v => v + targetShapeSigningIncrementHom uniform reuse v := by
    funext v G R
    exact add_assoc _ _ _
  rw [hfun, targetAdditiveIterate_binomial]
  apply mixedBinomial_sum_truncate
  intro degree hdegree
  exact targetShapeSigningIncrement_iterate_zero uniform reuse degree f groups remaining hvalid (by omega)

end SphincsSecurity.Concrete
