import SphincsSecurity.Proof.MixedMomentEnvelope
import Mathlib.Algebra.Group.Hom.End

namespace SphincsSecurity.Concrete

open ENNReal
set_option backward.isDefEq.respectTransparency false

noncomputable def mixedQueryIncrement (arrival : ENNReal) (moments : MixedMomentVector) (power order : Nat) : ENNReal :=
  arrival * mixedPowerLower moments power order

noncomputable def mixedSigningIncrement (uniform reuse : ENNReal) (moments : MixedMomentVector) (power order : Nat) : ENNReal :=
  uniform * (mixedPowerLower moments power order + moments power (order + 1) + mixedPowerLower moments power (order + 1)) +
    reuse * moments (power + 1) (order + 1)

theorem mixedPowerLower_eq_zero (moments : MixedMomentVector) (power order : Nat)
    (hzero : ∀ lower < power, moments lower order = 0) : mixedPowerLower moments power order = 0 := by
  apply Finset.sum_eq_zero
  intro lower hlower
  rw [hzero lower (Finset.mem_range.mp hlower), mul_zero]

noncomputable def mixedQueryIncrementHom (arrival : ENNReal) : AddMonoid.End MixedMomentVector where
  toFun := mixedQueryIncrement arrival
  map_zero' := by
    funext power order
    simp only [mixedQueryIncrement, mixedPowerLower, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  map_add' left right := by
    funext power order
    change arrival * mixedPowerLower (fun p o => left p o + right p o) power order = _
    rw [mixedPowerLower_add, mul_add]
    rfl

noncomputable def mixedSigningIncrementHom (uniform reuse : ENNReal) : AddMonoid.End MixedMomentVector where
  toFun := mixedSigningIncrement uniform reuse
  map_zero' := by
    funext power order
    simp only [mixedSigningIncrement, mixedPowerLower, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  map_add' left right := by
    funext power order
    change mixedSigningIncrement uniform reuse (fun p o => left p o + right p o) power order = _
    simp only [mixedSigningIncrement, mixedPowerLower_add, Pi.add_apply]
    ring

theorem mixedQueryEnvelope_eq_add_increment (arrival : ENNReal) (moments : MixedMomentVector) :
    mixedQueryEnvelope arrival moments = moments + mixedQueryIncrement arrival moments := rfl

theorem mixedSigningEnvelope_eq_add_increment (uniform reuse : ENNReal) (moments : MixedMomentVector) :
    mixedSigningEnvelope uniform reuse moments = moments + mixedSigningIncrement uniform reuse moments := by
  funext power order
  exact add_assoc _ _ _

theorem mixedQueryIncrement_iterate_zero (arrival : ENNReal) (moments : MixedMomentVector) (steps power order : Nat)
    (hsteps : power < steps) : (mixedQueryIncrement arrival)^[steps] moments power order = 0 := by
  induction steps generalizing power with
  | zero => omega
  | succ steps ih =>
      rw [Function.iterate_succ_apply']
      simp only [mixedQueryIncrement]
      rw [mixedPowerLower_eq_zero _ power order (fun lower hlower => ih lower (by omega)), mul_zero]

theorem mixedQueryEnvelope_order_zero (arrival : ENNReal) (moments : MixedMomentVector)
    (hzero : ∀ power order, 15 ≤ order → moments power order = 0) (steps power order : Nat) (horder : 15 ≤ order) :
    (mixedQueryEnvelope arrival)^[steps] moments power order = 0 := by
  induction steps generalizing power with
  | zero => exact hzero power order horder
  | succ steps ih =>
      rw [Function.iterate_succ_apply']
      simp only [mixedQueryEnvelope]
      rw [ih power, mixedPowerLower_eq_zero _ power order (fun lower _ => ih lower), mul_zero, add_zero]

theorem mixedSigningIncrement_order_zero (uniform reuse : ENNReal) (moments : MixedMomentVector)
    (hzero : ∀ power order, 15 ≤ order → moments power order = 0) (power order : Nat) (horder : 15 ≤ order) :
    mixedSigningIncrement uniform reuse moments power order = 0 := by
  unfold mixedSigningIncrement
  rw [mixedPowerLower_eq_zero _ power order (fun lower _ => hzero lower order horder),
    hzero power (order + 1) (by omega), hzero (power + 1) (order + 1) (by omega),
    mixedPowerLower_eq_zero _ power (order + 1) (fun lower _ => hzero lower (order + 1) (by omega))]
  simp only [add_zero, mul_zero]

theorem mixedSigningIncrement_iterate_order_zero (uniform reuse : ENNReal) (moments : MixedMomentVector)
    (hzero : ∀ power order, 15 ≤ order → moments power order = 0) (steps power order : Nat) (horder : 15 ≤ order) :
    (mixedSigningIncrement uniform reuse)^[steps] moments power order = 0 := by
  induction steps generalizing power order with
  | zero => exact hzero power order horder
  | succ steps ih =>
      rw [Function.iterate_succ_apply']
      exact mixedSigningIncrement_order_zero uniform reuse _ (fun p o ho => ih p o ho) power order horder

theorem mixedSigningIncrement_iterate_zero (uniform reuse : ENNReal) (moments : MixedMomentVector)
    (hzero : ∀ power order, 15 ≤ order → moments power order = 0) (steps power order : Nat)
    (hsteps : power + 2 * (15 - order) < steps + 2) :
    (mixedSigningIncrement uniform reuse)^[steps] moments power order = 0 := by
  induction steps generalizing power order with
  | zero =>
      have horder : 15 ≤ order := by omega
      exact hzero power order horder
  | succ steps ih =>
      by_cases horder : 15 ≤ order
      · exact mixedSigningIncrement_iterate_order_zero uniform reuse moments hzero (steps + 1) power order horder
      · rw [Function.iterate_succ_apply']
        simp only [mixedSigningIncrement]
        rw [mixedPowerLower_eq_zero _ power order (fun lower hlower => ih lower order (by omega)),
          ih power (order + 1) (by omega), ih (power + 1) (order + 1) (by omega),
          mixedPowerLower_eq_zero _ power (order + 1) (fun lower hlower => ih lower (order + 1) (by omega))]
        simp only [add_zero, mul_zero]

end SphincsSecurity.Concrete
