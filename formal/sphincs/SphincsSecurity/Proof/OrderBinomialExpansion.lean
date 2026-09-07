import SphincsSecurity.Proof.SigningOrderMajorant

namespace SphincsSecurity.Concrete

open ENNReal
set_option backward.isDefEq.respectTransparency false

noncomputable def orderRaiseHom (factor : ENNReal) : AddMonoid.End MixedMomentVector where
  toFun := fun moments power order => factor * moments power (order + 1)
  map_zero' := by funext p o; exact mul_zero _
  map_add' _ _ := by funext p o; exact mul_add _ _ _

theorem orderRaiseHom_iterate (factor : ENNReal) (moments : MixedMomentVector) (steps power order : Nat) :
    (orderRaiseHom factor)^[steps] moments power order = factor ^ steps * moments power (order + steps) := by
  induction steps generalizing order with
  | zero => simp only [Function.iterate_zero, id_eq, pow_zero, one_mul, Nat.add_zero]
  | succ steps ih =>
      rw [Function.iterate_succ_apply']
      change factor * (orderRaiseHom factor)^[steps] moments power (order + 1) = _
      rw [ih, pow_succ']
      simp only [Nat.add_assoc, Nat.add_comm 1 steps, mul_assoc]

noncomputable def orderNumeratorStep (factor : ENNReal) (weight : Nat → ENNReal) (order : Nat) : ENNReal :=
  weight order + factor * weight (order + 1)

theorem orderNumeratorStep_iterate_eq_binomial (factor : ENNReal) (weight : Nat → ENNReal) (steps order : Nat) :
    (orderNumeratorStep factor)^[steps] weight order =
      ∑ degree ∈ Finset.range (steps + 1), (steps.choose degree : ENNReal) * factor ^ degree * weight (order + degree) := by
  have hlift (count : Nat) : (fun v => v + orderRaiseHom factor v)^[count] (fun _ o => weight o) =
      fun _ o => (orderNumeratorStep factor)^[count] weight o := by
    induction count with
    | zero => rfl
    | succ count ih =>
        rw [Function.iterate_succ_apply', ih]
        funext p o
        rw [Function.iterate_succ_apply']
        rfl
  have h := mixedAdditiveIterate_binomial (orderRaiseHom factor) steps (fun _ o => weight o) 0 order
  rw [hlift] at h
  simpa only [orderRaiseHom_iterate, mul_assoc] using h

theorem orderNumeratorStep_mul (factor scalar : ENNReal) (weight : Nat → ENNReal) :
    orderNumeratorStep factor (fun o => scalar * weight o) = fun o => scalar * orderNumeratorStep factor weight o := by
  funext o
  simp only [orderNumeratorStep]
  ring

theorem signingOrderMajorant_eq_div (weight : Nat → ENNReal) :
    signingOrderMajorant weight = fun o => (65536 : ENNReal)⁻¹ * orderNumeratorStep 33296 weight o := by
  have hgamma : (2081 / 4096 : ENNReal) = (65536 : ENNReal)⁻¹ * 33296 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_mul]
  funext order
  simp only [signingOrderMajorant, orderNumeratorStep, one_div, hgamma]
  ring

theorem signingOrderMajorant_iterate_eq_div (weight : Nat → ENNReal) (steps : Nat) :
    signingOrderMajorant^[steps] weight = fun o => (65536 : ENNReal)⁻¹ ^ steps * (orderNumeratorStep 33296)^[steps] weight o := by
  induction steps with
  | zero => funext o; simp only [Function.iterate_zero, id_eq, pow_zero, one_mul]
  | succ steps ih =>
      rw [Function.iterate_succ_apply', ih, signingOrderMajorant_eq_div, orderNumeratorStep_mul]
      funext order
      simp only [Function.iterate_succ_apply', pow_succ']
      ring

theorem signingOrderMajorant_iterate_eq_binomial (weight : Nat → ENNReal) (steps order : Nat) :
    signingOrderMajorant^[steps] weight order =
      (∑ degree ∈ Finset.range (steps + 1), (steps.choose degree : ENNReal) * (33296 : ENNReal) ^ degree * weight (order + degree)) /
        (65536 : ENNReal) ^ steps := by
  rw [signingOrderMajorant_iterate_eq_div]
  dsimp only
  rw [orderNumeratorStep_iterate_eq_binomial]
  simp only [div_eq_mul_inv, ENNReal.inv_pow]
  exact mul_comm _ _

end SphincsSecurity.Concrete
