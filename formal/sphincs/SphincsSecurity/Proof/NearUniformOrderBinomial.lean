import SphincsSecurity.Proof.NearUniformSigningOrder
import SphincsSecurity.Proof.OrderBinomialExpansion

namespace SphincsSecurity.Concrete

open ENNReal

theorem nearUniformSigningOrderMajorant_eq_div (weight : Nat → ENNReal) :
    nearUniformSigningOrderMajorant weight = fun o => (65536 : ENNReal)⁻¹ * orderNumeratorStep 24585 weight o := by
  have hgamma : (24585 / 65536 : ENNReal) = (65536 : ENNReal)⁻¹ * 24585 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_mul]
  funext order
  simp only [nearUniformSigningOrderMajorant, orderNumeratorStep, one_div, hgamma]
  ring

theorem nearUniformSigningOrderMajorant_iterate_eq_div (weight : Nat → ENNReal) (steps : Nat) :
    nearUniformSigningOrderMajorant^[steps] weight = fun o => (65536 : ENNReal)⁻¹ ^ steps * (orderNumeratorStep 24585)^[steps] weight o := by
  induction steps with
  | zero => funext o; simp only [Function.iterate_zero, id_eq, pow_zero, one_mul]
  | succ steps ih =>
      rw [Function.iterate_succ_apply', ih, nearUniformSigningOrderMajorant_eq_div, orderNumeratorStep_mul]
      funext order
      simp only [Function.iterate_succ_apply', pow_succ']
      ring

theorem nearUniformSigningOrderMajorant_iterate_eq_binomial (weight : Nat → ENNReal) (steps order : Nat) :
    nearUniformSigningOrderMajorant^[steps] weight order =
      (∑ degree ∈ Finset.range (steps + 1), (steps.choose degree : ENNReal) * (24585 : ENNReal) ^ degree * weight (order + degree)) /
        (65536 : ENNReal) ^ steps := by
  rw [nearUniformSigningOrderMajorant_iterate_eq_div]
  dsimp only
  rw [orderNumeratorStep_iterate_eq_binomial]
  simp only [div_eq_mul_inv, ENNReal.inv_pow]
  exact mul_comm _ _

end SphincsSecurity.Concrete
