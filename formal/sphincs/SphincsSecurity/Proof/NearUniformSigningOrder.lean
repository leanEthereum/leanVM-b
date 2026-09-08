import SphincsSecurity.Proof.SigningOrderMajorant
import SphincsSecurity.Proof.NearUniformRawStep

namespace SphincsSecurity.Concrete

open ENNReal

noncomputable def nearUniformSigningOrderMajorant (weight : Nat → ENNReal) (order : Nat) : ENNReal :=
  (1 / 65536 : ENNReal) * weight order + (24585 / 65536 : ENNReal) * weight (order + 1)

theorem nearUniformMixedSigningIncrement_dominated (moments : MixedMomentVector) (weight : Nat → ENNReal)
    (h : MixedOrderDominated moments weight) :
    MixedOrderDominated (mixedSigningIncrement (1 / 4) ((signatureLimit : ENNReal) * nearUniformDigestReuseWeight) moments)
      (nearUniformSigningOrderMajorant weight) := by
  refine ⟨fun p o ho => mixedSigningIncrement_order_zero _ _ moments h.1 p o ho, ?_⟩
  intro power order hpo ho
  have hp : power ≤ 14 := by omega
  have hre : (signatureLimit : ENNReal) * nearUniformDigestReuseWeight * (2 : ENNReal) ^ 91 ≤ (1025 : ENNReal) / 8192 := by
    have hfinite := nearUniformDigestReuseWeight_ne_top
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num [nearUniformDigestReuseWeight, ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv, signatureLimit]
  have hreuse : (signatureLimit : ENNReal) * nearUniformDigestReuseWeight * moments (power + 1) (order + 1) ≤
      ((2 : ENNReal) ^ 91) ^ power * ((1025 / 8192 : ENNReal) * weight (order + 1)) := by
    apply (mul_le_mul_right (h.bound (power + 1) (order + 1) (by omega)) _).trans
    rw [pow_succ']
    calc
      _ = ((signatureLimit : ENNReal) * nearUniformDigestReuseWeight * (2 : ENNReal) ^ 91) *
          (((2 : ENNReal) ^ 91) ^ power * weight (order + 1)) := by ring
      _ ≤ (1025 / 8192 : ENNReal) * (((2 : ENNReal) ^ 91) ^ power * weight (order + 1)) := mul_le_mul_left hre _
      _ = _ := by ring
  have hmain : (1 / 4 : ENNReal) * moments power (order + 1) ≤
      ((2 : ENNReal) ^ 91) ^ power * ((1 / 4 : ENNReal) * weight (order + 1)) := by
    apply (mul_le_mul_right (h.bound power (order + 1) (by omega)) _).trans_eq
    ring
  have hcoeff : (1 / 4 : ENNReal) + 1 / 65536 + 1025 / 8192 ≤ 24585 / 65536 := by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num [ENNReal.toReal_div]
  simp only [mixedSigningIncrement, mul_add]
  apply (add_le_add (add_le_add (add_le_add
    (mixedPowerLower_quarter_le moments weight h power order hp hpo) hmain)
    (mixedPowerLower_quarter_le moments weight h power (order + 1) hp (by omega))) hreuse).trans
  calc
    _ = ((2 : ENNReal) ^ 91) ^ power * ((1 / 65536 : ENNReal) * weight order +
        ((1 / 4 : ENNReal) + 1 / 65536 + 1025 / 8192) * weight (order + 1)) := by ring
    _ ≤ _ := mul_le_mul_right (add_le_add le_rfl (mul_le_mul_left hcoeff _)) _

theorem nearUniformMixedSigningIncrement_iterate_dominated (moments : MixedMomentVector)
    (weight : Nat → ENNReal) (h : MixedOrderDominated moments weight) (steps : Nat) :
    MixedOrderDominated ((mixedSigningIncrement (1 / 4) ((signatureLimit : ENNReal) * nearUniformDigestReuseWeight))^[steps] moments)
      (nearUniformSigningOrderMajorant^[steps] weight) := by
  induction steps with
  | zero => exact h
  | succ steps ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact nearUniformMixedSigningIncrement_dominated _ _ ih

end SphincsSecurity.Concrete
