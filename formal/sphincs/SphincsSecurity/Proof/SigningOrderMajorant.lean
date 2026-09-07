import SphincsSecurity.Proof.QueryInitial127

namespace SphincsSecurity.Concrete

open ENNReal
set_option backward.isDefEq.respectTransparency false

noncomputable def signingOrderMajorant (weight : Nat → ENNReal) (order : Nat) : ENNReal :=
  (1 / 65536 : ENNReal) * weight order + (2081 / 4096 : ENNReal) * weight (order + 1)

def MixedOrderDominated (moments : MixedMomentVector) (weight : Nat → ENNReal) : Prop :=
  (∀ power order, 15 ≤ order → moments power order = 0) ∧
    ∀ power order, power ≤ order → order < 15 → moments power order ≤ ((2 : ENNReal) ^ 91) ^ power * weight order

theorem MixedOrderDominated.bound {moments : MixedMomentVector} {weight : Nat → ENNReal}
    (h : MixedOrderDominated moments weight) (power order : Nat) (hpower : power ≤ order) :
    moments power order ≤ ((2 : ENNReal) ^ 91) ^ power * weight order := by
  by_cases horder : order < 15
  · exact h.2 power order hpower horder
  · rw [h.1 power order (by omega)]
    exact bot_le

theorem mixedPowerLower_le_scaled (moments : MixedMomentVector) (weight : Nat → ENNReal)
    (h : MixedOrderDominated moments weight) (power order : Nat) (hpower : power ≤ 14) (horder : power ≤ order) :
    mixedPowerLower moments power order ≤ (2 : ENNReal) ^ 18 * ((2 : ENNReal) ^ 91) ^ (power - 1) * weight order := by
  have hterm (lower : Nat) (hlower : lower ∈ Finset.range power) :
      (power.choose lower : ENNReal) * moments lower order ≤
        (2 : ENNReal) ^ 14 * ((2 : ENNReal) ^ 91) ^ (power - 1) * weight order := by
    have hlt := Finset.mem_range.mp hlower
    have hchoose : (power.choose lower : ENNReal) ≤ (2 : ENNReal) ^ 14 := by
      have hn : power.choose lower ≤ 2 ^ 14 := (Nat.choose_le_two_pow power lower).trans (Nat.pow_le_pow_right (by omega) hpower)
      exact_mod_cast hn
    apply (mul_le_mul' hchoose (h.bound lower order (by omega))).trans
    rw [← mul_assoc]
    exact mul_le_mul' (mul_le_mul' le_rfl (pow_le_pow_right₀ (by norm_num) (by omega))) le_rfl
  apply (Finset.sum_le_sum hterm).trans
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc
    _ ≤ (14 : ENNReal) * ((2 : ENNReal) ^ 14 * ((2 : ENNReal) ^ 91) ^ (power - 1) * weight order) :=
      mul_le_mul_left (Nat.cast_le.mpr hpower) _
    _ ≤ _ := by
      rw [← mul_assoc, ← mul_assoc]
      exact mul_le_mul' (mul_le_mul' (by norm_num) le_rfl) le_rfl

theorem mixedPowerLower_quarter_le (moments : MixedMomentVector) (weight : Nat → ENNReal)
    (h : MixedOrderDominated moments weight) (power order : Nat) (hpower : power ≤ 14) (horder : power ≤ order) :
    (1 / 4 : ENNReal) * mixedPowerLower moments power order ≤
      ((2 : ENNReal) ^ 91) ^ power * ((1 / 65536 : ENNReal) * weight order) := by
  by_cases hzero : power = 0
  · subst power
    simp only [mixedPowerLower, Finset.range_zero, Finset.sum_empty, mul_zero]
    exact bot_le
  · have hcoeff : (1 / 4 : ENNReal) * (2 : ENNReal) ^ 18 ≤ (2 : ENNReal) ^ 91 * (1 / 65536 : ENNReal) := by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
    calc
      _ ≤ (1 / 4 : ENNReal) * ((2 : ENNReal) ^ 18 * ((2 : ENNReal) ^ 91) ^ (power - 1) * weight order) :=
        mul_le_mul_right (mixedPowerLower_le_scaled moments weight h power order hpower horder) _
      _ = ((1 / 4 : ENNReal) * (2 : ENNReal) ^ 18) * ((2 : ENNReal) ^ 91) ^ (power - 1) * weight order := by ring
      _ ≤ ((2 : ENNReal) ^ 91 * (1 / 65536 : ENNReal)) * ((2 : ENNReal) ^ 91) ^ (power - 1) * weight order :=
        mul_le_mul' (mul_le_mul' hcoeff le_rfl) le_rfl
      _ = _ := by
        have hp : ((2 : ENNReal) ^ 91) ^ power = (2 : ENNReal) ^ 91 * ((2 : ENNReal) ^ 91) ^ (power - 1) := by
          rw [← pow_succ', show power - 1 + 1 = power by omega]
        rw [hp]
        ring

theorem mixedSigningIncrement_dominated (q : Nat) (hq : q ≤ 2 ^ 127) (moments : MixedMomentVector) (weight : Nat → ENNReal)
    (h : MixedOrderDominated moments weight) :
    MixedOrderDominated (mixedSigningIncrement (1 / 4) ((signatureLimit : ENNReal) * digestReuseWeight q) moments)
      (signingOrderMajorant weight) := by
  refine ⟨fun p o ho => mixedSigningIncrement_order_zero _ _ moments h.1 p o ho, ?_⟩
  intro power order hpo ho
  have hp : power ≤ 14 := by omega
  have hre : (signatureLimit : ENNReal) * digestReuseWeight q * (2 : ENNReal) ^ 91 ≤ (33 : ENNReal) / 128 := by
    apply (mul_le_mul' (mul_le_mul' le_rfl (digestReuseWeight_le_coarse127 q hq)) le_rfl).trans
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_div, signatureLimit]
  have hreuse : (signatureLimit : ENNReal) * digestReuseWeight q * moments (power + 1) (order + 1) ≤
      ((2 : ENNReal) ^ 91) ^ power * ((33 / 128 : ENNReal) * weight (order + 1)) := by
    apply (mul_le_mul_right (h.bound (power + 1) (order + 1) (by omega)) _).trans
    rw [pow_succ']
    calc
      _ = ((signatureLimit : ENNReal) * digestReuseWeight q * (2 : ENNReal) ^ 91) *
          (((2 : ENNReal) ^ 91) ^ power * weight (order + 1)) := by ring
      _ ≤ (33 / 128 : ENNReal) * (((2 : ENNReal) ^ 91) ^ power * weight (order + 1)) := mul_le_mul_left hre _
      _ = _ := by ring
  have hmain : (1 / 4 : ENNReal) * moments power (order + 1) ≤
      ((2 : ENNReal) ^ 91) ^ power * ((1 / 4 : ENNReal) * weight (order + 1)) := by
    apply (mul_le_mul_right (h.bound power (order + 1) (by omega)) _).trans_eq
    ring
  have hcoeff : (1 / 4 : ENNReal) + 1 / 65536 + 33 / 128 ≤ 2081 / 4096 := by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num [ENNReal.toReal_div]
  simp only [mixedSigningIncrement, mul_add]
  apply (add_le_add (add_le_add (add_le_add
    (mixedPowerLower_quarter_le moments weight h power order hp hpo) hmain)
    (mixedPowerLower_quarter_le moments weight h power (order + 1) hp (by omega))) hreuse).trans
  calc
    _ = ((2 : ENNReal) ^ 91) ^ power * ((1 / 65536 : ENNReal) * weight order +
        ((1 / 4 : ENNReal) + 1 / 65536 + 33 / 128) * weight (order + 1)) := by ring
    _ ≤ _ := mul_le_mul_right (add_le_add le_rfl (mul_le_mul_left hcoeff _)) _

theorem mixedSigningIncrement_iterate_dominated (q : Nat) (hq : q ≤ 2 ^ 127) (moments : MixedMomentVector)
    (weight : Nat → ENNReal) (h : MixedOrderDominated moments weight) (steps : Nat) :
    MixedOrderDominated ((mixedSigningIncrement (1 / 4) ((signatureLimit : ENNReal) * digestReuseWeight q))^[steps] moments)
      (signingOrderMajorant^[steps] weight) := by
  induction steps with
  | zero => exact h
  | succ steps ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact mixedSigningIncrement_dominated q hq _ _ ih

theorem queryInitial_mixedOrderDominated (q : Nat) (hq : q ≤ 2 ^ 127) :
    MixedOrderDominated
      ((mixedQueryEnvelope (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ / (Fintype.card Index : ENNReal)))^[q] initialMixedDerivativeVector)
      (fun order => (1025 / 1024 : ENNReal) * initialMixedDerivativeVector 0 order) := by
  refine ⟨fun p o ho => mixedQueryEnvelope_order_zero _ _ initialMixedDerivativeVector_order_zero q p o ho, ?_⟩
  intro power order hp ho
  apply (queryInitialEnvelope_le_scaled q hq power order (by omega)).trans_eq
  ring

end SphincsSecurity.Concrete
