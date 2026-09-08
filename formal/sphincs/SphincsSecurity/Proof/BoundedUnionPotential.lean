import SphincsSecurity.Proof.StoppedLogPotentialDiscard

namespace SphincsSecurity

open _root_.OracleComp OracleSpec ENNReal

noncomputable def boundedUnionPotential (left right : ENNReal) : ENNReal :=
  min 1 right + (1 - min 1 right) * min 1 left

theorem boundedUnionPotential_le_one (left right : ENNReal) : boundedUnionPotential left right ≤ 1 := by
  apply (add_le_add le_rfl (mul_le_of_le_one_right' (min_le_left _ _))).trans_eq
  exact add_tsub_cancel_of_le (min_le_left _ _)

theorem boundedUnionPotential_add_product (left right : ENNReal) :
    boundedUnionPotential left right + min 1 right * min 1 left = min 1 right + min 1 left := by
  unfold boundedUnionPotential
  calc
    _ = min 1 right + ((1 - min 1 right) + min 1 right) * min 1 left := by ring
    _ = _ := by rw [tsub_add_cancel_of_le (min_le_left _ _), one_mul]

theorem boundedUnionPotential_comm (left right : ENNReal) :
    boundedUnionPotential left right = boundedUnionPotential right left := by
  have hf : min 1 right * min 1 left ≠ ⊤ := ENNReal.mul_ne_top
    (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_left _ _)) (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_left _ _))
  apply (ENNReal.add_left_inj hf).mp
  rw [boundedUnionPotential_add_product, mul_comm (min 1 right), boundedUnionPotential_add_product, add_comm]

theorem boundedUnionPotential_eq_one_of_left (left right : ENNReal) (h : 1 ≤ left) :
    boundedUnionPotential left right = 1 := by
  rw [boundedUnionPotential, min_eq_left h, mul_one, add_tsub_cancel_of_le (min_le_left _ _)]

theorem boundedUnionPotential_eq_one_of_right (left right : ENNReal) (h : 1 ≤ right) :
    boundedUnionPotential left right = 1 := by
  rw [boundedUnionPotential_comm]
  exact boundedUnionPotential_eq_one_of_left right left h

theorem boundedUnionPotential_le_add (left right : ENNReal) :
    boundedUnionPotential left right ≤ left + right := by
  unfold boundedUnionPotential
  apply (add_le_add (min_le_right _ _) ((mul_le_of_le_one_left' tsub_le_self).trans (min_le_right _ _))).trans_eq
  exact add_comm _ _

theorem boundedUnionPotential_mono_left {smaller larger : ENNReal} (h : smaller ≤ larger) (right : ENNReal) :
    boundedUnionPotential smaller right ≤ boundedUnionPotential larger right :=
  add_le_add le_rfl (mul_le_mul' le_rfl (min_le_min le_rfl h))

theorem boundedUnionPotential_mono_right (left : ENNReal) {smaller larger : ENNReal} (h : smaller ≤ larger) :
    boundedUnionPotential left smaller ≤ boundedUnionPotential left larger := by
  rw [boundedUnionPotential_comm left smaller, boundedUnionPotential_comm left larger]
  exact boundedUnionPotential_mono_left h left

theorem boundedUnionPotential_add_decrease (left before after : ENNReal) (h : min 1 after ≤ min 1 before) :
    boundedUnionPotential left after + (min 1 before - min 1 after) * (1 - min 1 left) =
      boundedUnionPotential left before := by
  rw [boundedUnionPotential_comm left after, boundedUnionPotential_comm left before]
  unfold boundedUnionPotential
  calc
    _ = min 1 left + (1 - min 1 left) * (min 1 after + (min 1 before - min 1 after)) := by ring
    _ = _ := by rw [add_tsub_cancel_of_le h]

theorem expected_boundedUnionPotential_le (computation : SPMF α) (left : α → ENNReal) (right : ENNReal) :
    (∑' result, Pr[= result | computation] * boundedUnionPotential (left result) right) ≤
      min 1 right + (1 - min 1 right) * ∑' result, Pr[= result | computation] * left result := by
  simp only [boundedUnionPotential, mul_add, ENNReal.tsum_add]
  apply add_le_add
  · rw [ENNReal.tsum_mul_right]
    exact mul_le_of_le_one_left' tsum_probOutput_le_one
  · rw [← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro result
    rw [mul_left_comm]
    exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (min_le_right _ _))

theorem expected_boundedUnionPotential_add_decrease_le
    (computation : SPMF α) (left : α → ENNReal) (beforeLeft beforeRight afterRight charge : ENNReal)
    (hleft : (∑' result, Pr[= result | computation] * left result) ≤ beforeLeft + charge)
    (hright : min 1 afterRight ≤ min 1 beforeRight) :
    (∑' result, Pr[= result | computation] * boundedUnionPotential (left result) afterRight) +
      (min 1 beforeRight - min 1 afterRight) * (1 - min 1 beforeLeft) ≤
      boundedUnionPotential beforeLeft beforeRight + (1 - min 1 afterRight) * charge := by
  by_cases hlarge : 1 ≤ beforeLeft
  · rw [min_eq_left hlarge, tsub_self, mul_zero, add_zero, boundedUnionPotential_eq_one_of_left _ _ hlarge]
    apply le_trans ?_ le_self_add
    calc
      _ ≤ ∑' result, Pr[= result | computation] * 1 :=
        ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (boundedUnionPotential_le_one _ _)
      _ ≤ 1 := by simpa only [mul_one] using (tsum_probOutput_le_one (mx := computation))
  · have hsmall : min 1 beforeLeft = beforeLeft := min_eq_right (le_of_not_ge hlarge)
    have hstep := (expected_boundedUnionPotential_le computation left afterRight).trans
      (add_le_add le_rfl (mul_le_mul' le_rfl hleft))
    have h := add_le_add hstep (le_refl ((min 1 beforeRight - min 1 afterRight) * (1 - min 1 beforeLeft)))
    apply h.trans_eq
    rw [mul_add, ← add_assoc]
    conv_lhs => arg 1; arg 1; arg 2; rw [← hsmall]
    change (boundedUnionPotential beforeLeft afterRight + (1 - min 1 afterRight) * charge) + _ = _
    rw [add_right_comm, boundedUnionPotential_add_decrease _ _ _ hright]

theorem expected_boundedUnionPotential_le_of_left_le
    (computation : SPMF α) (left right : α → ENNReal) (beforeLeft beforeRight : ENNReal)
    (hleft : ∀ result ∈ support computation, left result ≤ beforeLeft)
    (hright : (∑' result, Pr[= result | computation] * right result) ≤ beforeRight) :
    (∑' result, Pr[= result | computation] * boundedUnionPotential (left result) (right result)) ≤
      boundedUnionPotential beforeLeft beforeRight := by
  by_cases hlarge : 1 ≤ beforeRight
  · rw [boundedUnionPotential_eq_one_of_right _ _ hlarge]
    calc
      _ ≤ ∑' result, Pr[= result | computation] * 1 :=
        ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (boundedUnionPotential_le_one _ _)
      _ ≤ 1 := by simpa only [mul_one] using (tsum_probOutput_le_one (mx := computation))
  · calc
      _ ≤ ∑' result, Pr[= result | computation] * boundedUnionPotential (right result) beforeLeft := by
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases hr : result ∈ support computation
        · rw [boundedUnionPotential_comm (right result)]
          exact mul_le_mul' le_rfl (boundedUnionPotential_mono_left (hleft result hr) _)
        · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
      _ ≤ min 1 beforeLeft + (1 - min 1 beforeLeft) * beforeRight :=
        (expected_boundedUnionPotential_le computation right beforeLeft).trans (add_le_add le_rfl (mul_le_mul' le_rfl hright))
      _ = _ := by
        rw [boundedUnionPotential_comm, boundedUnionPotential, min_eq_right (le_of_not_ge hlarge)]

end SphincsSecurity
