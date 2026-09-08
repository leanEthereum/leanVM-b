import SphincsSecurity.Proof.FiniteInitialEnvelope

namespace SphincsSecurity.Concrete

open ENNReal
set_option backward.isDefEq.respectTransparency false

theorem ennreal_choose_le_pow_div_factorial (steps degree : Nat) :
    (steps.choose degree : ENNReal) ≤ (steps : ENNReal) ^ degree / (degree.factorial : ENNReal) := by
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast degree.factorial_ne_zero)) (Or.inl (by finiteness))).mpr
  have h : steps.choose degree * degree.factorial ≤ steps ^ degree := by
    rw [Nat.mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow steps degree
  exact_mod_cast h

theorem mixedQueryIncrement_mul (arrival scalar : ENNReal) (moments : MixedMomentVector) :
    mixedQueryIncrement arrival (fun p o => scalar * moments p o) =
      fun p o => scalar * mixedQueryIncrement arrival moments p o := by
  funext power order
  simp only [mixedQueryIncrement, mixedPowerLower_mul]
  ring

theorem mixedSigningIncrement_mul (uniform reuse scalar : ENNReal) (moments : MixedMomentVector) :
    mixedSigningIncrement uniform reuse (fun p o => scalar * moments p o) =
      fun p o => scalar * mixedSigningIncrement uniform reuse moments p o := by
  funext power order
  simp only [mixedSigningIncrement, mixedPowerLower_mul]
  ring

theorem mixedQueryIncrement_mono (arrival : ENNReal) : Monotone (mixedQueryIncrement arrival) := by
  intro left right h power order
  exact mul_le_mul_right (mixedPowerLower_mono h power order) arrival

theorem mixedSigningIncrement_mono (uniform reuse : ENNReal) : Monotone (mixedSigningIncrement uniform reuse) := by
  intro left right h power order
  exact add_le_add (mul_le_mul_right
    (add_le_add (add_le_add (mixedPowerLower_mono h power order) (h power (order + 1)))
      (mixedPowerLower_mono h power (order + 1))) uniform) (mul_le_mul_right (h (power + 1) (order + 1)) reuse)

theorem mixedSigningEnvelope_reuse_mono (uniform : ENNReal) {small large : ENNReal} (h : small ≤ large) (moments : MixedMomentVector) :
    mixedSigningEnvelope uniform small moments ≤ mixedSigningEnvelope uniform large moments := by
  intro power order
  exact add_le_add le_rfl (mul_le_mul_left h _)

theorem digestReuseWeight_mono : Monotone digestReuseWeight := by
  intro small large h
  unfold digestReuseWeight
  apply ENNReal.div_le_div_left
  apply mul_le_mul' _ le_rfl
  exact tsub_le_tsub_left (mul_le_mul' (Nat.cast_le.mpr (Nat.add_le_add_right h _)) le_rfl) _

theorem digestReuseWeight_le_coarse127 (q : Nat) (hq : q ≤ 2 ^ 127) : digestReuseWeight q ≤ (33 : ENNReal) / 2 ^ 122 := by
  apply (digestReuseWeight_mono hq).trans
  apply (ENNReal.toReal_le_toReal (digestReuseWeight_ne_top (2 ^ 127) le_rfl) (by finiteness)).mp
  norm_num [digestReuseWeight, ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_mul,
    randomnessBits, digestAttemptLimit, ftsTreeHeight]
  rw [ENNReal.toReal_sub_of_le (by
    rw [ENNReal.mul_inv_le_iff (by norm_num) (by finiteness)]
    norm_num) (by finiteness)]
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv]

theorem digestReuseWeight_le_precise127 (q : Nat) (hq : q ≤ 2 ^ 127) : digestReuseWeight q ≤ (2049 : ENNReal) / 2 ^ 128 := by
  apply (digestReuseWeight_mono hq).trans
  apply (ENNReal.toReal_le_toReal (digestReuseWeight_ne_top (2 ^ 127) le_rfl) (by finiteness)).mp
  norm_num [digestReuseWeight, ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_mul,
    randomnessBits, digestAttemptLimit, ftsTreeHeight]
  rw [ENNReal.toReal_sub_of_le (by
    rw [ENNReal.mul_inv_le_iff (by norm_num) (by finiteness)]
    norm_num) (by finiteness)]
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv]

end SphincsSecurity.Concrete
