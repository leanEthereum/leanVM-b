import SphincsSecurity.Proof.UniformProposalVariance

namespace SphincsSecurity.Concrete

open _root_.OracleComp ENNReal

theorem uniformWordAverage_const {α : Type} [SampleableType α] [Fintype α] [Nonempty α] [DecidableEq α]
    (steps : Nat) (value : ENNReal) :
    uniformWordAverage steps (fun _word : List α => value) = value := by
  let index : α := Classical.choice inferInstance
  rw [uniformWordAverage, expected_uniformProposalWord_count index steps (fun _ => value)]
  exact binomialAverage_const (ENNReal.inv_le_one.mpr (by exact_mod_cast Fintype.card_pos)) steps value

theorem excess_le_square_with_mean (value mean : ENNReal) (hvalue : value ≠ ⊤)
    (hmean : mean ≤ 1 / 5) :
    (26 / 5 : ENNReal) * (value - 3 / 2) + 2 * mean * value ≤ value ^ 2 + mean ^ 2 := by
  have hm : mean ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) hmean
  have hmr : mean.toReal ≤ 1 / 5 := by
    have h := (ENNReal.toReal_le_toReal hm (by finiteness)).mpr hmean
    simpa only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] using h
  by_cases hsmall : value ≤ 3 / 2
  · rw [tsub_eq_zero_of_le hsmall, mul_zero, zero_add]
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_add,
      ENNReal.toReal_ofNat]
    nlinarith [sq_nonneg (value.toReal - mean.toReal)]
  · have hlarge : 3 / 2 ≤ value := le_of_not_ge hsmall
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_sub_of_le hlarge hvalue, ENNReal.toReal_div, ENNReal.toReal_ofNat]
    nlinarith [sq_nonneg (value.toReal - mean.toReal - 13 / 5)]

theorem uniformWordAverage_excess_le_of_secondMoment {α : Type} [SampleableType α] [Fintype α]
    [Nonempty α] [DecidableEq α] (steps : Nat) (payoff : List α → ENNReal)
    (hfinite : ∀ word, payoff word ≠ ⊤)
    (hmean : uniformWordAverage steps payoff ≤ 1 / 5)
    (hsecond : uniformWordAverage steps (fun word => payoff word ^ 2) ≤
      uniformWordAverage steps payoff ^ 2 + 13 / 25000) :
    uniformWordAverage steps (fun word => payoff word - 3 / 2) ≤ (2 ^ 13 : ENNReal)⁻¹ := by
  let mean := uniformWordAverage steps payoff
  have hm : mean ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) hmean
  have h := uniformWordAverage_mono steps (fun word => excess_le_square_with_mean (payoff word) mean (hfinite word) hmean)
  rw [uniformWordAverage_add, uniformWordAverage_add,
    uniformWordAverage_mul_left, uniformWordAverage_mul_left, uniformWordAverage_const] at h
  have hcancel : (26 / 5 : ENNReal) * uniformWordAverage steps (fun word => payoff word - 3 / 2) ≤
      13 / 25000 := by
    apply ENNReal.le_of_add_le_add_right (a := 2 * mean ^ 2) (by finiteness)
    calc
      _ = (26 / 5 : ENNReal) * uniformWordAverage steps (fun word => payoff word - 3 / 2) +
          2 * mean * uniformWordAverage steps payoff := by change _ = _ + 2 * mean * mean; ring
      _ ≤ uniformWordAverage steps (fun word => payoff word ^ 2) + mean ^ 2 := h
      _ ≤ (mean ^ 2 + 13 / 25000) + mean ^ 2 := add_le_add hsecond le_rfl
      _ = _ := by ring
  have hunit : (5 / 26 : ENNReal) * (26 / 5) = 1 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
  calc
    _ = (5 / 26 : ENNReal) * ((26 / 5) * uniformWordAverage steps (fun word => payoff word - 3 / 2)) := by
      rw [← mul_assoc, hunit, one_mul]
    _ ≤ (5 / 26 : ENNReal) * (13 / 25000) := mul_le_mul' le_rfl hcancel
    _ ≤ _ := by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_pow]

end SphincsSecurity.Concrete
