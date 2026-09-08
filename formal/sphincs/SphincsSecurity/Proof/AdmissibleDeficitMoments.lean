import SphincsSecurity.Proof.FourthMomentExceptionBound

namespace SphincsSecurity

private theorem positivePart_evenPower_le (x : ℝ) (k : Nat) :
    max x 0 ^ (2 * k) ≤ x ^ (2 * k) := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx]
  · rw [max_eq_right (le_of_not_ge hx)]
    cases k with
    | zero => simp
    | succ k =>
        rw [zero_pow (by omega), pow_mul]
        exact pow_nonneg (sq_nonneg x) _

private theorem positivePart_shift_le (score shift : ℝ) :
    max (score + shift) 0 ≤ max (max score 0 + shift) 0 :=
  max_le_max (add_le_add (le_max_left score 0) le_rfl) le_rfl

theorem admissibleDeficit_secondMoment_le (score : ℝ) :
    (1023 * max (score + 1) 0 ^ 2 + max (score - 1023) 0 ^ 2) / 1024 ≤
      max score 0 ^ 2 + 1023 := by
  let d := max score 0
  have hd : 0 ≤ d := le_max_right score 0
  have hreject : max (score + 1) 0 ^ 2 ≤ (d + 1) ^ 2 := by
    apply pow_le_pow_left₀ (le_max_right _ _) _
    exact (positivePart_shift_le score 1).trans_eq (max_eq_left (by linarith))
  have haccept : max (score - 1023) 0 ^ 2 ≤ (d - 1023) ^ 2 := by
    apply le_trans (pow_le_pow_left₀ (le_max_right _ _) (positivePart_shift_le score (-1023)) 2)
    exact positivePart_evenPower_le (d - 1023) 1
  have hidentity : (1023 * (d + 1) ^ 2 + (d - 1023) ^ 2) / 1024 = d ^ 2 + 1023 := by ring
  change _ ≤ d ^ 2 + 1023
  nlinarith

theorem admissibleDeficit_fourthMoment_le (score : ℝ) :
    (1023 * max (score + 1) 0 ^ 4 + max (score - 1023) 0 ^ 4) / 1024 ≤
      max score 0 ^ 4 + 6138 * max score 0 ^ 2 + 2 ^ 30 := by
  let d := max score 0
  have hd : 0 ≤ d := le_max_right score 0
  have hreject : max (score + 1) 0 ^ 4 ≤ (d + 1) ^ 4 := by
    apply pow_le_pow_left₀ (le_max_right _ _) _
    exact (positivePart_shift_le score 1).trans_eq (max_eq_left (by linarith))
  have haccept : max (score - 1023) 0 ^ 4 ≤ (d - 1023) ^ 4 := by
    apply le_trans (pow_le_pow_left₀ (le_max_right _ _) (positivePart_shift_le score (-1023)) 4)
    exact positivePart_evenPower_le (d - 1023) 2
  have hidentity : (1023 * (d + 1) ^ 4 + (d - 1023) ^ 4) / 1024 =
      d ^ 4 + 6138 * d ^ 2 - 4182024 * d + 1069553661 := by ring
  change _ ≤ d ^ 4 + 6138 * d ^ 2 + 2 ^ 30
  nlinarith

end SphincsSecurity
