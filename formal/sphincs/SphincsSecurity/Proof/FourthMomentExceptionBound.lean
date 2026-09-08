import SphincsSecurity.Proof.ExceptionBudgetPotential

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

noncomputable def fourthMomentBudget (q : Nat) (second fourth : ENNReal) : ENNReal :=
  fourth + 6138 * q * second + 6279174 * q.choose 2 + (2 : ENNReal) ^ 30 * q

theorem fourthMomentBudget_succ (q : Nat) (second fourth : ENNReal) :
    fourthMomentBudget (q + 1) second fourth =
      fourthMomentBudget q second fourth + 6138 * second + 6279174 * q + 2 ^ 30 := by
  have hchoose : (q + 1).choose 2 = q + q.choose 2 := by
    simpa only [Nat.choose_one_right] using Nat.choose_succ_succ' q 1
  simp only [fourthMomentBudget, hchoose, Nat.cast_add, Nat.cast_one]
  ring

theorem fourthMomentBudget_mono (q : Nat) (second fourth : ENNReal) :
    fourthMomentBudget q second fourth ≤ fourthMomentBudget (q + 1) second fourth := by
  rw [fourthMomentBudget_succ]
  exact ((le_self_add.trans le_self_add).trans le_self_add)

theorem fourth_le_fourthMomentBudget (q : Nat) (second fourth : ENNReal) :
    fourth ≤ fourthMomentBudget q second fourth := by
  exact ((le_self_add.trans le_self_add).trans le_self_add)

theorem expected_fourthMomentBudget_fresh_le
    (second fourth : QueryCache HashSpec → ENNReal)
    (q : Nat) (cache : QueryCache HashSpec) (input : HashInput)
    (hsecond : (∑' answer, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
      second (cache.cacheQuery input answer)) ≤ second cache + 1023)
    (hfourth : (∑' answer, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
      fourth (cache.cacheQuery input answer)) ≤ fourth cache + 6138 * second cache + 2 ^ 30) :
    (∑' answer, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
      fourthMomentBudget q (second (cache.cacheQuery input answer)) (fourth (cache.cacheQuery input answer))) ≤
      fourthMomentBudget (q + 1) (second cache) (fourth cache) := by
  simp only [fourthMomentBudget, mul_add, ENNReal.tsum_add]
  have hsecond' : (∑' answer, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (6138 * q * second (cache.cacheQuery input answer))) ≤ 6138 * q * (second cache + 1023) := by
    calc
      _ = 6138 * q * ∑' answer, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
          second (cache.cacheQuery input answer) := by
        rw [← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro answer
        ring
      _ ≤ _ := mul_le_mul' le_rfl hsecond
  simp only [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
  apply (add_le_add (add_le_add (add_le_add hfourth hsecond') le_rfl) le_rfl).trans_eq
  change fourthMomentBudget q (second cache + 1023) (fourth cache + 6138 * second cache + 2 ^ 30) =
    fourthMomentBudget (q + 1) (second cache) (fourth cache)
  rw [fourthMomentBudget_succ]
  simp only [fourthMomentBudget]
  ring

theorem fourthMomentBudget_zero_le (q : Nat) (hq : q ≤ 2 ^ 127) :
    fourthMomentBudget q 0 0 / (2 : ENNReal) ^ 372 ≤ (q : ENNReal) / 2 ^ 223 := by
  have hchoose : 2 * q.choose 2 + q = q * q := by
    clear hq
    induction q with
    | zero => simp
    | succ q ih =>
        have hstep : (q + 1).choose 2 = q + q.choose 2 := by
          simpa only [Nat.choose_one_right] using Nat.choose_succ_succ' q 1
        rw [hstep]
        nlinarith
  have hchooseReal : 2 * (q.choose 2 : ℝ) + q = (q : ℝ) * q := by exact_mod_cast hchoose
  have hqReal : (q : ℝ) ≤ 2 ^ 127 := by exact_mod_cast hq
  have hqNonneg : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hproduct : (q : ℝ) * q ≤ q * 2 ^ 127 := mul_le_mul_of_nonneg_left hqReal hqNonneg
  apply (ENNReal.toReal_le_toReal (by simp [fourthMomentBudget]; finiteness) (by finiteness)).mp
  simp only [fourthMomentBudget, mul_zero, add_zero, zero_add]
  rw [ENNReal.toReal_div, ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_div]
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_pow, pow_succ] at hproduct ⊢
  nlinarith

theorem probEvent_cacheEntryException_le_fourthMoment
    (Bad : QueryCache HashSpec → Prop) (second fourth : QueryCache HashSpec → ENNReal)
    (hbad : ∀ cache, Finite cache → Bad cache → (2 : ENNReal) ^ 372 ≤ fourth cache)
    (hsecond : ∀ cache, Finite cache → ∀ input, cache input = none →
      (∑' answer, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
        second (cache.cacheQuery input answer)) ≤ second cache + 1023)
    (hfourth : ∀ cache, Finite cache → ∀ input, cache input = none →
      (∑' answer, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
        fourth (cache.cacheQuery input answer)) ≤ fourth cache + 6138 * second cache + 2 ^ 30)
    (computation : OracleComp OracleWorld α) (q : Nat)
    (hbound : computation.IsQueryBoundP (· matches Sum.inr _) q) (hq : q ≤ 2 ^ 127)
    (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (hsecondZero : second cache = 0) (hfourthZero : fourth cache = 0) :
    Pr[fun result => result.2 = true |
      runExceptionMonitor (cacheEntryException Bad) computation cache false] ≤ (q : ENNReal) / 2 ^ 223 := by
  apply le_trans (b := fourthMomentBudget q (second cache) (fourth cache) / (2 : ENNReal) ^ 372)
  · apply probEvent_cacheEntryException_le_budgetPotential Bad
      (fun q cache => fourthMomentBudget q (second cache) (fourth cache) / (2 : ENNReal) ^ 372)
      ?_ ?_ ?_ computation q hbound cache hfinite
    · intro remaining current hcurrent hbadCache
      have h := (hbad current hcurrent hbadCache).trans
        (fourth_le_fourthMomentBudget remaining (second current) (fourth current))
      calc
        1 = (2 : ENNReal) ^ 372 / 2 ^ 372 := (ENNReal.div_self (by positivity) (by finiteness)).symm
        _ ≤ _ := ENNReal.div_le_div_right h _
    · intro remaining current _
      exact ENNReal.div_le_div_right (fourthMomentBudget_mono remaining (second current) (fourth current)) _
    · intro remaining current hcurrent input hnew
      simp_rw [div_eq_mul_inv, ← mul_assoc, ENNReal.tsum_mul_right]
      exact mul_le_mul' (expected_fourthMomentBudget_fresh_le second fourth remaining current input
        (hsecond current hcurrent input hnew) (hfourth current hcurrent input hnew)) le_rfl
  · rw [hsecondZero, hfourthZero]
    exact fourthMomentBudget_zero_le q hq

end SphincsSecurity
