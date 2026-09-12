import SphincsSecurity.Proof.Fts.PoissonProposalMoments
namespace SphincsSecurity.Concrete

open _root_.OracleComp ENNReal
open scoped NNReal

private theorem descFactorial_two_add (n : Nat) : n.descFactorial 2 + n = n ^ 2 := by
  rw [Nat.descFactorial_succ, Nat.descFactorial_one]
  cases n with
  | zero => rfl
  | succ m =>
      simp only [Nat.succ_sub_one]
      ring

theorem expected_poisson_sq (rate : NNReal) :
    (∑' count, (ProbabilityTheory.poissonMeasure rate).toPMF count * ((count : ENNReal) ^ 2)) = (rate : ENNReal) ^ 2 + rate := by
  have h2 := expected_poisson_descFactorial rate 2
  have h1 := expected_poisson_descFactorial rate 1
  simp only [Nat.descFactorial_one, pow_one] at h1
  have hsplit : ∀ count : Nat, ((count : ENNReal) ^ 2) = (count.descFactorial 2 : ENNReal) + count := by
    intro count
    rw [← Nat.cast_add, descFactorial_two_add, Nat.cast_pow]
  simp_rw [hsplit, mul_add, ENNReal.tsum_add, h2, h1]

theorem poisson_variance_le (rate : NNReal) :
    (∑' count, (ProbabilityTheory.poissonMeasure rate).toPMF count * ((rate : ENNReal) - count) ^ 2) ≤ rate := by
  have hpoint : ∀ count : Nat, ((rate : ENNReal) - count) ^ 2 + 2 * rate * count ≤ (rate : ENNReal) ^ 2 + (count : ENNReal) ^ 2 := by
    intro count
    by_cases hle : (count : ENNReal) ≤ rate
    · apply le_of_eq
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_pow,
        ENNReal.toReal_sub_of_le hle (by finiteness), ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow,
        ENNReal.toReal_ofNat]
      ring
    · rw [tsub_eq_zero_of_le (le_of_not_ge hle)]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add]
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow,
        ENNReal.toReal_ofNat]
      nlinarith [sq_nonneg (((rate : ENNReal)).toReal - ((count : ENNReal)).toReal)]
  have hsum : (∑' count, (ProbabilityTheory.poissonMeasure rate).toPMF count * (((rate : ENNReal) - count) ^ 2 + 2 * rate * count)) ≤
      ∑' count, (ProbabilityTheory.poissonMeasure rate).toPMF count * ((rate : ENNReal) ^ 2 + (count : ENNReal) ^ 2) :=
    ENNReal.tsum_le_tsum fun count => mul_le_mul' le_rfl (hpoint count)
  have hleft : (∑' count, (ProbabilityTheory.poissonMeasure rate).toPMF count * (((rate : ENNReal) - count) ^ 2 + 2 * rate * count)) =
      (∑' count, (ProbabilityTheory.poissonMeasure rate).toPMF count * ((rate : ENNReal) - count) ^ 2) + 2 * (rate : ENNReal) ^ 2 := by
    simp only [mul_add, ENNReal.tsum_add]
    congr 1
    calc
      _ = ∑' count, (2 * (rate : ENNReal)) * ((ProbabilityTheory.poissonMeasure rate).toPMF count * ((count.descFactorial 1 : Nat) : ENNReal)) := by
        apply tsum_congr
        intro count
        rw [Nat.descFactorial_one]
        ring
      _ = _ := by
        rw [ENNReal.tsum_mul_left, expected_poisson_descFactorial rate 1, pow_one]
        ring
  have hright : (∑' count, (ProbabilityTheory.poissonMeasure rate).toPMF count * ((rate : ENNReal) ^ 2 + (count : ENNReal) ^ 2)) =
      (rate : ENNReal) + 2 * (rate : ENNReal) ^ 2 := by
    simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul, expected_poisson_sq]
    ring
  rw [hleft, hright] at hsum
  exact (ENNReal.add_le_add_iff_right (by finiteness)).mp hsum

theorem targetProposalPool_small_le :
    Pr[fun total : Nat => total < 25313293 | targetProposalPool] ≤ (2 ^ 10 : ENNReal)⁻¹ := by
  let rate : NNReal := (19 / 50 : NNReal) * ((2 ^ totalHeight : Nat) : NNReal)
  have hpool : targetProposalPool = (ProbabilityTheory.poissonMeasure rate).toPMF := rfl
  have hrate : ((rate : ENNReal)).toReal = 637534208 / 25 := by
    simp only [rate, ENNReal.coe_mul, ENNReal.toReal_mul, ENNReal.coe_natCast, ENNReal.toReal_natCast, totalHeight]
    norm_num [ENNReal.toReal_div]
  have hk : ((25313293 : Nat) : ENNReal) ≤ rate := by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    rw [hrate, ENNReal.toReal_natCast]
    norm_num
  let gap : ENNReal := (rate : ENNReal) - (25313293 : Nat)
  have hgap : gap.toReal = 4701883 / 25 := by
    simp only [gap]
    rw [ENNReal.toReal_sub_of_le hk (by finiteness), hrate, ENNReal.toReal_natCast]
    norm_num
  have hgap_ne : gap ≠ 0 := by
    intro h
    have := congrArg ENNReal.toReal h
    rw [hgap] at this
    norm_num at this
  have hgap_top : gap ≠ ⊤ := by finiteness
  have hkey : Pr[fun total : Nat => total < 25313293 | targetProposalPool] * gap ^ 2 ≤ rate := by
    rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
    apply le_trans ?_ (poisson_variance_le rate)
    apply ENNReal.tsum_le_tsum
    intro count
    split_ifs with hcount
    · rw [hpool, PMF.probOutput_eq_apply]
      apply mul_le_mul' le_rfl
      apply pow_le_pow_left' _ 2
      exact tsub_le_tsub_left (by exact_mod_cast hcount.le) _
    · simp only [zero_mul, zero_le]
  have hdiv : Pr[fun total : Nat => total < 25313293 | targetProposalPool] ≤ (rate : ENNReal) / gap ^ 2 := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (pow_ne_zero 2 hgap_ne)) (Or.inl (ENNReal.pow_ne_top hgap_top))]
    exact hkey
  refine hdiv.trans ?_
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_div, ENNReal.toReal_pow, hgap, hrate, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  norm_num

end SphincsSecurity.Concrete
