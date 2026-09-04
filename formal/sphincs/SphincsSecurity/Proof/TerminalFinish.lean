import SphincsSecurity.Proof.TerminalSampling

/-!
# Final residual interface

Once the five sampled residual probabilities fit in the remaining 64 units at denominator `2^128`,
the concrete advantage has the claimed `q / 2^120` bound. Budgets above `2^120` are immediate from
the fact that a probability is at most one.
-/

namespace SphincsSecurity.Concrete

open OracleComp ENNReal

theorem forgeAdvantage_le_of_sampled_remaining_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqMax : q ≤ 2 ^ 120)
    (hremaining :
      Pr[SampledViewedEvent cleanFreshEvent | sampledViewedGame adversary] +
        (Pr[SampledViewedEvent cleanEncodingEvent | sampledViewedGame adversary] +
        (Pr[SampledViewedEvent cleanBackwardEvent | sampledViewedGame adversary] +
        (Pr[SampledViewedEvent cleanMessageEvent | sampledViewedGame adversary] +
          Pr[SampledViewedEvent cleanUncoveredEvent | sampledViewedGame adversary]))) ≤
      ((64 * q : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) :
    forgeAdvantage scheme adversary ≤ q / ((2 ^ securityBits : Nat) : ℝ≥0∞) := by
  calc
    _ ≤ ((24 * q : Nat) : ℝ≥0∞) * ((2 ^ 125 : Nat) : ℝ≥0∞)⁻¹ +
        (Pr[SampledViewedEvent cleanFreshEvent | sampledViewedGame adversary] +
        (Pr[SampledViewedEvent cleanEncodingEvent | sampledViewedGame adversary] +
        (Pr[SampledViewedEvent cleanBackwardEvent | sampledViewedGame adversary] +
        (Pr[SampledViewedEvent cleanMessageEvent | sampledViewedGame adversary] +
          Pr[SampledViewedEvent cleanUncoveredEvent | sampledViewedGame adversary])))) :=
      forgeAdvantage_le_reserved_add_sampled_remaining adversary q hq hqMax
    _ ≤ ((24 * q : Nat) : ℝ≥0∞) * ((2 ^ 125 : Nat) : ℝ≥0∞)⁻¹ +
        ((64 * q : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ :=
      add_le_add_right hremaining _
    _ = (q : ℝ≥0∞) *
        (((24 : Nat) : ℝ≥0∞) * ((2 ^ 125 : Nat) : ℝ≥0∞)⁻¹ +
          ((64 : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) := by
      push_cast
      ring
    _ = (q : ℝ≥0∞) * ((2 ^ securityBits : Nat) : ℝ≥0∞)⁻¹ := by
      rw [show securityBits = 120 by rfl, terminal_budget_remainder]
    _ = q / ((2 ^ securityBits : Nat) : ℝ≥0∞) := by
      rw [div_eq_mul_inv]

theorem forgeAdvantage_le_of_security_pow_le
    (adversary : Adversary) (q : Nat) (hq : 2 ^ securityBits ≤ q) :
    forgeAdvantage scheme adversary ≤ q / ((2 ^ securityBits : Nat) : ℝ≥0∞) := by
  apply probOutput_le_one.trans
  rw [div_eq_mul_inv]
  have hcast : (((2 ^ securityBits : Nat) : Nat) : ℝ≥0∞) ≤ (q : ℝ≥0∞) := by
    exact_mod_cast hq
  calc
    (1 : ℝ≥0∞) = ((2 ^ securityBits : Nat) : ℝ≥0∞) *
        ((2 ^ securityBits : Nat) : ℝ≥0∞)⁻¹ := by
      rw [ENNReal.mul_inv_cancel]
      · norm_num
      · finiteness
    _ ≤ (q : ℝ≥0∞) * ((2 ^ securityBits : Nat) : ℝ≥0∞)⁻¹ := by
      gcongr

theorem security_of_sampled_remaining_le
    (hremaining : ∀ (q : Nat), 1 ≤ q → ∀ adversary : Adversary,
      HasHashQueryBound scheme adversary q → q ≤ 2 ^ securityBits →
      Pr[SampledViewedEvent cleanFreshEvent | sampledViewedGame adversary] +
        (Pr[SampledViewedEvent cleanEncodingEvent | sampledViewedGame adversary] +
        (Pr[SampledViewedEvent cleanBackwardEvent | sampledViewedGame adversary] +
        (Pr[SampledViewedEvent cleanMessageEvent | sampledViewedGame adversary] +
          Pr[SampledViewedEvent cleanUncoveredEvent | sampledViewedGame adversary]))) ≤
        ((64 * q : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) :
    SphincsSecurityStatement := by
  intro q hqPos adversary hq
  by_cases hqMax : q ≤ 2 ^ securityBits
  · apply forgeAdvantage_le_of_sampled_remaining_le adversary q hq
    · simpa only [securityBits] using hqMax
    · exact hremaining q hqPos adversary hq hqMax
  · apply forgeAdvantage_le_of_security_pow_le adversary q
    omega

end SphincsSecurity.Concrete
