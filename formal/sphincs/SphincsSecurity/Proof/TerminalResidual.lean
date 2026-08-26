import SphincsSecurity.Proof.EncodingSelectionSampling
import SphincsSecurity.Proof.TerminalFinish

/-!
# Residual terminal interface after encoding collisions

The completed encoding bound consumes 44 of the 64 units left at denominator `2^128`. The four
secret-opening and message branches therefore have a combined budget of 20 units.
-/

namespace SphincsSecurity.Concrete

open OracleComp ENNReal

noncomputable def sampledNonEncodingRisk (adversary : Adversary) : ℝ≥0∞ :=
  Pr[SampledViewedEvent cleanFreshEvent | sampledViewedGame adversary] +
    (Pr[SampledViewedEvent cleanBackwardEvent | sampledViewedGame adversary] +
    (Pr[SampledViewedEvent cleanMessageEvent | sampledViewedGame adversary] +
      Pr[SampledViewedEvent cleanUncoveredEvent | sampledViewedGame adversary]))

theorem forgeAdvantage_le_of_sampled_nonEncodingRisk_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqMax : q ≤ 2 ^ 120)
    (hresidual : sampledNonEncodingRisk adversary ≤
      ((20 * q : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) :
    forgeAdvantage scheme adversary ≤ q / ((2 ^ securityBits : Nat) : ℝ≥0∞) := by
  apply forgeAdvantage_le_of_sampled_remaining_le adversary q hq hqMax
  calc
    Pr[SampledViewedEvent cleanFreshEvent | sampledViewedGame adversary] +
        (Pr[SampledViewedEvent cleanEncodingEvent | sampledViewedGame adversary] +
        (Pr[SampledViewedEvent cleanBackwardEvent | sampledViewedGame adversary] +
        (Pr[SampledViewedEvent cleanMessageEvent | sampledViewedGame adversary] +
          Pr[SampledViewedEvent cleanUncoveredEvent | sampledViewedGame adversary]))) =
      Pr[SampledViewedEvent cleanEncodingEvent | sampledViewedGame adversary] +
        sampledNonEncodingRisk adversary := by
      rw [sampledNonEncodingRisk]
      ring
    _ ≤ ((44 * q : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
        ((20 * q : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ :=
      add_le_add (probEvent_sampled_cleanEncoding_le adversary q hq) hresidual
    _ = ((64 * q : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      push_cast
      ring

theorem security_of_sampled_nonEncodingRisk_le
    (hresidual : ∀ (q : Nat), 1 ≤ q → ∀ adversary : Adversary,
      HasHashQueryBound scheme adversary q → q ≤ 2 ^ securityBits →
      sampledNonEncodingRisk adversary ≤
        ((20 * q : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) :
    SphincsSecurityStatement := by
  intro q hqPos adversary hq
  by_cases hqMax : q ≤ 2 ^ securityBits
  · exact forgeAdvantage_le_of_sampled_nonEncodingRisk_le adversary q hq
      (by simpa only [securityBits] using hqMax)
      (hresidual q hqPos adversary hq hqMax)
  · exact forgeAdvantage_le_of_security_pow_le adversary q (by omega)

end SphincsSecurity.Concrete
