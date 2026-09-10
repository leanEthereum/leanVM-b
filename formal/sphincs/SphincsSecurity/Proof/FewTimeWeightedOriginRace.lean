import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.FewTimeParametricSignerRace

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

namespace Concrete

noncomputable def digestReuseWeight (q : Nat) : ℝ≥0∞ :=
  ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ /
    ((1 - ((q + digestAttemptLimit : Nat) : ℝ≥0∞) *
      ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹) *
      ((2 ^ ftsTreeHeight : Nat) : ℝ≥0∞)⁻¹)

theorem digestReuseWeight_ne_top (q : Nat) (hq : q ≤ 2 ^ 127) :
    digestReuseWeight q ≠ ∞ := by
  apply ENNReal.div_ne_top (by finiteness)
  apply digestRaceSuccessRate_ne_zero_of_budget_lt
  norm_num [digestAttemptLimit, randomnessBits] at *
  omega

end Concrete

end SphincsSecurity
