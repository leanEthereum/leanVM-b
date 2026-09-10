import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Statement

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

theorem rootBudget_four_thirds {q : Nat} (hq : q ≤ 2 ^ 126) :
    ((q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) * (4 / 3 : ℝ≥0∞) + 1 ≤
      (4 / 3 : ℝ≥0∞) := by
  calc
    _ ≤ (((2 ^ 126 : Nat) : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) *
        (4 / 3 : ℝ≥0∞) + 1 := by gcongr
    _ ≤ _ := by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
      simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
        ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one]
      norm_num [digestBits]

end SphincsSecurity.Concrete.OtsProbeSimulation
