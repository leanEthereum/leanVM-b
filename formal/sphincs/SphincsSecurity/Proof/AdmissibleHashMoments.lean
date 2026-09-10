import SphincsSecurity.Proof.Prelude

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

noncomputable def positiveScoreMoment (score : ℝ) (power : Nat) : ENNReal :=
  ENNReal.ofReal (max score 0 ^ power)

theorem positiveScoreMoment_ne_top (score : ℝ) (power : Nat) : positiveScoreMoment score power ≠ ⊤ := by
  exact ENNReal.ofReal_ne_top

theorem positiveScoreMoment_zero_of_nonpos (score : ℝ) (hscore : score ≤ 0) (power : Nat) (hpower : power ≠ 0) :
    positiveScoreMoment score power = 0 := by
  simp [positiveScoreMoment, max_eq_right hscore, zero_pow hpower]

end SphincsSecurity
