import XmssSecurity.Scheme
import VCVio.OracleComp.QueryTracking.Unpredictability

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Rom

noncomputable local instance : IsUniformSpec HashSpec :=
  IsUniformSpec.ofFintypeInhabited _

theorem card_hashOutput : Fintype.card HashOutput = 2 ^ hashOutputBits := by
  simp

/-- Among `q` random-oracle queries, the chance of sampling one fixed 256-bit output is at most `q / 2^256`. -/
theorem exact_output_hit_le {α : Type} (computation : OracleComp HashSpec α) (q : Nat)
    (hbound : computation.IsTotalQueryBound q) (target : HashOutput) :
    Pr[fun result => ∃ input, result.2 input = some target |
      (simulateQ cachingOracle computation).run ∅] ≤
      (q : ℝ≥0∞) / ((2 ^ hashOutputBits : Nat) : ℝ≥0∞) := by
  have h := probEvent_cache_has_value_le computation q hbound (fun _ => by
    change Fintype.card HashOutput ≤ Fintype.card HashOutput
    exact le_rfl) target ∅ (by simp)
  simpa [card_hashOutput, div_eq_mul_inv] using h

end XmssSecurity.Rom
