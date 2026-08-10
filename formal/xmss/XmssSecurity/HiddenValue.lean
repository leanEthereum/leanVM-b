import XmssSecurity.SecurityBudget
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.QueryTracking.RandomOracle.ProbeEps

open OracleComp ENNReal

namespace XmssSecurity.HiddenValue

noncomputable local instance : SampleableType Digest :=
  SampleableType.ofFintype Digest

theorem card_digest : Fintype.card Digest = 2 ^ digestBits := by
  simp

theorem uniform_digest_point_probability (target : Digest) :
    Pr[= target | $ᵗ Digest] =
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  rw [probOutput_uniformSample, card_digest]

/-- At most `q` adaptive equality probes hit one hidden uniform digest with probability `q / 2^128`. -/
theorem adaptive_guess_le (q : Nat) (strategy : List Bool → Digest) :
    Pr[(fun hit : Bool => hit = true) | hiddenReadMany ($ᵗ Digest) q strategy] ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  simpa [div_eq_mul_inv] using probEvent_hiddenReadMany_le
    (oa := ($ᵗ Digest)) (ε := ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹)
    (fun target => (uniform_digest_point_probability target).le) q strategy

/-- Up to 175 independent hidden digest targets and `q` adaptive probes fit within the 120-bit budget. -/
theorem adaptive_guess_list_le_120 (q targetCount : Nat)
    (strategy : List Bool → Digest) (hcount : targetCount ≤ totalBadEventSlots) :
    Pr[(fun hit : Bool => hit = true) |
      hiddenReadList ($ᵗ Digest) q strategy targetCount] ≤
      (q : ℝ≥0∞) / ((2 ^ targetSecurityBits : Nat) : ℝ≥0∞) := by
  refine (probEvent_hiddenReadList_le
    (oa := ($ᵗ Digest)) (ε := ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹)
    (fun target => (uniform_digest_point_probability target).le) q strategy targetCount).trans ?_
  calc
    (targetCount : ℝ≥0∞) *
        ((q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ≤
      (totalBadEventSlots : ℝ≥0∞) *
        ((q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) := by
      rw [div_eq_mul_inv]
      gcongr
    _ ≤ (q : ℝ≥0∞) / ((2 ^ targetSecurityBits : Nat) : ℝ≥0∞) :=
      totalBadEventSlots_budget_le_120 q

noncomputable def adaptiveGuessExperiment
    (strategyGenerator : ProbComp (List Bool → Digest)) (q targetCount : Nat) : ProbComp Bool :=
  strategyGenerator >>= fun strategy =>
    hiddenReadList ($ᵗ Digest) q strategy targetCount

/-- Public randomness may select the probing strategy before the independent hidden targets are drawn. -/
theorem adaptive_guess_after_public_sampling_le_120
    (strategyGenerator : ProbComp (List Bool → Digest)) (q targetCount : Nat)
    (hcount : targetCount ≤ totalBadEventSlots) :
    Pr[(fun hit : Bool => hit = true) |
      adaptiveGuessExperiment strategyGenerator q targetCount] ≤
      (q : ℝ≥0∞) / ((2 ^ targetSecurityBits : Nat) : ℝ≥0∞) := by
  unfold adaptiveGuessExperiment
  exact probEvent_bind_le_of_forall_le fun strategy _ =>
    adaptive_guess_list_le_120 q targetCount strategy hcount

end XmssSecurity.HiddenValue
