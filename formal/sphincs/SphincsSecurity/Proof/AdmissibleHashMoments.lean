import SphincsSecurity.Proof.AdmissibleDeficitMoments
import SphincsSecurity.Proof.FewTimeFresh

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

theorem probEvent_uniformHashOutput_admissible :
    Pr[fun answer : HashOutput => Concrete.signAttemptResultOfOutput answer ≠ none |
      ($ᵗ HashOutput : ProbComp HashOutput)] = (1 / 1024 : ENNReal) := by
  have h := Concrete.probEvent_uniformHashOutput_admissible_view (fun _ => True)
  simpa only [and_true, probEvent_const, if_true, probFailure_of_liftM_PMF, tsub_zero,
    mul_one, ftsTreeHeight, Nat.reducePow, Nat.cast_ofNat, one_div] using h

theorem probEvent_uniformHashOutput_rejected :
    Pr[fun answer : HashOutput => ¬ Concrete.signAttemptResultOfOutput answer ≠ none |
      ($ᵗ HashOutput : ProbComp HashOutput)] = (1023 / 1024 : ENNReal) := by
  have h := probEvent_compl ($ᵗ HashOutput : ProbComp HashOutput)
    (fun answer => Concrete.signAttemptResultOfOutput answer ≠ none)
  rw [probFailure_of_liftM_PMF, tsub_zero, add_comm] at h
  have hreal := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add probEvent_ne_top probEvent_ne_top,
    probEvent_uniformHashOutput_admissible] at hreal
  apply (ENNReal.toReal_eq_toReal_iff' probEvent_ne_top (by finiteness)).mp
  rw [show (1 / 1024 : ENNReal).toReal = (1 / 1024 : ℝ) by norm_num [ENNReal.toReal_div],
    ENNReal.toReal_one] at hreal
  rw [show (1023 / 1024 : ENNReal).toReal = (1023 / 1024 : ℝ) by norm_num [ENNReal.toReal_div]]
  linarith

theorem expected_uniformHashOutput_admissible_choice (accepted rejected : ENNReal) :
    (∑' answer, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Concrete.signAttemptResultOfOutput answer ≠ none then accepted else rejected)) =
      (1 / 1024 : ENNReal) * accepted + (1023 / 1024 : ENNReal) * rejected := by
  have hsplit (answer : HashOutput) :
      Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (if Concrete.signAttemptResultOfOutput answer ≠ none then accepted else rejected) =
        (if Concrete.signAttemptResultOfOutput answer ≠ none then
            Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] else 0) * accepted +
        (if ¬ Concrete.signAttemptResultOfOutput answer ≠ none then
            Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] else 0) * rejected := by
    split_ifs <;> simp_all
  simp_rw [hsplit, ENNReal.tsum_add, ENNReal.tsum_mul_right,
    ← probEvent_eq_tsum_ite, probEvent_uniformHashOutput_admissible, probEvent_uniformHashOutput_rejected]

noncomputable def positiveScoreMoment (score : ℝ) (power : Nat) : ENNReal :=
  ENNReal.ofReal (max score 0 ^ power)

theorem positiveScoreMoment_ne_top (score : ℝ) (power : Nat) : positiveScoreMoment score power ≠ ⊤ := by
  exact ENNReal.ofReal_ne_top

theorem positiveScoreMoment_zero_of_nonpos (score : ℝ) (hscore : score ≤ 0) (power : Nat) (hpower : power ≠ 0) :
    positiveScoreMoment score power = 0 := by
  simp [positiveScoreMoment, max_eq_right hscore, zero_pow hpower]

theorem expected_admissibleScore_second_le (score : ℝ) :
    (∑' answer, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
      positiveScoreMoment (score + if Concrete.signAttemptResultOfOutput answer ≠ none then -1023 else 1) 2) ≤
      positiveScoreMoment score 2 + 1023 := by
  have hchoice (answer : HashOutput) :
      positiveScoreMoment (score + if Concrete.signAttemptResultOfOutput answer ≠ none then -1023 else 1) 2 =
        if Concrete.signAttemptResultOfOutput answer ≠ none then positiveScoreMoment (score - 1023) 2
          else positiveScoreMoment (score + 1) 2 := by split_ifs <;> rfl
  simp_rw [hchoice]
  rw [expected_uniformHashOutput_admissible_choice]
  apply (ENNReal.toReal_le_toReal (by unfold positiveScoreMoment; finiteness)
    (by unfold positiveScoreMoment; finiteness)).mp
  rw [ENNReal.toReal_add (by unfold positiveScoreMoment; finiteness) (by unfold positiveScoreMoment; finiteness),
    ENNReal.toReal_add (positiveScoreMoment_ne_top _ _) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, positiveScoreMoment,
    ENNReal.toReal_ofReal (pow_nonneg (le_max_right _ _) _)]
  norm_num
  convert admissibleDeficit_secondMoment_le score using 1; ring

theorem expected_admissibleScore_fourth_le (score : ℝ) :
    (∑' answer, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
      positiveScoreMoment (score + if Concrete.signAttemptResultOfOutput answer ≠ none then -1023 else 1) 4) ≤
      positiveScoreMoment score 4 + 6138 * positiveScoreMoment score 2 + 2 ^ 30 := by
  have hchoice (answer : HashOutput) :
      positiveScoreMoment (score + if Concrete.signAttemptResultOfOutput answer ≠ none then -1023 else 1) 4 =
        if Concrete.signAttemptResultOfOutput answer ≠ none then positiveScoreMoment (score - 1023) 4
          else positiveScoreMoment (score + 1) 4 := by split_ifs <;> rfl
  simp_rw [hchoice]
  rw [expected_uniformHashOutput_admissible_choice]
  apply (ENNReal.toReal_le_toReal (by unfold positiveScoreMoment; finiteness)
    (by unfold positiveScoreMoment; finiteness)).mp
  rw [ENNReal.toReal_add (by unfold positiveScoreMoment; finiteness) (by unfold positiveScoreMoment; finiteness),
    ENNReal.toReal_add (by unfold positiveScoreMoment; finiteness) (by finiteness),
    ENNReal.toReal_add (positiveScoreMoment_ne_top _ _) (by unfold positiveScoreMoment; finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, positiveScoreMoment,
    ENNReal.toReal_ofReal (pow_nonneg (le_max_right _ _) _)]
  norm_num
  convert admissibleDeficit_fourthMoment_le score using 1 <;> ring

end SphincsSecurity
