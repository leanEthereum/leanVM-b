import SphincsSecurity.Proof.JointPrimitiveQueryBudget
import SphincsSecurity.Proof.FewTime126Bound
import SphincsSecurity.Proof.MessageCollision125

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

theorem concrete126_budget (q : Nat) :
    ((3 * q : Nat) : ℝ≥0∞) * ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ +
      ((q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹ +
        ((27 * q : Nat) : ℝ≥0∞) * ((2 ^ 133 : Nat) : ℝ≥0∞)⁻¹) ≤
      (q : ℝ≥0∞) / ((2 ^ 126 : Nat) : ℝ≥0∞) := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  repeat rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    Nat.cast_mul, Nat.cast_ofNat]
  norm_num
  have hq : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  linarith

theorem forgeAdvantage_le_sampled_jointPrimitive_add_remaining126
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126) :
    forgeAdvantage scheme adversary ≤
      Pr[SampledViewedEvent jointPrimitiveEvent | sampledViewedGame adversary] +
      ((q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹ +
        ((27 * q : Nat) : ℝ≥0∞) * ((2 ^ 133 : Nat) : ℝ≥0∞)⁻¹) := by
  let remaining := (q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹ +
    ((27 * q : Nat) : ℝ≥0∞) * ((2 ^ 133 : Nat) : ℝ≥0∞)⁻¹
  let risk := fun secrets : SampledSecrets =>
    Pr[jointPrimitiveEvent secrets.parameter secrets.otsSecret secrets.ftsSecret |
      gameAfterSecretsWithViewTrace adversary secrets.parameter secrets.otsSecret secrets.ftsSecret]
  rw [forgeAdvantage_eq_sampledGame, sampledGame]
  calc
    _ ≤ remaining + ∑' secrets : SampledSecrets, Pr[= secrets | sampleSecrets] * risk secrets := by
      rw [← probEvent_eq_eq_probOutput]
      apply probEvent_bind_le_const_add_weighted (oa := sampleSecrets)
        (run := fun secrets => (simulateQ romImpl
          (gameAfterSecrets adversary secrets.parameter secrets.otsSecret secrets.ftsSecret)).run' ∅)
        (event := fun verdict => verdict = true) (cost := remaining) risk
      intro secrets hsecrets
      obtain ⟨hparameter, hots, hfts⟩ := secrets.support_components hsecrets
      rw [probEvent_eq_eq_probOutput]
      have hforest := probEvent_gameAfterSecretsWithViewTrace_honest_leak_le_twenty_seven_mul_inv133
        adversary q hqPos hq hqMax secrets.parameter hparameter secrets.otsSecret hots
          secrets.ftsSecret hfts
      have hmessage : Pr[cleanMessageEvent secrets.parameter secrets.otsSecret secrets.ftsSecret |
          gameAfterSecretsWithViewTrace adversary secrets.parameter secrets.otsSecret secrets.ftsSecret] ≤
            (q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹ := by
        apply le_trans (probEvent_mono fun _ _ event => event.2)
        exact Range125.probEvent_gameAfterSecretsWithViewTrace_messageCollision_le_inv
          adversary q hqPos hq hqMax secrets.parameter hparameter secrets.otsSecret hots
            secrets.ftsSecret hfts
      exact (probEvent_win_le_jointPrimitive_add_message_add_forest adversary secrets.parameter
        secrets.otsSecret secrets.ftsSecret).trans
          ((add_le_add le_rfl (add_le_add hmessage hforest)).trans_eq (add_comm _ _))
    _ = _ := by
      rw [probEvent_sampledViewedGame_eq_weighted]
      exact add_comm _ _

/-- Conditional assembly: the joint primitive bound is still required. -/
theorem security126_of_sampled_jointPrimitive_le_three_mul
    (hprimitive : ∀ (q : Nat), 1 ≤ q → ∀ adversary : Adversary,
      HasHashQueryBound scheme adversary q → q ≤ 2 ^ 126 →
        Pr[SampledViewedEvent jointPrimitiveEvent | sampledViewedGame adversary] ≤
          ((3 * q : Nat) : ℝ≥0∞) * ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹) :
    HasClassicalSecurityBits scheme 126 := by
  intro q hqPos adversary hq
  by_cases hqMax : q ≤ 2 ^ 126
  · exact (forgeAdvantage_le_sampled_jointPrimitive_add_remaining126 adversary q hqPos hq hqMax).trans
      ((add_le_add (hprimitive q hqPos adversary hq hqMax) le_rfl).trans (concrete126_budget q))
  · apply probOutput_le_one.trans
    rw [div_eq_mul_inv]
    have hcast : ((2 ^ 126 : Nat) : ℝ≥0∞) ≤ (q : ℝ≥0∞) := by
      exact_mod_cast (show 2 ^ 126 ≤ q by omega)
    calc
      (1 : ℝ≥0∞) = ((2 ^ 126 : Nat) : ℝ≥0∞) * ((2 ^ 126 : Nat) : ℝ≥0∞)⁻¹ := by
        rw [ENNReal.mul_inv_cancel]
        · norm_num
        · finiteness
      _ ≤ _ := mul_le_mul' hcast le_rfl


/-- The residual estimate is an explicit remaining premise. -/
theorem security126_of_sampled_residual_le_queryCharge
    (hresidual : ∀ (q : Nat), 1 ≤ q → ∀ adversary : Adversary,
      HasHashQueryBound scheme adversary q → q ≤ 2 ^ 126 →
        Pr[SampledViewedEvent residualPrimitiveEvent | sampledViewedGame adversary] ≤
          sampledQueryCharge residualPrimitiveQueryCharge adversary *
            (Fintype.card Digest : ℝ≥0∞)⁻¹) :
    HasClassicalSecurityBits scheme 126 := by
  apply security126_of_sampled_jointPrimitive_le_three_mul
  intro q hqPos adversary hq hqMax
  exact probEvent_sampled_jointPrimitive_le_three_mul_of_residual adversary q hq
    (hresidual q hqPos adversary hq hqMax)

end SphincsSecurity.Concrete
