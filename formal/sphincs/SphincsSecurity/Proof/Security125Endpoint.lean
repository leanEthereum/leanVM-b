import SphincsSecurity.Proof.JointTerminalSampling
import SphincsSecurity.Proof.MessageCollision125
import SphincsSecurity.Proof.FtsProbeSampling

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

theorem forgeAdvantage_le_opening_add_concrete125
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 125) :
    forgeAdvantage scheme adversary ≤
      Pr[SampledViewedEvent cleanOtsOpeningEvent | sampledViewedGame adversary] +
      ((4 * q : Nat) : ℝ≥0∞) * ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ +
      ((3 * q : Nat) : ℝ≥0∞) * ((2 ^ 131 : Nat) : ℝ≥0∞)⁻¹ +
      (q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹ := by
  have hmessage := Range125.probEvent_sampled_cleanMessage_le adversary q hqPos hq hqMax
  have huncovered := FtsProbeSimulation.probEvent_sampledViewedGame_cleanUncovered_le
    adversary q hq
  change Pr[SampledViewedEvent cleanUncoveredEvent | sampledViewedGame adversary] ≤
    (q : ℝ≥0∞) * ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ at huncovered
  refine (forgeAdvantage_le_joint_reserved_add_sampled_remaining adversary q hqPos hq hqMax).trans ?_
  calc
    _ ≤ ((3 * q : Nat) : ℝ≥0∞) * ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ +
        ((3 * q : Nat) : ℝ≥0∞) * ((2 ^ 131 : Nat) : ℝ≥0∞)⁻¹ +
        (Pr[SampledViewedEvent cleanOtsOpeningEvent | sampledViewedGame adversary] +
        ((q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹ +
          (q : ℝ≥0∞) * ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹)) :=
      add_le_add le_rfl (add_le_add le_rfl (add_le_add hmessage huncovered))
    _ = _ := by push_cast; ring

theorem concrete125_budget (q : Nat) :
    ((7 * q : Nat) : ℝ≥0∞) * ((2 ^ 129 : Nat) : ℝ≥0∞)⁻¹ +
      ((4 * q : Nat) : ℝ≥0∞) * ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ +
      ((3 * q : Nat) : ℝ≥0∞) * ((2 ^ 131 : Nat) : ℝ≥0∞)⁻¹ +
      (q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹ ≤
      (q : ℝ≥0∞) / ((2 ^ 125 : Nat) : ℝ≥0∞) := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  repeat rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_natCast, Nat.cast_mul,
    Nat.cast_ofNat]
  norm_num
  have hq : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  linarith

/-- Assembly only: the sampled one-time opening estimate remains an explicit premise. -/
theorem security125_of_sampledOpening_le_seven_mul_inv129
    (hopening : ∀ (q : Nat), 1 ≤ q → ∀ adversary : Adversary,
      HasHashQueryBound scheme adversary q → q ≤ 2 ^ 125 →
      Pr[SampledViewedEvent cleanOtsOpeningEvent | sampledViewedGame adversary] ≤
        ((7 * q : Nat) : ℝ≥0∞) * ((2 ^ 129 : Nat) : ℝ≥0∞)⁻¹) :
    HasClassicalSecurityBits scheme 125 := by
  intro q hqPos adversary hq
  by_cases hqMax : q ≤ 2 ^ 125
  · refine (forgeAdvantage_le_opening_add_concrete125 adversary q hqPos hq hqMax).trans ?_
    calc
      _ ≤ ((7 * q : Nat) : ℝ≥0∞) * ((2 ^ 129 : Nat) : ℝ≥0∞)⁻¹ +
          ((4 * q : Nat) : ℝ≥0∞) * ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ +
          ((3 * q : Nat) : ℝ≥0∞) * ((2 ^ 131 : Nat) : ℝ≥0∞)⁻¹ +
          (q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹ :=
        add_le_add (add_le_add (add_le_add (hopening q hqPos adversary hq hqMax) le_rfl)
          le_rfl) le_rfl
      _ ≤ _ := concrete125_budget q
  · apply probOutput_le_one.trans
    rw [div_eq_mul_inv]
    have hcast : ((2 ^ 125 : Nat) : ℝ≥0∞) ≤ (q : ℝ≥0∞) := by
      exact_mod_cast (show 2 ^ 125 ≤ q by omega)
    calc
      (1 : ℝ≥0∞) = ((2 ^ 125 : Nat) : ℝ≥0∞) *
          ((2 ^ 125 : Nat) : ℝ≥0∞)⁻¹ := by
        rw [ENNReal.mul_inv_cancel]
        · norm_num
        · finiteness
      _ ≤ _ := mul_le_mul' hcast le_rfl

/-- The remaining opening bound can be supplied through the existing retained-verifier coupling. -/
theorem security125_of_sampledVerifyProbe_le_seven_mul_inv129
    (hprobe : ∀ (q : Nat), 1 ≤ q → ∀ adversary : Adversary,
      HasHashQueryBound scheme adversary q → q ≤ 2 ^ 125 →
      ∀ parameter ∈ support sampleParameter,
      ∀ ftsSecret ∈ support sampleFtsSecrets,
        Pr[fun result => OtsProbeSimulation.WinningRetainedVerifyProbeWitness parameter
            (OtsProbeSimulation.extendStartTable result.1) ftsSecret result.2 |
          OtsProbeSimulation.sampledActualRetainedOtsHashTable adversary parameter ftsSecret] ≤
          ((7 * q : Nat) : ℝ≥0∞) * ((2 ^ 129 : Nat) : ℝ≥0∞)⁻¹) :
    HasClassicalSecurityBits scheme 125 := by
  apply security125_of_sampledOpening_le_seven_mul_inv129
  intro q hqPos adversary hq hqMax
  apply OtsProbeSimulation.probEvent_sampledViewedGame_cleanOtsOpening_le_of_sampled
  intro parameter hparameter ftsSecret hfts
  exact hprobe q hqPos adversary hq hqMax parameter hparameter ftsSecret hfts

end SphincsSecurity.Concrete
