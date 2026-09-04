import SphincsSecurity.Proof.JointTerminalBounds

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

noncomputable def jointRemainingRisk (adversary : Adversary)
    (secrets : SampledSecrets) : ℝ≥0∞ :=
  let run := gameAfterSecretsWithViewTrace adversary secrets.parameter secrets.otsSecret
    secrets.ftsSecret
  Pr[cleanOtsOpeningEvent secrets.parameter secrets.otsSecret secrets.ftsSecret | run] +
    (Pr[cleanMessageEvent secrets.parameter secrets.otsSecret secrets.ftsSecret | run] +
      Pr[cleanUncoveredEvent secrets.parameter secrets.otsSecret secrets.ftsSecret | run])

theorem weighted_jointRemainingRisk_eq (adversary : Adversary) :
    (∑' secrets : SampledSecrets,
      Pr[= secrets | sampleSecrets] * jointRemainingRisk adversary secrets) =
      Pr[SampledViewedEvent cleanOtsOpeningEvent | sampledViewedGame adversary] +
      (Pr[SampledViewedEvent cleanMessageEvent | sampledViewedGame adversary] +
        Pr[SampledViewedEvent cleanUncoveredEvent | sampledViewedGame adversary]) := by
  simp only [jointRemainingRisk, mul_add, ENNReal.tsum_add]
  rw [← probEvent_sampledViewedGame_eq_weighted adversary cleanOtsOpeningEvent,
    ← probEvent_sampledViewedGame_eq_weighted adversary cleanMessageEvent,
    ← probEvent_sampledViewedGame_eq_weighted adversary cleanUncoveredEvent]

theorem forgeAdvantage_le_joint_reserved_add_sampled_remaining
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q)
    (hqMax : q ≤ 2 ^ 125) :
    forgeAdvantage scheme adversary ≤
      ((3 * q : Nat) : ℝ≥0∞) * ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ +
      ((3 * q : Nat) : ℝ≥0∞) * ((2 ^ 131 : Nat) : ℝ≥0∞)⁻¹ +
      (Pr[SampledViewedEvent cleanOtsOpeningEvent | sampledViewedGame adversary] +
      (Pr[SampledViewedEvent cleanMessageEvent | sampledViewedGame adversary] +
        Pr[SampledViewedEvent cleanUncoveredEvent | sampledViewedGame adversary])) := by
  rw [forgeAdvantage_eq_sampledGame, sampledGame]
  calc
    _ ≤ ((3 * q : Nat) : ℝ≥0∞) * ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ +
        ((3 * q : Nat) : ℝ≥0∞) * ((2 ^ 131 : Nat) : ℝ≥0∞)⁻¹ +
        ∑' secrets : SampledSecrets,
          Pr[= secrets | sampleSecrets] * jointRemainingRisk adversary secrets := by
      rw [← probEvent_eq_eq_probOutput]
      apply probEvent_bind_le_const_add_weighted
        (oa := sampleSecrets)
        (run := fun secrets => (simulateQ romImpl
          (gameAfterSecrets adversary secrets.parameter secrets.otsSecret
            secrets.ftsSecret)).run' ∅)
        (event := fun verdict => verdict = true)
        (cost := ((3 * q : Nat) : ℝ≥0∞) * ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ +
          ((3 * q : Nat) : ℝ≥0∞) * ((2 ^ 131 : Nat) : ℝ≥0∞)⁻¹)
        (jointRemainingRisk adversary)
      intro secrets hsecrets
      obtain ⟨hparameter, hots, hfts⟩ := secrets.support_components hsecrets
      rw [probEvent_eq_eq_probOutput]
      exact probEvent_win_le_joint_reserved_add_remaining adversary q hqPos hq hqMax
        secrets.parameter hparameter secrets.otsSecret hots secrets.ftsSecret hfts
    _ = _ := by rw [weighted_jointRemainingRisk_eq]

end SphincsSecurity.Concrete
