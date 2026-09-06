import SphincsSecurity.Proof.FewTimeOccupancyCount
import SphincsSecurity.Proof.JointNativeQueryCharge

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

theorem forgeAdvantage_le_sampled_jointPrimitive_add_occupancy_remaining
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126) :
    forgeAdvantage scheme adversary ≤
      Pr[SampledViewedEvent jointPrimitiveEvent | sampledViewedGame adversary] +
      ((q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹ +
        ((23 * q : Nat) : ℝ≥0∞) * ((2 ^ 134 : Nat) : ℝ≥0∞)⁻¹) := by
  let remaining := (q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹ +
    ((23 * q : Nat) : ℝ≥0∞) * ((2 ^ 134 : Nat) : ℝ≥0∞)⁻¹
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
      have hforest := probEvent_gameAfterSecretsWithViewTrace_honest_leak_le_twenty_three_mul_inv134
        adversary q hq hqMax secrets.parameter hparameter secrets.otsSecret hots
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

theorem forgeAdvantage_le_nativeQueryCharge_add_occupancy_remaining
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126) :
    forgeAdvantage scheme adversary ≤
      (sampledQueryCharge jointNativeQueryCharge adversary * (Fintype.card Digest : ENNReal)⁻¹ +
        (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹) +
      ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
        ((23 * q : Nat) : ENNReal) * ((2 ^ 134 : Nat) : ENNReal)⁻¹) :=
  (forgeAdvantage_le_sampled_jointPrimitive_add_occupancy_remaining adversary q hqPos hq hqMax).trans
    (add_le_add (probEvent_sampled_jointPrimitive_le_nativeQueryCharge_add_erasure adversary q hq hqMax) le_rfl)

end SphincsSecurity.Concrete
