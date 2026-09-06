import SphincsSecurity.Proof.VerifierPrimitiveTerminal
import SphincsSecurity.Proof.SecurityOccupancyEndpoint

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

theorem forgeAdvantage_le_sampled_verifierPrimitive_add_occupancy_remaining
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126) :
    forgeAdvantage scheme adversary ≤
      Pr[SampledViewedEvent verifierPrimitiveEvent | sampledViewedGame adversary] +
      ((q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹ +
        ((23 * q : Nat) : ℝ≥0∞) * ((2 ^ 134 : Nat) : ℝ≥0∞)⁻¹) := by
  let remaining := (q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹ +
    ((23 * q : Nat) : ℝ≥0∞) * ((2 ^ 134 : Nat) : ℝ≥0∞)⁻¹
  let risk := fun secrets : SampledSecrets =>
    Pr[verifierPrimitiveEvent secrets.parameter secrets.otsSecret secrets.ftsSecret |
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
      have hmessage : Pr[ViewedMessageDigestCollisionWitness secrets.parameter secrets.otsSecret secrets.ftsSecret |
          gameAfterSecretsWithViewTrace adversary secrets.parameter secrets.otsSecret secrets.ftsSecret] ≤
            (q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹ := by
        exact Range125.probEvent_gameAfterSecretsWithViewTrace_messageCollision_le_inv
          adversary q hqPos hq hqMax secrets.parameter hparameter secrets.otsSecret hots
            secrets.ftsSecret hfts
      exact (probEvent_win_le_verifierPrimitive_add_message_add_forest adversary secrets.parameter
        secrets.otsSecret secrets.ftsSecret).trans
          ((add_le_add le_rfl (add_le_add hmessage hforest)).trans_eq (add_comm _ _))
    _ = _ := by
      rw [probEvent_sampledViewedGame_eq_weighted]
      exact add_comm _ _

theorem probEvent_sampled_verifierPrimitive_le_nativeQueryCharge_add_erasure
    (adversary : Adversary) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126) :
    Pr[SampledViewedEvent verifierPrimitiveEvent | sampledViewedGame adversary] ≤
      sampledQueryCharge jointNativeQueryCharge adversary * (Fintype.card Digest : ENNReal)⁻¹ +
        (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  apply (probEvent_mono (q := SampledViewedEvent jointPrimitiveEvent) ?_).trans
    (probEvent_sampled_jointPrimitive_le_nativeQueryCharge_add_erasure adversary q hq hqMax)
  intro result _ hevent
  exact verifierPrimitiveEvent_implies_jointPrimitiveEvent result.secrets.parameter
    result.secrets.otsSecret result.secrets.ftsSecret result.result hevent

end SphincsSecurity.Concrete
