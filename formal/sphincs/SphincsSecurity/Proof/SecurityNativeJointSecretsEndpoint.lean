import SphincsSecurity.Proof.RetainedJointSecretProjection
import SphincsSecurity.Proof.SecuritySharedTargetsEndpoint

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation

theorem probEvent_sampled_messageOrForest_le127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    Pr[SampledViewedEvent messageOrForestEvent | sampledViewedGame adversary] ≤
      (q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
        (q : ENNReal) * (15 * ((2 ^ 132 : Nat) : ENNReal)⁻¹) := by
  change Pr[fun result => SampledViewedEvent cleanMessageEvent result ∨
    SampledViewedEvent ViewedHonestProperFewTimeLeakWitness result | sampledViewedGame adversary] ≤ _
  exact (probEvent_or_le _ _ _).trans (add_le_add
    (probEvent_sampled_cleanMessage_le127 adversary q hqPos hq hqMax)
    (probEvent_sampled_honest_leak_le_sharedTargetBudget adversary q hq hqMax))

theorem forgeAdvantage_le_native_joint_secret_risk_remaining127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    forgeAdvantage scheme adversary ≤
      sampledQueryCharge (fun secretKey cache input => parentStoppedEncodingQueryCharge secretKey cache input +
        ftsParentQueryCharge secretKey cache input) adversary * (Fintype.card Digest : ENNReal)⁻¹ +
      sampledNativeJointSecretRisk adversary fuel +
      ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
        (q : ENNReal) * (15 * ((2 ^ 132 : Nat) : ENNReal)⁻¹)) := by
  apply (forgeAdvantage_le_answerEncodingQueryCharge_add_first_parent_residual adversary).trans
  apply (add_le_add le_rfl (probEvent_firstParentEncodingResidual_le_secret_allowance adversary _
    (probEvent_sampledFirstParentOrSecretWitness_le_native_joint adversary fuel))).trans
  apply (add_le_add le_rfl (add_le_add le_rfl (add_le_add le_rfl
    (probEvent_sampled_messageOrForest_le127 adversary q hqPos hq hqMax)))).trans_eq
  rw [sampledQueryCharge_add]
  simp only [show Fintype.card Digest = 2 ^ digestBits by simp]
  ring

theorem forgeAdvantage_le_native_joint_secrets_remaining127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    forgeAdvantage scheme adversary ≤
      sampledQueryCharge (fun secretKey cache input => parentStoppedEncodingQueryCharge secretKey cache input +
        ftsParentQueryCharge secretKey cache input) adversary * (Fintype.card Digest : ENNReal)⁻¹ +
      Pr[fun verdict => verdict = true | sampledNativeTerminalFailure adversary fuel] +
      sampledNativeFtsWitnessRisk adversary fuel +
      ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
        (q : ENNReal) * (15 * ((2 ^ 132 : Nat) : ENNReal)⁻¹)) := by
  apply (forgeAdvantage_le_answerEncodingQueryCharge_add_first_parent_residual adversary).trans
  apply (add_le_add le_rfl (probEvent_firstParentEncodingResidual_le_secret_allowance adversary _
    (probEvent_sampledFirstParentOrSecretWitness_le_native_failure_add_fts adversary fuel))).trans
  apply (add_le_add le_rfl (add_le_add le_rfl (add_le_add le_rfl
    (probEvent_sampled_messageOrForest_le127 adversary q hqPos hq hqMax)))).trans_eq
  rw [sampledQueryCharge_add]
  simp only [show Fintype.card Digest = 2 ^ digestBits by simp]
  ring

theorem forgeAdvantage_le_sharedHistory_add_nativeFts_remaining127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary ≤
      sampledQueryCharge (fun secretKey cache input => parentStoppedEncodingQueryCharge secretKey cache input +
        ftsParentQueryCharge secretKey cache input) adversary * (Fintype.card Digest : ENNReal)⁻¹ +
      min (sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary * privateHistoryGuessRate q)
        ((sampledNativeHistoryStartCharge Finset.univ adversary q +
          sampledNativeHistoryPrivateCharge Finset.univ adversary q) * (Fintype.card Digest : ENNReal)⁻¹) +
      sampledNativeFtsWitnessRisk adversary (q + 1) +
      (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ +
      ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
        (q : ENNReal) * (15 * ((2 ^ 132 : Nat) : ENNReal)⁻¹)) := by
  have hspace : q + 1 < Fintype.card Digest := by
    have : 2 ^ 127 + 1 < Fintype.card Digest := by norm_num [digestBits]
    omega
  have hfailure := sampledNativeTerminalRisk_le_min_sharedHistory adversary q hq hspace
  rw [← probEvent_sampledNativeTerminalFailure_eq_risk] at hfailure
  apply (forgeAdvantage_le_native_joint_secrets_remaining127 adversary q hqPos hq hqMax (q + 1)).trans
  apply (add_le_add (add_le_add (add_le_add le_rfl hfailure) le_rfl) le_rfl).trans_eq
  ring

end SphincsSecurity.Concrete
