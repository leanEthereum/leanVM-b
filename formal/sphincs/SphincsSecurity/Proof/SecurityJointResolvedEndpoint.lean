import SphincsSecurity.Proof.JointProbeResolvedJointRisk
import SphincsSecurity.Proof.SecurityNativeJointSecretsEndpoint

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation
attribute [local instance] Classical.propDecidable

noncomputable def sampledNativeFtsCompletionRisk (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' otsTable, Pr[= otsTable | sampleOtsHashTable] *
        Pr[fun result => result = none | FtsProbeSimulation.nativeFtsRetainedCompletion adversary parameter otsTable
          (fun coordinate => ftsSecret coordinate.1 coordinate.2.1 coordinate.2.2) q fuel]

theorem sampledNativeJointSecretRisk_le_nativeFts_completion
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (fuel : Nat) :
    sampledNativeJointSecretRisk adversary fuel ≤ sampledNativeFtsCompletionRisk adversary q fuel := by
  unfold sampledNativeJointSecretRisk sampledNativeFtsCompletionRisk
  apply ENNReal.tsum_le_tsum
  intro parameter
  by_cases hparameter : parameter ∈ support sampleParameter
  · apply mul_le_mul' le_rfl
    apply ENNReal.tsum_le_tsum
    intro ftsSecret
    exact mul_le_mul' le_rfl (FtsProbeSimulation.probEvent_sampled_native_joint_le_nativeFts_completion
      adversary q hq parameter hparameter
      (fun coordinate => ftsSecret coordinate.1 coordinate.2.1 coordinate.2.2)
      (FtsProbeSimulation.mem_support_sampleFtsSecrets ftsSecret) fuel)
  · simp [probOutput_eq_zero_of_not_mem_support hparameter]

theorem forgeAdvantage_le_jointResolved_completion_remaining127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    forgeAdvantage scheme adversary ≤
      sampledQueryCharge (fun secretKey cache input => parentStoppedEncodingQueryCharge secretKey cache input +
        ftsParentQueryCharge secretKey cache input) adversary * (Fintype.card Digest : ENNReal)⁻¹ +
      sampledNativeFtsCompletionRisk adversary q fuel +
      ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
        (q : ENNReal) * (15 * ((2 ^ 132 : Nat) : ENNReal)⁻¹)) :=
  (forgeAdvantage_le_native_joint_secret_risk_remaining127 adversary q hqPos hq hqMax fuel).trans
    (add_le_add (add_le_add le_rfl (sampledNativeJointSecretRisk_le_nativeFts_completion adversary q hq fuel)) le_rfl)

end SphincsSecurity.Concrete
