import SphincsSecurity.Proof.StoppedParentGame
import SphincsSecurity.Proof.SecurityJointNonSecretEndpoint

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal
open OtsProbeSimulation

theorem forgeAdvantage_le_preParentCharge_add_nativeFts_remaining127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    forgeAdvantage scheme adversary ≤
      sampledPreParentQueryCharge (fun secretKey cache input => parentStoppedEncodingQueryCharge secretKey cache input +
        ftsParentQueryCharge secretKey cache input) adversary * (Fintype.card Digest : ENNReal)⁻¹ +
      (sampledNativeFtsOtsFailureRisk adversary q fuel + sampledJointRetainedFtsHitRisk adversary q) +
      ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
        (q : ENNReal) * (15 * ((2 ^ 132 : Nat) : ENNReal)⁻¹)) := by
  apply (forgeAdvantage_le_preParentQueryCharge_add_secret_allowance adversary _
    (probEvent_sampledFirstParentOrSecretWitness_le_native_joint adversary fuel)).trans
  exact add_le_add (add_le_add le_rfl
    ((sampledNativeJointSecretRisk_le_nativeFts_completion adversary q hq fuel).trans
      (sampledNativeFtsCompletionRisk_le_ots_add_fts_hit adversary q fuel)))
    (probEvent_sampled_messageOrForest_le127 adversary q hqPos hq hqMax)

theorem forgeAdvantage_add_nonSecret_reserve_le_preParent_remaining127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary +
      sampledJointNonSecretQueryCharge adversary q * (Fintype.card Digest : ENNReal)⁻¹ ≤
      sampledPreParentQueryCharge (fun secretKey cache input => parentStoppedEncodingQueryCharge secretKey cache input +
        ftsParentQueryCharge secretKey cache input) adversary * (Fintype.card Digest : ENNReal)⁻¹ +
      ((q : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ + (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal)) +
      ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
        (q : ENNReal) * (15 * ((2 ^ 132 : Nat) : ENNReal)⁻¹)) := by
  have hspace : q + 1 < Fintype.card Digest := by
    have hcard : Fintype.card Digest = 2 ^ 128 := by
      rw [show Fintype.card Digest = 2 ^ digestBits from card_bitVec digestBits]
      rfl
    rw [hcard]
    omega
  apply (add_le_add (forgeAdvantage_le_preParentCharge_add_nativeFts_remaining127 adversary q hqPos hq hqMax (q + 1)) le_rfl).trans
  calc
    _ = sampledPreParentQueryCharge (fun secretKey cache input => parentStoppedEncodingQueryCharge secretKey cache input +
          ftsParentQueryCharge secretKey cache input) adversary * (Fintype.card Digest : ENNReal)⁻¹ +
        ((sampledNativeFtsOtsFailureRisk adversary q (q + 1) + sampledJointRetainedFtsHitRisk adversary q) +
          sampledJointNonSecretQueryCharge adversary q * (Fintype.card Digest : ENNReal)⁻¹) +
        ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
          (q : ENNReal) * (15 * ((2 ^ 132 : Nat) : ENNReal)⁻¹)) := by ac_rfl
    _ ≤ _ := add_le_add (add_le_add le_rfl
      (sampledNativeFtsOtsFailure_add_fts_hit_add_nonSecret_le_query_rate adversary q (q + 1) (by omega) hspace)) le_rfl

end SphincsSecurity.Concrete
