import SphincsSecurity.Proof.JointProbeNonSecretStructuralBudget
import SphincsSecurity.Proof.SecurityJointMaterializedBoundEndpoint

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

theorem sampledNativeFtsOtsFailure_add_fts_hit_add_nonSecret_le_query_rate
    (adversary : Adversary) (q fuel : Nat) (hbudget : q < fuel) (hspace : fuel < Fintype.card Digest) :
    (sampledNativeFtsOtsFailureRisk adversary q fuel + sampledJointRetainedFtsHitRisk adversary q) +
      sampledJointNonSecretQueryCharge adversary q * (Fintype.card Digest : ENNReal)⁻¹ ≤
      (q : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ + (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) := by
  have hfailure := (sampledNativeFtsOtsFailureRisk_le_direct_add_materialized adversary q fuel hbudget hspace).trans
    (add_le_add (sampledNativeFtsDirectRisk_le_cost Finset.univ adversary fuel q (hbudget.trans hspace).le)
      (sampledNativeFtsMaterializedProbeRisk_le_inv216 adversary q fuel))
  calc
    _ ≤ (sampledNativeFtsOtsCharge adversary q * (Fintype.card Digest : ENNReal)⁻¹ +
          (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) + sampledJointRetainedFtsHitRisk adversary q) +
          sampledJointNonSecretQueryCharge adversary q * (Fintype.card Digest : ENNReal)⁻¹ :=
      add_le_add (add_le_add hfailure le_rfl) le_rfl
    _ = ((sampledNativeFtsOtsCharge adversary q + sampledJointNonSecretQueryCharge adversary q) *
          (Fintype.card Digest : ENNReal)⁻¹ + sampledJointRetainedFtsHitRisk adversary q) +
          (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) := by ring
    _ ≤ _ := add_le_add (sampledNativeFtsOts_add_nonSecret_add_fts_hit_le_query_rate adversary q) le_rfl

theorem forgeAdvantage_add_nonSecret_reserve_le_remaining127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary +
      sampledJointNonSecretQueryCharge adversary q * (Fintype.card Digest : ENNReal)⁻¹ ≤
      sampledQueryCharge (fun secretKey cache input => parentStoppedEncodingQueryCharge secretKey cache input +
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
  apply (add_le_add (forgeAdvantage_le_nativeFts_ots_add_fts_remaining127 adversary q hqPos hq hqMax (q + 1)) le_rfl).trans
  calc
    _ = sampledQueryCharge (fun secretKey cache input => parentStoppedEncodingQueryCharge secretKey cache input +
          ftsParentQueryCharge secretKey cache input) adversary * (Fintype.card Digest : ENNReal)⁻¹ +
        ((sampledNativeFtsOtsFailureRisk adversary q (q + 1) + sampledJointRetainedFtsHitRisk adversary q) +
          sampledJointNonSecretQueryCharge adversary q * (Fintype.card Digest : ENNReal)⁻¹) +
        ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
          (q : ENNReal) * (15 * ((2 ^ 132 : Nat) : ENNReal)⁻¹)) := by ac_rfl
    _ ≤ _ := add_le_add (add_le_add le_rfl
      (sampledNativeFtsOtsFailure_add_fts_hit_add_nonSecret_le_query_rate adversary q (q + 1) (by omega) hspace)) le_rfl

end SphincsSecurity.Concrete
