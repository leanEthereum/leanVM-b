import SphincsSecurity.Proof.SecurityCollisionBeforeFailure
import SphincsSecurity.Proof.SecuritySettledAllocation

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem forgeAdvantage_add_executionReserves_remainder_gap_le_collisionEnvelope
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary + (sampledUnusedExecutionReserve adversary q (q + 1) +
      (sampledStoppedIndexRemainder adversary q (q + 1) + sampledStoppedSigningGap adversary q (q + 1))) ≤
      sampledParentSharedFailureRisk adversary q (q + 1) +
      sampledBeforeFailureCollisionBaseCharge adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹ +
      (q : ENNReal) * (1 / 64) * (Fintype.card Digest : ENNReal)⁻¹ + (q : ENNReal) * initialRawIndexRate q := by
  have hbase := (forgeAdvantage_le_sharedFailure_add_beforeFailureCollisionBase127 adversary q hq hqMax (q + 1)).trans
    (add_le_add le_rfl (sampledLiveNonSecretResidual_le_stopped_arrival adversary q hq hqMax (q + 1)))
  apply (add_le_add hbase le_rfl).trans
  rw [add_assoc]
  exact add_le_add le_rfl (sampledStoppedTargetCharge_add_executionReserve_remainder_gap_le_initial adversary q hq hqMax (q + 1))

theorem forgeAdvantage_add_nonSecret_executionReserves_remainder_gap_le_collisionEnvelope
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary + sampledJointNonSecretQueryCharge adversary q * (Fintype.card Digest : ENNReal)⁻¹ +
      (sampledUnusedExecutionReserve adversary q (q + 1) +
        (sampledStoppedIndexRemainder adversary q (q + 1) + sampledStoppedSigningGap adversary q (q + 1))) ≤
      (sampledBeforeFailureCollisionBaseCharge adversary q (q + 1) + (q : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ +
      (q : ENNReal) * (1 / 64) * (Fintype.card Digest : ENNReal)⁻¹ +
      (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) + (q : ENNReal) * initialRawIndexRate q := by
  have hspace : q + 1 < Fintype.card Digest := by
    rw [show Fintype.card Digest = 2 ^ 128 from card_bitVec digestBits]
    omega
  have hshared : sampledParentSharedFailureRisk adversary q (q + 1) +
      sampledJointNonSecretQueryCharge adversary q * (Fintype.card Digest : ENNReal)⁻¹ ≤
      (q : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ + (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) :=
    (add_le_add ((sampledParentSharedFailureRisk_le_nativeCompletion adversary q (q + 1)).trans
      (sampledNativeFtsCompletionRisk_le_ots_add_fts_hit adversary q (q + 1))) le_rfl).trans
      (sampledNativeFtsOtsFailure_add_fts_hit_add_nonSecret_le_query_rate adversary q (q + 1) (by omega) hspace)
  have hbase := add_le_add (forgeAdvantage_add_executionReserves_remainder_gap_le_collisionEnvelope adversary q hq hqMax)
    (le_refl (sampledJointNonSecretQueryCharge adversary q * (Fintype.card Digest : ENNReal)⁻¹))
  calc
    _ = (forgeAdvantage scheme adversary + (sampledUnusedExecutionReserve adversary q (q + 1) +
        (sampledStoppedIndexRemainder adversary q (q + 1) + sampledStoppedSigningGap adversary q (q + 1)))) +
        sampledJointNonSecretQueryCharge adversary q * (Fintype.card Digest : ENNReal)⁻¹ := by ac_rfl
    _ ≤ _ := hbase
    _ = (sampledParentSharedFailureRisk adversary q (q + 1) +
        sampledJointNonSecretQueryCharge adversary q * (Fintype.card Digest : ENNReal)⁻¹) +
        (sampledBeforeFailureCollisionBaseCharge adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹ +
          (q : ENNReal) * (1 / 64) * (Fintype.card Digest : ENNReal)⁻¹ + (q : ENNReal) * initialRawIndexRate q) := by ac_rfl
    _ ≤ _ := add_le_add hshared le_rfl
    _ = _ := by simp only [add_mul]; ac_rfl

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
