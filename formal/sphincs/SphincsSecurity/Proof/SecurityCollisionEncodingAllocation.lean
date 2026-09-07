import SphincsSecurity.Proof.SampledCollisionEncodingReserve
import SphincsSecurity.Proof.SecurityStructuralTerminalReserve
import SphincsSecurity.Proof.SecuritySigningGap

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem forgeAdvantage_add_message_signing_encodingReserves_le_collision_live
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary +
      (sampledSelectedJointQueryCharge MessageHashInput adversary q + sampledBeforeFailureHashCharge messageHashCharge adversary q (q + 1) +
        sampledSigningNonEncodingReserve adversary q (q + 1) + sampledOuterEncodingReserve adversary q (q + 1)) * (Fintype.card Digest : ENNReal)⁻¹ ≤
      (sampledBeforeFailureRestHashCharge adversary q (q + 1) + (q : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ +
      (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) +
      sampledBeforeFailureEncodingPairCharge adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹ + sampledLiveNonSecretResidual adversary q (q + 1) := by
  have hspace : q + 1 < Fintype.card Digest := by
    have hcard : Fintype.card Digest = 2 ^ 128 := by
      rw [show Fintype.card Digest = 2 ^ digestBits from card_bitVec digestBits]
      rfl
    rw [hcard]
    omega
  have hshared := (add_le_add ((sampledParentSharedFailureRisk_le_nativeCompletion adversary q (q + 1)).trans
    (sampledNativeFtsCompletionRisk_le_ots_add_fts_hit adversary q (q + 1))) le_rfl).trans
      (sampledNativeFtsOtsFailure_add_fts_hit_add_nonSecret_le_query_rate adversary q (q + 1) (by omega) hspace)
  have hstructural := (sampledBeforeFailureCollisionBase_add_signingNonEncoding_add_encoding_le adversary q (q + 1)).trans
    (add_le_add le_rfl (sampledBeforeFailureSelectedCharge_le_erased NonMessageNonSecretHashInput adversary q (q + 1)))
  have hbound : forgeAdvantage scheme adversary +
      (sampledSigningNonEncodingReserve adversary q (q + 1) + sampledOuterEncodingReserve adversary q (q + 1) + sampledJointNonSecretQueryCharge adversary q) * (Fintype.card Digest : ENNReal)⁻¹ ≤
      (sampledBeforeFailureHashCharge nonMessageHashCharge adversary q (q + 1) + sampledSelectedJointQueryCharge NonMessageNonSecretHashInput adversary q) *
          (Fintype.card Digest : ENNReal)⁻¹ +
        ((q : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ + (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal)) +
        sampledBeforeFailureEncodingPairCharge adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹ +
        sampledLiveNonSecretResidual adversary q (q + 1) := by
    have hcollision := forgeAdvantage_le_sharedFailure_add_collisionCharge_add_live_residual adversary q hq (q + 1)
    rw [sampledBeforeFailureCollisionCharge_eq_base_add_pairs, add_mul] at hcollision
    apply (add_le_add hcollision le_rfl).trans
    calc
      _ = (sampledBeforeFailureCollisionBaseCharge adversary q (q + 1) + sampledSigningNonEncodingReserve adversary q (q + 1) + sampledOuterEncodingReserve adversary q (q + 1)) *
            (Fintype.card Digest : ENNReal)⁻¹ +
          (sampledParentSharedFailureRisk adversary q (q + 1) + sampledJointNonSecretQueryCharge adversary q * (Fintype.card Digest : ENNReal)⁻¹) +
          sampledBeforeFailureEncodingPairCharge adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹ +
          sampledLiveNonSecretResidual adversary q (q + 1) := by simp only [add_mul]; ac_rfl
      _ ≤ _ := add_le_add (add_le_add (add_le_add (mul_le_mul' hstructural le_rfl) hshared) le_rfl) le_rfl
  have hother : sampledSelectedJointQueryCharge NonMessageNonSecretHashInput adversary q ≤ q := by
    apply le_trans _ (sampledJointNonSecretQueryCharge_le_queryBound adversary q)
    rw [sampledJointNonSecretQueryCharge_eq_nonMessage_add_message]
    exact le_self_add
  have he : sampledSelectedJointQueryCharge NonMessageNonSecretHashInput adversary q ≠ ⊤ :=
    ne_top_of_le_ne_top (by finiteness) hother
  have hc : (Fintype.card Digest : ENNReal) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  apply ENNReal.le_of_add_le_add_right (ENNReal.mul_ne_top he (ENNReal.inv_ne_top.mpr hc))
  rw [sampledJointNonSecretQueryCharge_eq_nonMessage_add_message] at hbound
  have hbound' := add_le_add hbound (le_refl
    (sampledBeforeFailureHashCharge messageHashCharge adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹))
  rw [sampledBeforeFailureRestHashCharge_eq_nonMessage_add_message]
  simpa only [add_mul, add_assoc, add_comm, add_left_comm] using hbound'

theorem forgeAdvantage_add_message_signing_encoding_executionReserves_remainder_gap_le_collisionEnvelope
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary +
      (sampledSelectedJointQueryCharge MessageHashInput adversary q + sampledBeforeFailureHashCharge messageHashCharge adversary q (q + 1) +
        sampledSigningNonEncodingReserve adversary q (q + 1) + sampledOuterEncodingReserve adversary q (q + 1)) * (Fintype.card Digest : ENNReal)⁻¹ +
      (sampledUnusedExecutionReserve adversary q (q + 1) +
        (sampledStoppedIndexRemainder adversary q (q + 1) + sampledStoppedSigningGap adversary q (q + 1))) ≤
      (sampledBeforeFailureRestHashCharge adversary q (q + 1) + (q : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ +
      (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) +
      sampledBeforeFailureEncodingPairCharge adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹ +
      (q : ENNReal) * initialRawIndexRate q := by
  have hbase := (forgeAdvantage_add_message_signing_encodingReserves_le_collision_live adversary q hq hqMax).trans
    (add_le_add le_rfl (sampledLiveNonSecretResidual_le_stopped_arrival adversary q hq hqMax (q + 1)))
  apply (add_le_add hbase le_rfl).trans
  rw [add_assoc]
  exact add_le_add le_rfl (sampledStoppedTargetCharge_add_executionReserve_remainder_gap_le_initial adversary q hq hqMax (q + 1))

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
