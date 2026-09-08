import SphincsSecurity.Proof.SecurityDoubleSharedParentRefund
import SphincsSecurity.Proof.SecurityParentReserveConservation
import SphincsSecurity.Proof.ParentLossDecomposition

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

private theorem parent_funding_double_shared_refund
    (adv base extra pending funding loss terminal shared release rate : ENNReal)
    (hbalance : pending + loss = funding) (hloss : loss ≤ terminal + shared + release)
    (hbound : adv + (2 * pending * rate + (terminal + 2 * shared) * rate) + extra ≤ base) :
    adv + 2 * funding * rate + extra ≤ base + (terminal + 2 * release) * rate := by
  by_cases hb : base = ⊤
  · simp [hb]
  have hfinite : (terminal + 2 * shared) * rate ≠ ⊤ := by
    apply ne_top_of_le_ne_top hb
    exact (le_add_self.trans (le_add_self.trans le_self_add)).trans hbound
  have h := (add_le_add hbound (le_refl (2 * loss * rate))).trans
    (add_le_add le_rfl (mul_le_mul' (mul_le_mul' le_rfl hloss) le_rfl))
  apply ENNReal.le_of_add_le_add_right hfinite
  rw [← hbalance]
  convert h using 1 <;> first | rfl | ring

theorem forgeAdvantage_add_doubleParentCredit_executionReserves_le_collisionEnvelope
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary + sampledCollisionDoubleParentCredit adversary q (q + 1) +
      (sampledSelectedJointQueryCharge MessageHashInput adversary q + sampledBeforeFailureHashCharge messageHashCharge adversary q (q + 1) +
        sampledSigningNonEncodingReserve adversary q (q + 1) + sampledOuterEncodingReserve adversary q (q + 1)) * (Fintype.card Digest : ENNReal)⁻¹ +
      (sampledUnusedExecutionReserve adversary q (q + 1) +
        (sampledStoppedIndexRemainder adversary q (q + 1) + sampledStoppedSigningGap adversary q (q + 1))) ≤
      (sampledBeforeFailureRestHashCharge adversary q (q + 1) + (q : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ +
      (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) +
      sampledBeforeFailureEncodingPairCharge adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹ +
      (q : ENNReal) * initialRawIndexRate q := by
  have hbase := (forgeAdvantage_add_collisionCredit_message_signing_encodingReserves_le_collision_live adversary q hqMax
    (sampledCollisionDoubleParentCredit adversary q (q + 1))
    (forgeAdvantage_add_collisionDoubleParentCredit_le_sharedFailure_add_charge_add_live_residual adversary q hq hqMax (q + 1))).trans
    (add_le_add le_rfl (sampledLiveNonSecretResidual_le_stopped_arrival adversary q hq hqMax (q + 1)))
  apply (add_le_add hbase le_rfl).trans
  rw [add_assoc]
  exact add_le_add le_rfl (sampledStoppedTargetCharge_add_executionReserve_remainder_gap_le_initial adversary q hq hqMax (q + 1))


theorem forgeAdvantage_add_parentFunding_le_doubleSharedRefundedCollisionEnvelope
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary + 2 * sampledFreshParentReserveCharge adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹ +
      (sampledSelectedJointQueryCharge MessageHashInput adversary q + sampledBeforeFailureHashCharge messageHashCharge adversary q (q + 1) +
        sampledSigningNonEncodingReserve adversary q (q + 1) + sampledOuterEncodingReserve adversary q (q + 1)) * (Fintype.card Digest : ENNReal)⁻¹ +
      (sampledUnusedExecutionReserve adversary q (q + 1) +
        (sampledStoppedIndexRemainder adversary q (q + 1) + sampledStoppedSigningGap adversary q (q + 1))) ≤
      (sampledBeforeFailureRestHashCharge adversary q (q + 1) + (q : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ +
      (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) +
      sampledBeforeFailureEncodingPairCharge adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹ +
      (q : ENNReal) * initialRawIndexRate q +
      (sampledTerminalParentDiscard adversary q (q + 1) + 2 * sampledLocalizedParentReleaseCharge adversary q (q + 1)) * (Fintype.card Digest : ENNReal)⁻¹ := by
  have hcredit : 2 * sampledPendingParentCount adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹ +
      (sampledTerminalParentDiscard adversary q (q + 1) + 2 * sampledSharedParentDiscard adversary q (q + 1)) * (Fintype.card Digest : ENNReal)⁻¹ ≤
      sampledCollisionDoubleParentCredit adversary q (q + 1) := by
    rw [sampledCollisionDoubleParentCredit_eq_terminal_add_shared]
    have h := add_le_add (twice_sampledPendingParentCount_add_discard_scaled_le adversary q hq hqMax (q + 1))
      (le_refl (sampledSharedParentDiscard adversary q (q + 1) * (2 * (Fintype.card Digest : ENNReal)⁻¹)))
    simpa only [add_mul, mul_add, mul_assoc, mul_left_comm, mul_comm, add_assoc] using h
  have hbase := (add_le_add (add_le_add (add_le_add le_rfl hcredit) le_rfl) le_rfl).trans
    (forgeAdvantage_add_doubleParentCredit_executionReserves_le_collisionEnvelope adversary q hq hqMax)
  have hloss := sampledParentReserveLoss_le_localized adversary q (q + 1)
  rw [sampledLocalizedParentLoss_eq_discard_add_shared_add_release] at hloss
  have h := parent_funding_double_shared_refund _ _ _ _ _ _ _ _ _ _
    (sampledPendingParentCount_add_loss_eq_funding adversary q (q + 1)) hloss
    (by simpa only [add_assoc] using hbase)
  simpa only [add_assoc] using h

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
