import SphincsSecurity.Proof.SampledParentReserveConservation
import SphincsSecurity.Proof.SecurityCollisionTerminalAllocation

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem forgeAdvantage_add_freshParents_message_signing_encoding_executionReserves_remainder_gap_le_collisionEnvelope_add_parentLoss
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
      2 * sampledParentReserveLoss adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹ := by
  have h := add_le_add
    (forgeAdvantage_add_pendingParents_message_signing_encoding_executionReserves_remainder_gap_le_collisionEnvelope adversary q hq hqMax)
    (le_refl (2 * sampledParentReserveLoss adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹))
  rw [← sampledPendingParentCount_add_loss_eq_funding]
  simpa only [mul_add, add_mul, add_assoc, add_comm, add_left_comm] using h

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
