import SphincsSecurity.Proof.SecurityJointTerminalParentRefund
import SphincsSecurity.Proof.SecurityParentReserveConservation
import SphincsSecurity.Proof.ParentLossDecomposition

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

private theorem funded_parent_refund
    (amount pending shared funding loss terminal release rate base : ENNReal)
    (hbalance : pending + loss = funding) (hloss : loss ≤ terminal + shared + release)
    (hbound : amount + (pending + shared) * rate ≤ base) :
    amount + funding * rate ≤ base + (terminal + release) * rate := by
  by_cases hb : base = ⊤
  · simp [hb]
  have hfinite : shared * rate ≠ ⊤ := by
    apply ne_top_of_le_ne_top hb
    exact ((mul_le_mul' le_add_self le_rfl).trans le_add_self).trans hbound
  have h := (add_le_add hbound (le_refl (loss * rate))).trans (add_le_add le_rfl (mul_le_mul' hloss le_rfl))
  apply ENNReal.le_of_add_le_add_right hfinite
  rw [← hbalance]
  convert h using 1 <;> first | rfl | ring

theorem forgeAdvantage_add_jointParentFunding_executionReserves_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary +
      (sampledJointCollisionCoverageCompletionCredit adversary q (q + 1) + sampledJointCollisionCoverageCredit adversary q (q + 1) +
        sampledJointCoverageAfterParentRefund adversary q (q + 1) +
        (sampledSelectedJointQueryCharge MessageHashInput adversary q + sampledBeforeFailureHashCharge messageHashCharge adversary q (q + 1) +
          sampledSigningNonEncodingReserve adversary q (q + 1) + sampledOuterEncodingReserve adversary q (q + 1)) * (Fintype.card Digest : ENNReal)⁻¹) +
      sampledFreshParentReserveCharge adversary q (q + 1) * (2 * (Fintype.card Digest : ENNReal)⁻¹) ≤
      (sampledBeforeFailureRestHashCharge adversary q (q + 1) + (q : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ +
        (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) + sampledBeforeFailureEncodingPairCharge adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹ +
        (min 1 ((q : ENNReal) * initialRawIndexRate q) + (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹) +
        sampledTerminalParentCoverageOverlap adversary q (q + 1) +
        (sampledTerminalParentDiscard adversary q (q + 1) + sampledLocalizedParentReleaseCharge adversary q (q + 1)) *
          (2 * (Fintype.card Digest : ENNReal)⁻¹) := by
  let credit := sampledJointCollisionCoverageCompletionCredit adversary q (q + 1) + sampledJointCollisionCoverageCredit adversary q (q + 1) +
    sampledJointCoverageAfterParentRefund adversary q (q + 1) +
    (sampledSelectedJointQueryCharge MessageHashInput adversary q + sampledBeforeFailureHashCharge messageHashCharge adversary q (q + 1) +
      sampledSigningNonEncodingReserve adversary q (q + 1) + sampledOuterEncodingReserve adversary q (q + 1)) * (Fintype.card Digest : ENNReal)⁻¹
  let base := (sampledBeforeFailureRestHashCharge adversary q (q + 1) + (q : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ +
    (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) + sampledBeforeFailureEncodingPairCharge adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹ +
    (min 1 ((q : ENNReal) * initialRawIndexRate q) + (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹)
  have hbase := add_le_add (forgeAdvantage_add_jointParentCredits_executionReserves_le adversary q hq hqMax)
    (le_refl (sampledTerminalParentCoverageOverlap adversary q (q + 1)))
  have hbound : (forgeAdvantage scheme adversary + credit) +
      (sampledPendingParentCount adversary q (q + 1) + sampledSharedParentDiscard adversary q (q + 1)) *
        (2 * (Fintype.card Digest : ENNReal)⁻¹) ≤ base + sampledTerminalParentCoverageOverlap adversary q (q + 1) := by
    convert hbase using 1 <;> first
    | rfl
    | rw [add_mul, ← sampledJointTerminalParentCredit_add_overlap]
      dsimp only [credit]
      ring
  have hloss := sampledParentReserveLoss_le_localized adversary q (q + 1)
  rw [sampledLocalizedParentLoss_eq_discard_add_shared_add_release] at hloss
  exact funded_parent_refund _ _ _ _ _ _ _ _ _
    (sampledPendingParentCount_add_loss_eq_funding adversary q (q + 1)) hloss hbound

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
