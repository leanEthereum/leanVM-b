import SphincsSecurity.Proof.SecurityNetCoverageRefund
import SphincsSecurity.Proof.SampledParentCrossRelease

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem forgeAdvantage_add_fundingAfterDirectRelease_netCoverageRefund_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary + 2 * sampledParentFundingAfterDirectRelease adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹ +
      (sampledSelectedJointQueryCharge MessageHashInput adversary q + sampledBeforeFailureHashCharge messageHashCharge adversary q (q + 1) +
        sampledOuterEncodingReserveAfterPairs adversary q (q + 1)) * (Fintype.card Digest : ENNReal)⁻¹ +
      sampledNetCoverageRefund adversary q (q + 1) ≤
      (sampledBeforeFailureRestHashCharge adversary q (q + 1) + (q : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ +
        (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) + (q : ENNReal) * initialRawIndexRate q +
        (sampledTerminalParentDiscard adversary q (q + 1) + 2 * sampledCrossParentReleaseCharge adversary q (q + 1)) *
          (Fintype.card Digest : ENNReal)⁻¹ := by
  have h := forgeAdvantage_add_parentFunding_netCoverageRefund_le adversary q hq hqMax
  rw [← sampledParentFundingAfterDirectRelease_add_direct, sampledLocalizedParentReleaseCharge_eq_direct_add_cross] at h
  have hd : 2 * sampledDirectParentReleaseCharge adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by finiteness) (sampledDirectParentReleaseCharge_ne_top adversary q hq (q + 1)))
      (ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
  apply ENNReal.le_of_add_le_add_right hd
  convert h using 1 <;> ring

theorem forgeAdvantage_add_netParentFunding_netCoverageRefund_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary + sampledNetParentFunding adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹ +
      (sampledSelectedJointQueryCharge MessageHashInput adversary q + sampledBeforeFailureHashCharge messageHashCharge adversary q (q + 1) +
        sampledOuterEncodingReserveAfterPairs adversary q (q + 1)) * (Fintype.card Digest : ENNReal)⁻¹ +
      sampledNetCoverageRefund adversary q (q + 1) ≤
      (sampledBeforeFailureRestHashCharge adversary q (q + 1) + (q : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ +
        (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) + (q : ENNReal) * initialRawIndexRate q +
        2 * sampledCrossParentReleaseCharge adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹ := by
  have h := forgeAdvantage_add_fundingAfterDirectRelease_netCoverageRefund_le adversary q hq hqMax
  rw [← sampledNetParentFunding_add_terminal adversary q hq (q + 1)] at h
  have ht : sampledTerminalParentDiscard adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (sampledTerminalParentDiscard_ne_top adversary q hq (q + 1))
      (ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
  apply ENNReal.le_of_add_le_add_right ht
  convert h using 1 <;> ring

theorem forgeAdvantage_add_netParentFunding_netCoverageRefund_pairs_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary + sampledNetParentFunding adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹ +
      (sampledSelectedJointQueryCharge MessageHashInput adversary q + sampledBeforeFailureHashCharge messageHashCharge adversary q (q + 1) +
        sampledOuterEncodingReserveAfterPairs adversary q (q + 1)) * (Fintype.card Digest : ENNReal)⁻¹ +
      sampledNetCoverageRefund adversary q (q + 1) ≤
      (sampledBeforeFailureRestHashCharge adversary q (q + 1) + (q : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ +
        (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) + (q : ENNReal) * initialRawIndexRate q +
        2 * (q.choose 2 : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ ^ 2 := by
  apply (forgeAdvantage_add_netParentFunding_netCoverageRefund_le adversary q hq hqMax).trans
  apply add_le_add le_rfl
  convert mul_le_mul' (mul_le_mul' (le_refl (2 : ENNReal)) (sampledCrossParentReleaseCharge_le_pairs adversary q hq (q + 1)))
    (le_refl (Fintype.card Digest : ENNReal)⁻¹) using 1
  ring

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
