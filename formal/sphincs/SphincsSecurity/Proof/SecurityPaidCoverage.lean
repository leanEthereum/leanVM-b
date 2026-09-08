import SphincsSecurity.Proof.SampledPaidCoverage
import SphincsSecurity.Proof.SampledSigningSurvival

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

private theorem pay_coverage_from_reserve
    (forge credit message signing outer afterOuter outerPairs signingPairs cover refund before initial residual : ENNReal)
    (hsigning : signing ≠ ⊤) (houterPairs : outerPairs ≠ ⊤) (hsigningPairs : signingPairs ≠ ⊤)
    (houter : afterOuter + outerPairs = outer)
    (hbase : forge + credit + (message + signing + outer) ≤ before + (outerPairs + signingPairs) + cover)
    (hcoverage : cover + refund + signingPairs ≤ initial + signing + residual) :
    forge + credit + (message + afterOuter) + refund ≤ before + initial + residual := by
  have h : forge + credit + (message + signing + outer) + refund + signingPairs ≤
      before + (outerPairs + signingPairs) + (initial + signing + residual) := by
    apply (add_le_add (add_le_add hbase le_rfl) le_rfl).trans
    convert add_le_add (le_refl (before + (outerPairs + signingPairs))) hcoverage using 1
    ring
  apply ENNReal.le_of_add_le_add_right (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hsigning, houterPairs⟩, hsigningPairs⟩)
  rw [← houter] at h
  convert h using 1 <;> ring

theorem forgeAdvantage_add_doubleParentCredit_coverageRefund_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127)
    (refund : ENNReal)
    (hcoverage : sampledLiveNonSecretResidual adversary q (q + 1) + refund +
      sampledSigningEncodingPairCharge adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹ ≤
      (q : ENNReal) * initialRawIndexRate q +
        sampledSigningNonEncodingReserve adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹ +
        sampledPaidCoverageResidual adversary q (q + 1)) :
    forgeAdvantage scheme adversary + sampledCollisionDoubleParentCredit adversary q (q + 1) +
      (sampledSelectedJointQueryCharge MessageHashInput adversary q + sampledBeforeFailureHashCharge messageHashCharge adversary q (q + 1) +
        sampledOuterEncodingReserveAfterPairs adversary q (q + 1)) * (Fintype.card Digest : ENNReal)⁻¹ +
      refund ≤
      (sampledBeforeFailureRestHashCharge adversary q (q + 1) + (q : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ +
        (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) +
        (q : ENNReal) * initialRawIndexRate q + sampledPaidCoverageResidual adversary q (q + 1) := by
  have hbase := forgeAdvantage_add_collisionCredit_message_signing_encodingReserves_le_collision_live adversary q hqMax
    (sampledCollisionDoubleParentCredit adversary q (q + 1))
    (forgeAdvantage_add_collisionDoubleParentCredit_le_sharedFailure_add_charge_add_live_residual adversary q hq hqMax (q + 1))
  rw [sampledBeforeFailureEncodingPairCharge_eq_outer_add_signing] at hbase
  have hsigning : sampledSigningNonEncodingReserve adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (sampledSigningNonEncodingReserve_ne_top adversary q hq (q + 1))
      (ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
  have houter : sampledOuterEncodingReserveAfterPairs adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹ +
      sampledOuterEncodingPairCharge adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹ =
      sampledOuterEncodingReserve adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹ := by
    rw [← add_mul, sampledOuterEncodingReserveAfterPairs_add_pairs adversary q hq hqMax (q + 1)]
  have h := pay_coverage_from_reserve
    (forgeAdvantage scheme adversary) (sampledCollisionDoubleParentCredit adversary q (q + 1))
    ((sampledSelectedJointQueryCharge MessageHashInput adversary q + sampledBeforeFailureHashCharge messageHashCharge adversary q (q + 1)) *
      (Fintype.card Digest : ENNReal)⁻¹)
    (sampledSigningNonEncodingReserve adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹)
    (sampledOuterEncodingReserve adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹)
    (sampledOuterEncodingReserveAfterPairs adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹)
    (sampledOuterEncodingPairCharge adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹)
    (sampledSigningEncodingPairCharge adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹)
    (sampledLiveNonSecretResidual adversary q (q + 1)) (refund)
    ((sampledBeforeFailureRestHashCharge adversary q (q + 1) + (q : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ +
      (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal))
    ((q : ENNReal) * initialRawIndexRate q) (sampledPaidCoverageResidual adversary q (q + 1))
    hsigning (sampledOuterEncodingPairCharge_scaled_ne_top adversary q hq hqMax (q + 1))
    (sampledSigningEncodingPairCharge_scaled_ne_top adversary q hq hqMax (q + 1)) houter
    (by simpa only [add_mul] using hbase)
    hcoverage
  simpa only [add_mul] using h

theorem forgeAdvantage_add_doubleParentCredit_paidCoverage_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary + sampledCollisionDoubleParentCredit adversary q (q + 1) +
      (sampledSelectedJointQueryCharge MessageHashInput adversary q + sampledBeforeFailureHashCharge messageHashCharge adversary q (q + 1) +
        sampledOuterEncodingReserveAfterPairs adversary q (q + 1)) * (Fintype.card Digest : ENNReal)⁻¹ +
      sampledPaidCoverageRefund adversary q (q + 1) ≤
      (sampledBeforeFailureRestHashCharge adversary q (q + 1) + (q : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ +
        (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) +
        (q : ENNReal) * initialRawIndexRate q + sampledPaidCoverageResidual adversary q (q + 1) := by
  exact forgeAdvantage_add_doubleParentCredit_coverageRefund_le adversary q hq hqMax
    (sampledPaidCoverageRefund adversary q (q + 1))
    (sampledLiveNonSecretResidual_pairs_refund_le_reserved_add_residual adversary q hq hqMax (q + 1))

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
