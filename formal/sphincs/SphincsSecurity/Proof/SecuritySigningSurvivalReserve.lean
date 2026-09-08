import SphincsSecurity.Proof.SecuritySigningEncodingPayment
import SphincsSecurity.Proof.SampledSigningSurvival

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem forgeAdvantage_add_parentFunding_signingSurvival_le
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary +
      (sampledJointCollisionCoverageCompletionCredit adversary q (q + 1) + sampledJointCollisionCoverageCredit adversary q (q + 1) +
        sampledJointCoverageAfterTerminalRefund adversary q (q + 1) +
        (sampledSelectedJointQueryCharge MessageHashInput adversary q + sampledBeforeFailureHashCharge messageHashCharge adversary q (q + 1) +
          sampledSigningNonEncodingReserveAfterSurvival adversary q (q + 1) + sampledOuterEncodingReserveAfterPairs adversary q (q + 1)) * (Fintype.card Digest : ENNReal)⁻¹) +
      sampledSigningSurvivalCredit adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹ +
      sampledFreshParentReserveCharge adversary q (q + 1) * (2 * (Fintype.card Digest : ENNReal)⁻¹) ≤
      (sampledBeforeFailureRestHashCharge adversary q (q + 1) + (q : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ +
        (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) +
        (min 1 ((q : ENNReal) * initialRawIndexRate q) + (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹) +
        (sampledTerminalParentDiscard adversary q (q + 1) + sampledLocalizedParentReleaseCharge adversary q (q + 1)) *
          (2 * (Fintype.card Digest : ENNReal)⁻¹) := by
  have h := forgeAdvantage_add_parentFunding_afterSigningEncodingPairs_le adversary q hq hqMax
  rw [← sampledSigningNonEncodingReserveAfterSurvival_add_credit adversary q hq hqMax (q + 1)] at h
  convert h using 1
  ring

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
