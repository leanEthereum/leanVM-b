import SphincsSecurity.Proof.LiveObservedMessageResidual
import SphincsSecurity.Proof.SecurityJointMessageReserve

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal

theorem forgeAdvantage_add_messageReserves_le_erasedMessagePatterns
    (adversary : Adversary) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary +
      (sampledSelectedJointQueryCharge MessageHashInput adversary q + sampledBeforeFailureHashCharge messageHashCharge adversary q (q + 1)) *
        (Fintype.card Digest : ENNReal)⁻¹ ≤
      (sampledBeforeFailureRestHashCharge adversary q (q + 1) + (q : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ +
      (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) + sampledErasedObservedRetainedCoverRisk adversary q :=
  (forgeAdvantage_add_messageReserves_le_joint_beforeFailureBudget_live adversary q hq hqMax).trans
    (add_le_add le_rfl (sampledLiveNonSecretResidual_le_erasedObservedCover adversary q hq (q + 1)))

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
