import SphincsSecurity.Proof.SecurityJointProbeChargeEndpoint
import SphincsSecurity.Proof.OtsProbeErasedHistoryGameCost
import SphincsSecurity.Proof.JointErasedProbeStepBudget

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation

theorem forgeAdvantage_le_erasedOtsCost_add_jointFtsCost_remaining127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary ≤
      sampledQueryCharge (fun secretKey cache input => parentStoppedEncodingQueryCharge secretKey cache input +
        ftsParentQueryCharge secretKey cache input) adversary * (Fintype.card Digest : ENNReal)⁻¹ +
      min (sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary * privateHistoryGuessRate q)
        (sampledErasedHistoryProbeCost Finset.univ adversary q * (Fintype.card Digest : ENNReal)⁻¹) +
      sampledJointRetainedProbeCharge adversary q * (Fintype.card Digest : ENNReal)⁻¹ +
      (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ +
      ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
        (q : ENNReal) * (15 * ((2 ^ 132 : Nat) : ENNReal)⁻¹)) := by
  apply (forgeAdvantage_le_sharedHistory_add_jointProbeCharge_remaining127 adversary q hqPos hq hqMax).trans
  apply add_le_add (add_le_add (add_le_add (add_le_add le_rfl ?_) le_rfl) le_rfl) le_rfl
  exact min_le_min le_rfl (mul_le_mul' (sampledNativeHistoryCharge_le_erasedProbeCost Finset.univ adversary q) le_rfl)

end SphincsSecurity.Concrete
