import SphincsSecurity.Proof.OtsProbeNativeErasedFts
import SphincsSecurity.Proof.SecurityNativeJointSecretsEndpoint

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation

theorem forgeAdvantage_le_sharedHistory_add_erasedFts_remaining127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary ≤
      sampledQueryCharge (fun secretKey cache input => parentStoppedEncodingQueryCharge secretKey cache input +
        ftsParentQueryCharge secretKey cache input) adversary * (Fintype.card Digest : ENNReal)⁻¹ +
      min (sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary * privateHistoryGuessRate q)
        ((sampledNativeHistoryStartCharge Finset.univ adversary q +
          sampledNativeHistoryPrivateCharge Finset.univ adversary q) * (Fintype.card Digest : ENNReal)⁻¹) +
      sampledErasedHistoryFtsWitnessRisk adversary +
      (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ +
      ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
        (q : ENNReal) * (15 * ((2 ^ 132 : Nat) : ENNReal)⁻¹)) := by
  apply (forgeAdvantage_le_sharedHistory_add_nativeFts_remaining127 adversary q hqPos hq hqMax).trans
  exact add_le_add (add_le_add (add_le_add le_rfl
    (sampledNativeFtsWitnessRisk_le_erased_history adversary (q + 1))) le_rfl) le_rfl

end SphincsSecurity.Concrete
