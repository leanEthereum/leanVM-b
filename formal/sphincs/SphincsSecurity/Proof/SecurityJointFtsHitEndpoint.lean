import SphincsSecurity.Proof.FtsProbeJointWitnessClassification
import SphincsSecurity.Proof.SecurityJointRetainedFtsEndpoint

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation

noncomputable def sampledJointRetainedFtsHitRisk (adversary : Adversary) (q : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      FtsProbeSimulation.jointRetainedFtsHitRisk adversary parameter
        (fun coordinate => ftsSecret coordinate.1 coordinate.2.1 coordinate.2.2) q

theorem sampledJointRetainedFtsWitnessRisk_eq_hit (adversary : Adversary) (q : Nat) :
    sampledJointRetainedFtsWitnessRisk adversary q = sampledJointRetainedFtsHitRisk adversary q := by
  simp only [sampledJointRetainedFtsWitnessRisk, sampledJointRetainedFtsHitRisk,
    FtsProbeSimulation.jointRetainedFtsWitnessRisk_eq_hit]

theorem forgeAdvantage_le_sharedHistory_add_jointFtsHit_remaining127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary ≤
      sampledQueryCharge (fun secretKey cache input => parentStoppedEncodingQueryCharge secretKey cache input +
        ftsParentQueryCharge secretKey cache input) adversary * (Fintype.card Digest : ENNReal)⁻¹ +
      min (sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary * privateHistoryGuessRate q)
        ((sampledNativeHistoryStartCharge Finset.univ adversary q +
          sampledNativeHistoryPrivateCharge Finset.univ adversary q) * (Fintype.card Digest : ENNReal)⁻¹) +
      sampledJointRetainedFtsHitRisk adversary q +
      (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ +
      ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
        (q : ENNReal) * (15 * ((2 ^ 132 : Nat) : ENNReal)⁻¹)) := by
  simpa only [sampledJointRetainedFtsWitnessRisk_eq_hit] using
    forgeAdvantage_le_sharedHistory_add_jointFts_remaining127 adversary q hqPos hq hqMax

end SphincsSecurity.Concrete
