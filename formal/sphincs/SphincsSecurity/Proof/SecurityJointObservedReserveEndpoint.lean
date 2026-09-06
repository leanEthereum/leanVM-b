import SphincsSecurity.Proof.FtsProbeJointSampledBudget

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation

theorem forgeAdvantage_add_observedOts_reserve_le_remaining127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary + sampledJointObservedOtsCharge adversary q * (Fintype.card Digest : ENNReal)⁻¹ ≤
      sampledQueryCharge (fun secretKey cache input => parentStoppedEncodingQueryCharge secretKey cache input +
        ftsParentQueryCharge secretKey cache input) adversary * (Fintype.card Digest : ENNReal)⁻¹ +
      min (sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary * privateHistoryGuessRate q)
        ((sampledNativeHistoryStartCharge Finset.univ adversary q +
          sampledNativeHistoryPrivateCharge Finset.univ adversary q) * (Fintype.card Digest : ENNReal)⁻¹) +
      (q : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ +
      (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ +
      ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
        (q : ENNReal) * (15 * ((2 ^ 132 : Nat) : ENNReal)⁻¹)) := by
  have hforge := forgeAdvantage_le_sharedHistory_add_jointFtsHit_remaining127 adversary q hqPos hq hqMax
  have hbudget := sampledJointObservedOts_add_fts_hit_le_query_rate adversary q
  apply (add_le_add hforge (le_refl (sampledJointObservedOtsCharge adversary q * (Fintype.card Digest : ENNReal)⁻¹))).trans
  calc
    _ = sampledQueryCharge (fun secretKey cache input => parentStoppedEncodingQueryCharge secretKey cache input +
          ftsParentQueryCharge secretKey cache input) adversary * (Fintype.card Digest : ENNReal)⁻¹ +
        min (sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary * privateHistoryGuessRate q)
          ((sampledNativeHistoryStartCharge Finset.univ adversary q +
            sampledNativeHistoryPrivateCharge Finset.univ adversary q) * (Fintype.card Digest : ENNReal)⁻¹) +
        (sampledJointObservedOtsCharge adversary q * (Fintype.card Digest : ENNReal)⁻¹ + sampledJointRetainedFtsHitRisk adversary q) +
        (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ +
        ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
          (q : ENNReal) * (15 * ((2 ^ 132 : Nat) : ENNReal)⁻¹)) := by ring
    _ ≤ _ := add_le_add (add_le_add (add_le_add le_rfl hbudget) le_rfl) le_rfl

end SphincsSecurity.Concrete
