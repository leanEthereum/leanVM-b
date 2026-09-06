import SphincsSecurity.Proof.OtsProbeNativeRateBound
import SphincsSecurity.Proof.SecurityOccupancyEndpoint

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

theorem probEvent_sampled_jointPrimitive_le_queryRate_add_erasure
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126) :
    Pr[SampledViewedEvent jointPrimitiveEvent | sampledViewedGame adversary] ≤
      sampledQueryCharge (fun secretKey cache input =>
        TightEncoding.refinedStructuralEncodingQueryCharge secretKey cache input + ftsOpeningQueryReserve secretKey cache input)
          adversary * (Fintype.card Digest : ENNReal)⁻¹ +
      (sampledQueryCharge (fun secretKey _ input => OtsProbeSimulation.otsHashInputCharge secretKey.parameter input) adversary *
        OtsProbeSimulation.privateHistoryGuessRate q + (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹) := by
  have hfts := FtsProbeSimulation.probEvent_sampledViewedGame_cleanUncovered_le_queryCharge126 adversary q hq hqMax
  rw [← sampled_ftsOpeningQueryReserve_eq] at hfts
  apply (probEvent_sampled_jointPrimitive_le_prehit_charge_add_openings adversary).trans
  apply (add_le_add le_rfl (add_le_add
    (OtsProbeSimulation.probEvent_sampled_prehitFree_residual_le_actualOtsCount_rate_add_erasure adversary q hq hqMax) hfts)).trans_eq
  rw [sampledQueryCharge_add]
  ring

theorem forgeAdvantage_le_queryRate_add_occupancy_remaining
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126) :
    forgeAdvantage scheme adversary ≤
      (sampledQueryCharge (fun secretKey cache input =>
        TightEncoding.refinedStructuralEncodingQueryCharge secretKey cache input + ftsOpeningQueryReserve secretKey cache input)
          adversary * (Fintype.card Digest : ENNReal)⁻¹ +
        (sampledQueryCharge (fun secretKey _ input => OtsProbeSimulation.otsHashInputCharge secretKey.parameter input) adversary *
          OtsProbeSimulation.privateHistoryGuessRate q + (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹)) +
      ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
        ((23 * q : Nat) : ENNReal) * ((2 ^ 134 : Nat) : ENNReal)⁻¹) :=
  (forgeAdvantage_le_sampled_jointPrimitive_add_occupancy_remaining adversary q hqPos hq hqMax).trans
    (add_le_add (probEvent_sampled_jointPrimitive_le_queryRate_add_erasure adversary q hq hqMax) le_rfl)

end SphincsSecurity.Concrete
