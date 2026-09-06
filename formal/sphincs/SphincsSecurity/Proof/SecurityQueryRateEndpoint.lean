import SphincsSecurity.Proof.OtsProbeNativeRateBound
import SphincsSecurity.Proof.FtsProbeQueryRate
import SphincsSecurity.Proof.SecurityOccupancyEndpoint

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

theorem forgeAdvantage_le_sampled_jointPrimitive_add_message_add_forest (adversary : Adversary) :
    forgeAdvantage scheme adversary ≤
      Pr[SampledViewedEvent jointPrimitiveEvent | sampledViewedGame adversary] +
        (Pr[SampledViewedEvent cleanMessageEvent | sampledViewedGame adversary] +
          Pr[SampledViewedEvent ViewedHonestProperFewTimeLeakWitness | sampledViewedGame adversary]) := by
  rw [forgeAdvantage_eq_sampledGame, sampledGame, ← probEvent_eq_eq_probOutput, probEvent_bind_eq_tsum]
  simp only [probEvent_sampledViewedGame_eq_weighted, ← ENNReal.tsum_add, ← mul_add]
  apply ENNReal.tsum_le_tsum
  intro secrets
  apply mul_le_mul' le_rfl
  rw [probEvent_eq_eq_probOutput]
  exact probEvent_win_le_jointPrimitive_add_message_add_forest adversary secrets.parameter secrets.otsSecret secrets.ftsSecret

theorem probEvent_sampled_jointPrimitive_le_queryRates_add_erasure
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqSpace : q + 1 < Fintype.card Digest) :
    Pr[SampledViewedEvent jointPrimitiveEvent | sampledViewedGame adversary] ≤
      sampledQueryCharge TightEncoding.refinedStructuralEncodingQueryCharge adversary *
          (Fintype.card Digest : ENNReal)⁻¹ +
        sampledQueryCharge (fun secretKey cache input =>
          OtsProbeSimulation.otsHashInputCharge secretKey.parameter input +
            FtsProbeSimulation.ftsHashQueryCharge secretKey.parameter cache input) adversary *
          OtsProbeSimulation.privateHistoryGuessRate q +
        (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  apply (probEvent_sampled_jointPrimitive_le_prehit_charge_add_openings adversary).trans
  apply (add_le_add le_rfl (add_le_add
    (OtsProbeSimulation.probEvent_sampled_prehitFree_residual_le_actualOtsCount_rate_add_erasure_of_querySpace
      adversary q hq hqSpace)
    (FtsProbeSimulation.probEvent_sampledViewedGame_cleanUncovered_le_queryRate adversary q hq (by omega)))).trans_eq
  rw [sampledQueryCharge_add]
  ring

theorem forgeAdvantage_le_queryRates_add_message_add_forest
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqSpace : q + 1 < Fintype.card Digest) :
    forgeAdvantage scheme adversary ≤
      (sampledQueryCharge TightEncoding.refinedStructuralEncodingQueryCharge adversary *
          (Fintype.card Digest : ENNReal)⁻¹ +
        sampledQueryCharge (fun secretKey cache input =>
          OtsProbeSimulation.otsHashInputCharge secretKey.parameter input +
            FtsProbeSimulation.ftsHashQueryCharge secretKey.parameter cache input) adversary *
          OtsProbeSimulation.privateHistoryGuessRate q +
        (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹) +
      (Pr[SampledViewedEvent cleanMessageEvent | sampledViewedGame adversary] +
        Pr[SampledViewedEvent ViewedHonestProperFewTimeLeakWitness | sampledViewedGame adversary]) :=
  (forgeAdvantage_le_sampled_jointPrimitive_add_message_add_forest adversary).trans
    (add_le_add (probEvent_sampled_jointPrimitive_le_queryRates_add_erasure adversary q hq hqSpace) le_rfl)

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
