import SphincsSecurity.Proof.FtsProbeQueryRate

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (privateHistoryGuessRate)

theorem sampledMaskedFtsProbeCharge_le_query_budget (adversary : Adversary) (q : Nat) :
    sampledMaskedFtsProbeCharge adversary q ≤ q := by
  unfold sampledMaskedFtsProbeCharge
  calc
    _ ≤ ∑' parameter, Pr[= parameter | sampleParameter] *
        ∑' otsSecret, Pr[= otsSecret | sampleOtsSecrets] * (q : ENNReal) := by
      apply ENNReal.tsum_le_tsum
      intro parameter
      apply mul_le_mul' le_rfl
      apply ENNReal.tsum_le_tsum
      intro otsSecret
      exact mul_le_mul' le_rfl (maskedFtsProbeCharge_le_q adversary parameter otsSecret q)
    _ ≤ _ := by
      simp_rw [ENNReal.tsum_mul_right]
      exact (mul_le_mul' tsum_probOutput_le_one (mul_le_mul' tsum_probOutput_le_one le_rfl)).trans_eq (by simp)

theorem probEvent_sampledViewedGame_cleanUncovered_le_min_probeCharge
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqSpace : q < Fintype.card Digest) :
    Pr[SampledViewedEvent cleanUncoveredEvent | sampledViewedGame adversary] ≤
      min (sampledQueryCharge (fun secretKey => ftsHashQueryCharge secretKey.parameter) adversary * privateHistoryGuessRate q)
        (sampledMaskedFtsProbeCharge adversary q * (Fintype.card Digest : ENNReal)⁻¹) :=
  le_min (probEvent_sampledViewedGame_cleanUncovered_le_queryRate adversary q hq hqSpace)
    (probEvent_sampledViewedGame_cleanUncovered_le_probeCharge adversary q hq)

theorem probEvent_sampledViewedGame_cleanUncovered_le_min_queryBudget
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqSpace : q < Fintype.card Digest) :
    Pr[SampledViewedEvent cleanUncoveredEvent | sampledViewedGame adversary] ≤
      min (sampledQueryCharge (fun secretKey => ftsHashQueryCharge secretKey.parameter) adversary * privateHistoryGuessRate q)
        ((q : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹) :=
  (probEvent_sampledViewedGame_cleanUncovered_le_min_probeCharge adversary q hq hqSpace).trans
    (min_le_min le_rfl (mul_le_mul' (sampledMaskedFtsProbeCharge_le_query_budget adversary q) le_rfl))

end SphincsSecurity.Concrete.FtsProbeSimulation
