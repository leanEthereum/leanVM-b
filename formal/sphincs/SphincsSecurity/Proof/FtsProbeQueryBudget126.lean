import SphincsSecurity.Proof.FtsProbeCostBound

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

theorem sampledMaskedFtsProbeCharge_le_four_thirds_queryCharge
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126) :
    sampledMaskedFtsProbeCharge adversary q ≤
      (4 / 3 : ℝ≥0∞) * sampledQueryCharge (fun secretKey => ftsHashQueryCharge secretKey.parameter) adversary := by
  rw [sampledMaskedFtsProbeCharge, sampledQueryCharge, sampleSecrets, tsum_probOutput_bind_mul]
  simp only [tsum_probOutput_bind_mul, tsum_probOutput_pure_mul]
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro parameter
  rw [mul_left_comm (4 / 3)]
  by_cases hparameter : parameter ∈ support sampleParameter
  · apply mul_le_mul' le_rfl
    rw [← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro otsSecret
    rw [mul_left_comm (4 / 3)]
    by_cases hots : otsSecret ∈ support sampleOtsSecrets
    · exact mul_le_mul' le_rfl
        (maskedFtsProbeCharge_le_four_thirds_queryCharge adversary parameter hparameter otsSecret hots q hq hqMax)
    · rw [probOutput_eq_zero_of_not_mem_support hots, zero_mul, zero_mul]
  · rw [probOutput_eq_zero_of_not_mem_support hparameter, zero_mul, zero_mul]

theorem probEvent_sampledViewedGame_cleanUncovered_le_queryCharge126
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126) :
    Pr[SampledViewedEvent cleanUncoveredEvent | sampledViewedGame adversary] ≤
      (4 / 3 : ℝ≥0∞) * sampledQueryCharge (fun secretKey => ftsHashQueryCharge secretKey.parameter) adversary *
        (Fintype.card Digest : ℝ≥0∞)⁻¹ :=
  (probEvent_sampledViewedGame_cleanUncovered_le_probeCharge adversary q hq).trans
    (mul_le_mul' (sampledMaskedFtsProbeCharge_le_four_thirds_queryCharge adversary q hq hqMax) le_rfl)

end SphincsSecurity.Concrete.FtsProbeSimulation
