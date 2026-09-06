import SphincsSecurity.Proof.MessageCollision127
import SphincsSecurity.Proof.SecurityQueryRateEndpoint

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

theorem forgeAdvantage_le_sampled_jointPrimitive_add_weighted_remaining127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary ≤
      Pr[SampledViewedEvent jointPrimitiveEvent | sampledViewedGame adversary] +
        ((q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹ +
          ((2 * q + 1 : Nat) : ℝ≥0∞) *
            weightedRawTargetOriginUnionBound signatureLimit q (digestReuseWeight q)) :=
  (forgeAdvantage_le_sampled_jointPrimitive_add_message_add_forest adversary).trans
    (add_le_add le_rfl (add_le_add
      (probEvent_sampled_cleanMessage_le127 adversary q hqPos hq hqMax)
      (probEvent_sampled_honest_leak_le_weighted adversary q hq hqMax)))

theorem forgeAdvantage_le_queryRates_add_weighted_remaining127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary ≤
      (sampledQueryCharge TightEncoding.refinedStructuralEncodingQueryCharge adversary *
          (Fintype.card Digest : ℝ≥0∞)⁻¹ +
        sampledQueryCharge (fun secretKey cache input =>
          OtsProbeSimulation.otsHashInputCharge secretKey.parameter input +
            FtsProbeSimulation.ftsHashQueryCharge secretKey.parameter cache input) adversary *
          OtsProbeSimulation.privateHistoryGuessRate q +
        (q : ℝ≥0∞) * ((2 ^ 216 : Nat) : ℝ≥0∞)⁻¹) +
      ((q : ℝ≥0∞) * ((2 ^ 139 : Nat) : ℝ≥0∞)⁻¹ +
        ((2 * q + 1 : Nat) : ℝ≥0∞) *
          weightedRawTargetOriginUnionBound signatureLimit q (digestReuseWeight q)) := by
  apply (forgeAdvantage_le_sampled_jointPrimitive_add_weighted_remaining127 adversary q hqPos hq hqMax).trans
  apply add_le_add _ le_rfl
  apply probEvent_sampled_jointPrimitive_le_queryRates_add_erasure adversary q hq
  have hspace : 2 ^ 127 + 1 < Fintype.card Digest := by norm_num [digestBits]
  omega

end SphincsSecurity.Concrete
