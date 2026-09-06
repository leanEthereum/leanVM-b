import SphincsSecurity.Proof.AnswerQueryCharge
import SphincsSecurity.Proof.RetainedNonOtsProjection
import SphincsSecurity.Proof.SecurityWeighted127Endpoint

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal
open OtsProbeSimulation

theorem probEvent_nonOtsViewedTerminal_le_components (adversary : Adversary) :
    Pr[SampledViewedEvent nonOtsViewedTerminalEvent | sampledViewedGame adversary] ≤
      Pr[SampledViewedEvent ViewedEncodingCollisionWitness | sampledViewedGame adversary] +
        (Pr[SampledViewedEvent cleanUncoveredEvent | sampledViewedGame adversary] +
          (Pr[SampledViewedEvent cleanMessageEvent | sampledViewedGame adversary] +
            Pr[SampledViewedEvent ViewedHonestProperFewTimeLeakWitness | sampledViewedGame adversary])) := by
  change Pr[fun result =>
    SampledViewedEvent ViewedEncodingCollisionWitness result ∨
      SampledViewedEvent cleanUncoveredEvent result ∨
      SampledViewedEvent cleanMessageEvent result ∨
      SampledViewedEvent ViewedHonestProperFewTimeLeakWitness result | sampledViewedGame adversary] ≤ _
  exact (probEvent_or_le _ _ _).trans (add_le_add le_rfl
    ((probEvent_or_le _ _ _).trans (add_le_add le_rfl (probEvent_or_le _ _ _))))

theorem probEvent_retainedNonOtsResidual_le_encoding_add_queryRate_remaining127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    Pr[retainedNonOtsResidual | sampledFirstParentRetainedGame adversary] ≤
      Pr[SampledViewedEvent ViewedEncodingCollisionWitness | sampledViewedGame adversary] +
        (sampledQueryCharge (fun secretKey => FtsProbeSimulation.ftsHashQueryCharge secretKey.parameter) adversary *
          privateHistoryGuessRate q +
          ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
            ((2 * q + 1 : Nat) : ENNReal) *
              weightedRawTargetOriginUnionBound signatureLimit q (digestReuseWeight q))) := by
  apply (probEvent_retainedNonOtsResidual_le_viewed adversary).trans
  apply (probEvent_nonOtsViewedTerminal_le_components adversary).trans
  apply add_le_add le_rfl
  apply add_le_add
    (FtsProbeSimulation.probEvent_sampledViewedGame_cleanUncovered_le_queryRate adversary q hq ?_)
    (add_le_add (probEvent_sampled_cleanMessage_le127 adversary q hqPos hq hqMax)
      (probEvent_sampled_honest_leak_le_weighted adversary q hq hqMax))
  have hspace : 2 ^ 127 < Fintype.card Digest := by norm_num [digestBits]
  omega

theorem forgeAdvantage_le_answerQueryCharge_jointOts_fts_encoding_remaining127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary ≤
      (sampledQueryCharge structuralAnswerQueryCharge adversary +
        sampledQueryCharge ftsParentQueryCharge adversary) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
      sampledQueryCharge (fun secretKey cache input =>
        otsHashInputCharge secretKey.parameter input +
          FtsProbeSimulation.ftsHashQueryCharge secretKey.parameter cache input) adversary * privateHistoryGuessRate q +
      (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ +
      Pr[SampledViewedEvent ViewedEncodingCollisionWitness | sampledViewedGame adversary] +
      ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
        ((2 * q + 1 : Nat) : ENNReal) *
          weightedRawTargetOriginUnionBound signatureLimit q (digestReuseWeight q)) := by
  have hspace : q + 1 < Fintype.card Digest := by
    have : 2 ^ 127 + 1 < Fintype.card Digest := by norm_num [digestBits]
    omega
  apply (forgeAdvantage_le_answerQueryCharge_add_first_parent_residual adversary).trans
  apply (add_le_add le_rfl
    (probEvent_firstParentResidual_le_jointOts_add_fts_add_remaining adversary q hq hspace)).trans
  apply (add_le_add le_rfl (add_le_add le_rfl (add_le_add le_rfl
    (probEvent_retainedNonOtsResidual_le_encoding_add_queryRate_remaining127 adversary q hqPos hq hqMax)))).trans_eq
  rw [sampledQueryCharge_add]
  ring

end SphincsSecurity.Concrete
