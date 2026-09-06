import SphincsSecurity.Proof.AnswerEncodingQueryBudget
import SphincsSecurity.Proof.RetainedOtherProjection
import SphincsSecurity.Proof.SecurityWeighted127Endpoint

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal
open OtsProbeSimulation

theorem probEvent_otherViewedTerminal_le_queryRate_remaining127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    Pr[SampledViewedEvent otherViewedTerminalEvent | sampledViewedGame adversary] ≤
      sampledQueryCharge (fun secretKey => FtsProbeSimulation.ftsHashQueryCharge secretKey.parameter) adversary *
        privateHistoryGuessRate q +
        ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
          ((2 * q + 1 : Nat) : ENNReal) *
            weightedRawTargetOriginUnionBound signatureLimit q (digestReuseWeight q)) := by
  change Pr[fun result => SampledViewedEvent cleanUncoveredEvent result ∨
    SampledViewedEvent cleanMessageEvent result ∨ SampledViewedEvent ViewedHonestProperFewTimeLeakWitness result |
      sampledViewedGame adversary] ≤ _
  apply (probEvent_or_le _ _ _).trans
  apply add_le_add
    (FtsProbeSimulation.probEvent_sampledViewedGame_cleanUncovered_le_queryRate adversary q hq ?_)
    ((probEvent_or_le _ _ _).trans (add_le_add
      (probEvent_sampled_cleanMessage_le127 adversary q hqPos hq hqMax)
      (probEvent_sampled_honest_leak_le_weighted adversary q hq hqMax)))
  have hspace : 2 ^ 127 < Fintype.card Digest := by norm_num [digestBits]
  omega

theorem forgeAdvantage_le_answerEncoding_jointOts_fts_remaining127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary ≤
      sampledQueryCharge (fun secretKey cache input =>
        parentStoppedEncodingQueryCharge secretKey cache input + ftsParentQueryCharge secretKey cache input) adversary *
          (Fintype.card Digest : ENNReal)⁻¹ +
      sampledQueryCharge (fun secretKey cache input =>
        otsHashInputCharge secretKey.parameter input +
          FtsProbeSimulation.ftsHashQueryCharge secretKey.parameter cache input) adversary * privateHistoryGuessRate q +
      (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ +
      ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
        ((2 * q + 1 : Nat) : ENNReal) *
          weightedRawTargetOriginUnionBound signatureLimit q (digestReuseWeight q)) := by
  have hspace : q + 1 < Fintype.card Digest := by
    have : 2 ^ 127 + 1 < Fintype.card Digest := by norm_num [digestBits]
    omega
  apply (forgeAdvantage_le_answerEncodingQueryCharge_add_first_parent_residual adversary).trans
  apply (add_le_add le_rfl
    (probEvent_firstParentEncodingResidual_le_jointOts_add_fts_add_remaining adversary q hq hspace)).trans
  apply (add_le_add le_rfl (add_le_add le_rfl (add_le_add le_rfl
    (probEvent_otherViewedTerminal_le_queryRate_remaining127 adversary q hqPos hq hqMax)))).trans_eq
  rw [sampledQueryCharge_add, sampledQueryCharge_add]
  simp only [show Fintype.card Digest = 2 ^ digestBits by simp]
  ring

theorem forgeAdvantage_le_two_unit_budget_add_history_excess_remaining127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary ≤
      (2 * (q : ENNReal)) * (Fintype.card Digest : ENNReal)⁻¹ +
      sampledQueryCharge (fun secretKey cache input =>
        otsHashInputCharge secretKey.parameter input +
          FtsProbeSimulation.ftsHashQueryCharge secretKey.parameter cache input) adversary *
        (privateHistoryGuessRate q - (Fintype.card Digest : ENNReal)⁻¹) +
      (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ +
      ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
        ((2 * q + 1 : Nat) : ENNReal) *
          weightedRawTargetOriginUnionBound signatureLimit q (digestReuseWeight q)) := by
  have hrate : (Fintype.card Digest : ENNReal)⁻¹ ≤ privateHistoryGuessRate q := by
    apply ENNReal.inv_le_inv.mpr
    exact Nat.cast_le.mpr (Nat.sub_le _ _)
  have hsplit : privateHistoryGuessRate q = (Fintype.card Digest : ENNReal)⁻¹ +
      (privateHistoryGuessRate q - (Fintype.card Digest : ENNReal)⁻¹) := (add_tsub_cancel_of_le hrate).symm
  apply (forgeAdvantage_le_answerEncoding_jointOts_fts_remaining127 adversary q hqPos hq hqMax).trans
  calc
    _ = (sampledQueryCharge (fun secretKey cache input =>
          parentStoppedEncodingQueryCharge secretKey cache input + ftsParentQueryCharge secretKey cache input) adversary +
        sampledQueryCharge (fun secretKey cache input => otsHashInputCharge secretKey.parameter input +
          FtsProbeSimulation.ftsHashQueryCharge secretKey.parameter cache input) adversary) * (Fintype.card Digest : ENNReal)⁻¹ +
      sampledQueryCharge (fun secretKey cache input => otsHashInputCharge secretKey.parameter input +
          FtsProbeSimulation.ftsHashQueryCharge secretKey.parameter cache input) adversary *
        (privateHistoryGuessRate q - (Fintype.card Digest : ENNReal)⁻¹) +
      (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ +
      ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
        ((2 * q + 1 : Nat) : ENNReal) *
          weightedRawTargetOriginUnionBound signatureLimit q (digestReuseWeight q)) := by
      conv_lhs => rw [hsplit]
      ring
    _ ≤ _ := add_le_add (add_le_add (add_le_add
      (mul_le_mul' (sampled_answerEncoding_parent_ots_fts_queryCharge_le_two adversary q hq) le_rfl) le_rfl) le_rfl) le_rfl

end SphincsSecurity.Concrete
