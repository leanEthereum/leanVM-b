import SphincsSecurity.Proof.OtsProbeSharedHistoryGame
import SphincsSecurity.Proof.SecurityAnswerEncodingEndpoint

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal
open OtsProbeSimulation

theorem forgeAdvantage_le_answerEncoding_min_sharedHistory_remaining127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary ≤
      sampledQueryCharge (fun secretKey cache input => parentStoppedEncodingQueryCharge secretKey cache input +
        ftsParentQueryCharge secretKey cache input) adversary * (Fintype.card Digest : ENNReal)⁻¹ +
      min (sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary * privateHistoryGuessRate q)
        ((sampledNativeHistoryStartCharge Finset.univ adversary q +
          sampledNativeHistoryPrivateCharge Finset.univ adversary q) * (Fintype.card Digest : ENNReal)⁻¹) +
      sampledQueryCharge (fun secretKey => FtsProbeSimulation.ftsHashQueryCharge secretKey.parameter) adversary * privateHistoryGuessRate q +
      (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ +
      ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
        ((2 * q + 1 : Nat) : ENNReal) *
          weightedRawTargetOriginUnionBound signatureLimit q (digestReuseWeight q)) := by
  have hspace : q + 1 < Fintype.card Digest := by
    have : 2 ^ 127 + 1 < Fintype.card Digest := by norm_num [digestBits]
    omega
  have hots := probEvent_sampledFirstParentOrOtsWitness_le_min_sharedHistory adversary q hq hspace
  apply (forgeAdvantage_le_answerEncodingQueryCharge_add_first_parent_residual adversary).trans
  apply (add_le_add le_rfl (probEvent_firstParentEncodingResidual_le_ots_allowance adversary _ hots)).trans
  apply (add_le_add le_rfl (add_le_add le_rfl (add_le_add le_rfl
    (probEvent_otherViewedTerminal_le_queryRate_remaining127 adversary q hqPos hq hqMax)))).trans_eq
  rw [sampledQueryCharge_add]
  simp only [show Fintype.card Digest = 2 ^ digestBits by simp]
  ring

theorem forgeAdvantage_le_answerEncoding_min_queryBudget_remaining127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary ≤
      sampledQueryCharge (fun secretKey cache input => parentStoppedEncodingQueryCharge secretKey cache input +
        ftsParentQueryCharge secretKey cache input) adversary * (Fintype.card Digest : ENNReal)⁻¹ +
      min (sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary * privateHistoryGuessRate q)
        ((q : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹) +
      sampledQueryCharge (fun secretKey => FtsProbeSimulation.ftsHashQueryCharge secretKey.parameter) adversary * privateHistoryGuessRate q +
      (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ +
      ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
        ((2 * q + 1 : Nat) : ENNReal) *
          weightedRawTargetOriginUnionBound signatureLimit q (digestReuseWeight q)) := by
  apply (forgeAdvantage_le_answerEncoding_min_sharedHistory_remaining127 adversary q hqPos hq hqMax).trans
  apply add_le_add _ le_rfl
  apply add_le_add _ le_rfl
  apply add_le_add _ le_rfl
  exact add_le_add le_rfl (min_le_min le_rfl
    (mul_le_mul' (sampledNativeHistoryCharge_le_query_budget Finset.univ adversary q) le_rfl))

end SphincsSecurity.Concrete
