import SphincsSecurity.Proof.OtsProbePrivateErasedGame
import SphincsSecurity.Proof.SecurityAnswerEncodingEndpoint

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal
open OtsProbeSimulation

theorem forgeAdvantage_le_answerEncoding_min_erasedPrefix_remaining127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary ≤
      sampledQueryCharge (fun secretKey cache input => parentStoppedEncodingQueryCharge secretKey cache input +
        ftsParentQueryCharge secretKey cache input) adversary * (Fintype.card Digest : ENNReal)⁻¹ +
      min (sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary * privateHistoryGuessRate q)
        ((sampledNativeStartPrefixCharge Finset.univ adversary (q + 1) q +
          sampledNativePrivateErasedCharge Finset.univ adversary (q + 1) q) * (Fintype.card Digest : ENNReal)⁻¹) +
      sampledQueryCharge (fun secretKey => FtsProbeSimulation.ftsHashQueryCharge secretKey.parameter) adversary * privateHistoryGuessRate q +
      (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ +
      ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
        ((2 * q + 1 : Nat) : ENNReal) *
          weightedRawTargetOriginUnionBound signatureLimit q (digestReuseWeight q)) := by
  have hspace : q + 1 < Fintype.card Digest := by
    have : 2 ^ 127 + 1 < Fintype.card Digest := by norm_num [digestBits]
    omega
  have hots := probEvent_sampledFirstParentOrOtsWitness_le_min_erased_prefix_charge adversary q hq hspace
  apply (forgeAdvantage_le_answerEncodingQueryCharge_add_first_parent_residual adversary).trans
  apply (add_le_add le_rfl (probEvent_firstParentEncodingResidual_le_ots_allowance adversary _ hots)).trans
  apply (add_le_add le_rfl (add_le_add le_rfl (add_le_add le_rfl
    (probEvent_otherViewedTerminal_le_queryRate_remaining127 adversary q hqPos hq hqMax)))).trans_eq
  rw [sampledQueryCharge_add]
  simp only [show Fintype.card Digest = 2 ^ digestBits by simp]
  ring

end SphincsSecurity.Concrete
