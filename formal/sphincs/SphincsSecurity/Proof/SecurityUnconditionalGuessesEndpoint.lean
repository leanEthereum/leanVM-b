import SphincsSecurity.Proof.SecuritySharedHistoryEndpoint
import SphincsSecurity.Proof.FtsProbeUnconditionalCharge

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation

theorem forgeAdvantage_le_answerEncoding_guess_allowances_remaining127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (otsAllowance ftsAllowance : ENNReal)
    (hots : Pr[SampledFirstParentOrOtsWitness | sampledFirstParentRetainedGame adversary] ≤ otsAllowance)
    (hfts : Pr[SampledViewedEvent cleanUncoveredEvent | sampledViewedGame adversary] ≤ ftsAllowance) :
    forgeAdvantage scheme adversary ≤
      sampledQueryCharge (fun secretKey cache input => parentStoppedEncodingQueryCharge secretKey cache input +
        ftsParentQueryCharge secretKey cache input) adversary * (Fintype.card Digest : ENNReal)⁻¹ +
      otsAllowance + ftsAllowance +
      ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
        ((2 * q + 1 : Nat) : ENNReal) * weightedRawTargetOriginUnionBound signatureLimit q (digestReuseWeight q)) := by
  apply (forgeAdvantage_le_answerEncodingQueryCharge_add_first_parent_residual adversary).trans
  apply (add_le_add le_rfl (probEvent_firstParentEncodingResidual_le_ots_allowance adversary _ hots)).trans
  apply (add_le_add le_rfl (add_le_add le_rfl (add_le_add le_rfl
    (probEvent_otherViewedTerminal_le_fts_allowance_remaining127 adversary q hqPos hq hqMax _ hfts)))).trans_eq
  rw [sampledQueryCharge_add]
  simp only [show Fintype.card Digest = 2 ^ digestBits by simp]
  ring

theorem forgeAdvantage_le_unconditional_guess_charges_remaining127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary ≤
      (sampledQueryCharge (fun secretKey cache input => parentStoppedEncodingQueryCharge secretKey cache input +
        ftsParentQueryCharge secretKey cache input) adversary +
        (sampledNativeHistoryStartCharge Finset.univ adversary q + sampledNativeHistoryPrivateCharge Finset.univ adversary q) +
        FtsProbeSimulation.sampledMaskedFtsProbeCharge adversary q) * (Fintype.card Digest : ENNReal)⁻¹ +
      (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ +
      ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
        ((2 * q + 1 : Nat) : ENNReal) * weightedRawTargetOriginUnionBound signatureLimit q (digestReuseWeight q)) := by
  have hspace : q + 1 < Fintype.card Digest := by
    have : 2 ^ 127 + 1 < Fintype.card Digest := by norm_num [digestBits]
    omega
  have hots := (probEvent_sampledFirstParentOrOtsWitness_le_min_sharedHistory adversary q hq hspace).trans
    (add_le_add (min_le_right _ _) le_rfl)
  apply (forgeAdvantage_le_answerEncoding_guess_allowances_remaining127 adversary q hqPos hq hqMax _ _ hots
    (FtsProbeSimulation.probEvent_sampledViewedGame_cleanUncovered_le_probeCharge adversary q hq)).trans_eq
  ring

theorem forgeAdvantage_le_min_unconditional_guesses_remaining127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary ≤
      sampledQueryCharge (fun secretKey cache input => parentStoppedEncodingQueryCharge secretKey cache input +
        ftsParentQueryCharge secretKey cache input) adversary * (Fintype.card Digest : ENNReal)⁻¹ +
      min (sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary * privateHistoryGuessRate q)
        ((sampledNativeHistoryStartCharge Finset.univ adversary q + sampledNativeHistoryPrivateCharge Finset.univ adversary q) *
          (Fintype.card Digest : ENNReal)⁻¹) +
      min (sampledQueryCharge (fun secretKey => FtsProbeSimulation.ftsHashQueryCharge secretKey.parameter) adversary * privateHistoryGuessRate q)
        (FtsProbeSimulation.sampledMaskedFtsProbeCharge adversary q * (Fintype.card Digest : ENNReal)⁻¹) +
      (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ +
      ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
        ((2 * q + 1 : Nat) : ENNReal) * weightedRawTargetOriginUnionBound signatureLimit q (digestReuseWeight q)) := by
  have hspace : q + 1 < Fintype.card Digest := by
    have : 2 ^ 127 + 1 < Fintype.card Digest := by norm_num [digestBits]
    omega
  apply (forgeAdvantage_le_answerEncoding_guess_allowances_remaining127 adversary q hqPos hq hqMax _ _
    (probEvent_sampledFirstParentOrOtsWitness_le_min_sharedHistory adversary q hq hspace)
    (FtsProbeSimulation.probEvent_sampledViewedGame_cleanUncovered_le_min_probeCharge adversary q hq (by omega))).trans_eq
  ring

theorem forgeAdvantage_le_min_guess_query_budgets_remaining127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary ≤
      sampledQueryCharge (fun secretKey cache input => parentStoppedEncodingQueryCharge secretKey cache input +
        ftsParentQueryCharge secretKey cache input) adversary * (Fintype.card Digest : ENNReal)⁻¹ +
      min (sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary * privateHistoryGuessRate q)
        ((q : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹) +
      min (sampledQueryCharge (fun secretKey => FtsProbeSimulation.ftsHashQueryCharge secretKey.parameter) adversary * privateHistoryGuessRate q)
        ((q : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹) +
      (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ +
      ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
        ((2 * q + 1 : Nat) : ENNReal) * weightedRawTargetOriginUnionBound signatureLimit q (digestReuseWeight q)) := by
  apply (forgeAdvantage_le_min_unconditional_guesses_remaining127 adversary q hqPos hq hqMax).trans
  apply add_le_add _ le_rfl
  apply add_le_add _ le_rfl
  exact add_le_add (add_le_add le_rfl (min_le_min le_rfl
    (mul_le_mul' (sampledNativeHistoryCharge_le_query_budget Finset.univ adversary q) le_rfl)))
    (min_le_min le_rfl (mul_le_mul' (FtsProbeSimulation.sampledMaskedFtsProbeCharge_le_query_budget adversary q) le_rfl))

end SphincsSecurity.Concrete
