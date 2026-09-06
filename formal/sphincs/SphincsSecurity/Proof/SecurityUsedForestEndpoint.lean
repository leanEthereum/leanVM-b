import SphincsSecurity.Proof.SecurityUnconditionalGuessesEndpoint
import SphincsSecurity.Proof.FewTimeUsedOccupancy127

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation

theorem probEvent_otherViewedTerminal_le_fts_allowance_usedForest127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (allowance : ENNReal)
    (hfts : Pr[SampledViewedEvent cleanUncoveredEvent | sampledViewedGame adversary] ≤ allowance) :
    Pr[SampledViewedEvent otherViewedTerminalEvent | sampledViewedGame adversary] ≤
      allowance + ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
        ((2 * q + 1 : Nat) : ENNReal) * (29 * ((2 ^ 133 : Nat) : ENNReal)⁻¹)) := by
  change Pr[fun result => SampledViewedEvent cleanUncoveredEvent result ∨
    SampledViewedEvent cleanMessageEvent result ∨ SampledViewedEvent ViewedHonestProperFewTimeLeakWitness result |
      sampledViewedGame adversary] ≤ _
  exact (probEvent_or_le _ _ _).trans (add_le_add hfts
    ((probEvent_or_le _ _ _).trans (add_le_add
      (probEvent_sampled_cleanMessage_le127 adversary q hqPos hq hqMax)
      (probEvent_sampled_honest_leak_le_usedOccupancy127 adversary q hq hqMax))))

theorem forgeAdvantage_le_answerEncoding_guess_allowances_usedForest127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (otsAllowance ftsAllowance : ENNReal)
    (hots : Pr[SampledFirstParentOrOtsWitness | sampledFirstParentRetainedGame adversary] ≤ otsAllowance)
    (hfts : Pr[SampledViewedEvent cleanUncoveredEvent | sampledViewedGame adversary] ≤ ftsAllowance) :
    forgeAdvantage scheme adversary ≤
      sampledQueryCharge (fun secretKey cache input => parentStoppedEncodingQueryCharge secretKey cache input +
        ftsParentQueryCharge secretKey cache input) adversary * (Fintype.card Digest : ENNReal)⁻¹ +
      otsAllowance + ftsAllowance +
      ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ +
        ((2 * q + 1 : Nat) : ENNReal) * (29 * ((2 ^ 133 : Nat) : ENNReal)⁻¹)) := by
  apply (forgeAdvantage_le_answerEncodingQueryCharge_add_first_parent_residual adversary).trans
  apply (add_le_add le_rfl (probEvent_firstParentEncodingResidual_le_ots_allowance adversary _ hots)).trans
  apply (add_le_add le_rfl (add_le_add le_rfl (add_le_add le_rfl
    (probEvent_otherViewedTerminal_le_fts_allowance_usedForest127 adversary q hqPos hq hqMax _ hfts)))).trans_eq
  rw [sampledQueryCharge_add]
  simp only [show Fintype.card Digest = 2 ^ digestBits by simp]
  ring

theorem forgeAdvantage_le_min_unconditional_guesses_usedForest127
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
        ((2 * q + 1 : Nat) : ENNReal) * (29 * ((2 ^ 133 : Nat) : ENNReal)⁻¹)) := by
  have hspace : q + 1 < Fintype.card Digest := by
    have : 2 ^ 127 + 1 < Fintype.card Digest := by norm_num [digestBits]
    omega
  apply (forgeAdvantage_le_answerEncoding_guess_allowances_usedForest127 adversary q hqPos hq hqMax _ _
    (probEvent_sampledFirstParentOrOtsWitness_le_min_sharedHistory adversary q hq hspace)
    (FtsProbeSimulation.probEvent_sampledViewedGame_cleanUncovered_le_min_probeCharge adversary q hq (by omega))).trans_eq
  ring

end SphincsSecurity.Concrete
