import SphincsSecurity.Proof.FtsProbeQueryBudget126
import SphincsSecurity.Proof.OtsProbePrivateHistoryRate

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (privateHistoryGuessRate privateHistoryGuessRate_ne_top)

theorem historyRate_feedback_coefficient (q : Nat) (hq : q < Fintype.card Digest) :
    ((q : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹) *
        ((Fintype.card Digest : ENNReal) * privateHistoryGuessRate q) + 1 =
      (Fintype.card Digest : ENNReal) * privateHistoryGuessRate q := by
  have hspace : (Fintype.card Digest : ENNReal) ≠ 0 := by
    exact_mod_cast (show Fintype.card Digest ≠ 0 from Fintype.card_ne_zero)
  have hremaining : ((Fintype.card Digest - q : Nat) : ENNReal) ≠ 0 := by
    exact_mod_cast Nat.sub_ne_zero_of_lt hq
  have hcancel : ((Fintype.card Digest - q : Nat) : ENNReal) * privateHistoryGuessRate q = 1 :=
    ENNReal.mul_inv_cancel hremaining (by simp)
  have hsum : (q : ENNReal) + ((Fintype.card Digest - q : Nat) : ENNReal) =
      (Fintype.card Digest : ENNReal) := by
    exact_mod_cast (show q + (Fintype.card Digest - q) = Fintype.card Digest by omega)
  calc
    _ = (q : ENNReal) * privateHistoryGuessRate q *
        ((Fintype.card Digest : ENNReal)⁻¹ * (Fintype.card Digest : ENNReal)) + 1 := by ring
    _ = (q : ENNReal) * privateHistoryGuessRate q + 1 := by
      rw [ENNReal.inv_mul_cancel hspace (by simp), mul_one]
    _ = _ := by rw [← hcancel, ← add_mul, hsum]

theorem maskedFtsProbeCharge_le_historyRate_actual_cache
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (q : Nat)
    (hq : q < Fintype.card Digest)
    (hbound : ∀ table : Coordinate → Digest, (gameAfterSecrets adversary parameter otsSecret
      (fun index tree leafIdx => table (index, tree, leafIdx))).IsQueryBoundP (· matches Sum.inr _) q) :
    maskedFtsProbeCharge adversary parameter otsSecret q ≤
      ((Fintype.card Digest : ENNReal) * privateHistoryGuessRate q) *
        sampledActualFtsCacheCount adversary parameter otsSecret := by
  letI : Nonempty Coordinate :=
    ⟨(⟨0, by norm_num [totalHeight]⟩, ⟨0, by norm_num [ftsTrees]⟩,
      ⟨0, by norm_num [ftsTreeHeight]⟩)⟩
  have hrate := privateHistoryGuessRate_ne_top hq
  refine cost_le_factor_of_feedback _ _ _ _ q (maskedFtsProbeCharge_le_q _ _ _ _) (by finiteness) ?_
    (maskedFtsProbeCharge_le_actual_cache_add_hit adversary parameter otsSecret q hbound) ?_
  · simpa only [show Fintype.card Digest = 2 ^ digestBits by simp] using
      (historyRate_feedback_coefficient q hq).le
  · simpa only [AdaptiveRevealProbe.chargedExperiment_expectedCost_eq, maskedFtsProbeCharge] using
      AdaptiveRevealProbe.chargedExperiment_probability_le_expectedCost q
        ((maskedRetainedGameAfterSecrets adversary parameter otsSecret).run emptySplitHashCache)

theorem maskedFtsProbeCharge_le_historyRate_queryCharge
    (adversary : Adversary) (parameter : PublicParameter)
    (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q) (hqSpace : q < Fintype.card Digest) :
    maskedFtsProbeCharge adversary parameter otsSecret q ≤
      ((Fintype.card Digest : ENNReal) * privateHistoryGuessRate q) *
        ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
          expectedQueryCharge (ftsHashQueryCharge parameter)
            (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅ := by
  apply (maskedFtsProbeCharge_le_historyRate_actual_cache adversary parameter otsSecret q hqSpace ?_).trans
  · exact mul_le_mul' le_rfl (sampledActualFtsCacheCount_le_queryCharge adversary parameter otsSecret)
  · intro table
    exact isQueryBoundP_gameAfterSecrets adversary q hq hparameter hots
      (mem_support_sampleFtsSecrets (fun index tree leafIdx => table (index, tree, leafIdx)))

theorem sampledMaskedFtsProbeCharge_le_historyRate_queryCharge
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqSpace : q < Fintype.card Digest) :
    sampledMaskedFtsProbeCharge adversary q ≤
      ((Fintype.card Digest : ENNReal) * privateHistoryGuessRate q) *
        sampledQueryCharge (fun secretKey => ftsHashQueryCharge secretKey.parameter) adversary := by
  rw [sampledMaskedFtsProbeCharge, sampledQueryCharge, sampleSecrets, tsum_probOutput_bind_mul]
  simp only [tsum_probOutput_bind_mul, tsum_probOutput_pure_mul]
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro parameter
  rw [mul_left_comm ((Fintype.card Digest : ENNReal) * privateHistoryGuessRate q)]
  by_cases hparameter : parameter ∈ support sampleParameter
  · apply mul_le_mul' le_rfl
    rw [← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro otsSecret
    rw [mul_left_comm ((Fintype.card Digest : ENNReal) * privateHistoryGuessRate q)]
    by_cases hots : otsSecret ∈ support sampleOtsSecrets
    · exact mul_le_mul' le_rfl
        (maskedFtsProbeCharge_le_historyRate_queryCharge adversary parameter hparameter otsSecret hots q hq hqSpace)
    · rw [probOutput_eq_zero_of_not_mem_support hots, zero_mul, zero_mul]
  · rw [probOutput_eq_zero_of_not_mem_support hparameter, zero_mul, zero_mul]

theorem probEvent_sampledViewedGame_cleanUncovered_le_queryRate
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqSpace : q < Fintype.card Digest) :
    Pr[SampledViewedEvent cleanUncoveredEvent | sampledViewedGame adversary] ≤
      sampledQueryCharge (fun secretKey => ftsHashQueryCharge secretKey.parameter) adversary *
        privateHistoryGuessRate q := by
  apply (probEvent_sampledViewedGame_cleanUncovered_le_probeCharge adversary q hq).trans
  apply (mul_le_mul' (sampledMaskedFtsProbeCharge_le_historyRate_queryCharge adversary q hq hqSpace) le_rfl).trans_eq
  have hspace : (Fintype.card Digest : ENNReal) ≠ 0 := by
    exact_mod_cast (show Fintype.card Digest ≠ 0 from Fintype.card_ne_zero)
  calc
    _ = (sampledQueryCharge (fun secretKey => ftsHashQueryCharge secretKey.parameter) adversary *
        privateHistoryGuessRate q) * ((Fintype.card Digest : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹) := by ring
    _ = _ := by rw [ENNReal.mul_inv_cancel hspace (by simp), mul_one]

end SphincsSecurity.Concrete.FtsProbeSimulation
