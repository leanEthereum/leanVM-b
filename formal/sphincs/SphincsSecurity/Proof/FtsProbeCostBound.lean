import SphincsSecurity.Proof.FtsProbeActualQueryCost

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

theorem cost_le_four_thirds_of_feedback (cost actual probability : ℝ≥0∞) (q : Nat)
    (hcost : cost ≤ q) (hq : q ≤ 2 ^ 126)
    (hfeedback : cost ≤ actual + probability * q)
    (hprobability : probability ≤ cost * (Fintype.card Digest : ℝ≥0∞)⁻¹) :
    cost ≤ (4 / 3 : ℝ≥0∞) * actual := by
  classical
  rcases Classical.em (actual = ∞) with hactual | hactual
  · simp [hactual]
  have hfinite : cost ≠ ∞ := ne_top_of_le_ne_top (by finiteness) hcost
  let fraction : ℝ≥0∞ := (q : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹
  have hbound : cost ≤ actual + cost * fraction := by
    apply hfeedback.trans
    apply add_le_add le_rfl
    apply (mul_le_mul' hprobability le_rfl).trans_eq
    dsimp [fraction]
    rw [show Fintype.card Digest = 2 ^ digestBits by simp]
    ring
  have hcoefficient := OtsProbeSimulation.rootBudget_four_thirds hq
  change fraction * (4 / 3 : ℝ≥0∞) + 1 ≤ (4 / 3 : ℝ≥0∞) at hcoefficient
  have hboundReal := (ENNReal.toReal_le_toReal hfinite (by dsimp [fraction]; finiteness)).mpr hbound
  have hcoefficientReal := (ENNReal.toReal_le_toReal (by dsimp [fraction]; finiteness)
    (by finiteness)).mpr hcoefficient
  rw [ENNReal.toReal_add hactual (by dsimp [fraction]; finiteness), ENNReal.toReal_mul] at hboundReal
  rw [ENNReal.toReal_add (by dsimp [fraction]; finiteness) (by norm_num),
    ENNReal.toReal_mul, ENNReal.toReal_one] at hcoefficientReal
  apply (ENNReal.toReal_le_toReal hfinite (by finiteness)).mp
  rw [ENNReal.toReal_mul]
  have hscaled := mul_le_mul_of_nonneg_right hboundReal
    (show 0 ≤ (4 / 3 : ℝ≥0∞).toReal from ENNReal.toReal_nonneg)
  have hcancel := mul_le_mul_of_nonneg_left hcoefficientReal cost.toReal_nonneg
  nlinarith

theorem maskedFtsProbeCharge_le_four_thirds_actual_cache
    (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (q : Nat) (hq : q ≤ 2 ^ 126)
    (hbound : ∀ table : Coordinate → Digest, (gameAfterSecrets adversary parameter otsSecret
      (fun index tree leafIdx => table (index, tree, leafIdx))).IsQueryBoundP (· matches Sum.inr _) q) :
    maskedFtsProbeCharge adversary parameter otsSecret q ≤
      (4 / 3 : ℝ≥0∞) * sampledActualFtsCacheCount adversary parameter otsSecret := by
  letI : Nonempty Coordinate :=
    ⟨(⟨0, by norm_num [totalHeight]⟩, ⟨0, by norm_num [ftsTrees]⟩,
      ⟨0, by norm_num [ftsTreeHeight]⟩)⟩
  apply cost_le_four_thirds_of_feedback _ _ _ q (maskedFtsProbeCharge_le_q _ _ _ _) hq
    (maskedFtsProbeCharge_le_actual_cache_add_hit adversary parameter otsSecret q hbound)
  simpa only [AdaptiveRevealProbe.chargedExperiment_expectedCost_eq, maskedFtsProbeCharge] using
    AdaptiveRevealProbe.chargedExperiment_probability_le_expectedCost q
      ((maskedRetainedGameAfterSecrets adversary parameter otsSecret).run emptySplitHashCache)

theorem maskedFtsProbeCharge_le_four_thirds_queryCharge
    (adversary : Adversary) (parameter : PublicParameter)
    (hparameter : parameter ∈ support sampleParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (hots : otsSecret ∈ support sampleOtsSecrets) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126) :
    maskedFtsProbeCharge adversary parameter otsSecret q ≤
      (4 / 3 : ℝ≥0∞) * ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
        expectedQueryCharge (ftsHashQueryCharge parameter)
          (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅ := by
  apply (maskedFtsProbeCharge_le_four_thirds_actual_cache adversary parameter otsSecret q hqMax ?_).trans
  · exact mul_le_mul' le_rfl (sampledActualFtsCacheCount_le_queryCharge adversary parameter otsSecret)
  · intro table
    exact isQueryBoundP_gameAfterSecrets adversary q hq hparameter hots
      (mem_support_sampleFtsSecrets (fun index tree leafIdx => table (index, tree, leafIdx)))

end SphincsSecurity.Concrete.FtsProbeSimulation
