import SphincsSecurity.Proof.OtsProbeInitializedRate
import SphincsSecurity.Proof.OtsProbeNativeDirectBound

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local irreducible] instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem sampled_actualOtsCount_rate_le_directCharge
    (adversary : Adversary) (q : Nat) (hqMax : q ≤ 2 ^ 126) :
    sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary *
        privateHistoryGuessRate q ≤
      sampledQueryCharge (fun secretKey => directOtsQueryCharge secretKey.parameter) adversary *
        (Fintype.card Digest : ENNReal)⁻¹ := by
  apply (mul_le_mul' le_rfl (privateHistoryGuessRate_le_four_thirds hqMax)).trans_eq
  unfold sampledQueryCharge directOtsQueryCharge
  simp_rw [expectedQueryCharge_mul, ← mul_assoc, ENNReal.tsum_mul_right]
  simp only [show Fintype.card Digest = 2 ^ digestBits by simp, mul_assoc]

theorem sampledNativeTerminalRisk_le_actualOtsCount_rate_add_erasure
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126) :
    sampledNativeTerminalRisk adversary (q + 1) ≤
      sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary *
        privateHistoryGuessRate q + (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  apply (sampledNativeTerminalRisk_le_missing_add_erasure adversary q hq hqMax).trans
  apply add_le_add _ le_rfl
  exact (sampledNativeMissingAllowances_le_directRisk Finset.univ adversary q hq (q + 1)).trans
    (sampledInitializedNativeDirectRisk_le_actualOtsCount_rate Finset.univ adversary (q + 1) q
      (hqMax.trans_lt (by norm_num [digestBits])))

theorem probEvent_sampled_prehitFree_residual_le_actualOtsCount_rate_add_erasure
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126) :
    Pr[prehitFreeResidualOtsOpeningEvent | sampledEncodingPrehitViewedGame adversary] ≤
      sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary *
        privateHistoryGuessRate q + (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  apply (probEvent_sampled_prehitFree_residual_le_nativeTerminalFailure adversary (q + 1)).trans
  rw [probEvent_sampledNativeTerminalFailure_eq_risk]
  exact sampledNativeTerminalRisk_le_actualOtsCount_rate_add_erasure adversary q hq hqMax

end SphincsSecurity.Concrete.OtsProbeSimulation
