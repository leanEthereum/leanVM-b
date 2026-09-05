import SphincsSecurity.Proof.Security126Completion

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local irreducible] instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem sampledNativeTerminalRisk_le_directCharge_add_erasure
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126) :
    sampledNativeTerminalRisk adversary (q + 1) ≤
      sampledQueryCharge (fun secretKey => directOtsQueryCharge secretKey.parameter) adversary *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ + (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  apply (sampledNativeTerminalRisk_le_missing_add_erasure adversary q hq hqMax).trans
  apply add_le_add _ le_rfl
  exact (sampledNativeMissingAllowances_le_directRisk Finset.univ adversary q hq (q + 1)).trans
    (sampledInitializedNativeDirectRisk_le_directCharge Finset.univ adversary (q + 1) q hqMax)

theorem probEvent_sampled_prehitFree_residual_le_directCharge_add_erasure
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126) :
    Pr[prehitFreeResidualOtsOpeningEvent | sampledEncodingPrehitViewedGame adversary] ≤
      sampledQueryCharge (fun secretKey => directOtsQueryCharge secretKey.parameter) adversary *
        (Fintype.card Digest : ENNReal)⁻¹ + (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  apply (probEvent_sampled_prehitFree_residual_le_nativeTerminalFailure adversary (q + 1)).trans
  rw [probEvent_sampledNativeTerminalFailure_eq_risk]
  simpa only [show Fintype.card Digest = 2 ^ digestBits by simp] using
    sampledNativeTerminalRisk_le_directCharge_add_erasure adversary q hq hqMax

end SphincsSecurity.Concrete.OtsProbeSimulation
