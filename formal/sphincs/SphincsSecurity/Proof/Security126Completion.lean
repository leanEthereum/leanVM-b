import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeNativeRetainedProjection
import SphincsSecurity.Proof.OtsProbePrehitOpeningProjection

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem probEvent_prehitFreeRetainedVerifyProbe_le_nativeTerminalFailure
    (targets : Finset Position) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[prehitFreeRetainedVerifyProbeEvent parameter table ftsSecret |
      prehitRetainedQueryTrace adversary parameter table ftsSecret] ≤
      Pr[fun verdict => verdict = true | nativeTerminalFailureAfterRoot targets adversary parameter table ftsSecret fuel] := by
  apply le_trans _ (probEvent_winningRetainedVerifyProbe_le_nativeTerminalFailure targets adversary parameter table ftsSecret fuel)
  rw [← prehitRetainedQueryTrace_cache_projection, probEvent_map]
  exact probEvent_mono (fun _ _ hevent => hevent.2)

theorem sampledPrehitFreeRetainedVerifyProbeRisk_le_nativeTerminalFailure
    (adversary : Adversary) (fuel : Nat) :
    sampledPrehitFreeRetainedVerifyProbeRisk adversary ≤
      Pr[fun verdict => verdict = true | sampledNativeTerminalFailure adversary fuel] := by
  simp only [sampledPrehitFreeRetainedVerifyProbeRisk, sampledNativeTerminalFailure, probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro parameter
  apply mul_le_mul' le_rfl
  calc
    _ ≤ ∑' table, Pr[= table | sampleOtsHashTable] *
        ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
          Pr[fun verdict => verdict = true | nativeTerminalFailureAfterRoot Finset.univ adversary parameter table ftsSecret fuel] := by
      apply ENNReal.tsum_le_tsum
      intro table
      apply mul_le_mul' le_rfl
      apply ENNReal.tsum_le_tsum
      intro ftsSecret
      exact mul_le_mul' le_rfl (probEvent_prehitFreeRetainedVerifyProbe_le_nativeTerminalFailure
        Finset.univ adversary parameter table ftsSecret fuel)
    _ = _ := by
      simp_rw [← ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro ftsSecret
      apply tsum_congr
      intro table
      exact mul_left_comm _ _ _

theorem probEvent_sampled_prehitFree_residual_le_nativeTerminalFailure
    (adversary : Adversary) (fuel : Nat) :
    Pr[prehitFreeResidualOtsOpeningEvent | sampledEncodingPrehitViewedGame adversary] ≤
      Pr[fun verdict => verdict = true | sampledNativeTerminalFailure adversary fuel] :=
  (probEvent_sampled_prehitFree_residual_le_retainedVerifyProbe adversary).trans
    (sampledPrehitFreeRetainedVerifyProbeRisk_le_nativeTerminalFailure adversary fuel)

theorem probEvent_sampled_prehitFree_residual_le_refinedReserve_add_erasure
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126) :
    Pr[prehitFreeResidualOtsOpeningEvent | sampledEncodingPrehitViewedGame adversary] ≤
      sampledQueryCharge otsOpeningRefinedQueryReserve adversary * (Fintype.card Digest : ENNReal)⁻¹ +
        (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  have hbound := probEvent_sampledNativeTerminalFailure_add_rootMatch_le_refinedReserve
    ∅ (by simp) (by simp) adversary q hq hqMax
  have hfailure := probEvent_sampled_prehitFree_residual_le_nativeTerminalFailure adversary (q + 1)
  apply hfailure.trans
  apply (show Pr[fun verdict => verdict = true | sampledNativeTerminalFailure adversary (q + 1)] ≤
      Pr[fun verdict => verdict = true | sampledNativeTerminalFailure adversary (q + 1)] +
        sampledNativeFinalRootMatchRisk Finset.univ ∅ adversary (q + 1) from le_add_of_nonneg_right zero_le).trans
  simpa only [show Fintype.card Digest = 2 ^ digestBits by simp] using hbound

theorem security126_of_completed_native_boundary : HasClassicalSecurityBits scheme 126 := by
  apply security126_of_sampled_prehitFree_otsOpening_le_refinedQueryReserve_add_query_erasure
  intro q _hqPos adversary hq hqMax
  exact probEvent_sampled_prehitFree_residual_le_refinedReserve_add_erasure adversary q hq hqMax

end SphincsSecurity.Concrete.OtsProbeSimulation
