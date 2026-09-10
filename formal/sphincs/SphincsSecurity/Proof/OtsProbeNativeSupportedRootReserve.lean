import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeNativeSupportedRootProjection
import SphincsSecurity.Proof.OtsProbeSampledJointRootRisk

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def sampledNativeFinalRootMatchRisk
    (targets roots : Finset Position) (adversary : Adversary) (fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | sampleOtsHashTable] *
        Pr[fun trace => ∃ target ∈ roots, NativeFinalRootHistoryMatch parameter target trace |
          nativeChainTraceAfterRoot targets parameter table ftsSecret fuel
            (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩)]

theorem sampledNativeFinalRootMatchRisk_le_chargedRootRisk
    (targets roots : Finset Position) (hroots : ∀ target ∈ roots, IsLayerRoot target)
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (fuel : Nat) :
    sampledNativeFinalRootMatchRisk targets roots adversary fuel ≤
      sampledInitializedChargedRootRisk targets roots adversary fuel q := by
  unfold sampledNativeFinalRootMatchRisk sampledInitializedChargedRootRisk initializedChargedRootRisk
  apply ENNReal.tsum_le_tsum
  intro parameter
  by_cases hparameter : parameter ∈ support sampleParameter
  · apply mul_le_mul_right
    apply ENNReal.tsum_le_tsum
    intro ftsSecret
    by_cases hfts : ftsSecret ∈ support sampleFtsSecrets
    · apply mul_le_mul_right
      apply ENNReal.tsum_le_tsum
      intro table
      apply mul_le_mul_right
      exact probEvent_exists_nativeRetainedFinalRootMatch_le_initializedCutHitSum targets roots hroots adversary q hq
        parameter hparameter table ftsSecret hfts fuel
    · simp [probOutput_eq_zero_of_not_mem_support hfts]
  · simp [probOutput_eq_zero_of_not_mem_support hparameter]

theorem sampledNativeDirectRisk_add_finalRootMatch_le_refinedReserve
    (targets roots : Finset Position) (hsubset : roots ⊆ targets)
    (hroots : ∀ target ∈ roots, IsLayerRoot target) (hne : ∀ target ∈ roots, target ≠ layerRootPosition topLayer rootTree)
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126) (fuel : Nat) :
    sampledInitializedNativeDirectRisk targets adversary fuel q + sampledNativeFinalRootMatchRisk targets roots adversary fuel ≤
      sampledQueryCharge otsOpeningRefinedQueryReserve adversary * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  exact (add_le_add le_rfl (sampledNativeFinalRootMatchRisk_le_chargedRootRisk targets roots hroots adversary q hq fuel)).trans
    (sampledInitializedNativeDirectRisk_add_chargedRootRisk_le_refinedReserve targets roots hsubset hroots hne adversary fuel q hqMax)

end SphincsSecurity.Concrete.OtsProbeSimulation
