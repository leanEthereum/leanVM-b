import SphincsSecurity.Proof.OtsProbeNativeAfterRootRisk

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] maskedPublishedTreeRoot instFintypePosition
set_option backward.isDefEq.respectTransparency false

noncomputable def sampledNativeTerminalRisk (adversary : Adversary) (fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | sampleOtsHashTable] *
        ∑' trace, Pr[= trace | nativeChainTraceAfterRoot Finset.univ parameter table ftsSecret fuel
          (fun root => retainedGameRestComputation adversary ⟨root, parameter⟩)] * resolvedOutcomeFailureRisk trace.1

theorem sampledNativeTerminalRisk_le_missing_add_erasure_of_querySpace
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqSpace : q + 1 < Fintype.card Digest) :
    sampledNativeTerminalRisk adversary (q + 1) ≤ sampledNativeMissingAllowances Finset.univ adversary (q + 1) +
      (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  unfold sampledNativeTerminalRisk sampledNativeMissingAllowances
  calc
    _ ≤ ∑' parameter, Pr[= parameter | sampleParameter] *
        ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
          ∑' table, Pr[= table | sampleOtsHashTable] *
            ((liveStartProbeAllowance (nativeChronologicalRetainedComputation adversary parameter ftsSecret)
                (ensuredInitialContext Finset.univ) (q + 1) table +
              ∑ target : Position, privateLiveMissingProbeAllowance target
                (nativeChronologicalRetainedComputation adversary parameter ftsSecret) (ensuredInitialContext Finset.univ) (q + 1) table) +
              (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹) := by
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
          exact expectedNativeTerminalRisk_afterRoot_le_missing_add_erasure_of_querySpace adversary q hq hqSpace
            parameter hparameter table ftsSecret hfts
        · simp [probOutput_eq_zero_of_not_mem_support hfts]
      · simp [probOutput_eq_zero_of_not_mem_support hparameter]
    _ = _ := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
      rw [tsum_probOutput_eq_one' (mx := sampleParameter) (by simp),
        tsum_probOutput_eq_one' (mx := sampleFtsSecrets) (by simp),
        tsum_probOutput_eq_one' (mx := sampleOtsHashTable) (by simp)]
      simp only [one_mul]

theorem sampledNativeTerminalRisk_le_missing_add_erasure
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126) :
    sampledNativeTerminalRisk adversary (q + 1) ≤ sampledNativeMissingAllowances Finset.univ adversary (q + 1) +
      (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  exact sampledNativeTerminalRisk_le_missing_add_erasure_of_querySpace adversary q hq
    (by
      have hspace : 2 ^ 126 + 1 < Fintype.card Digest := by norm_num [digestBits]
      omega)

theorem sampledNativeTerminalRisk_add_rootMatch_le_refinedReserve
    (roots : Finset Position) (hroots : ∀ target ∈ roots, IsLayerRoot target)
    (hne : ∀ target ∈ roots, target ≠ layerRootPosition topLayer rootTree)
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126) :
    sampledNativeTerminalRisk adversary (q + 1) + sampledNativeFinalRootMatchRisk Finset.univ roots adversary (q + 1) ≤
      sampledQueryCharge otsOpeningRefinedQueryReserve adversary * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
        (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  have hreserve := sampledNativeMissingAllowances_add_rootMatch_le_refinedReserve Finset.univ roots
    (fun target _ => Finset.mem_univ target) hroots hne adversary q hq hqMax (q + 1)
  calc
    _ ≤ (sampledNativeMissingAllowances Finset.univ adversary (q + 1) + (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹) +
        sampledNativeFinalRootMatchRisk Finset.univ roots adversary (q + 1) :=
      add_le_add (sampledNativeTerminalRisk_le_missing_add_erasure adversary q hq hqMax) le_rfl
    _ = (sampledNativeMissingAllowances Finset.univ adversary (q + 1) +
        sampledNativeFinalRootMatchRisk Finset.univ roots adversary (q + 1)) +
        (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by ac_rfl
    _ ≤ _ := add_le_add hreserve le_rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
