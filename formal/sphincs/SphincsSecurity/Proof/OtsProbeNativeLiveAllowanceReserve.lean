import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeLivePrivateAllowanceCounting
import SphincsSecurity.Proof.OtsProbeLiveStartAllowanceCounting
import SphincsSecurity.Proof.OtsProbeNativeLiveBudget
import SphincsSecurity.Proof.OtsProbeNativeSupportedRootReserve
import SphincsSecurity.Proof.OtsProbePrivateMissingAllowance

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem sum_sampledEnsuredNativeProbeCut_startHits_eq_liveAllowance_of_liveBound
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (fuel q : Nat)
    (hbound : ∀ table, LiveResolvedQueryBound LazyRevealProbe.IsProbe computation q (ensuredInitialContext targets) fuel table) :
    (∑ ordinal ∈ Finset.range q,
      Pr[LiveUnresolvedStartHit nativeCutCandidate | sampledEnsuredNativeProbeCut targets computation fuel ordinal]) =
      ∑' table, Pr[= table | sampleOtsHashTable] * liveStartProbeAllowance computation (ensuredInitialContext targets) fuel table := by
  simp only [sampledEnsuredNativeProbeCut, probEvent_bind_eq_tsum]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  simp only [← Finset.mul_sum]
  apply tsum_congr
  intro table
  rw [sum_nativeProbeCut_startHits_eq_liveAllowance_of_liveBound computation q (ensuredInitialContext targets) fuel table
    (ensuredInitialContext_valid targets).valuesConsistent
    (startTableAgrees_of_deferredCompletable (ensuredInitialContext_completable targets table)) (hbound table)]

theorem sum_privateHits_ensuredInitial_eq_liveAllowance_of_liveBound
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (fuel q : Nat) (table : OtsSecretIndex → HashOutput)
    (hbound : LiveResolvedQueryBound LazyRevealProbe.IsProbe computation q (ensuredInitialContext targets) fuel table) :
    (∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
      Pr[PrivateCandidatePairHit | privateResolvedSelectedCandidate target (privateRawCutCandidate target) <$>
        runPrivateResolvedView target table (ensuredInitialContext targets) fuel (privatePositionProbeCutAt target computation ordinal)]) =
      ∑ target ∈ targets, privateLiveProbeAllowance target computation (ensuredInitialContext targets) fuel table := by
  apply Finset.sum_congr rfl
  intro target _
  apply sum_privateProbeCut_hits_eq_liveAllowance_of_liveBound target computation q (ensuredInitialContext targets) fuel table
    (ensuredInitialContext_valid targets).valuesConsistent
    (startTableAgrees_of_deferredCompletable (ensuredInitialContext_completable targets table))
    (by simp [ensuredInitialContext, LazyRevealProbe.State.empty])
  apply LiveResolvedQueryBound.of_imp _ hbound
  intro input hinput
  cases input <;> simp_all [IsPrivatePositionProbe, LazyRevealProbe.IsProbe]

theorem initializedNativeDirectRisk_eq_allowances_of_gameBudget
    (targets : Finset Position) (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (hfts : ftsSecret ∈ support sampleFtsSecrets) (fuel : Nat) :
    initializedNativeDirectRisk targets adversary parameter ftsSecret fuel q =
      ∑' table, Pr[= table | sampleOtsHashTable] *
        (liveStartProbeAllowance (nativeChronologicalRetainedComputation adversary parameter ftsSecret)
          (ensuredInitialContext targets) fuel table +
          ∑ target ∈ targets, privateLiveProbeAllowance target
            (nativeChronologicalRetainedComputation adversary parameter ftsSecret) (ensuredInitialContext targets) fuel table) := by
  have hbound := fun table => liveResolvedProbeBound_nativeRetained_of_gameBudget targets adversary q hq
    parameter hparameter table ftsSecret hfts fuel
  unfold initializedNativeDirectRisk
  rw [sum_sampledEnsuredNativeProbeCut_startHits_eq_liveAllowance_of_liveBound targets _ fuel q hbound]
  simp_rw [sum_privateHits_ensuredInitial_eq_liveAllowance_of_liveBound targets _ fuel q _ (hbound _)]
  simp only [mul_add, ENNReal.tsum_add]

theorem nativeMissingAllowances_le_directRisk_of_gameBudget
    (targets : Finset Position) (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (hfts : ftsSecret ∈ support sampleFtsSecrets) (fuel : Nat) :
    (∑' table, Pr[= table | sampleOtsHashTable] *
      (liveStartProbeAllowance (nativeChronologicalRetainedComputation adversary parameter ftsSecret)
        (ensuredInitialContext targets) fuel table +
        ∑ target ∈ targets, privateLiveMissingProbeAllowance target
          (nativeChronologicalRetainedComputation adversary parameter ftsSecret) (ensuredInitialContext targets) fuel table)) ≤
      initializedNativeDirectRisk targets adversary parameter ftsSecret fuel q := by
  rw [initializedNativeDirectRisk_eq_allowances_of_gameBudget targets adversary q hq parameter hparameter ftsSecret hfts fuel]
  apply ENNReal.tsum_le_tsum
  intro table
  apply mul_le_mul_right
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro target _
  exact privateLiveMissingProbeAllowance_le_stoppedAllowance target _ (ensuredInitialContext targets) fuel table

noncomputable def sampledNativeMissingAllowances
    (targets : Finset Position) (adversary : Adversary) (fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | sampleOtsHashTable] *
        (liveStartProbeAllowance (nativeChronologicalRetainedComputation adversary parameter ftsSecret)
          (ensuredInitialContext targets) fuel table +
          ∑ target ∈ targets, privateLiveMissingProbeAllowance target
            (nativeChronologicalRetainedComputation adversary parameter ftsSecret) (ensuredInitialContext targets) fuel table)

theorem sampledNativeMissingAllowances_le_directRisk
    (targets : Finset Position) (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (fuel : Nat) :
    sampledNativeMissingAllowances targets adversary fuel ≤ sampledInitializedNativeDirectRisk targets adversary fuel q := by
  unfold sampledNativeMissingAllowances sampledInitializedNativeDirectRisk
  apply ENNReal.tsum_le_tsum
  intro parameter
  by_cases hparameter : parameter ∈ support sampleParameter
  · apply mul_le_mul_right
    apply ENNReal.tsum_le_tsum
    intro ftsSecret
    by_cases hfts : ftsSecret ∈ support sampleFtsSecrets
    · apply mul_le_mul_right
      exact nativeMissingAllowances_le_directRisk_of_gameBudget targets adversary q hq parameter hparameter ftsSecret hfts fuel
    · simp [probOutput_eq_zero_of_not_mem_support hfts]
  · simp [probOutput_eq_zero_of_not_mem_support hparameter]

theorem sampledNativeMissingAllowances_add_rootMatch_le_refinedReserve
    (targets roots : Finset Position) (hsubset : roots ⊆ targets)
    (hroots : ∀ target ∈ roots, IsLayerRoot target) (hne : ∀ target ∈ roots, target ≠ layerRootPosition topLayer rootTree)
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 126) (fuel : Nat) :
    sampledNativeMissingAllowances targets adversary fuel + sampledNativeFinalRootMatchRisk targets roots adversary fuel ≤
      sampledQueryCharge otsOpeningRefinedQueryReserve adversary * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  exact (add_le_add (sampledNativeMissingAllowances_le_directRisk targets adversary q hq fuel) le_rfl).trans
    (sampledNativeDirectRisk_add_finalRootMatch_le_refinedReserve targets roots hsubset hroots hne adversary q hq hqMax fuel)

end SphincsSecurity.Concrete.OtsProbeSimulation
