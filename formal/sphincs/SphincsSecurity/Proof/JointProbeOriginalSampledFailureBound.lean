import SphincsSecurity.Proof.JointProbeOriginalRetainedFailureComparison
import SphincsSecurity.Proof.JointProbeTerminalBudget
import SphincsSecurity.Proof.JointProbeMaterializedRiskBound

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

noncomputable def sampledParentSharedFailureRisk (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' otsTable, Pr[= otsTable | OtsProbeSimulation.sampleOtsHashTable] *
        Pr[fun result => result.2 = true | runRetainedWithFailure
          (parentException parameter otsTable (curryFtsTableEquiv ftsSecret)) adversary parameter otsTable
          (curryFtsTableEquiv ftsSecret) q fuel]

theorem sampledParentSharedFailureRisk_le_nativeCompletion (adversary : Adversary) (q fuel : Nat) :
    sampledParentSharedFailureRisk adversary q fuel ≤ sampledNativeFtsCompletionRisk adversary q fuel := by
  unfold sampledParentSharedFailureRisk sampledNativeFtsCompletionRisk
  apply ENNReal.tsum_le_tsum
  intro parameter
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro ftsSecret
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro otsTable
  exact mul_le_mul' le_rfl (probEvent_runRetainedWithFailure_le_nativeCompletion
    (parentException parameter otsTable (curryFtsTableEquiv ftsSecret)) adversary parameter otsTable
    (curryFtsTableEquiv ftsSecret) q fuel)

theorem sampledParentSharedFailureRisk_le_query_rate_add_materialized
    (adversary : Adversary) (q fuel : Nat) (hbudget : q < fuel) (hspace : fuel < Fintype.card Digest) :
    sampledParentSharedFailureRisk adversary q fuel ≤
      (q : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ + (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) :=
  (sampledParentSharedFailureRisk_le_nativeCompletion adversary q fuel).trans
    ((sampledNativeFtsCompletionRisk_le_ots_add_fts_hit adversary q fuel).trans
      ((sampledNativeFtsOtsFailure_add_fts_hit_le_query_rate_add_materialized adversary q fuel hbudget hspace).trans
        (add_le_add le_rfl (sampledNativeFtsMaterializedProbeRisk_le_inv216 adversary q fuel))))

theorem sampledParentSharedFailureRisk_le_query_rate127
    (adversary : Adversary) (q : Nat) (hqMax : q ≤ 2 ^ 127) :
    sampledParentSharedFailureRisk adversary q (q + 1) ≤
      (q : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ + (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) := by
  apply sampledParentSharedFailureRisk_le_query_rate_add_materialized adversary q (q + 1) (by omega)
  have hcard : Fintype.card Digest = 2 ^ 128 := by
    rw [show Fintype.card Digest = 2 ^ digestBits from card_bitVec digestBits]
    rfl
  rw [hcard]
  omega

noncomputable def sampledOriginalParentCleanFtsRisk (adversary : Adversary) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' otsTable, Pr[= otsTable | OtsProbeSimulation.sampleOtsHashTable] *
        Pr[fun result => result.2 = false ∧ RetainedUncoveredFtsSecretWitness parameter
          (OtsProbeSimulation.tableOtsSecret (OtsProbeSimulation.extendStartTable otsTable))
          (curryFtsTableEquiv ftsSecret) result.1 |
          originalParentMonitor adversary parameter otsTable (curryFtsTableEquiv ftsSecret)]

theorem sampledOriginalParentCleanFtsRisk_le_sharedFailure
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (fuel : Nat) :
    sampledOriginalParentCleanFtsRisk adversary ≤ sampledParentSharedFailureRisk adversary q fuel := by
  unfold sampledOriginalParentCleanFtsRisk sampledParentSharedFailureRisk
  apply ENNReal.tsum_le_tsum
  intro parameter
  by_cases hp : parameter ∈ support sampleParameter
  · apply mul_le_mul' le_rfl
    apply ENNReal.tsum_le_tsum
    intro ftsSecret
    apply mul_le_mul' le_rfl
    apply ENNReal.tsum_le_tsum
    intro otsTable
    by_cases ho : otsTable ∈ support OtsProbeSimulation.sampleOtsHashTable
    · exact mul_le_mul' le_rfl (probEvent_original_parentClean_ftsWitness_le_sharedFailure adversary q hq parameter hp otsTable ho
        (curryFtsTableEquiv ftsSecret) (mem_support_sampleFtsSecrets ftsSecret) fuel)
    · simp [probOutput_eq_zero_of_not_mem_support ho]
  · simp [probOutput_eq_zero_of_not_mem_support hp]

theorem sampledOriginalParentCleanFtsRisk_le_query_rate127
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    sampledOriginalParentCleanFtsRisk adversary ≤
      (q : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ + (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) :=
  (sampledOriginalParentCleanFtsRisk_le_sharedFailure adversary q hq (q + 1)).trans
    (sampledParentSharedFailureRisk_le_query_rate127 adversary q hqMax)

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
