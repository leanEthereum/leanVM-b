import SphincsSecurity.Proof.JointProbeOriginalOtsParentRetained
import SphincsSecurity.Proof.JointProbeOriginalSampledFailureBound

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

noncomputable def sampledOriginalFirstOtsOrCleanFtsRisk (adversary : Adversary) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' otsTable, Pr[= otsTable | OtsProbeSimulation.sampleOtsHashTable] *
        Pr[FirstOtsOrClean parameter (RetainedUncoveredFtsSecretWitness parameter
          (OtsProbeSimulation.tableOtsSecret (OtsProbeSimulation.extendStartTable otsTable)) (curryFtsTableEquiv ftsSecret)) |
          originalParentRecords adversary parameter otsTable (curryFtsTableEquiv ftsSecret)]

theorem sampledOriginalFirstOtsOrCleanFtsRisk_le_sharedFailure
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (fuel : Nat) :
    sampledOriginalFirstOtsOrCleanFtsRisk adversary ≤ sampledParentSharedFailureRisk adversary q fuel := by
  unfold sampledOriginalFirstOtsOrCleanFtsRisk sampledParentSharedFailureRisk
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
    · exact mul_le_mul' le_rfl (probEvent_original_firstOtsOrCleanFts_le_sharedFailure adversary q hq parameter hp otsTable ho
        (curryFtsTableEquiv ftsSecret) (mem_support_sampleFtsSecrets ftsSecret) fuel)
    · simp [probOutput_eq_zero_of_not_mem_support ho]
  · simp [probOutput_eq_zero_of_not_mem_support hp]

theorem sampledOriginalFirstOtsOrCleanFtsRisk_le_query_rate127
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    sampledOriginalFirstOtsOrCleanFtsRisk adversary ≤
      (q : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ + (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) :=
  (sampledOriginalFirstOtsOrCleanFtsRisk_le_sharedFailure adversary q hq (q + 1)).trans
    (sampledParentSharedFailureRisk_le_query_rate127 adversary q hqMax)

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
