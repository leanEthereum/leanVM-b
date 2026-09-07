import SphincsSecurity.Proof.JointProbeOriginalSecretBound
import SphincsSecurity.Proof.JointProbeOriginalSampledFailureBound
import SphincsSecurity.Proof.FirstParentJointSecrets

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

def SampledFirstOtsOrCleanSecret
    (result : SampledSecrets × ((RetainedGameResult × QueryCache HashSpec) × Option ExceptionRecord)) : Prop :=
  FirstOtsOrClean result.1.parameter (SecretWitness result.1.parameter result.1.otsSecret result.1.ftsSecret) result.2

theorem probEvent_sampledFirstOtsOrCleanSecret_le_sharedFailure
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (fuel : Nat) :
    Pr[SampledFirstOtsOrCleanSecret | OtsProbeSimulation.sampledFirstParentRetainedGame adversary] ≤
      sampledParentSharedFailureRisk adversary q fuel := by
  unfold OtsProbeSimulation.sampledFirstParentRetainedGame sampledParentSharedFailureRisk
  simp only [sampleSecrets, bind_assoc, bind_pure_comp, bind_map_left, probEvent_bind_eq_tsum, probEvent_map,
    Function.comp_def, SampledFirstOtsOrCleanSecret]
  apply ENNReal.tsum_le_tsum
  intro parameter
  by_cases hp : parameter ∈ support sampleParameter
  · apply mul_le_mul' le_rfl
    have hsampling : RelTriple OtsProbeSimulation.sampleOtsHashTable sampleOtsSecrets
        (fun table secret => OtsProbeSimulation.otsSecretTableEquiv.symm (fun index => truncateHash (table index)) = secret) := by
      simpa only [OtsProbeSimulation.sampleOtsHashTable] using OtsProbeSimulation.relTriple_uniformOtsHashTable_sampleOtsSecrets
    have hc := expected_cost_le_of_relTriple
      (relTriple_and_right_support (relTriple_symm hsampling))
      (fun otsSecret => ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
        Pr[FirstOtsOrClean parameter (SecretWitness parameter otsSecret ftsSecret) |
          runFirstException (CleanParentSettlement parameter otsSecret ftsSecret)
            (OtsProbeSimulation.retainedAfterSecretsComputation adversary parameter otsSecret ftsSecret) ∅ none])
      (fun table => ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
        Pr[fun result => result.2 = true | runRetainedWithFailure (parentException parameter table (curryFtsTableEquiv ftsSecret))
          adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel])
      (fun _ => 0) (by
        intro otsSecret table hs
        simp only [add_zero]
        rw [← hs.1]
        apply ENNReal.tsum_le_tsum
        intro ftsSecret
        apply mul_le_mul' le_rfl
        exact probEvent_original_firstOtsOrCleanSecret_le_sharedFailure adversary q hq parameter hp table hs.2
          (curryFtsTableEquiv ftsSecret) (mem_support_sampleFtsSecrets ftsSecret) fuel)
    calc
      _ ≤ ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
          ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
            Pr[fun result => result.2 = true | runRetainedWithFailure (parentException parameter table (curryFtsTableEquiv ftsSecret))
              adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel] := by
        simpa only [mul_zero, tsum_zero, add_zero] using hc
      _ = _ := by
        simp_rw [← ENNReal.tsum_mul_left]
        rw [ENNReal.tsum_comm]
        apply tsum_congr
        intro ftsSecret
        apply tsum_congr
        intro table
        exact mul_left_comm _ _ _
  · simp [probOutput_eq_zero_of_not_mem_support hp]

theorem probEvent_sampledFirstOtsOrCleanSecret_le_query_rate127
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    Pr[SampledFirstOtsOrCleanSecret | OtsProbeSimulation.sampledFirstParentRetainedGame adversary] ≤
      (q : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ + (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal) :=
  (probEvent_sampledFirstOtsOrCleanSecret_le_sharedFailure adversary q hq (q + 1)).trans
    (sampledParentSharedFailureRisk_le_query_rate127 adversary q hqMax)

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
