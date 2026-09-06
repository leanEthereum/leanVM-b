import SphincsSecurity.Proof.FirstParentOtsWitness
import SphincsSecurity.Proof.FirstOtsParentGame

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational

attribute [local irreducible] instFintypePosition
set_option backward.isDefEq.respectTransparency false

noncomputable def sampledFirstParentRetainedGame (adversary : Adversary) :
    ProbComp (SampledSecrets × ((RetainedGameResult × QueryCache HashSpec) × Option ExceptionRecord)) := do
  let secrets ← sampleSecrets
  let result ← runFirstException (CleanParentSettlement secrets.parameter secrets.otsSecret secrets.ftsSecret)
    (retainedAfterSecretsComputation adversary secrets.parameter secrets.otsSecret secrets.ftsSecret) ∅ none
  pure (secrets, result)

theorem sampledFirstParentRetainedGame_verdict_projection (adversary : Adversary) :
    (fun result => (result.1, firstParentRetainedVerdictProjection result.2)) <$>
      sampledFirstParentRetainedGame adversary = sampledFirstParentSettlementGame adversary := by
  rw [sampledFirstParentRetainedGame, sampledFirstParentSettlementGame, map_bind]
  apply bind_congr
  intro secrets
  rw [bind_pure_comp, bind_pure_comp, Functor.map_map, ← firstParentRetained_verdict_projection, Functor.map_map]

def SampledFirstParentOrOtsWitness
    (result : SampledSecrets × ((RetainedGameResult × QueryCache HashSpec) × Option ExceptionRecord)) : Prop :=
  FirstParentOrOtsWitness result.1.parameter result.1.otsSecret result.1.ftsSecret result.2

theorem probEvent_sampledFirstParentOrOtsWitness_le_nativeTerminalFailure (adversary : Adversary) (fuel : Nat) :
    Pr[SampledFirstParentOrOtsWitness | sampledFirstParentRetainedGame adversary] ≤
      Pr[fun verdict => verdict = true | sampledNativeTerminalFailure adversary fuel] := by
  unfold sampledFirstParentRetainedGame sampledNativeTerminalFailure
  simp only [sampleSecrets, bind_assoc, bind_pure_comp, bind_map_left, probEvent_bind_eq_tsum, probEvent_map,
    Function.comp_def, SampledFirstParentOrOtsWitness]
  apply ENNReal.tsum_le_tsum
  intro parameter
  have hcoupled := expected_cost_le_of_relTriple (relTriple_symm relTriple_uniformOtsHashTable_sampleOtsSecrets)
    (fun otsSecret => ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      Pr[FirstParentOrOtsWitness parameter otsSecret ftsSecret |
        runFirstException (CleanParentSettlement parameter otsSecret ftsSecret)
          (retainedAfterSecretsComputation adversary parameter otsSecret ftsSecret) ∅ none])
    (fun table => ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      Pr[fun verdict => verdict = true | nativeTerminalFailureAfterRoot Finset.univ adversary parameter table ftsSecret fuel])
    (fun _ => 0) (by
      intro otsSecret table hsecrets
      simp only [add_zero]
      rw [← hsecrets]
      apply ENNReal.tsum_le_tsum
      intro ftsSecret
      exact mul_le_mul' le_rfl (probEvent_firstParentOrOtsWitness_le_nativeTerminalFailure adversary parameter table ftsSecret fuel))
  apply mul_le_mul' le_rfl
  calc
    _ ≤ ∑' table, Pr[= table | sampleOtsHashTable] *
        ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
          Pr[fun verdict => verdict = true | nativeTerminalFailureAfterRoot Finset.univ adversary parameter table ftsSecret fuel] := by
      simpa only [sampleOtsHashTable, mul_zero, tsum_zero, add_zero] using hcoupled
    _ = _ := by
      simp_rw [← ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro ftsSecret
      apply tsum_congr
      intro table
      exact mul_left_comm _ _ _

theorem probEvent_sampledFirstParentOrOtsWitness_le_actualOtsCount_rate_add_erasure
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqSpace : q + 1 < Fintype.card Digest) :
    Pr[SampledFirstParentOrOtsWitness | sampledFirstParentRetainedGame adversary] ≤
      sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary *
        privateHistoryGuessRate q + (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  apply (probEvent_sampledFirstParentOrOtsWitness_le_nativeTerminalFailure adversary (q + 1)).trans
  rw [probEvent_sampledNativeTerminalFailure_eq_risk]
  exact sampledNativeTerminalRisk_le_actualOtsCount_rate_add_erasure_of_querySpace adversary q hq hqSpace

end SphincsSecurity.Concrete.OtsProbeSimulation
