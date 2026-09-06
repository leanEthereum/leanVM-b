import SphincsSecurity.Proof.FirstOtsParentRetained
import SphincsSecurity.Proof.FirstParentSettlementGame

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational

attribute [local irreducible] instFintypePosition
set_option backward.isDefEq.respectTransparency false

def SampledFirstOtsParentRecord
    (result : SampledSecrets × ((Bool × QueryCache HashSpec) × Option ExceptionRecord)) : Prop :=
  FirstOtsParentRecord result.1.parameter result.2

theorem probEvent_sampledFirstOtsParentRecord_le_early_parent (adversary : Adversary) :
    Pr[SampledFirstOtsParentRecord | sampledFirstParentSettlementGame adversary] ≤
      sampledEarlyOtsParentQueryRisk adversary := by
  unfold sampledFirstParentSettlementGame sampledEarlyOtsParentQueryRisk
  simp only [sampleSecrets, bind_assoc, bind_pure_comp, bind_map_left, probEvent_bind_eq_tsum, probEvent_map,
    Function.comp_def, SampledFirstOtsParentRecord]
  apply ENNReal.tsum_le_tsum
  intro parameter
  apply mul_le_mul' le_rfl
  have hcoupled := expected_cost_le_of_relTriple (relTriple_symm relTriple_uniformOtsHashTable_sampleOtsSecrets)
    (fun otsSecret => ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      Pr[FirstOtsParentRecord parameter |
        runFirstException (CleanParentSettlement parameter otsSecret ftsSecret)
          (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅ none])
    (fun table => ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      Pr[EarlyOtsParentAtQuery parameter
        (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret |
        prehitRetainedQueryTrace adversary parameter table ftsSecret])
    (fun _ => 0) (by
      intro otsSecret table hsecrets
      simp only [add_zero]
      rw [← hsecrets]
      apply ENNReal.tsum_le_tsum
      intro ftsSecret
      exact mul_le_mul' le_rfl (probEvent_firstOtsParentRecord_game_le_early_parent adversary parameter table ftsSecret))
  calc
    _ ≤ ∑' table, Pr[= table | sampleOtsHashTable] *
        ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
          Pr[EarlyOtsParentAtQuery parameter
            (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret |
            prehitRetainedQueryTrace adversary parameter table ftsSecret] := by
      simpa only [sampleOtsHashTable, mul_zero, tsum_zero, add_zero] using hcoupled
    _ = _ := by
      simp_rw [← ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro ftsSecret
      apply tsum_congr
      intro table
      exact mul_left_comm _ _ _

theorem probEvent_sampledFirstOtsParentRecord_le_nativeTerminalFailure
    (adversary : Adversary) (fuel : Nat) :
    Pr[SampledFirstOtsParentRecord | sampledFirstParentSettlementGame adversary] ≤
      Pr[fun verdict => verdict = true | sampledNativeTerminalFailure adversary fuel] :=
  (probEvent_sampledFirstOtsParentRecord_le_early_parent adversary).trans
    (sampledEarlyOtsParentQueryRisk_le_nativeTerminalFailure adversary fuel)

theorem probEvent_sampledFirstOtsParentRecord_le_actualOtsCount_rate_add_erasure
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (hqSpace : q + 1 < Fintype.card Digest) :
    Pr[SampledFirstOtsParentRecord | sampledFirstParentSettlementGame adversary] ≤
      sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary *
        privateHistoryGuessRate q + (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ :=
  (probEvent_sampledFirstOtsParentRecord_le_early_parent adversary).trans
    (sampledEarlyOtsParentQueryRisk_le_actualOtsCount_rate_add_erasure adversary q hq hqSpace)

theorem probEvent_sampledFirstOtsParentRecord_le_actualOtsCount127_add_erasure
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    Pr[SampledFirstOtsParentRecord | sampledFirstParentSettlementGame adversary] ≤
      sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary *
        (2 * (Fintype.card Digest : ENNReal)⁻¹) + (q : ENNReal) * ((2 ^ 216 : Nat) : ENNReal)⁻¹ :=
  (probEvent_sampledFirstOtsParentRecord_le_early_parent adversary).trans
    (sampledEarlyOtsParentQueryRisk_le_actualOtsCount127_add_erasure adversary q hq hqMax)

end SphincsSecurity.Concrete.OtsProbeSimulation
