import SphincsSecurity.Proof.SecurityBeforeSharedFailure
import SphincsSecurity.Proof.JointProbeBeforeFailureNonSecretBudget
import SphincsSecurity.Proof.SecurityJointNonSecretEndpoint

namespace SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal

open _root_.OracleComp OracleSpec ENNReal
open OtsProbeSimulation (OtsSecretIndex retainedRestVerdict sampledFirstParentRetainedGame)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] OtsProbeSimulation.sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

noncomputable def sampledOriginalRecordRisk (adversary : Adversary)
    (event : SampledSecrets × ((RetainedGameResult × QueryCache HashSpec) × Option ExceptionRecord) → Prop) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        Pr[fun result => event (tableSecrets parameter table (curryFtsTableEquiv ftsSecret), result) |
          originalParentRecords adversary parameter table (curryFtsTableEquiv ftsSecret)]

private theorem expected_evalDist_eq (computation : ProbComp α) (cost : α → ENNReal) :
    (∑' value, Pr[= value | evalDist computation] * cost value) =
      ∑' value, Pr[= value | computation] * cost value := rfl

theorem probEvent_sampledRetained_eq_recordRisk (adversary : Adversary)
    (event : SampledSecrets × ((RetainedGameResult × QueryCache HashSpec) × Option ExceptionRecord) → Prop) :
    Pr[event | sampledFirstParentRetainedGame adversary] = sampledOriginalRecordRisk adversary event := by
  unfold sampledFirstParentRetainedGame sampledOriginalRecordRisk
  simp only [sampleSecrets, bind_assoc, bind_pure_comp, bind_map_left, probEvent_bind_eq_tsum, probEvent_map, Function.comp_def]
  apply tsum_congr
  intro parameter
  congr 1
  let cost := fun otsSecret => ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
    Pr[fun result => event (⟨parameter, otsSecret, ftsSecret⟩, result) |
      runFirstException (CleanParentSettlement parameter otsSecret ftsSecret)
        (OtsProbeSimulation.retainedAfterSecretsComputation adversary parameter otsSecret ftsSecret) ∅ none]
  have hs : evalDist ((fun table : OtsSecretIndex → HashOutput =>
        OtsProbeSimulation.otsSecretTableEquiv.symm (fun index => truncateHash (table index))) <$> OtsProbeSimulation.sampleOtsHashTable) =
      evalDist sampleOtsSecrets := by
    simpa only [OtsProbeSimulation.sampleOtsHashTable] using OtsProbeSimulation.evalDist_uniformOtsHashTable_truncate
  have hm := congrArg (fun computation => ∑' secret, Pr[= secret | computation] * cost secret) hs
  rw [expected_evalDist_eq, expected_evalDist_eq, tsum_probOutput_map_mul] at hm
  calc
    _ = ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
          Pr[fun result => event (tableSecrets parameter table (curryFtsTableEquiv ftsSecret), result) |
            originalParentRecords adversary parameter table (curryFtsTableEquiv ftsSecret)] := hm.symm
    _ = _ := by
      simp_rw [← ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro ftsSecret
      apply tsum_congr
      intro table
      exact mul_left_comm _ _ _

noncomputable def sampledBeforeFailureStructuralCharge (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        initializedBeforeFailureStructuralCharge adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel

theorem forgeAdvantage_eq_sampledRetained_win (adversary : Adversary) :
    forgeAdvantage scheme adversary =
      Pr[fun result => retainedRestVerdict result.2.1.1.2 = true | sampledFirstParentRetainedGame adversary] := by
  rw [forgeAdvantage_eq_sampledGame, ← sampledParentSettlementGame_project, probOutput_map,
    ← sampledFirstParentSettlementGame_flag_projection, probEvent_map,
    ← OtsProbeSimulation.sampledFirstParentRetainedGame_verdict_projection, probEvent_map]
  rfl

theorem forgeAdvantage_le_sharedFailure_add_beforeFailureStructural
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (fuel : Nat) :
    forgeAdvantage scheme adversary ≤ sampledParentSharedFailureRisk adversary q fuel +
      sampledBeforeFailureStructuralCharge adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
      Pr[retainedNonSecretResidual | sampledFirstParentRetainedGame adversary] := by
  rw [forgeAdvantage_eq_sampledRetained_win, probEvent_sampledRetained_eq_recordRisk, probEvent_sampledRetained_eq_recordRisk]
  unfold sampledOriginalRecordRisk sampledParentSharedFailureRisk sampledBeforeFailureStructuralCharge
  calc
    _ ≤ ∑' parameter, Pr[= parameter | sampleParameter] *
        ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
          ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
            (Pr[fun result => result.2 = true | runRetainedWithFailure (parentException parameter table (curryFtsTableEquiv ftsSecret))
              adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel] +
              initializedBeforeFailureStructuralCharge adversary parameter table (curryFtsTableEquiv ftsSecret) q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
              Pr[fun result => retainedNonSecretResidual (tableSecrets parameter table (curryFtsTableEquiv ftsSecret), result) |
                originalParentRecords adversary parameter table (curryFtsTableEquiv ftsSecret)]) := by
      apply ENNReal.tsum_le_tsum
      intro parameter
      by_cases hp : parameter ∈ support sampleParameter
      · apply mul_le_mul' le_rfl
        apply ENNReal.tsum_le_tsum
        intro ftsSecret
        apply mul_le_mul' le_rfl
        apply ENNReal.tsum_le_tsum
        intro table
        by_cases ht : table ∈ support OtsProbeSimulation.sampleOtsHashTable
        · exact mul_le_mul' le_rfl (probEvent_original_win_le_failure_add_beforeFailureCharge adversary q hq parameter hp table ht
            (curryFtsTableEquiv ftsSecret) (mem_support_sampleFtsSecrets ftsSecret) fuel)
        · rw [probOutput_eq_zero_of_not_mem_support ht, zero_mul, zero_mul]
      · rw [probOutput_eq_zero_of_not_mem_support hp, zero_mul, zero_mul]
    _ = _ := by
      simp only [mul_add, ENNReal.tsum_add, ← mul_assoc, ENNReal.tsum_mul_right]

theorem forgeAdvantage_le_sharedFailure_add_beforeFailureStructural_remaining127
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) (fuel : Nat) :
    forgeAdvantage scheme adversary ≤ sampledParentSharedFailureRisk adversary q fuel +
      sampledBeforeFailureStructuralCharge adversary q fuel * (Fintype.card Digest : ENNReal)⁻¹ +
      ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ + (q : ENNReal) * (15 * ((2 ^ 132 : Nat) : ENNReal)⁻¹)) :=
  (forgeAdvantage_le_sharedFailure_add_beforeFailureStructural adversary q hq fuel).trans
    (add_le_add le_rfl ((probEvent_retainedNonSecretResidual_le_viewed adversary).trans
      (probEvent_sampled_messageOrForest_le127 adversary q hqPos hq hqMax)))

noncomputable def sampledBeforeFailureRestHashCharge (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        ∑' initial, Pr[= initial | initializeRoot parameter table (curryFtsTableEquiv ftsSecret) q fuel] *
          expectedBeforeFailureCharge (parentException parameter table (curryFtsTableEquiv ftsSecret)) (fun _ _ => 1)
            parameter initial.2.1 table (curryFtsTableEquiv ftsSecret) (retainedComputation adversary parameter initial.2.1 q)
              initial.1 initial.2.2 false initial.1.isNone

noncomputable def sampledBeforeFailureOuterNonSecretCharge (adversary : Adversary) (q fuel : Nat) : ENNReal :=
  ∑' parameter, Pr[= parameter | sampleParameter] *
    ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
      ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] *
        ∑' initial, Pr[= initial | initializeRoot parameter table (curryFtsTableEquiv ftsSecret) q fuel] *
          expectedBeforeFailureOuterCharge (parentException parameter table (curryFtsTableEquiv ftsSecret))
            (fun _ input => if NonSecretHashInput parameter input then 1 else 0)
            parameter initial.2.1 table (curryFtsTableEquiv ftsSecret) (retainedComputation adversary parameter initial.2.1 q)
              initial.1 initial.2.2 false initial.1.isNone

theorem sampledBeforeFailureRestHashCharge_le_queryBound
    (adversary : Adversary) (q : Nat) (hq : HasHashQueryBound scheme adversary q) (fuel : Nat) :
    sampledBeforeFailureRestHashCharge adversary q fuel ≤ q := by
  unfold sampledBeforeFailureRestHashCharge
  calc
    _ ≤ ∑' parameter, Pr[= parameter | sampleParameter] *
        ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
          ∑' table, Pr[= table | OtsProbeSimulation.sampleOtsHashTable] * (q : ENNReal) := by
      apply ENNReal.tsum_le_tsum
      intro parameter
      by_cases hp : parameter ∈ support sampleParameter
      · apply mul_le_mul' le_rfl
        apply ENNReal.tsum_le_tsum
        intro ftsSecret
        apply mul_le_mul' le_rfl
        apply ENNReal.tsum_le_tsum
        intro table
        exact mul_le_mul' le_rfl (initializedBeforeFailureHashCharge_le_queryBound adversary q hq parameter hp table
          (curryFtsTableEquiv ftsSecret) (mem_support_sampleFtsSecrets ftsSecret) fuel)
      · rw [probOutput_eq_zero_of_not_mem_support hp, zero_mul, zero_mul]
    _ ≤ _ := by
      simp_rw [ENNReal.tsum_mul_right]
      exact (mul_le_mul' tsum_probOutput_le_one
        (mul_le_mul' tsum_probOutput_le_one (mul_le_mul' tsum_probOutput_le_one le_rfl))).trans_eq (by simp)

theorem sampledBeforeFailureStructural_le_restHash_add_outerNonSecret (adversary : Adversary) (q fuel : Nat) :
    sampledBeforeFailureStructuralCharge adversary q fuel ≤
      sampledBeforeFailureRestHashCharge adversary q fuel + sampledBeforeFailureOuterNonSecretCharge adversary q fuel := by
  unfold sampledBeforeFailureStructuralCharge initializedBeforeFailureStructuralCharge
    sampledBeforeFailureRestHashCharge sampledBeforeFailureOuterNonSecretCharge
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro parameter
  rw [← mul_add, ← ENNReal.tsum_add]
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro ftsSecret
  rw [← mul_add, ← ENNReal.tsum_add]
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro table
  rw [← mul_add, ← ENNReal.tsum_add]
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro initial
  rw [← mul_add]
  exact mul_le_mul' le_rfl (beforeFailureStructural_le_hash_add_nonSecret
    (parentException parameter table (curryFtsTableEquiv ftsSecret)) parameter initial.2.1 table (curryFtsTableEquiv ftsSecret)
    (retainedComputation adversary parameter initial.2.1 q) initial.1 initial.2.2 false initial.1.isNone)

theorem forgeAdvantage_add_sharedNonSecret_le_beforeFailureBudget
    (adversary : Adversary) (q : Nat) (hqPos : 1 ≤ q)
    (hq : HasHashQueryBound scheme adversary q) (hqMax : q ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary + sampledJointNonSecretQueryCharge adversary q * (Fintype.card Digest : ENNReal)⁻¹ ≤
      (sampledBeforeFailureRestHashCharge adversary q (q + 1) + sampledBeforeFailureOuterNonSecretCharge adversary q (q + 1)) *
        (Fintype.card Digest : ENNReal)⁻¹ +
      ((q : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ + (q : ENNReal) / ((2 ^ 216 : Nat) : ENNReal)) +
      ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ + (q : ENNReal) * (15 * ((2 ^ 132 : Nat) : ENNReal)⁻¹)) := by
  have hspace : q + 1 < Fintype.card Digest := by
    have hcard : Fintype.card Digest = 2 ^ 128 := by
      rw [show Fintype.card Digest = 2 ^ digestBits from card_bitVec digestBits]
      rfl
    rw [hcard]
    omega
  have hshared := (add_le_add ((sampledParentSharedFailureRisk_le_nativeCompletion adversary q (q + 1)).trans
    (sampledNativeFtsCompletionRisk_le_ots_add_fts_hit adversary q (q + 1))) le_rfl).trans
      (sampledNativeFtsOtsFailure_add_fts_hit_add_nonSecret_le_query_rate adversary q (q + 1) (by omega) hspace)
  apply (add_le_add (forgeAdvantage_le_sharedFailure_add_beforeFailureStructural_remaining127 adversary q hqPos hq hqMax (q + 1)) le_rfl).trans
  calc
    _ = sampledBeforeFailureStructuralCharge adversary q (q + 1) * (Fintype.card Digest : ENNReal)⁻¹ +
        (sampledParentSharedFailureRisk adversary q (q + 1) + sampledJointNonSecretQueryCharge adversary q * (Fintype.card Digest : ENNReal)⁻¹) +
        ((q : ENNReal) * ((2 ^ 139 : Nat) : ENNReal)⁻¹ + (q : ENNReal) * (15 * ((2 ^ 132 : Nat) : ENNReal)⁻¹)) := by ac_rfl
    _ ≤ _ := add_le_add (add_le_add
      (mul_le_mul' (sampledBeforeFailureStructural_le_restHash_add_outerNonSecret adversary q (q + 1)) le_rfl) hshared) le_rfl

end SphincsSecurity.Concrete.FtsProbeSimulation.JointOriginal
