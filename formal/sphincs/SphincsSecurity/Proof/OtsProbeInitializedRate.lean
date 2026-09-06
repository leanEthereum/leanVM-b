import SphincsSecurity.Proof.OtsProbeStartAdaptiveRate
import SphincsSecurity.Proof.OtsProbePrivateWeightedGame

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem probEvent_sampledEnsuredNativeProbeCut_unresolvedStart_le_rate
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (fuel ordinal budget : Nat) (hordinal : ordinal ≤ budget) (hspace : budget < Fintype.card Digest) :
    Pr[LiveUnresolvedStartHit nativeCutCandidate | sampledEnsuredNativeProbeCut targets computation fuel ordinal] ≤
      (∑' result, Pr[= result | sampledEnsuredNativeProbeCut targets computation fuel ordinal] *
        historyUnresolvedStartCharge nativeCutCandidate (retainCompletableResult result)) *
        privateHistoryGuessRate budget := by
  have hnative := probEvent_live_unresolvedStart_hit_le_native_charge_rate (nativeProbeCutAt computation ordinal)
    (ensuredInitialContext targets) fuel ordinal budget [] nativeCutCandidate (ensuredInitialContext_valid targets).valuesConsistent
    (show PendingCoveredBy [] (ensuredInitialContext targets) from pendingCoveredBy_empty)
    (nativeProbeCutAt_probeBound computation ordinal)
    (by simpa only [List.length_nil, Nat.zero_add] using hordinal) hspace
  have htable : ∀ base, completedStartTable (ensuredInitialContext targets).state base = base := by
    intro base
    funext index
    rfl
  simpa only [sampledEnsuredNativeProbeCut, sampledHistoryFilteredRun, ChainStartHistoryHit, List.not_mem_nil,
    false_and, exists_false, ↓reduceIte, htable] using hnative

theorem sum_sampledEnsuredNativeProbeCut_unresolvedStart_le_rate
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (fuel q : Nat)
    (hq : q < Fintype.card Digest) :
    (∑ ordinal ∈ Finset.range q,
      Pr[LiveUnresolvedStartHit nativeCutCandidate | sampledEnsuredNativeProbeCut targets computation fuel ordinal]) ≤
      (∑ ordinal ∈ Finset.range q, ∑' result,
        Pr[= result | sampledEnsuredNativeProbeCut targets computation fuel ordinal] *
          historyUnresolvedStartCharge nativeCutCandidate (retainCompletableResult result)) *
        privateHistoryGuessRate q := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ordinal hmem
  exact probEvent_sampledEnsuredNativeProbeCut_unresolvedStart_le_rate targets computation fuel ordinal q
    (Nat.le_of_lt (Finset.mem_range.mp hmem)) hq

theorem sum_sampledEnsuredNativeProbeCut_unresolvedStart_le_expectedChainStartCharge_rate
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (fuel q : Nat)
    (hq : q < Fintype.card Digest) :
    (∑ ordinal ∈ Finset.range q,
      Pr[LiveUnresolvedStartHit nativeCutCandidate | sampledEnsuredNativeProbeCut targets computation fuel ordinal]) ≤
      (∑' table, Pr[= table | sampleOtsHashTable] *
        expectedLiveResolvedQueryCharge chainStartProbeQueryCharge computation
          (ensuredInitialContext targets) fuel table) * privateHistoryGuessRate q := by
  apply (sum_sampledEnsuredNativeProbeCut_unresolvedStart_le_rate targets computation fuel q hq).trans
  apply mul_le_mul' _ le_rfl
  calc
    _ ≤ ∑ ordinal ∈ Finset.range q, ∑' result,
        Pr[= result | sampledEnsuredNativeProbeCut targets computation fuel ordinal] * liveNativeCutCharge chainStartProbeQueryCharge result := by
      apply Finset.sum_le_sum
      intro ordinal _
      exact ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (historyUnresolvedStartCharge_le_liveNativeCutCharge result)
    _ = ∑' table, Pr[= table | sampleOtsHashTable] *
        ∑ ordinal ∈ Finset.range q, expectedLiveNativeCutCharge chainStartProbeQueryCharge
          (nativeProbeCutAt computation ordinal)
          (ensuredInitialContext targets) fuel table := by
      simp only [sampledEnsuredNativeProbeCut, tsum_probOutput_bind_mul]
      rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      simp only [← Finset.mul_sum, expectedLiveNativeCutCharge]
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro table
      exact mul_le_mul' le_rfl (sum_expectedLiveNativeProbeCutCharge_le_expectedCharge chainStartProbeQueryCharge computation q
        (ensuredInitialContext targets) fuel table
        (ensuredInitialContext_valid targets).valuesConsistent
          (startTableAgrees_of_deferredCompletable (ensuredInitialContext_completable targets table)))

theorem initializedNativeDirectRisk_le_actualOtsCount_rate
    (targets : Finset Position) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel q : Nat) (hq : q < Fintype.card Digest) :
    initializedNativeDirectRisk targets adversary parameter ftsSecret fuel q ≤
      (∑' table, Pr[= table | sampleOtsHashTable] *
        expectedQueryCharge (fun _ input => otsHashInputCharge parameter input)
          (gameAfterSecrets adversary parameter
            (fun lay tree leafIdx chainIdx => truncateHash (table ⟨lay, tree, leafIdx, chainIdx⟩)) ftsSecret) ∅) *
        privateHistoryGuessRate q := by
  let computation := nativeChronologicalRetainedComputation adversary parameter ftsSecret
  have hstart := sum_sampledEnsuredNativeProbeCut_unresolvedStart_le_expectedChainStartCharge_rate targets computation fuel q hq
  have hstruct : (∑' table, Pr[= table | sampleOtsHashTable] *
      ∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
        Pr[PrivateCandidatePairHit | privateResolvedSelectedCandidate target (privateRawCutCandidate target) <$>
          runPrivateResolvedView target table (ensuredInitialContext targets) fuel (privatePositionProbeCutAt target computation ordinal)]) ≤
      (∑' table, Pr[= table | sampleOtsHashTable] *
        expectedLiveResolvedQueryCharge structuralProbeQueryCharge computation (ensuredInitialContext targets) fuel table) *
        privateHistoryGuessRate q := by
    rw [← ENNReal.tsum_mul_right]
    apply ENNReal.tsum_le_tsum
    intro table
    rw [mul_assoc]
    exact mul_le_mul' le_rfl (sum_targets_privateHits_ensuredInitial_le_historyRate targets computation q fuel table hq)
  apply (add_le_add hstart hstruct).trans
  rw [← add_mul, ← ENNReal.tsum_add]
  simp only [← mul_add]
  apply mul_le_mul' _ le_rfl
  apply ENNReal.tsum_le_tsum
  intro table
  exact mul_le_mul' le_rfl (initializedNative_joint_probe_count_le_actual_ots_count targets adversary parameter table ftsSecret fuel)

theorem sampledInitializedNativeDirectRisk_le_actualOtsCount_rate
    (targets : Finset Position) (adversary : Adversary) (fuel q : Nat) (hq : q < Fintype.card Digest) :
    sampledInitializedNativeDirectRisk targets adversary fuel q ≤
      sampledQueryCharge (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) adversary *
        privateHistoryGuessRate q := by
  calc
    _ ≤ ∑' parameter, Pr[= parameter | sampleParameter] *
        ∑' ftsSecret, Pr[= ftsSecret | sampleFtsSecrets] *
          ((∑' otsSecret, Pr[= otsSecret | sampleOtsSecrets] *
            expectedQueryCharge (fun _ input => otsHashInputCharge parameter input)
              (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅) * privateHistoryGuessRate q) := by
      apply ENNReal.tsum_le_tsum
      intro parameter
      apply mul_le_mul' le_rfl
      apply ENNReal.tsum_le_tsum
      intro ftsSecret
      apply mul_le_mul' le_rfl
      exact (initializedNativeDirectRisk_le_actualOtsCount_rate targets adversary parameter ftsSecret fuel q hq).trans
        (mul_le_mul' (uniformTable_actualOtsCount_le_sampledSecrets adversary parameter ftsSecret) le_rfl)
    _ = _ := by
      unfold sampledQueryCharge
      simp only [sampleSecrets, tsum_probOutput_bind_mul, tsum_probOutput_pure_mul, primitiveAccountingKey]
      simp only [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right, mul_assoc]
      apply tsum_congr
      intro parameter
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro otsSecret
      apply tsum_congr
      intro ftsSecret
      ring

theorem sampledInitializedNativeDirectRisk_le_queryBudget_rate
    (targets : Finset Position) (adversary : Adversary) (fuel q : Nat)
    (hq : HasHashQueryBound scheme adversary q) (hqSpace : q < Fintype.card Digest) :
    sampledInitializedNativeDirectRisk targets adversary fuel q ≤ (q : ENNReal) * privateHistoryGuessRate q := by
  apply (sampledInitializedNativeDirectRisk_le_actualOtsCount_rate targets adversary fuel q hqSpace).trans
  apply mul_le_mul' _ le_rfl
  simpa only [one_mul] using sampledQueryCharge_le_const
    (fun secretKey _ input => otsHashInputCharge secretKey.parameter input) 1 (by
      intro secretKey cache input
      unfold otsHashInputCharge
      split_ifs <;> simp) adversary q hq

end SphincsSecurity.Concrete.OtsProbeSimulation
