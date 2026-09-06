import SphincsSecurity.Proof.OtsProbeInitializedRate

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

noncomputable def prefixUnresolvedStartCharge (candidate : DeferredContext → α → Option Probe) :
    Option (HistoryResolvedPrefix α) → ENNReal
  | none => 0
  | some entry => unresolvedStartCandidateCharge entry.context (candidate entry.context entry.value)

theorem expected_completeHistoryResolvedPrefix_unresolvedStart_le_prefixCharge
    (entry : HistoryResolvedPrefix α) (candidate : DeferredContext → α → Option Probe) :
    (∑' result, Pr[= result | completeHistoryResolvedPrefix (some entry)] * historyUnresolvedStartAllowance candidate result) ≤
      prefixUnresolvedStartCharge candidate (some entry) * (Fintype.card Digest : ENNReal)⁻¹ := by
  unfold historyUnresolvedStartAllowance
  rw [expected_completeHistoryResolvedPrefix_function entry (fun table context value =>
    unresolvedStartCandidateAllowance table context (candidate context value))]
  change _ ≤ unresolvedStartCandidateCharge entry.context (candidate entry.context entry.value) * _
  cases hcandidate : candidate entry.context entry.value with
  | none => simp [unresolvedStartCandidateAllowance, unresolvedStartCandidateCharge]
  | some probe =>
      rcases probe with ⟨coordinate, digest⟩
      cases coordinate with
      | position position => simp [unresolvedStartCandidateAllowance, unresolvedStartCandidateCharge]
      | chainStart lay tree leafIdx chainIdx =>
          by_cases hmissing : entry.context.state.values (.chainStart lay tree leafIdx chainIdx) = none
          · simp only [unresolvedStartCandidateAllowance, unresolvedStartCandidateCharge, if_pos hmissing]
            calc
              _ ≤ ∑' base, Pr[= base | sampleOtsHashTable] *
                  candidateFailureAllowance (completedStartTable entry.context.state base) entry.context
                    (some ⟨.chainStart lay tree leafIdx chainIdx, digest⟩) := by
                apply ENNReal.tsum_le_tsum
                intro base
                apply mul_le_mul' le_rfl
                split_ifs <;> first | exact bot_le | exact le_rfl
              _ ≤ _ := by
                simpa only [OtsSecretIndex.coordinate, show Fintype.card Digest = 2 ^ digestBits by simp] using
                  expected_candidateFailureAllowance_chainStart_of_missing entry.context ⟨lay, tree, leafIdx, chainIdx⟩ digest hmissing
          · simp [unresolvedStartCandidateAllowance, unresolvedStartCandidateCharge, hmissing]

theorem historyUnresolvedStartAllowance_retain_le
    (candidate : DeferredContext → α → Option Probe) (result : Option (ResolvedRunResult α)) :
    historyUnresolvedStartAllowance candidate (retainCompletableResult result) ≤ historyUnresolvedStartAllowance candidate result := by
  cases result with
  | none => rfl
  | some result =>
      simp only [retainCompletableResult]
      split_ifs
      · exact le_rfl
      · exact bot_le

theorem expected_live_historyAdaptive_unresolvedStart_le_prefixCharge
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (context : DeferredContext) (fuel : Nat) (history : List Probe)
    (candidate : DeferredContext → α → Option Probe) :
    (∑' result, Pr[= result | runResolvedHistoryAdaptive computation context fuel history] *
      historyUnresolvedStartAllowance candidate (retainCompletableResult result)) ≤
      (∑' entry, Pr[= entry | runResolvedHistoryPrefix computation context fuel history] * prefixUnresolvedStartCharge candidate entry) *
        (Fintype.card Digest : ENNReal)⁻¹ := by
  simp only [runResolvedHistoryAdaptive_eq_prefix_complete, tsum_probOutput_bind_mul]
  rw [← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro option
  rw [mul_assoc]
  apply mul_le_mul' le_rfl
  cases option with
  | none => simp [completeHistoryResolvedPrefix, prefixUnresolvedStartCharge, retainCompletableResult, historyUnresolvedStartAllowance]
  | some entry =>
      apply le_trans _ (expected_completeHistoryResolvedPrefix_unresolvedStart_le_prefixCharge entry candidate)
      exact ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (historyUnresolvedStartAllowance_retain_le candidate result)

theorem probEvent_live_unresolvedStart_hit_le_prefixCharge
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel bound budget : Nat) (history : List Probe)
    (candidate : DeferredContext → α → Option Probe)
    (hconsistent : context.ValuesConsistent) (hcovered : PendingCoveredBy history context)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe bound)
    (hbudget : history.length + bound ≤ budget) (hspace : budget < Fintype.card Digest) :
    Pr[LiveUnresolvedStartHit candidate | sampledHistoryFilteredRun computation context fuel history] ≤
      (∑' entry, Pr[= entry | runResolvedHistoryPrefix computation context fuel history] * prefixUnresolvedStartCharge candidate entry) *
        (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [probEvent_liveUnresolvedStartHit_eq_expected,
    expected_live_sampledHistoryFilteredRun_eq_adaptive_rate computation context fuel bound budget history
      (historyUnresolvedStartAllowance candidate) hconsistent hcovered hbound hbudget hspace]
  exact expected_live_historyAdaptive_unresolvedStart_le_prefixCharge computation context fuel history candidate

noncomputable def nativeStartPrefixCharge
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (fuel ordinal : Nat) : ENNReal :=
  ∑' entry, Pr[= entry | runResolvedHistoryPrefix (nativeProbeCutAt computation ordinal) (ensuredInitialContext targets) fuel []] *
    prefixUnresolvedStartCharge nativeCutCandidate entry

theorem probEvent_sampledEnsuredNativeProbeCut_unresolvedStart_le_prefixCharge
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (fuel ordinal : Nat) (hordinal : ordinal < Fintype.card Digest) :
    Pr[LiveUnresolvedStartHit nativeCutCandidate | sampledEnsuredNativeProbeCut targets computation fuel ordinal] ≤
      nativeStartPrefixCharge targets computation fuel ordinal * (Fintype.card Digest : ENNReal)⁻¹ := by
  have hnative := probEvent_live_unresolvedStart_hit_le_prefixCharge (nativeProbeCutAt computation ordinal)
    (ensuredInitialContext targets) fuel ordinal ordinal [] nativeCutCandidate (ensuredInitialContext_valid targets).valuesConsistent
    (show PendingCoveredBy [] (ensuredInitialContext targets) from pendingCoveredBy_empty)
    (nativeProbeCutAt_probeBound computation ordinal) (by simp) hordinal
  have htable : ∀ base, completedStartTable (ensuredInitialContext targets).state base = base := by
    intro base
    funext index
    rfl
  simpa only [sampledEnsuredNativeProbeCut, sampledHistoryFilteredRun, ChainStartHistoryHit, List.not_mem_nil,
    false_and, exists_false, if_false, htable, nativeStartPrefixCharge] using hnative

theorem sum_sampledEnsuredNativeProbeCut_unresolvedStart_le_prefixCharge
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (fuel q : Nat) (hq : q ≤ Fintype.card Digest) :
    (∑ ordinal ∈ Finset.range q,
      Pr[LiveUnresolvedStartHit nativeCutCandidate | sampledEnsuredNativeProbeCut targets computation fuel ordinal]) ≤
      (∑ ordinal ∈ Finset.range q, nativeStartPrefixCharge targets computation fuel ordinal) * (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ordinal hmem
  exact probEvent_sampledEnsuredNativeProbeCut_unresolvedStart_le_prefixCharge targets computation fuel ordinal
    ((Finset.mem_range.mp hmem).trans_le hq)

end SphincsSecurity.Concrete.OtsProbeSimulation
