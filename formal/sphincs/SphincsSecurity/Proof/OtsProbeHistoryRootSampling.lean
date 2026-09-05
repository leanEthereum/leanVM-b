import SphincsSecurity.Proof.OtsProbeHistoryCanonicalRisk

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local instance] Classical.propDecidable
attribute [local irreducible] sampleOtsHashTable maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000

noncomputable def canonicalRootHistoryPrefix (fuel : Nat) : ProbComp (Option (HistoryResolvedPrefix (Digest × SplitHashCache))) :=
  runCanonicalHistoryBlockPrefix (maskedPublishedTreeRoot.run emptySplitHashCache)
    { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues } fuel []

noncomputable def guardedRootContinuation
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (continuation : Digest → OracleComp (OracleWorld + SigningSpec) α) :
    Option (ResolvedRunResult (Digest × SplitHashCache)) → ProbComp (Option (ResolvedRunResult (α × SplitHashCache)))
  | none => pure none
  | some result =>
      runGuardedCanonicalNative parameter result.value.1 ftsSecret (continuation result.value.1)
        result.context result.remaining result.table result.value.2

noncomputable def guardedRootHistoryContinuation
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (continuation : Digest → OracleComp (OracleWorld + SigningSpec) α) :
    Option (HistoryResolvedPrefix (Digest × SplitHashCache)) → ProbComp (Option (ResolvedRunResult (α × SplitHashCache)))
  | none => pure none
  | some entry =>
      sampledGuardedCanonicalNative parameter entry.value.1 ftsSecret (continuation entry.value.1)
        entry.context entry.remaining entry.history entry.value.2

theorem canonicalHistoryBoundary_of_mem_root
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput) (fuel : Nat)
    (result : ResolvedRunResult (Digest × SplitHashCache))
    (hresult : some result ∈ support (runResolvedFromTable
      { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
      fuel table (maskedPublishedTreeRoot.run emptySplitHashCache))) :
    canonicalHistoryBoundary (some result) = some result := by
  have hcore := resolvedCore_of_mem_runResolved_maskedPublishedTreeRoot parameter table fuel result hresult
  have hcanonical := canonicalMaterializedValues_of_mem_maskedPublishedTreeRoot parameter table fuel result hresult
  have hcomplete := deferredCompletable_of_mem_resolved_maskedPublishedTreeRoot parameter table fuel result hresult
  have hpublished := resolvedPreservesPublished_maskedPublishedTreeRoot _ _ _ _ _ publishedValues_empty hresult
  have hpublic := materializedStartsPublished_of_canonical table result.context hcanonical
  have hsame : canonicalizeMaterializedValues result.table result.context = result.context := by
    rw [hcore.1]
    exact canonicalizeMaterializedValues_eq_of_canonical table result.context hcanonical
  simp [canonicalHistoryBoundary, hcomplete, hpublic, hpublished, hsame]

theorem evalDist_guardedAfterRoot_eq_boundary_continuation
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (continuation : Digest → OracleComp (OracleWorld + SigningSpec) α) :
    evalDist (guardedCanonicalAfterRoot parameter table ftsSecret fuel continuation) =
      evalDist (runResolvedFromTable
        { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues }
        fuel table (maskedPublishedTreeRoot.run emptySplitHashCache) >>= fun result =>
          guardedRootContinuation parameter ftsSecret continuation (canonicalHistoryBoundary result)) := by
  rw [guardedCanonicalAfterRoot]
  apply evalDist_bind_congr
  intro option hoption
  cases option with
  | none => rfl
  | some result =>
      rw [canonicalHistoryBoundary_of_mem_root parameter table fuel result hoption]
      simp only [guardedRootContinuation]
      rw [(resolvedCore_of_mem_runResolved_maskedPublishedTreeRoot parameter table fuel result hoption).1]

theorem complete_rootHistory_guardedContinuation
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (continuation : Digest → OracleComp (OracleWorld + SigningSpec) α)
    (option : Option (HistoryResolvedPrefix (Digest × SplitHashCache))) :
    (completeHistoryResolvedPrefix option >>= guardedRootContinuation parameter ftsSecret continuation) =
      guardedRootHistoryContinuation parameter ftsSecret continuation option := by
  cases option with
  | none => simp [completeHistoryResolvedPrefix, guardedRootContinuation, guardedRootHistoryContinuation]
  | some entry =>
      simp only [completeHistoryResolvedPrefix, completeResolvedHistory, guardedRootHistoryContinuation,
        sampledGuardedCanonicalNative, bind_assoc]
      apply bind_congr
      intro base
      split_ifs <;> simp only [pure_bind, guardedRootContinuation]

theorem evalDist_sampledGuardedAfterRoot_eq_historyPrefix
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (continuation : Digest → OracleComp (OracleWorld + SigningSpec) α) :
    evalDist (sampleOtsHashTable >>= fun table => guardedCanonicalAfterRoot parameter table ftsSecret fuel continuation) =
      evalDist (canonicalRootHistoryPrefix fuel >>= guardedRootHistoryContinuation parameter ftsSecret continuation) := by
  have htable : ∀ base, completedStartTable LazyRevealProbe.State.empty base = base := by
    intro base
    funext index
    rfl
  have hsample := evalDist_sampledHistoryFilteredRun_canonicalBoundary
    (maskedPublishedTreeRoot.run emptySplitHashCache)
    { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues } fuel 0 []
    DeferredContext.valid_empty.valuesConsistent pendingCoveredBy_empty
    (maskedPublishedTreeRoot_probeFree emptySplitHashCache) (by simp)
  have hfirst : evalDist (sampleOtsHashTable >>= fun table => guardedCanonicalAfterRoot parameter table ftsSecret fuel continuation) =
      evalDist ((sampledHistoryFilteredRun (maskedPublishedTreeRoot.run emptySplitHashCache)
        { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues } fuel [] >>= fun result =>
          pure (canonicalHistoryBoundary result)) >>= guardedRootContinuation parameter ftsSecret continuation) := by
    simp only [sampledHistoryFilteredRun, bind_assoc, pure_bind, ChainStartHistoryHit, List.not_mem_nil,
      false_and, exists_false, if_false, htable]
    apply evalDist_bind_congr
    intro table _
    exact evalDist_guardedAfterRoot_eq_boundary_continuation parameter table ftsSecret fuel continuation
  rw [hfirst, evalDist_bind, hsample, ← evalDist_bind]
  simp only [canonicalRootHistoryPrefix, runCanonicalHistoryBlockPrefix, bind_assoc, pure_bind]
  apply evalDist_bind_congr
  intro option _
  exact congrArg evalDist (complete_rootHistory_guardedContinuation parameter ftsSecret continuation (canonicalHistoryPrefix option))

theorem canonicalRootHistoryPrefix_invariant (fuel : Nat) (entry : HistoryResolvedPrefix (Digest × SplitHashCache))
    (hentry : some entry ∈ support (canonicalRootHistoryPrefix fuel)) :
    entry.context.ValuesConsistent ∧ PendingCoveredBy entry.history entry.context ∧ PublishedValues entry.context.state ∧
      (∀ base, CanonicalMaterializedValues (completedStartTable entry.context.state base) entry.context) ∧ entry.history = [] := by
  have hinvariant := canonicalHistoryBlockPrefix_invariant (maskedPublishedTreeRoot.run emptySplitHashCache)
    { state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues } fuel 0 [] entry
    DeferredContext.valid_empty.valuesConsistent pendingCoveredBy_empty (maskedPublishedTreeRoot_probeFree emptySplitHashCache) hentry
  exact ⟨hinvariant.1, hinvariant.2.1, hinvariant.2.2.1, hinvariant.2.2.2,
    canonicalHistoryBlockPrefix_history_of_probeFree _ _ fuel [] entry (maskedPublishedTreeRoot_probeFree emptySplitHashCache) hentry⟩

theorem probEvent_sampledGuardedAfterRoot_unresolvedStart_le
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel bound : Nat)
    (continuation : Digest → OracleComp (OracleWorld + SigningSpec) α)
    (candidate : DeferredContext → (α × SplitHashCache) → Option Probe)
    (hbound : ∀ root, (continuation root).IsQueryBoundP IsOuterHash bound) (hbudget : bound ≤ 2 ^ 126) :
    Pr[LiveUnresolvedStartHit candidate | sampleOtsHashTable >>= fun table =>
      guardedCanonicalAfterRoot parameter table ftsSecret fuel continuation] ≤
      (∑' result, Pr[= result | sampleOtsHashTable >>= fun table =>
        guardedCanonicalAfterRoot parameter table ftsSecret fuel continuation] * historyUnresolvedStartCharge candidate result) *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  have hdist := evalDist_sampledGuardedAfterRoot_eq_historyPrefix parameter ftsSecret fuel continuation
  rw [OracleComp.probEvent_congr' (fun _ _ => Iff.rfl) hdist]
  have hcost : (∑' result, Pr[= result | sampleOtsHashTable >>= fun table =>
      guardedCanonicalAfterRoot parameter table ftsSecret fuel continuation] * historyUnresolvedStartCharge candidate result) =
      ∑' result, Pr[= result | canonicalRootHistoryPrefix fuel >>=
        guardedRootHistoryContinuation parameter ftsSecret continuation] * historyUnresolvedStartCharge candidate result := by
    apply tsum_congr
    intro result
    rw [_root_.OracleComp.probOutput_congr rfl hdist]
  rw [hcost, probEvent_bind_eq_tsum, tsum_probOutput_bind_mul, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro option
  by_cases hsupport : option ∈ support (canonicalRootHistoryPrefix fuel)
  · cases option with
    | none => simp [guardedRootHistoryContinuation, LiveUnresolvedStartHit, historyUnresolvedStartCharge]
    | some entry =>
        have hinv := canonicalRootHistoryPrefix_invariant fuel entry hsupport
        have hlocal := probEvent_guardedCanonical_unresolvedStart_le parameter entry.value.1 ftsSecret
          (continuation entry.value.1) entry.context entry.remaining bound entry.history entry.value.2 candidate
          hinv.1 hinv.2.1 hinv.2.2.1 (hbound _) (by simpa only [hinv.2.2.2.2, List.length_nil, Nat.zero_add] using hbudget)
        simpa only [guardedRootHistoryContinuation, mul_assoc] using mul_le_mul' le_rfl hlocal
  · simp [probOutput_eq_zero_of_not_mem_support hsupport]

noncomputable def sampledCanonicalAfterRootTrace
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (continuation : Digest → OracleComp (OracleWorld + SigningSpec) α) :
    ProbComp (Option (ResolvedRunResult (α × SplitHashCache)) × Bool) := do
  let table ← sampleOtsHashTable
  canonicalStartErasureAfterRoot parameter table ftsSecret fuel continuation

theorem evalDist_eraseFlagged_sampledAfterRoot_eq_guarded
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (continuation : Digest → OracleComp (OracleWorld + SigningSpec) α) :
    evalDist (eraseFlaggedResult <$> sampledCanonicalAfterRootTrace parameter ftsSecret fuel continuation) =
      evalDist (sampleOtsHashTable >>= fun table => guardedCanonicalAfterRoot parameter table ftsSecret fuel continuation) := by
  simp only [sampledCanonicalAfterRootTrace, map_bind]
  apply evalDist_bind_congr
  intro table _
  exact evalDist_eraseFlagged_afterRoot_eq_guarded parameter table ftsSecret fuel continuation

theorem probEvent_sampledAfterRoot_erasure_le_inv216
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (continuation : Digest → OracleComp (OracleWorld + SigningSpec) α) :
    Pr[fun result => result.2 = true | sampledCanonicalAfterRootTrace parameter ftsSecret fuel continuation] ≤
      ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  unfold sampledCanonicalAfterRootTrace
  apply probEvent_bind_le_of_forall_le
  intro table _
  exact probEvent_canonicalStartErasureAfterRoot_le_inv216 parameter table ftsSecret fuel continuation

theorem probEvent_sampledCanonicalAfterRoot_unresolvedStart_le
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel bound : Nat)
    (continuation : Digest → OracleComp (OracleWorld + SigningSpec) α)
    (candidate : DeferredContext → (α × SplitHashCache) → Option Probe)
    (hbound : ∀ root, (continuation root).IsQueryBoundP IsOuterHash bound) (hbudget : bound ≤ 2 ^ 126) :
    Pr[LiveUnresolvedStartHit candidate | Prod.fst <$> sampledCanonicalAfterRootTrace parameter ftsSecret fuel continuation] ≤
      (∑' result, Pr[= result | Prod.fst <$> sampledCanonicalAfterRootTrace parameter ftsSecret fuel continuation] *
        historyUnresolvedStartCharge candidate result) * ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) +
        ((2 ^ 216 : Nat) : ENNReal)⁻¹ := by
  have hdist := evalDist_eraseFlagged_sampledAfterRoot_eq_guarded parameter ftsSecret fuel continuation
  have hcomparison := probEvent_fst_le_erased_add_flag
    (sampledCanonicalAfterRootTrace parameter ftsSecret fuel continuation) (LiveUnresolvedStartHit candidate)
  rw [OracleComp.probEvent_congr' (fun _ _ => Iff.rfl) hdist] at hcomparison
  have hcost := expected_erased_le_fst (sampledCanonicalAfterRootTrace parameter ftsSecret fuel continuation)
    (historyUnresolvedStartCharge candidate) rfl
  have hcostEq :
      (∑' result, Pr[= result | eraseFlaggedResult <$> sampledCanonicalAfterRootTrace parameter ftsSecret fuel continuation] *
        historyUnresolvedStartCharge candidate result) =
      ∑' result, Pr[= result | sampleOtsHashTable >>= fun table => guardedCanonicalAfterRoot parameter table ftsSecret fuel continuation] *
        historyUnresolvedStartCharge candidate result := by
    apply tsum_congr
    intro result
    rw [_root_.OracleComp.probOutput_congr rfl hdist]
  rw [hcostEq] at hcost
  exact hcomparison.trans (add_le_add
    ((probEvent_sampledGuardedAfterRoot_unresolvedStart_le parameter ftsSecret fuel bound continuation candidate hbound hbudget).trans
      (mul_le_mul' hcost le_rfl))
    (probEvent_sampledAfterRoot_erasure_le_inv216 parameter ftsSecret fuel continuation))

end SphincsSecurity.Concrete.OtsProbeSimulation
