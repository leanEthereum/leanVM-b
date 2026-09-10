import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeLiveStartCounting

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def ensuredInitialContext (targets : Finset Position) : DeferredContext :=
  { state := { LazyRevealProbe.State.empty with ensured := targets.image Coordinate.position }
    values := emptyDeferredStructuralValues }

theorem ensuredInitialContext_coreEq (targets : Finset Position) :
    ({ state := LazyRevealProbe.State.empty, values := emptyDeferredStructuralValues } : DeferredContext).CoreEq
      (ensuredInitialContext targets) := ⟨rfl, rfl, rfl⟩

theorem ensuredInitialContext_valid (targets : Finset Position) : (ensuredInitialContext targets).Valid :=
  DeferredContext.valid_empty.of_coreEq (ensuredInitialContext_coreEq targets)

theorem ensuredInitialContext_resolvedInvariant
    (targets : Finset Position) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput) :
    ResolvedContextInvariant parameter table (ensuredInitialContext targets) ∅ ∅ :=
  (resolvedContextInvariant_empty parameter table).of_coreEq (ensuredInitialContext_coreEq targets)

theorem ensuredInitialContext_completable (targets : Finset Position) (table : OtsSecretIndex → HashOutput) :
    DeferredCompletable table (ensuredInitialContext targets) :=
  (deferredCompletable_iff_of_coreEq (ensuredInitialContext_coreEq targets)).mp (deferredCompletable_empty table)

theorem ensuredInitialContext_visible
    (targets : Finset Position) (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput) :
    VisibleResolvedComputationsCached parameter table (ensuredInitialContext targets) ∅ := by
  intro position output _hresolvable hvalue
  simp [ensuredInitialContext, LazyRevealProbe.State.empty] at hvalue

theorem ensuredInitialContext_published (targets : Finset Position) : PublishedValues (ensuredInitialContext targets).state := by
  intro coordinate hrevealed
  simp [ensuredInitialContext, LazyRevealProbe.State.empty] at hrevealed

theorem ensuredInitialContext_mem_ensured (targets : Finset Position) (target : Position) (hmem : target ∈ targets) :
    .position target ∈ (ensuredInitialContext targets).state.ensured :=
  Finset.mem_image.mpr ⟨target, hmem, rfl⟩

theorem sum_targets_privateHits_ensuredInitial_le_structuralCharge
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (q fuel : Nat) (table : OtsSecretIndex → HashOutput) (hq : q ≤ 2 ^ 126) :
    (∑ target ∈ targets, ∑ ordinal ∈ Finset.range q,
      Pr[PrivateCandidatePairHit | privateResolvedSelectedCandidate target (privateRawCutCandidate target) <$>
        runPrivateResolvedView target table (ensuredInitialContext targets) fuel (privatePositionProbeCutAt target computation ordinal)]) ≤
      expectedLiveResolvedQueryCharge structuralProbeQueryCharge computation (ensuredInitialContext targets) fuel table *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  apply sum_targets_privateResolvedRawCandidate_hit_le_expectedLiveStructuralCharge targets computation q (ensuredInitialContext targets) fuel table
    (ensuredInitialContext_valid targets) (ensuredInitialContext_completable targets table)
    (ensuredInitialContext_mem_ensured targets)
  · intro target _
    rfl
  · intro target _
    rfl
  · intro target _
    simp [ensuredInitialContext, LazyRevealProbe.State.empty]
  · intro target _
    simpa [ensuredInitialContext, LazyRevealProbe.State.empty, LazyRevealProbe.State.pendingAt] using hq

noncomputable def sampledEnsuredNativeProbeCut
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (fuel ordinal : Nat) :
    ProbComp (Option (ResolvedRunResult (PrivateValueCut α))) := do
  let table ← sampleOtsHashTable
  runResolvedFromTable (ensuredInitialContext targets) fuel table (nativeProbeCutAt computation ordinal)

theorem probEvent_sampledEnsuredNativeProbeCut_unresolvedStart_le
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (fuel ordinal : Nat)
    (hordinal : ordinal ≤ 2 ^ 126) :
    Pr[LiveUnresolvedStartHit nativeCutCandidate | sampledEnsuredNativeProbeCut targets computation fuel ordinal] ≤
      (∑' result, Pr[= result | sampledEnsuredNativeProbeCut targets computation fuel ordinal] *
        historyUnresolvedStartCharge nativeCutCandidate (retainCompletableResult result)) *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  have hnative := probEvent_live_unresolvedStart_hit_le_native_charge (nativeProbeCutAt computation ordinal)
    (ensuredInitialContext targets) fuel ordinal [] nativeCutCandidate (ensuredInitialContext_valid targets).valuesConsistent
    (show PendingCoveredBy [] (ensuredInitialContext targets) from pendingCoveredBy_empty)
    (nativeProbeCutAt_probeBound computation ordinal) (by simpa only [List.length_nil, Nat.zero_add] using hordinal)
  have htable : ∀ base, completedStartTable (ensuredInitialContext targets).state base = base := by
    intro base
    funext index
    rfl
  simpa only [sampledEnsuredNativeProbeCut, sampledHistoryFilteredRun, ChainStartHistoryHit, List.not_mem_nil,
    false_and, exists_false, ↓reduceIte, htable] using hnative

theorem sum_sampledEnsuredNativeProbeCut_unresolvedStart_le
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (fuel q : Nat)
    (hq : q ≤ 2 ^ 126) :
    (∑ ordinal ∈ Finset.range q,
      Pr[LiveUnresolvedStartHit nativeCutCandidate | sampledEnsuredNativeProbeCut targets computation fuel ordinal]) ≤
      (∑ ordinal ∈ Finset.range q, ∑' result,
        Pr[= result | sampledEnsuredNativeProbeCut targets computation fuel ordinal] *
          historyUnresolvedStartCharge nativeCutCandidate (retainCompletableResult result)) *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ordinal hmem
  exact probEvent_sampledEnsuredNativeProbeCut_unresolvedStart_le targets computation fuel ordinal
    ((Nat.le_of_lt (Finset.mem_range.mp hmem)).trans hq)

theorem sum_sampledEnsuredNativeProbeCut_unresolvedStart_le_expectedChainStartCharge
    (targets : Finset Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α) (fuel q : Nat) (hq : q ≤ 2 ^ 126) :
    (∑ ordinal ∈ Finset.range q,
      Pr[LiveUnresolvedStartHit nativeCutCandidate | sampledEnsuredNativeProbeCut targets computation fuel ordinal]) ≤
      (∑' table, Pr[= table | sampleOtsHashTable] *
        expectedLiveResolvedQueryCharge chainStartProbeQueryCharge computation
          (ensuredInitialContext targets) fuel table) *
        ((4 / 3 : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  apply (sum_sampledEnsuredNativeProbeCut_unresolvedStart_le targets computation fuel q hq).trans
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

end SphincsSecurity.Concrete.OtsProbeSimulation
