import SphincsSecurity.Proof.OtsProbeHistoryLiveRisk
import SphincsSecurity.Proof.OtsProbeSigningFailureCoupling

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2000

noncomputable def historyCanonicalContext (context : DeferredContext) : DeferredContext :=
  canonicalizeMaterializedValues (completedStartTable context.state (fun _ => 0)) context

noncomputable def canonicalHistoryBoundary : Option (ResolvedRunResult α) → Option (ResolvedRunResult α)
  | none => none
  | some result =>
      if DeferredCompletable result.table result.context ∧ MaterializedStartsPublished result.context ∧
          PublishedValues result.context.state then
        some { result with context := canonicalizeMaterializedValues result.table result.context }
      else none

noncomputable def canonicalHistoryPrefix : Option (HistoryResolvedPrefix α) → Option (HistoryResolvedPrefix α)
  | none => none
  | some entry =>
      if entry.context.Valid ∧ ¬PrivateStructuralHit entry.context ∧ MaterializedStartsPublished entry.context ∧
          PublishedValues entry.context.state then
        some { entry with context := historyCanonicalContext entry.context }
      else none

theorem completeHistoryResolvedPrefix_canonicalBoundary
    (entry : HistoryResolvedPrefix α) (hconsistent : entry.context.ValuesConsistent)
    (hcovered : PendingCoveredBy entry.history entry.context)
    (hcard : entry.context.state.pending.card < Fintype.card Digest) :
    evalDist (completeHistoryResolvedPrefix (some entry) >>= fun result => pure (canonicalHistoryBoundary result)) =
      evalDist (completeHistoryResolvedPrefix (canonicalHistoryPrefix (some entry))) := by
  by_cases hgood : entry.context.Valid ∧ ¬PrivateStructuralHit entry.context
  · by_cases hpublic : MaterializedStartsPublished entry.context ∧ PublishedValues entry.context.state
    · have hguard : entry.context.Valid ∧ ¬PrivateStructuralHit entry.context ∧ MaterializedStartsPublished entry.context ∧
          PublishedValues entry.context.state := ⟨hgood.1, hgood.2, hpublic⟩
      simp only [canonicalHistoryPrefix, if_pos hguard, completeHistoryResolvedPrefix]
      unfold historyCanonicalContext
      rw [← completeResolvedHistory_canonicalize entry.context entry.remaining entry.history entry.value
        (fun _ => 0) hpublic.1 hpublic.2]
      unfold completeResolvedHistory
      simp only [bind_assoc]
      apply evalDist_bind_congr
      intro base _
      by_cases hhit : ChainStartHistoryHit entry.context entry.history base
      · simp [hhit, canonicalHistoryBoundary]
      · have hcomplete := (deferredCompletable_history_clean_iff entry.context entry.history base
          hconsistent hcovered hcard hhit).mpr hgood
        simp [hhit, canonicalHistoryBoundary, hcomplete, hpublic.1, hpublic.2]
    · have hguard : ¬(entry.context.Valid ∧ ¬PrivateStructuralHit entry.context ∧ MaterializedStartsPublished entry.context ∧
          PublishedValues entry.context.state) := fun h => hpublic h.2.2
      simp only [canonicalHistoryPrefix, if_neg hguard, completeHistoryResolvedPrefix]
      unfold completeResolvedHistory
      simp only [bind_assoc]
      rw [← evalDist_sampleOtsHashTable_bind_const (pure (none : Option (ResolvedRunResult α)))]
      apply evalDist_bind_congr
      intro base _
      by_cases hhit : ChainStartHistoryHit entry.context entry.history base
      · simp [hhit, canonicalHistoryBoundary]
      · have hguard : ¬(DeferredCompletable (completedStartTable entry.context.state base) entry.context ∧
            MaterializedStartsPublished entry.context ∧ PublishedValues entry.context.state) := fun h => hpublic h.2
        simp [hhit, canonicalHistoryBoundary, hguard]
  · have hguard : ¬(entry.context.Valid ∧ ¬PrivateStructuralHit entry.context ∧ MaterializedStartsPublished entry.context ∧
        PublishedValues entry.context.state) := fun h => hgood ⟨h.1, h.2.1⟩
    simp only [canonicalHistoryPrefix, if_neg hguard, completeHistoryResolvedPrefix]
    unfold completeResolvedHistory
    simp only [bind_assoc]
    rw [← evalDist_sampleOtsHashTable_bind_const (pure (none : Option (ResolvedRunResult α)))]
    apply evalDist_bind_congr
    intro base _
    by_cases hhit : ChainStartHistoryHit entry.context entry.history base
    · simp [hhit, canonicalHistoryBoundary]
    · have hcomplete : ¬DeferredCompletable (completedStartTable entry.context.state base) entry.context :=
        fun h => hgood ((deferredCompletable_history_clean_iff entry.context entry.history base
          hconsistent hcovered hcard hhit).mp h)
      simp [hhit, canonicalHistoryBoundary, hcomplete]

theorem evalDist_sampledHistoryFilteredRun_canonicalBoundary
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel bound : Nat) (history : List Probe)
    (hconsistent : context.ValuesConsistent) (hcovered : PendingCoveredBy history context)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe bound)
    (hbudget : history.length + bound ≤ 2 ^ 126) :
    evalDist (sampledHistoryFilteredRun computation context fuel history >>= fun result => pure (canonicalHistoryBoundary result)) =
      evalDist (runResolvedHistoryPrefix computation context fuel history >>= fun entry =>
        completeHistoryResolvedPrefix (canonicalHistoryPrefix entry)) := by
  have hfirst := evalDist_history_filtered_runResolved_eq_prefix_observe computation context fuel bound history
    (fun result => pure (canonicalHistoryBoundary result)) (by
      intro result _hvalues _hstarts hdoomed
      simp [canonicalHistoryBoundary, hdoomed]) hconsistent hcovered hbound hbudget
  change evalDist (sampledHistoryFilteredRun computation context fuel history >>= fun result => pure (canonicalHistoryBoundary result)) = _ at hfirst
  rw [hfirst, bind_assoc]
  apply evalDist_bind_congr
  intro option hsupport
  cases option with
  | none => simp [canonicalHistoryPrefix, completeHistoryResolvedPrefix, canonicalHistoryBoundary]
  | some entry =>
      have hentry := historyPrefix_invariant_of_mem computation context fuel bound history entry hcovered hbound hsupport
      have hvalues := valuesConsistent_of_mem_historyPrefix computation context fuel history entry hconsistent hsupport
      have hspace : 2 ^ 126 < Fintype.card Digest := by norm_num [digestBits]
      rw [completeHistoryResolvedPrefix_canonicalBoundary entry hvalues hentry.1
        ((hentry.1.card_le.trans (hentry.2.trans hbudget)).trans_lt hspace)]

theorem canonicalHistoryBoundary_eq_liveCanonical_of_no_erasure
    (result : ResolvedRunResult (α × SplitHashCache))
    (hconsistent : result.context.ValuesConsistent) (hstarts : StartTableAgrees result.context.state result.table)
    (hpublished : PublishedValues result.context.state)
    (hnoErasure : ¬LiveSigningStartErasure result.table (some result)) :
    canonicalHistoryBoundary (some result) = retainCompletableResult (canonicalizeResolvedRun result.table (some result)) := by
  by_cases hcomplete : DeferredCompletable result.table result.context
  · have hpublic : MaterializedStartsPublished result.context := by
      intro start hknown
      by_contra hnot
      apply hnoErasure
      refine ⟨hcomplete, start, hknown, ?_⟩
      change (if start.coordinate ∈ result.context.state.revealed then some (result.table start) else none) = none
      simp [hnot]
    have hcanonicalComplete : DeferredCompletable result.table (canonicalizeMaterializedValues result.table result.context) := by
      obtain ⟨completion, hcompletion⟩ := hcomplete
      exact ⟨completion, hcompletion.to_canonicalizedMaterializedValues⟩
    simp [canonicalHistoryBoundary, canonicalizeResolvedRun, retainCompletableResult, hcomplete, hpublic, hpublished,
      hcanonicalComplete]
  · have hcanonicalDead := (doomedResolvedContext_canonicalizeMaterializedValues ⟨hconsistent, hstarts, hcomplete⟩).2.2
    simp [canonicalHistoryBoundary, canonicalizeResolvedRun, retainCompletableResult, hcomplete, hcanonicalDead]

theorem canonicalHistoryPrefix_history_length
    (entry result : HistoryResolvedPrefix α) (hresult : canonicalHistoryPrefix (some entry) = some result) :
    result.history = entry.history := by
  simp only [canonicalHistoryPrefix] at hresult
  split_ifs at hresult
  · cases hresult
    rfl

theorem expected_canonicalHistoryBoundary_unresolvedStart_le
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel bound : Nat) (history : List Probe)
    (candidate : DeferredContext → α → Option Probe)
    (hconsistent : context.ValuesConsistent) (hcovered : PendingCoveredBy history context)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe bound)
    (hbudget : history.length + bound ≤ 2 ^ 126) :
    (∑' result, Pr[= result | sampledHistoryFilteredRun computation context fuel history] *
      historyUnresolvedStartAllowance candidate (canonicalHistoryBoundary result)) ≤
    (∑' result, Pr[= result | sampledHistoryFilteredRun computation context fuel history] *
      historyUnresolvedStartCharge candidate (canonicalHistoryBoundary result)) *
      ((4 / 3 : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) := by
  have hdist := evalDist_sampledHistoryFilteredRun_canonicalBoundary computation context fuel bound history
    hconsistent hcovered hbound hbudget
  have hcost (cost : Option (ResolvedRunResult α) → ℝ≥0∞) :
      (∑' result, Pr[= result | sampledHistoryFilteredRun computation context fuel history] * cost (canonicalHistoryBoundary result)) =
      ∑' result, Pr[= result | runResolvedHistoryPrefix computation context fuel history >>= fun entry =>
        completeHistoryResolvedPrefix (canonicalHistoryPrefix entry)] * cost result := by
    have hprob : ∀ result, Pr[= result | sampledHistoryFilteredRun computation context fuel history >>=
        fun result => pure (canonicalHistoryBoundary result)] =
        Pr[= result | runResolvedHistoryPrefix computation context fuel history >>= fun entry =>
          completeHistoryResolvedPrefix (canonicalHistoryPrefix entry)] := fun result => _root_.OracleComp.probOutput_congr rfl hdist
    calc
      _ = ∑' result, Pr[= result | sampledHistoryFilteredRun computation context fuel history >>=
          fun result => pure (canonicalHistoryBoundary result)] * cost result := by
        simp only [tsum_probOutput_bind_mul, tsum_probOutput_pure_mul]
      _ = _ := tsum_congr fun result => congrArg (fun p => p * cost result) (hprob result)
  rw [hcost, hcost]
  simp only [tsum_probOutput_bind_mul]
  rw [← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro option
  by_cases hsupport : option ∈ support (runResolvedHistoryPrefix computation context fuel history)
  · cases option with
    | none => simp [canonicalHistoryPrefix, completeHistoryResolvedPrefix, historyUnresolvedStartAllowance, historyUnresolvedStartCharge]
    | some entry =>
        cases hcanonical : canonicalHistoryPrefix (some entry) with
        | none => simp [completeHistoryResolvedPrefix, historyUnresolvedStartAllowance, historyUnresolvedStartCharge]
        | some result =>
            have hlength := (historyPrefix_invariant_of_mem computation context fuel bound history entry hcovered hbound hsupport).2
            rw [← canonicalHistoryPrefix_history_length entry result hcanonical] at hlength
            have hlocal := expected_completeHistoryResolvedPrefix_unresolvedStart_le result candidate (hlength.trans hbudget)
            simpa only [mul_assoc] using mul_le_mul' le_rfl hlocal
  · simp [probOutput_eq_zero_of_not_mem_support hsupport]

theorem retainCompletableResult_canonicalHistoryBoundary (result : Option (ResolvedRunResult α)) :
    retainCompletableResult (canonicalHistoryBoundary result) = canonicalHistoryBoundary result := by
  cases result with
  | none => rfl
  | some result =>
      simp only [canonicalHistoryBoundary]
      split_ifs with hguard
      · have hcomplete : DeferredCompletable result.table (canonicalizeMaterializedValues result.table result.context) := by
          obtain ⟨completion, hcompletion⟩ := hguard.1
          exact ⟨completion, hcompletion.to_canonicalizedMaterializedValues⟩
        simp [retainCompletableResult, hcomplete]
      · rfl

theorem probEvent_canonicalHistoryBoundary_unresolvedStart_le
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel bound : Nat) (history : List Probe)
    (candidate : DeferredContext → α → Option Probe)
    (hconsistent : context.ValuesConsistent) (hcovered : PendingCoveredBy history context)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe bound)
    (hbudget : history.length + bound ≤ 2 ^ 126) :
    Pr[LiveUnresolvedStartHit candidate | sampledHistoryFilteredRun computation context fuel history >>=
      fun result => pure (canonicalHistoryBoundary result)] ≤
    (∑' result, Pr[= result | sampledHistoryFilteredRun computation context fuel history] *
      historyUnresolvedStartCharge candidate (canonicalHistoryBoundary result)) *
      ((4 / 3 : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) := by
  rw [probEvent_liveUnresolvedStartHit_eq_expected]
  simp only [tsum_probOutput_bind_mul, tsum_probOutput_pure_mul, retainCompletableResult_canonicalHistoryBoundary]
  exact expected_canonicalHistoryBoundary_unresolvedStart_le computation context fuel bound history candidate
    hconsistent hcovered hbound hbudget

theorem historyCanonicalContext_start_values
    (context : DeferredContext) (hpublic : MaterializedStartsPublished context) (hpublished : PublishedValues context.state)
    (start : OtsSecretIndex) :
    (historyCanonicalContext context).state.values start.coordinate = context.state.values start.coordinate :=
  canonicalize_start_values_eq_of_materializedStartsPublished _ context hpublic hpublished
    (startTableAgrees_completedStartTable context.state (fun _ => 0)) start

theorem historyCanonicalContext_completedStartTable
    (context : DeferredContext) (hpublic : MaterializedStartsPublished context) (hpublished : PublishedValues context.state)
    (base : OtsSecretIndex → HashOutput) :
    completedStartTable (historyCanonicalContext context).state base = completedStartTable context.state base := by
  funext start
  unfold completedStartTable
  rw [historyCanonicalContext_start_values context hpublic hpublished start]

theorem historyCanonicalContext_canonical
    (context : DeferredContext) (hconsistent : context.ValuesConsistent)
    (hpublic : MaterializedStartsPublished context) (hpublished : PublishedValues context.state)
    (base : OtsSecretIndex → HashOutput) :
    CanonicalMaterializedValues (completedStartTable (historyCanonicalContext context).state base) (historyCanonicalContext context) := by
  rw [historyCanonicalContext_completedStartTable context hpublic hpublished base]
  have hcontext : historyCanonicalContext context = canonicalizeMaterializedValues (completedStartTable context.state base) context :=
    canonicalize_completedStartTable_independent context (fun _ => 0) base hpublished
  rw [hcontext]
  exact canonicalizeMaterializedValues_canonical _ context hconsistent

theorem canonicalHistoryPrefix_invariant
    (entry result : HistoryResolvedPrefix α) (hresult : canonicalHistoryPrefix (some entry) = some result)
    (hconsistent : entry.context.ValuesConsistent) (hcovered : PendingCoveredBy entry.history entry.context) :
    result.context.ValuesConsistent ∧ PendingCoveredBy result.history result.context ∧
      PublishedValues result.context.state ∧
      ∀ base, CanonicalMaterializedValues (completedStartTable result.context.state base) result.context := by
  simp only [canonicalHistoryPrefix] at hresult
  split_ifs at hresult with hguard
  cases hresult
  refine ⟨canonicalizeMaterializedValues_valuesConsistent _ _ hconsistent, ?_, ?_, ?_⟩
  · exact hcovered.of_subset (Finset.Subset.refl _)
  · exact hguard.2.2.2.to_canonicalizedMaterializedValues
  · exact historyCanonicalContext_canonical entry.context hconsistent hguard.2.2.1 hguard.2.2.2

end SphincsSecurity.Concrete.OtsProbeSimulation
