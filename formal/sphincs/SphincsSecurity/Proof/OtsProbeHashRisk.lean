import SphincsSecurity.Proof.OtsProbeProbeFreeRisk

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

theorem evalDist_runResolvedFinishIsNone_probeFree_of_core
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput) (value : β)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe 0)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hcard : context.state.pending.card < Fintype.card Digest) :
    evalDist (runResolvedFinishIsNone context fuel table computation) =
      evalDist (finishResolvedRunIsNone (some ⟨context, fuel, value, table⟩)) := by
  by_cases hcomplete : DeferredCompletable table context
  · rw [finishResolvedRunIsNone_some_eq_finalize _ hcomplete]
    exact evalDist_runResolvedFinishIsNone_of_probeFree computation context fuel table hbound
      (valid_of_resolvedCore_completable table context hconsistent hstarts hcomplete) hstarts hcard
  · rw [runResolvedFinishIsNone,
      evalDist_runResolvedFinishIsNone_eq_true_of_not_completable context fuel table computation hconsistent hstarts hcomplete]
    simp [finishResolvedRunIsNone, finishResolvedRun, hcomplete]

theorem evalDist_runResolvedFinishIsNone_bind_of_probeFree
    (left : OracleComp (LazyRevealProbe.World Coordinate) α)
    (next : α → OracleComp (LazyRevealProbe.World Coordinate) β)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hbound : ∀ value, (next value).IsQueryBoundP LazyRevealProbe.IsProbe 0)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hcard : ∀ result, some result ∈ support (runResolvedFromTable context fuel table left) →
      result.context.state.pending.card < Fintype.card Digest) :
    evalDist (runResolvedFinishIsNone context fuel table (left >>= next)) =
      evalDist (runResolvedFinishIsNone context fuel table left) := by
  rw [runResolvedFinishIsNone, runResolvedFromTable_bind, bind_assoc, runResolvedFinishIsNone]
  apply evalDist_bind_congr
  intro option hoption
  cases option with
  | none => simp [finishResolvedRunIsNone, finishResolvedRun]
  | some result =>
      have hcore := resolvedCore_of_mem_runResolvedFromTable left context fuel table result hconsistent hstarts hoption
      exact evalDist_runResolvedFinishIsNone_probeFree_of_core (next result.value)
        result.context result.remaining result.table result.value (hbound result.value)
        hcore.2.1 (hcore.1 ▸ hcore.2.2) (hcard result hoption)

noncomputable def afterCandidateContext (context : DeferredContext) : Option Probe → DeferredContext
  | none => context
  | some candidate => if candidate.coordinate ∈ context.state.revealed then context
      else { context with state := context.state.addPending candidate.coordinate candidate.candidate }

theorem runResolvedFromTable_executeCandidate_positive
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (cache : SplitHashCache) (candidate : Option Probe) :
    runResolvedFromTable context (fuel + 1) table ((executeCandidate? candidate).run cache) =
      pure (some ⟨afterCandidateContext context candidate,
        if candidate.isSome then fuel else fuel + 1, ((), cache), table⟩) := by
  cases candidate with
  | none => simp [executeCandidate?, afterCandidateContext, runResolvedFromTable]
  | some candidate =>
      change runResolvedFromTable context (fuel + 1) table
        (LazyRevealProbe.probeQuery candidate.coordinate candidate.candidate >>= fun _ => pure ((), cache)) = _
      rw [LazyRevealProbe.probeQuery, runResolvedFromTable_probe_query_bind]
      by_cases hrevealed : candidate.coordinate ∈ context.state.revealed <;>
        simp [hrevealed, afterCandidateContext, runResolvedFromTable]

theorem afterCandidateContext_pending_card_le (context : DeferredContext) (candidate : Option Probe) :
    (afterCandidateContext context candidate).state.pending.card ≤ context.state.pending.card + 1 := by
  cases candidate with
  | none => exact Nat.le_succ _
  | some candidate =>
      by_cases hrevealed : candidate.coordinate ∈ context.state.revealed
      · simpa only [afterCandidateContext, hrevealed, ↓reduceIte] using Nat.le_succ context.state.pending.card
      · simpa only [afterCandidateContext, hrevealed, ↓reduceIte, LazyRevealProbe.State.addPending] using
          Finset.card_insert_le (candidate.coordinate, candidate.candidate) context.state.pending

theorem finishResolvedRunIsNone_metadata_eq
    (context : DeferredContext) (table : OtsSecretIndex → HashOutput)
    (fuel remaining : Nat) (value : α) (other : β) :
    finishResolvedRunIsNone (some ⟨context, fuel, value, table⟩) =
      finishResolvedRunIsNone (some ⟨context, remaining, other, table⟩) := by
  by_cases hcomplete : DeferredCompletable table context
  · rw [finishResolvedRunIsNone_some_eq_finalize _ hcomplete,
      finishResolvedRunIsNone_some_eq_finalize _ hcomplete]
  · simp [finishResolvedRunIsNone, finishResolvedRun, hcomplete]

theorem evalDist_probingHashQuery_finished_eq_candidate
    (parameter : PublicParameter) (input : HashInput) (context : DeferredContext)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hcard : context.state.pending.card + 1 < Fintype.card Digest) :
    evalDist (runResolvedFinishIsNone context (fuel + 1) table ((probingHashQuery parameter input).run cache)) =
      evalDist (resolvedFinalizationObserve table
        (afterCandidateContext context (purePlanProbingHashQuery parameter input context.state).candidate?) 0 ()) := by
  let plan := purePlanProbingHashQuery parameter input context.state
  have hdrop := evalDist_runResolvedFinishIsNone_bind_of_probeFree
    ((executeCandidate? plan.candidate?).run cache)
    (fun result : Unit × SplitHashCache =>
      ((match plan.action with
        | .ordinary => splitHashQuery (.ordinary input)
        | .resolve coordinate => resolveKnownInput parameter coordinate input)).run result.2)
    context (fuel + 1) table (by
      intro result
      cases plan.action with
      | ordinary => exact splitHashQuery_probeFree _ result.2
      | resolve coordinate => exact resolveKnownInput_probeFree parameter coordinate input result.2)
    hconsistent hstarts (by
      intro result hresult
      rw [runResolvedFromTable_executeCandidate_positive] at hresult
      simp only [mem_support_pure_iff, Option.some.injEq] at hresult
      subst result
      exact (afterCandidateContext_pending_card_le context plan.candidate?).trans_lt hcard)
  calc
    _ = evalDist (runResolvedFinishIsNone context (fuel + 1) table
        ((probingHashQueryAfterPlan parameter input plan).run cache)) := by
      unfold runResolvedFinishIsNone
      rw [runResolved_probingHashQuery_eq_afterPlan]
    _ = evalDist (runResolvedFinishIsNone context (fuel + 1) table
        ((executeCandidate? plan.candidate?).run cache)) := by
      unfold probingHashQueryAfterPlan executePlannedHashQuery
      rw [StateT.run_bind]
      convert hdrop using 1
      cases plan.action <;> rfl
    _ = _ := by
      rw [runResolvedFinishIsNone, runResolvedFromTable_executeCandidate_positive, pure_bind]
      exact congrArg evalDist (finishResolvedRunIsNone_metadata_eq _ table _ 0 ((), cache) ())

theorem evalDist_finish_canonicalizeResolvedRun_of_core
    (result : ResolvedRunResult α) (hconsistent : result.context.ValuesConsistent)
    (hstarts : StartTableAgrees result.context.state result.table) :
    evalDist (finishResolvedRunIsNone (canonicalizeResolvedRun result.table (some result))) =
      evalDist (finishResolvedRunIsNone (some result)) := by
  by_cases hcomplete : DeferredCompletable result.table result.context
  · exact evalDist_finish_canonicalizeResolvedRun result
      (valid_of_resolvedCore_completable result.table result.context hconsistent hstarts hcomplete) hstarts
  · have hcanonical := doomedResolvedContext_canonicalizeMaterializedValues
      (show DoomedResolvedContext result.table result.context from ⟨hconsistent, hstarts, hcomplete⟩)
    simp [canonicalizeResolvedRun, finishResolvedRunIsNone, finishResolvedRun, hcomplete, hcanonical.2.2]

theorem evalDist_canonicalQuery_finished_eq_raw
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table) :
    evalDist (canonicalChronologicalAdversaryImpl parameter root table ftsSecret input context fuel table cache >>=
      finishResolvedRunIsNone) =
      evalDist (runResolvedFinishIsNone context fuel table
        ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret input).run cache)) := by
  rw [canonicalChronologicalAdversaryImpl_eq_raw_then_canonicalize, bind_assoc, runResolvedFinishIsNone]
  apply evalDist_bind_congr
  intro option hoption
  simp only [pure_bind]
  cases option with
  | none => rfl
  | some result =>
      have hcore := resolvedCore_of_mem_runResolvedFromTable _ context fuel table result hconsistent hstarts hoption
      have heq := evalDist_finish_canonicalizeResolvedRun_of_core result hcore.2.1 (hcore.1 ▸ hcore.2.2)
      simpa only [hcore.1] using heq

theorem evalDist_canonicalHashQuery_finished_eq_candidate
    (parameter : PublicParameter) (root : Digest) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : HashInput) (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hcard : context.state.pending.card + 1 < Fintype.card Digest) :
    evalDist (canonicalChronologicalAdversaryImpl parameter root table ftsSecret (.inl (.inr input))
      context (fuel + 1) table cache >>= finishResolvedRunIsNone) =
      evalDist (resolvedFinalizationObserve table
        (afterCandidateContext context (purePlanProbingHashQuery parameter input context.state).candidate?) 0 ()) := by
  rw [evalDist_canonicalQuery_finished_eq_raw parameter root table ftsSecret (.inl (.inr input))
    context (fuel + 1) cache hconsistent hstarts]
  exact evalDist_probingHashQuery_finished_eq_candidate parameter input context fuel table cache hconsistent hstarts hcard

noncomputable def resolvedContextFailureRisk
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext) : ℝ≥0∞ :=
  Pr[fun verdict => verdict = true | resolvedFinalizationObserve table context 0 ()]

theorem resolvedContextFailureRisk_of_not_completable
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hstop : ¬DeferredCompletable table context) : resolvedContextFailureRisk table context = 1 := by
  simp [resolvedContextFailureRisk, resolvedFinalizationObserve, finishResolvedRunIsNone, finishResolvedRun, hstop]

theorem resolvedContextFailureRisk_le_one (table : OtsSecretIndex → HashOutput) (context : DeferredContext) :
    resolvedContextFailureRisk table context ≤ 1 := probEvent_le_one

theorem canonicalHashQueryRejectionRisk_le_afterCandidate
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (entry : CanonicalQuerySelection) (input : HashInput) (hinput : entry.input = .inl (.inr input))
    (hfuel : 0 < entry.fuel)
    (hconsistent : entry.context.ValuesConsistent) (hstarts : StartTableAgrees entry.context.state entry.table)
    (hcard : entry.context.state.pending.card + 1 < Fintype.card Digest) :
    canonicalQueryRejectionRisk parameter root ftsSecret entry ≤
      resolvedContextFailureRisk entry.table
        (afterCandidateContext entry.context (purePlanProbingHashQuery parameter input entry.context.state).candidate?) := by
  unfold canonicalQueryRejectionRisk
  rw [hinput]
  apply (probEvent_resolvedQueryRejected_le_finished _).trans_eq
  obtain ⟨fuel, heq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hfuel)
  have hdist := evalDist_canonicalHashQuery_finished_eq_candidate parameter root entry.table ftsSecret input
    entry.context fuel entry.cache hconsistent hstarts hcard
  have hprob := congrArg (fun distribution : SPMF Bool => distribution true) hdist
  change Pr[= true | _] = Pr[= true | _] at hprob
  rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput] at hprob
  simpa only [heq, resolvedContextFailureRisk] using hprob

theorem resolvedContextFailureRisk_addPending_hit
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (coordinate : Coordinate) (candidate : Digest) (output : HashOutput)
    (hvalue : resolvedCompletionValue table context coordinate = some output)
    (hhit : truncateHash output = candidate) :
    resolvedContextFailureRisk table { context with state := context.state.addPending coordinate candidate } = 1 := by
  apply resolvedContextFailureRisk_of_not_completable
  rintro ⟨completion, hcompletion⟩
  have heq := hcompletion.eq_resolvedCompletionValue coordinate output hvalue
  have hpending : (coordinate, candidate) ∈ (context.state.addPending coordinate candidate).pending := by
    simp [LazyRevealProbe.State.addPending]
  exact hcompletion.2.2.1 coordinate candidate hpending (by rw [heq, hhit])

theorem resolvedContextFailureRisk_addPending_miss
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (coordinate : Coordinate) (candidate : Digest) (output : HashOutput)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hvalue : resolvedCompletionValue table context coordinate = some output)
    (hmiss : truncateHash output ≠ candidate) :
    resolvedContextFailureRisk table { context with state := context.state.addPending coordinate candidate } =
      resolvedContextFailureRisk table context := by
  by_cases hcomplete : DeferredCompletable table context
  · have hvalid := valid_of_resolvedCore_completable table context hconsistent hstarts hcomplete
    have hview := FinalizationViewEq.refl table context hvalid hstarts
      (fun coordinate output hvalue hhit => hcomplete.not_pendingResolvedHit ⟨coordinate, output, hvalue, hhit⟩)
    have hbase : FinalizationContextEq table (some context) (some context) := ⟨hview, hvalid, hvalid, hcomplete⟩
    have hnext := hbase.addPending_left_of_resolved coordinate candidate output hvalue hmiss
    have heq := evalDist_finishResolvedRunIsNone_eq_of_finalizationContextEq table _ context 0 () hnext
    unfold resolvedContextFailureRisk resolvedFinalizationObserve
    rw [probEvent_eq_eq_probOutput, probEvent_eq_eq_probOutput]
    exact congrArg (fun distribution : SPMF Bool => distribution true) heq
  · have hnext : ¬DeferredCompletable table
        { context with state := context.state.addPending coordinate candidate } := by
      rintro ⟨completion, hcompletion⟩
      exact hcomplete ⟨completion, hcompletion.of_addPending coordinate candidate⟩
    rw [resolvedContextFailureRisk_of_not_completable _ _ hnext,
      resolvedContextFailureRisk_of_not_completable _ _ hcomplete]

theorem resolvedContextFailureRisk_afterCandidate_of_duplicate
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext) (candidate : Probe)
    (hduplicate : (candidate.coordinate, candidate.candidate) ∈ context.state.pending) :
    resolvedContextFailureRisk table (afterCandidateContext context (some candidate)) =
      resolvedContextFailureRisk table context := by
  unfold afterCandidateContext
  dsimp only
  split_ifs with hrevealed
  · rfl
  · simp only [LazyRevealProbe.State.addPending, Finset.insert_eq_of_mem hduplicate]

end SphincsSecurity.Concrete.OtsProbeSimulation
