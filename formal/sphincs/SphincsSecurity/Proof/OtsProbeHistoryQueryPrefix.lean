import SphincsSecurity.Proof.OtsProbeHistoryCanonicalBoundary

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local instance] Classical.propDecidable
attribute [local irreducible] sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

theorem runResolvedHistoryCompletion_eq_adaptive_of_probeFree
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (history : List Probe)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe 0) :
    runResolvedHistoryCompletion history computation context fuel = runResolvedHistoryAdaptive computation context fuel history := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value => rfl
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [runResolvedHistoryCompletion_query_bind, runResolvedHistoryAdaptive_query_bind]
      have hnext : (fun output context fuel => runResolvedHistoryCompletion history (next output) context fuel) =
          (fun output context fuel => runResolvedHistoryAdaptive (next output) context fuel history) := by
        funext output context fuel
        exact ih output context fuel (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output)
      cases input with
      | probe coordinate digest => simpa [LazyRevealProbe.IsProbe] using hbound.1
      | uniform n => simp only [historyAdaptiveQueryStep]; rw [hnext]
      | hashOutput => simp only [historyAdaptiveQueryStep]; rw [hnext]
      | ensure coordinate => simp only [historyAdaptiveQueryStep]; rw [hnext]
      | peek coordinate => simp only [historyAdaptiveQueryStep]; rw [hnext]
      | publish coordinate => simp only [historyAdaptiveQueryStep]; rw [hnext]
      | reveal coordinate => simp only [historyAdaptiveQueryStep]; rw [hnext]

theorem historyPrefix_history_eq_of_probeFree
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (history : List Probe) (result : HistoryResolvedPrefix α)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe 0)
    (hresult : some result ∈ support (runResolvedHistoryPrefix computation context fuel history)) :
    result.history = history := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      simp only [runResolvedHistoryPrefix, OracleComp.construct_pure, mem_support_pure_iff, Option.some.injEq] at hresult
      cases hresult
      rfl
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [runResolvedHistoryPrefix_query_bind] at hresult
      cases input with
      | probe coordinate digest => simpa [LazyRevealProbe.IsProbe] using hbound.1
      | uniform n =>
          simp only [historyAdaptiveQueryStep, historyCompletionQueryStep, mem_support_bind_iff] at hresult
          obtain ⟨output, _, htail⟩ := hresult
          exact ih output context fuel (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output) htail
      | hashOutput =>
          simp only [historyAdaptiveQueryStep, historyCompletionQueryStep, mem_support_bind_iff] at hresult
          obtain ⟨output, _, htail⟩ := hresult
          exact ih output context fuel (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output) htail
      | ensure coordinate =>
          exact ih () { context with state := context.state.ensure coordinate } fuel
            (by simpa [LazyRevealProbe.IsProbe] using hbound.2 ()) hresult
      | peek coordinate =>
          exact ih (context.state.values coordinate) context fuel
            (by simpa [LazyRevealProbe.IsProbe] using hbound.2 _) hresult
      | publish coordinate =>
          exact ih () { context with state := context.state.publish coordinate } fuel
            (by simpa [LazyRevealProbe.IsProbe] using hbound.2 ()) hresult
      | reveal coordinate =>
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              simp only [historyAdaptiveQueryStep, historyCompletionQueryStep, OtsSecretIndex.coordinate] at hresult
              cases hknown : context.state.values (.chainStart lay tree leafIdx chainIdx) with
              | some output =>
                  rw [hknown] at hresult
                  dsimp only at hresult
                  split_ifs at hresult with hhit
                  · simp at hresult
                  · exact ih output
                      { context with state := context.state.materialize (.chainStart lay tree leafIdx chainIdx) output }
                      fuel (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output) hresult
              | none =>
                  rw [hknown] at hresult
                  dsimp only at hresult
                  rw [mem_support_bind_iff] at hresult
                  obtain ⟨output, _, htail⟩ := hresult
                  split_ifs at htail with hhit
                  · simp at htail
                  · exact ih output
                      { context with state := context.state.materialize (.chainStart lay tree leafIdx chainIdx) output }
                      fuel (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output) htail
          | position position =>
              simp only [historyAdaptiveQueryStep, historyCompletionQueryStep, mem_support_bind_iff] at hresult
              obtain ⟨option, _, htail⟩ := hresult
              cases option with
              | none => simp at htail
              | some resolved =>
                  exact ih resolved.output
                    { state := context.state.materialize (.position position) resolved.output, values := resolved.values }
                    fuel (by simpa [LazyRevealProbe.IsProbe] using hbound.2 resolved.output) htail

theorem canonicalHistoryPrefix_history_eq_of_probeFree
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (history : List Probe)
    (entry result : HistoryResolvedPrefix α)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe 0)
    (hentry : some entry ∈ support (runResolvedHistoryPrefix computation context fuel history))
    (hcanonical : canonicalHistoryPrefix (some entry) = some result) : result.history = history :=
  (canonicalHistoryPrefix_history_length entry result hcanonical).trans
    (historyPrefix_history_eq_of_probeFree computation context fuel history entry hbound hentry)

theorem evalDist_probeFree_canonicalBoundary_observe_history
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (history : List Probe)
    (observe : List Probe → Option (ResolvedRunResult α) → ProbComp β)
    (hconsistent : context.ValuesConsistent) (hcovered : PendingCoveredBy history context)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe 0) (hbudget : history.length ≤ 2 ^ 126) :
    evalDist (sampledHistoryFilteredRun computation context fuel history >>= fun result =>
      observe history (canonicalHistoryBoundary result)) =
    evalDist (runResolvedHistoryPrefix computation context fuel history >>= fun option =>
      match canonicalHistoryPrefix option with
      | none => observe history none
      | some entry => completeHistoryResolvedPrefix (some entry) >>= observe entry.history) := by
  have hdist := evalDist_sampledHistoryFilteredRun_canonicalBoundary computation context fuel 0 history
    hconsistent hcovered hbound (by simpa using hbudget)
  calc
    _ = evalDist ((sampledHistoryFilteredRun computation context fuel history >>= fun result =>
        pure (canonicalHistoryBoundary result)) >>= observe history) := by simp only [bind_assoc, pure_bind]
    _ = evalDist ((runResolvedHistoryPrefix computation context fuel history >>= fun option =>
        completeHistoryResolvedPrefix (canonicalHistoryPrefix option)) >>= observe history) := by
      rw [evalDist_bind, hdist, ← evalDist_bind]
    _ = _ := by
      rw [bind_assoc]
      apply evalDist_bind_congr
      intro option hsupport
      cases option with
      | none => simp only [canonicalHistoryPrefix, completeHistoryResolvedPrefix, pure_bind]
      | some original =>
          cases hcanonical : canonicalHistoryPrefix (some original) with
          | none => simp only [completeHistoryResolvedPrefix, pure_bind]
          | some entry =>
              dsimp only
              rw [canonicalHistoryPrefix_history_eq_of_probeFree computation context fuel history original entry
                hbound hsupport hcanonical]

theorem evalDist_historyCompletion_canonicalBoundary
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (history : List Probe)
    (hconsistent : context.ValuesConsistent) (hcovered : PendingCoveredBy history context)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe 0) (hbudget : history.length ≤ 2 ^ 126) :
    evalDist (runResolvedHistoryCompletion history computation context fuel >>= fun result => pure (canonicalHistoryBoundary result)) =
      evalDist (runResolvedHistoryPrefix computation context fuel history >>= fun option =>
        completeHistoryResolvedPrefix (canonicalHistoryPrefix option)) := by
  have hspace : 2 ^ 126 < Fintype.card Digest := by norm_num [digestBits]
  have hraw := evalDist_history_filtered_runResolved_eq_completion_of_probeFree history computation context fuel
    hcovered ((hcovered.card_le.trans hbudget).trans_lt hspace) hbound
  have hdist := evalDist_sampledHistoryFilteredRun_canonicalBoundary computation context fuel 0 history
    hconsistent hcovered hbound (by simpa using hbudget)
  change evalDist (sampledHistoryFilteredRun computation context fuel history) = _ at hraw
  rw [evalDist_bind, ← hraw, ← evalDist_bind]
  exact hdist

noncomputable def historyHashQuerySuffix (parameter : PublicParameter) (input : HashInput) (context : DeferredContext) :
    StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)) HashOutput :=
  match (purePlanProbingHashQuery parameter input context.state).action with
  | .ordinary => splitHashQuery (.ordinary input)
  | .resolve coordinate => resolveKnownInput parameter coordinate input

theorem historyHashQuerySuffix_probeFree (parameter : PublicParameter) (input : HashInput) (context : DeferredContext) :
    ProbeFree (historyHashQuerySuffix parameter input context) := by
  unfold historyHashQuerySuffix
  cases (purePlanProbingHashQuery parameter input context.state).action with
  | ordinary => exact splitHashQuery_probeFree _
  | resolve coordinate => exact resolveKnownInput_probeFree parameter coordinate input

noncomputable def runCanonicalHistoryHashPrefix
    (parameter : PublicParameter) (input : HashInput) (context : DeferredContext)
    (history : List Probe) (fuel : Nat) (cache : SplitHashCache) :
    ProbComp (Option (HistoryResolvedPrefix (HashOutput × SplitHashCache))) := do
  let candidate := (purePlanProbingHashQuery parameter input context.state).candidate?
  let entry ← runResolvedHistoryPrefix ((historyHashQuerySuffix parameter input context).run cache)
    (afterCandidateContext context candidate) (if candidate.isSome then fuel else fuel + 1) (history ++ candidate.toList)
  pure (canonicalHistoryPrefix entry)

theorem evalDist_sampledHistoryHash_canonicalPrefix
    (parameter : PublicParameter) (input : HashInput) (context : DeferredContext)
    (history : List Probe) (fuel : Nat) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent)
    (hpublic : ∀ index : OtsSecretIndex, index.coordinate ∈ context.state.revealed → context.state.values index.coordinate ≠ none)
    (hcovered : PendingCoveredBy history context) (hbudget : history.length + 1 ≤ 2 ^ 126) :
    evalDist (sampledHistoryFilteredRun ((probingHashQuery parameter input).run cache) context (fuel + 1) history >>=
      fun result => pure (canonicalHistoryBoundary result)) =
    evalDist (runCanonicalHistoryHashPrefix parameter input context history fuel cache >>= completeHistoryResolvedPrefix) := by
  let candidate := (purePlanProbingHashQuery parameter input context.state).candidate?
  have hspace : 2 ^ 126 < Fintype.card Digest := by norm_num [digestBits]
  have hcard : context.state.pending.card + 1 < Fintype.card Digest :=
    ((Nat.add_le_add_right hcovered.card_le 1).trans hbudget).trans_lt hspace
  have hraw := evalDist_history_filtered_probingHashQuery_observe parameter input context history fuel cache
    (pure (none : Option (ResolvedRunResult (HashOutput × SplitHashCache))))
    (fun result => pure (canonicalHistoryBoundary result)) rfl (by
      intro result _ _ hdoomed
      simp [canonicalHistoryBoundary, hdoomed]) hconsistent hpublic hcovered hcard
  have hlength : (history ++ candidate.toList).length ≤ 2 ^ 126 := by
    have hle : candidate.toList.length ≤ 1 := by cases candidate <;> simp
    simp only [List.length_append]
    omega
  have hcompletion := evalDist_historyCompletion_canonicalBoundary ((historyHashQuerySuffix parameter input context).run cache)
    (afterCandidateContext context candidate) (if candidate.isSome then fuel else fuel + 1) (history ++ candidate.toList)
    (afterCandidateContext_valuesConsistent context candidate hconsistent) (hcovered.afterCandidate candidate)
    (historyHashQuerySuffix_probeFree parameter input context cache) hlength
  calc
    _ = evalDist (runHistoryHashQueryCompletion parameter input context history fuel cache >>=
        fun result => pure (canonicalHistoryBoundary result)) := by
      calc
        _ = _ := ?_
        _ = _ := hraw
      unfold sampledHistoryFilteredRun
      rw [bind_assoc]
      apply evalDist_bind_congr
      intro base _
      split_ifs <;> simp only [pure_bind, canonicalHistoryBoundary]
    _ = _ := by
      unfold runHistoryHashQueryCompletion runCanonicalHistoryHashPrefix
      dsimp only
      rw [bind_assoc]
      simp only [pure_bind]
      exact hcompletion

theorem canonicalHistoryHashPrefix_history
    (parameter : PublicParameter) (input : HashInput) (context : DeferredContext)
    (history : List Probe) (fuel : Nat) (cache : SplitHashCache)
    (result : HistoryResolvedPrefix (HashOutput × SplitHashCache))
    (hresult : some result ∈ support (runCanonicalHistoryHashPrefix parameter input context history fuel cache)) :
    result.history = history ++ (purePlanProbingHashQuery parameter input context.state).candidate?.toList := by
  unfold runCanonicalHistoryHashPrefix at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨option, hoption, hcanonical⟩ := hresult
  simp only [mem_support_pure_iff] at hcanonical
  cases option with
  | none => simp [canonicalHistoryPrefix] at hcanonical
  | some entry =>
      exact canonicalHistoryPrefix_history_eq_of_probeFree _ _ _ _ entry result
        (historyHashQuerySuffix_probeFree parameter input context cache) hoption hcanonical.symm

theorem evalDist_sampledHistoryHash_canonicalPrefix_observe_history
    (parameter : PublicParameter) (input : HashInput) (context : DeferredContext)
    (history : List Probe) (fuel : Nat) (cache : SplitHashCache)
    (observe : List Probe → Option (ResolvedRunResult (HashOutput × SplitHashCache)) → ProbComp β)
    (hconsistent : context.ValuesConsistent)
    (hpublic : ∀ index : OtsSecretIndex, index.coordinate ∈ context.state.revealed → context.state.values index.coordinate ≠ none)
    (hcovered : PendingCoveredBy history context) (hbudget : history.length + 1 ≤ 2 ^ 126) :
    let updated := history ++ (purePlanProbingHashQuery parameter input context.state).candidate?.toList
    evalDist (sampledHistoryFilteredRun ((probingHashQuery parameter input).run cache) context (fuel + 1) history >>=
      fun result => observe updated (canonicalHistoryBoundary result)) =
    evalDist (runCanonicalHistoryHashPrefix parameter input context history fuel cache >>= fun option =>
      match option with
      | none => observe updated none
      | some entry => completeHistoryResolvedPrefix (some entry) >>= observe entry.history) := by
  dsimp only
  let updated := history ++ (purePlanProbingHashQuery parameter input context.state).candidate?.toList
  have hdist := evalDist_sampledHistoryHash_canonicalPrefix parameter input context history fuel cache
    hconsistent hpublic hcovered hbudget
  calc
    _ = evalDist ((sampledHistoryFilteredRun ((probingHashQuery parameter input).run cache) context (fuel + 1) history >>=
        fun result => pure (canonicalHistoryBoundary result)) >>= observe updated) := by simp only [bind_assoc, pure_bind, updated]
    _ = evalDist ((runCanonicalHistoryHashPrefix parameter input context history fuel cache >>=
        completeHistoryResolvedPrefix) >>= observe updated) := by rw [evalDist_bind, hdist, ← evalDist_bind]
    _ = _ := by
      rw [bind_assoc]
      apply evalDist_bind_congr
      intro option hsupport
      cases option with
      | none => simp only [completeHistoryResolvedPrefix, pure_bind, updated]
      | some entry =>
          dsimp only
          rw [canonicalHistoryHashPrefix_history parameter input context history fuel cache entry hsupport]

theorem canonicalHistoryHashPrefix_invariant
    (parameter : PublicParameter) (input : HashInput) (context : DeferredContext)
    (history : List Probe) (fuel : Nat) (cache : SplitHashCache)
    (result : HistoryResolvedPrefix (HashOutput × SplitHashCache))
    (hconsistent : context.ValuesConsistent) (hcovered : PendingCoveredBy history context)
    (hresult : some result ∈ support (runCanonicalHistoryHashPrefix parameter input context history fuel cache)) :
    result.context.ValuesConsistent ∧ PendingCoveredBy result.history result.context ∧ PublishedValues result.context.state ∧
      ∀ base, CanonicalMaterializedValues (completedStartTable result.context.state base) result.context := by
  unfold runCanonicalHistoryHashPrefix at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨option, hoption, hcanonical⟩ := hresult
  simp only [mem_support_pure_iff] at hcanonical
  cases option with
  | none => simp [canonicalHistoryPrefix] at hcanonical
  | some entry =>
      have hafter := afterCandidateContext_valuesConsistent context
        (purePlanProbingHashQuery parameter input context.state).candidate? hconsistent
      have hentry := historyPrefix_invariant_of_mem _ _ _ 0 _ entry (hcovered.afterCandidate _)
        (historyHashQuerySuffix_probeFree parameter input context cache) hoption
      exact canonicalHistoryPrefix_invariant entry result hcanonical.symm
        (valuesConsistent_of_mem_historyPrefix _ _ _ _ entry hafter hoption) hentry.1

theorem evalDist_sampledHistorySign_canonicalPrefix_observe_history
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message)
    (context : DeferredContext) (fuel : Nat) (history : List Probe) (cache : SplitHashCache)
    (observe : List Probe → Option (ResolvedRunResult (Option Signature × SplitHashCache)) → ProbComp β)
    (hconsistent : context.ValuesConsistent) (hcovered : PendingCoveredBy history context) (hbudget : history.length ≤ 2 ^ 126) :
    evalDist (sampledHistoryFilteredRun ((maskedPublishedChronologicalSign parameter root ftsSecret message).run cache)
      context fuel history >>= fun result => observe history (canonicalHistoryBoundary result)) =
    evalDist (runResolvedHistoryPrefix ((maskedPublishedChronologicalSign parameter root ftsSecret message).run cache)
      context fuel history >>= fun option =>
      match canonicalHistoryPrefix option with
      | none => observe history none
      | some entry => completeHistoryResolvedPrefix (some entry) >>= observe entry.history) := by
  have h := evalDist_probeFree_canonicalBoundary_observe_history
    ((maskedPublishedChronologicalSign parameter root ftsSecret message).run cache) context fuel history observe hconsistent hcovered
    (maskedPublishedChronologicalSign_probeFree parameter root ftsSecret message cache) hbudget
  convert h using 1
  congr 1
  apply bind_congr
  intro option
  cases canonicalHistoryPrefix option <;> rfl

noncomputable def nativeCanonicalHistoryNext
    (next : α → OracleComp (LazyRevealProbe.World Coordinate) β) :
    Option (ResolvedRunResult α) → ProbComp (Option (ResolvedRunResult β))
  | none => pure none
  | some result => do
      let final ← runResolvedFromTable result.context result.remaining result.table (next result.value)
      pure (canonicalHistoryBoundary final)

theorem completeHistoryResolvedPrefix_nativeNext
    (entry : HistoryResolvedPrefix α) (next : α → OracleComp (LazyRevealProbe.World Coordinate) β) :
    (completeHistoryResolvedPrefix (some entry) >>= nativeCanonicalHistoryNext next) =
      (sampledHistoryFilteredRun (next entry.value) entry.context entry.remaining entry.history >>=
        fun result => pure (canonicalHistoryBoundary result)) := by
  simp only [completeHistoryResolvedPrefix, completeResolvedHistory, sampledHistoryFilteredRun, bind_assoc]
  apply bind_congr
  intro base
  split_ifs <;> simp only [pure_bind, nativeCanonicalHistoryNext, canonicalHistoryBoundary]

theorem evalDist_probeFree_then_block_canonicalPrefix
    (first : OracleComp (LazyRevealProbe.World Coordinate) α)
    (next : α → OracleComp (LazyRevealProbe.World Coordinate) β)
    (context : DeferredContext) (fuel bound : Nat) (history : List Probe)
    (hconsistent : context.ValuesConsistent) (hcovered : PendingCoveredBy history context)
    (hfirst : first.IsQueryBoundP LazyRevealProbe.IsProbe 0)
    (hnext : ∀ value, (next value).IsQueryBoundP LazyRevealProbe.IsProbe bound)
    (hbudget : history.length + bound ≤ 2 ^ 126) :
    evalDist (sampledHistoryFilteredRun first context fuel history >>= fun result =>
      nativeCanonicalHistoryNext next (canonicalHistoryBoundary result)) =
    evalDist (runResolvedHistoryPrefix first context fuel history >>= fun option =>
      match canonicalHistoryPrefix option with
      | none => pure none
      | some entry => runResolvedHistoryPrefix (next entry.value) entry.context entry.remaining entry.history >>= fun final =>
          completeHistoryResolvedPrefix (canonicalHistoryPrefix final)) := by
  have hfirstBudget : history.length ≤ 2 ^ 126 := by omega
  have hdist := evalDist_probeFree_canonicalBoundary_observe_history first context fuel history
    (fun _ => nativeCanonicalHistoryNext next) hconsistent hcovered hfirst hfirstBudget
  calc
    _ = _ := hdist
    _ = _ := by
      apply evalDist_bind_congr
      intro option hsupport
      cases option with
      | none => simp only [canonicalHistoryPrefix, nativeCanonicalHistoryNext]
      | some original =>
          cases hcanonical : canonicalHistoryPrefix (some original) with
          | none => simp only [nativeCanonicalHistoryNext]
          | some entry =>
              dsimp only
              rw [completeHistoryResolvedPrefix_nativeNext]
              have hhistory := canonicalHistoryPrefix_history_eq_of_probeFree first context fuel history original entry
                hfirst hsupport hcanonical
              have horiginal := historyPrefix_invariant_of_mem first context fuel 0 history original hcovered hfirst hsupport
              have hinvariant := canonicalHistoryPrefix_invariant original entry hcanonical
                (valuesConsistent_of_mem_historyPrefix first context fuel history original hconsistent hsupport) horiginal.1
              exact evalDist_sampledHistoryFilteredRun_canonicalBoundary (next entry.value) entry.context entry.remaining bound
                entry.history hinvariant.1 hinvariant.2.1 (hnext entry.value) (by rwa [hhistory])

end SphincsSecurity.Concrete.OtsProbeSimulation
