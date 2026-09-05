import SphincsSecurity.Proof.OtsProbeHistoryQueryPrefix

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local instance] Classical.propDecidable
attribute [local irreducible] sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false

theorem runResolvedFromTable_executeCandidate_zero
    (context : DeferredContext) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) (candidate : Option Probe) :
    runResolvedFromTable context 0 table ((executeCandidate? candidate).run cache) =
      if candidate.isSome then pure none else pure (some ⟨context, 0, ((), cache), table⟩) := by
  cases candidate with
  | none => simp [executeCandidate?, runResolvedFromTable]
  | some candidate =>
      change runResolvedFromTable context 0 table
        (LazyRevealProbe.probeQuery candidate.coordinate candidate.candidate >>= fun _ => pure ((), cache)) = _
      rw [LazyRevealProbe.probeQuery, runResolvedFromTable_probe_query_bind]
      rfl

theorem runResolved_probingHashQuery_zero
    (parameter : PublicParameter) (input : HashInput) (context : DeferredContext)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    runResolvedFromTable context 0 table ((probingHashQuery parameter input).run cache) =
      if (purePlanProbingHashQuery parameter input context.state).candidate?.isSome then pure none
      else runResolvedFromTable context 0 table ((historyHashQuerySuffix parameter input context).run cache) := by
  rw [runResolved_probingHashQuery_eq_afterPlan]
  unfold probingHashQueryAfterPlan executePlannedHashQuery
  rw [StateT.run_bind, runResolvedFromTable_bind, runResolvedFromTable_executeCandidate_zero]
  split_ifs <;> simp only [pure_bind]
  rfl

noncomputable def runCanonicalHistoryHashPrefixAtFuel
    (parameter : PublicParameter) (input : HashInput) (context : DeferredContext)
    (history : List Probe) (fuel : Nat) (cache : SplitHashCache) :
    ProbComp (Option (HistoryResolvedPrefix (HashOutput × SplitHashCache))) :=
  match fuel with
  | 0 =>
      if (purePlanProbingHashQuery parameter input context.state).candidate?.isSome then pure none
      else do
        let entry ← runResolvedHistoryPrefix ((historyHashQuerySuffix parameter input context).run cache) context 0 history
        pure (canonicalHistoryPrefix entry)
  | fuel + 1 => runCanonicalHistoryHashPrefix parameter input context history fuel cache

theorem evalDist_sampledHistoryHash_canonicalPrefix_all_fuel
    (parameter : PublicParameter) (input : HashInput) (context : DeferredContext)
    (history : List Probe) (fuel : Nat) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent)
    (hpublic : ∀ index : OtsSecretIndex, index.coordinate ∈ context.state.revealed → context.state.values index.coordinate ≠ none)
    (hcovered : PendingCoveredBy history context) (hbudget : history.length + 1 ≤ 2 ^ 126) :
    evalDist (sampledHistoryFilteredRun ((probingHashQuery parameter input).run cache) context fuel history >>=
      fun result => pure (canonicalHistoryBoundary result)) =
    evalDist (runCanonicalHistoryHashPrefixAtFuel parameter input context history fuel cache >>= completeHistoryResolvedPrefix) := by
  cases fuel with
  | succ fuel =>
      exact evalDist_sampledHistoryHash_canonicalPrefix parameter input context history fuel cache
        hconsistent hpublic hcovered hbudget
  | zero =>
      simp only [runCanonicalHistoryHashPrefixAtFuel]
      by_cases hcandidate : (purePlanProbingHashQuery parameter input context.state).candidate?.isSome = true
      · simp only [if_pos hcandidate, pure_bind, completeHistoryResolvedPrefix]
        unfold sampledHistoryFilteredRun
        simp_rw [runResolved_probingHashQuery_zero, if_pos hcandidate]
        simp only [ite_self, bind_assoc, pure_bind, canonicalHistoryBoundary]
        exact evalDist_sampleOtsHashTable_bind_const (pure none)
      · simp only [if_neg hcandidate, bind_assoc, pure_bind]
        have hrun : sampledHistoryFilteredRun ((probingHashQuery parameter input).run cache) context 0 history =
            sampledHistoryFilteredRun ((historyHashQuerySuffix parameter input context).run cache) context 0 history := by
          unfold sampledHistoryFilteredRun
          apply bind_congr
          intro base
          split_ifs
          · rfl
          · rw [runResolved_probingHashQuery_zero, if_neg hcandidate]
        rw [hrun]
        exact evalDist_sampledHistoryFilteredRun_canonicalBoundary _ context 0 0 history hconsistent hcovered
          (historyHashQuerySuffix_probeFree parameter input context cache) (by omega)

theorem canonicalHistoryHashPrefix_history_all_fuel
    (parameter : PublicParameter) (input : HashInput) (context : DeferredContext)
    (history : List Probe) (fuel : Nat) (cache : SplitHashCache)
    (result : HistoryResolvedPrefix (HashOutput × SplitHashCache))
    (hresult : some result ∈ support (runCanonicalHistoryHashPrefixAtFuel parameter input context history fuel cache)) :
    result.history = history ++ (purePlanProbingHashQuery parameter input context.state).candidate?.toList := by
  cases fuel with
  | succ fuel => exact canonicalHistoryHashPrefix_history parameter input context history fuel cache result hresult
  | zero =>
      simp only [runCanonicalHistoryHashPrefixAtFuel] at hresult
      split_ifs at hresult with hcandidate
      · simp at hresult
      · have hnone : (purePlanProbingHashQuery parameter input context.state).candidate? = none := by
          cases hc : (purePlanProbingHashQuery parameter input context.state).candidate? <;> simp_all
        rw [hnone, Option.toList_none, List.append_nil]
        rw [mem_support_bind_iff] at hresult
        obtain ⟨option, hoption, hcanonical⟩ := hresult
        simp only [mem_support_pure_iff] at hcanonical
        cases option with
        | none => simp [canonicalHistoryPrefix] at hcanonical
        | some entry =>
            exact canonicalHistoryPrefix_history_eq_of_probeFree _ _ _ _ entry result
              (historyHashQuerySuffix_probeFree parameter input context cache) hoption hcanonical.symm

noncomputable def runCanonicalHistoryBlockPrefix
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (history : List Probe) : ProbComp (Option (HistoryResolvedPrefix α)) := do
  let entry ← runResolvedHistoryPrefix computation context fuel history
  pure (canonicalHistoryPrefix entry)

theorem canonicalHistoryBlockPrefix_invariant
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel bound : Nat) (history : List Probe) (result : HistoryResolvedPrefix α)
    (hconsistent : context.ValuesConsistent) (hcovered : PendingCoveredBy history context)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe bound)
    (hresult : some result ∈ support (runCanonicalHistoryBlockPrefix computation context fuel history)) :
    result.context.ValuesConsistent ∧ PendingCoveredBy result.history result.context ∧ PublishedValues result.context.state ∧
      ∀ base, CanonicalMaterializedValues (completedStartTable result.context.state base) result.context := by
  rw [runCanonicalHistoryBlockPrefix, mem_support_bind_iff] at hresult
  obtain ⟨option, hoption, hcanonical⟩ := hresult
  simp only [mem_support_pure_iff] at hcanonical
  cases option with
  | none => simp [canonicalHistoryPrefix] at hcanonical
  | some entry =>
      have hentry := historyPrefix_invariant_of_mem computation context fuel bound history entry hcovered hbound hoption
      exact canonicalHistoryPrefix_invariant entry result hcanonical.symm
        (valuesConsistent_of_mem_historyPrefix computation context fuel history entry hconsistent hoption) hentry.1

theorem canonicalHistoryBlockPrefix_history_of_probeFree
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (history : List Probe) (result : HistoryResolvedPrefix α)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe 0)
    (hresult : some result ∈ support (runCanonicalHistoryBlockPrefix computation context fuel history)) :
    result.history = history := by
  rw [runCanonicalHistoryBlockPrefix, mem_support_bind_iff] at hresult
  obtain ⟨option, hoption, hcanonical⟩ := hresult
  simp only [mem_support_pure_iff] at hcanonical
  cases option with
  | none => simp [canonicalHistoryPrefix] at hcanonical
  | some entry =>
      exact canonicalHistoryPrefix_history_eq_of_probeFree computation context fuel history entry result hbound hoption hcanonical.symm

theorem canonicalHistoryHashPrefix_invariant_all_fuel
    (parameter : PublicParameter) (input : HashInput) (context : DeferredContext)
    (history : List Probe) (fuel : Nat) (cache : SplitHashCache)
    (result : HistoryResolvedPrefix (HashOutput × SplitHashCache))
    (hconsistent : context.ValuesConsistent) (hcovered : PendingCoveredBy history context)
    (hresult : some result ∈ support (runCanonicalHistoryHashPrefixAtFuel parameter input context history fuel cache)) :
    result.context.ValuesConsistent ∧ PendingCoveredBy result.history result.context ∧ PublishedValues result.context.state ∧
      ∀ base, CanonicalMaterializedValues (completedStartTable result.context.state base) result.context := by
  cases fuel with
  | succ fuel => exact canonicalHistoryHashPrefix_invariant parameter input context history fuel cache result hconsistent hcovered hresult
  | zero =>
      simp only [runCanonicalHistoryHashPrefixAtFuel] at hresult
      split_ifs at hresult
      · simp at hresult
      · exact canonicalHistoryBlockPrefix_invariant _ context 0 0 history result hconsistent hcovered
          (historyHashQuerySuffix_probeFree parameter input context cache) hresult

noncomputable def runCanonicalHistoryOuterPrefix
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (query : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) (fuel : Nat) (history : List Probe)
    (cache : SplitHashCache) : ProbComp (Option (HistoryResolvedPrefix ((OracleWorld + SigningSpec).Range query × SplitHashCache))) :=
  match query with
  | .inl (.inl n) => runCanonicalHistoryBlockPrefix ((splitUniformImpl n).run cache) context fuel history
  | .inl (.inr input) => runCanonicalHistoryHashPrefixAtFuel parameter input context history fuel cache
  | .inr message => runCanonicalHistoryBlockPrefix ((maskedPublishedChronologicalSign parameter root ftsSecret message).run cache)
      context fuel history

theorem evalDist_sampledHistoryOuter_canonicalPrefix
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (query : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) (fuel : Nat) (history : List Probe)
    (cache : SplitHashCache) (hconsistent : context.ValuesConsistent)
    (hpublic : ∀ index : OtsSecretIndex, index.coordinate ∈ context.state.revealed → context.state.values index.coordinate ≠ none)
    (hcovered : PendingCoveredBy history context)
    (hbudget : history.length + (if IsOuterHash query then 1 else 0) ≤ 2 ^ 126) :
    evalDist (sampledHistoryFilteredRun ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret query).run cache)
      context fuel history >>= fun result => pure (canonicalHistoryBoundary result)) =
    evalDist (runCanonicalHistoryOuterPrefix parameter root ftsSecret query context fuel history cache >>=
      completeHistoryResolvedPrefix) := by
  cases query with
  | inl query =>
      cases query with
      | inl n =>
          change evalDist (sampledHistoryFilteredRun ((splitUniformImpl n).run cache) context fuel history >>=
            fun result => pure (canonicalHistoryBoundary result)) = _
          unfold runCanonicalHistoryOuterPrefix runCanonicalHistoryBlockPrefix
          rw [bind_assoc]
          simp only [pure_bind]
          exact evalDist_sampledHistoryFilteredRun_canonicalBoundary _ context fuel 0 history hconsistent hcovered
            (splitUniformImpl_probeFree n cache) (by simpa [IsOuterHash] using hbudget)
      | inr input =>
          exact evalDist_sampledHistoryHash_canonicalPrefix_all_fuel parameter input context history fuel cache
            hconsistent hpublic hcovered (by simpa [IsOuterHash] using hbudget)
  | inr message =>
      change evalDist (sampledHistoryFilteredRun ((maskedPublishedChronologicalSign parameter root ftsSecret message).run cache)
        context fuel history >>= fun result => pure (canonicalHistoryBoundary result)) = _
      unfold runCanonicalHistoryOuterPrefix runCanonicalHistoryBlockPrefix
      rw [bind_assoc]
      simp only [pure_bind]
      exact evalDist_sampledHistoryFilteredRun_canonicalBoundary _ context fuel 0 history hconsistent hcovered
        (maskedPublishedChronologicalSign_probeFree parameter root ftsSecret message cache) (by simpa [IsOuterHash] using hbudget)

theorem canonicalHistoryOuterPrefix_history
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (query : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) (fuel : Nat) (history : List Probe)
    (cache : SplitHashCache) (result : HistoryResolvedPrefix ((OracleWorld + SigningSpec).Range query × SplitHashCache))
    (hresult : some result ∈ support (runCanonicalHistoryOuterPrefix parameter root ftsSecret query context fuel history cache)) :
    result.history = history ++ canonicalQueryCandidates parameter query context := by
  cases query with
  | inl query =>
      cases query with
      | inl n =>
          simpa only [canonicalQueryCandidates, List.append_nil] using canonicalHistoryBlockPrefix_history_of_probeFree
            _ context fuel history result (splitUniformImpl_probeFree n cache) hresult
      | inr input => exact canonicalHistoryHashPrefix_history_all_fuel parameter input context history fuel cache result hresult
  | inr message =>
      simpa only [canonicalQueryCandidates, List.append_nil] using canonicalHistoryBlockPrefix_history_of_probeFree
        _ context fuel history result (maskedPublishedChronologicalSign_probeFree parameter root ftsSecret message cache) hresult

theorem canonicalHistoryOuterPrefix_history_length
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (query : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) (fuel : Nat) (history : List Probe)
    (cache : SplitHashCache) (result : HistoryResolvedPrefix ((OracleWorld + SigningSpec).Range query × SplitHashCache))
    (hresult : some result ∈ support (runCanonicalHistoryOuterPrefix parameter root ftsSecret query context fuel history cache)) :
    result.history.length ≤ history.length + (if IsOuterHash query then 1 else 0) := by
  rw [canonicalHistoryOuterPrefix_history parameter root ftsSecret query context fuel history cache result hresult,
    List.length_append]
  apply Nat.add_le_add_left
  cases query with
  | inl query =>
      cases query with
      | inl n => simp [canonicalQueryCandidates, IsOuterHash]
      | inr input =>
          simp only [canonicalQueryCandidates, IsOuterHash, if_true]
          cases (purePlanProbingHashQuery parameter input context.state).candidate? <;> simp
  | inr message => simp [canonicalQueryCandidates, IsOuterHash]

theorem canonicalHistoryOuterPrefix_invariant
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (query : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) (fuel : Nat) (history : List Probe)
    (cache : SplitHashCache) (result : HistoryResolvedPrefix ((OracleWorld + SigningSpec).Range query × SplitHashCache))
    (hconsistent : context.ValuesConsistent) (hcovered : PendingCoveredBy history context)
    (hresult : some result ∈ support (runCanonicalHistoryOuterPrefix parameter root ftsSecret query context fuel history cache)) :
    result.context.ValuesConsistent ∧ PendingCoveredBy result.history result.context ∧ PublishedValues result.context.state ∧
      ∀ base, CanonicalMaterializedValues (completedStartTable result.context.state base) result.context := by
  cases query with
  | inl query =>
      cases query with
      | inl n =>
          exact canonicalHistoryBlockPrefix_invariant _ context fuel 0 history result hconsistent hcovered
            (splitUniformImpl_probeFree n cache) hresult
      | inr input =>
          exact canonicalHistoryHashPrefix_invariant_all_fuel parameter input context history fuel cache result hconsistent hcovered hresult
  | inr message =>
      exact canonicalHistoryBlockPrefix_invariant _ context fuel 0 history result hconsistent hcovered
        (maskedPublishedChronologicalSign_probeFree parameter root ftsSecret message cache) hresult

theorem evalDist_sampledHistoryOuter_canonicalPrefix_observe
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (query : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) (fuel : Nat) (history : List Probe)
    (cache : SplitHashCache)
    (observe : List Probe → Option (ResolvedRunResult ((OracleWorld + SigningSpec).Range query × SplitHashCache)) → ProbComp β)
    (hconsistent : context.ValuesConsistent)
    (hpublic : ∀ index : OtsSecretIndex, index.coordinate ∈ context.state.revealed → context.state.values index.coordinate ≠ none)
    (hcovered : PendingCoveredBy history context)
    (hbudget : history.length + (if IsOuterHash query then 1 else 0) ≤ 2 ^ 126) :
    let updated := history ++ canonicalQueryCandidates parameter query context
    evalDist (sampledHistoryFilteredRun ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret query).run cache)
      context fuel history >>= fun result => observe updated (canonicalHistoryBoundary result)) =
    evalDist (runCanonicalHistoryOuterPrefix parameter root ftsSecret query context fuel history cache >>= fun option =>
      match option with
      | none => observe updated none
      | some entry => completeHistoryResolvedPrefix (some entry) >>= observe entry.history) := by
  dsimp only
  let updated := history ++ canonicalQueryCandidates parameter query context
  have hdist := evalDist_sampledHistoryOuter_canonicalPrefix parameter root ftsSecret query context fuel history cache
    hconsistent hpublic hcovered hbudget
  calc
    _ = evalDist ((sampledHistoryFilteredRun ((maskedChronologicalExpandedAdversaryImpl parameter root ftsSecret query).run cache)
        context fuel history >>= fun result => pure (canonicalHistoryBoundary result)) >>= observe updated) := by
      simp only [bind_assoc, pure_bind, updated]
    _ = evalDist ((runCanonicalHistoryOuterPrefix parameter root ftsSecret query context fuel history cache >>=
        completeHistoryResolvedPrefix) >>= observe updated) := by rw [evalDist_bind, hdist, ← evalDist_bind]
    _ = _ := by
      rw [bind_assoc]
      apply evalDist_bind_congr
      intro option hsupport
      cases option with
      | none => simp only [completeHistoryResolvedPrefix, pure_bind, updated]
      | some entry =>
          dsimp only
          rw [canonicalHistoryOuterPrefix_history parameter root ftsSecret query context fuel history cache entry hsupport]

end SphincsSecurity.Concrete.OtsProbeSimulation
