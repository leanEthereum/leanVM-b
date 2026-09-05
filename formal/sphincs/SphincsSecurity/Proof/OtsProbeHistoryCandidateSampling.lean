import SphincsSecurity.Proof.OtsProbeHistoryCompletionInterpreter

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

theorem afterCandidateContext_values (context : DeferredContext) (candidate : Option Probe) :
    (afterCandidateContext context candidate).state.values = context.state.values := by
  cases candidate with
  | none => rfl
  | some candidate =>
      unfold afterCandidateContext
      dsimp only
      split_ifs <;> rfl

theorem completedStartTable_afterCandidateContext
    (context : DeferredContext) (candidate : Option Probe) (base : OtsSecretIndex → HashOutput) :
    completedStartTable (afterCandidateContext context candidate).state base =
      completedStartTable context.state base := by
  funext index
  simp only [completedStartTable, afterCandidateContext_values]

theorem PendingCoveredBy.afterCandidate
    {history : List Probe} {context : DeferredContext} (hcovered : PendingCoveredBy history context)
    (candidate : Option Probe) :
    PendingCoveredBy (history ++ candidate.toList) (afterCandidateContext context candidate) := by
  cases candidate with
  | none => simpa only [Option.toList_none, List.append_nil, afterCandidateContext] using hcovered
  | some candidate =>
      unfold afterCandidateContext
      dsimp only
      split_ifs
      · exact hcovered.mono_candidates (List.sublist_append_left _ _)
      · exact hcovered.addPending_append history context candidate

theorem chainStartHistoryHit_afterCandidate_append_iff
    (context : DeferredContext) (history : List Probe) (candidate : Option Probe)
    (base : OtsSecretIndex → HashOutput) :
    ChainStartHistoryHit (afterCandidateContext context candidate) (history ++ candidate.toList) base ↔
      ChainStartHistoryHit context history base ∨
        ∃ probe ∈ candidate.toList, context.state.values probe.coordinate = none ∧
          ChainStartEntryHit base (probe.coordinate, probe.candidate) := by
  unfold ChainStartHistoryHit
  simp only [afterCandidateContext_values, List.mem_append, or_and_right, exists_or]

theorem revealed_chainStart_known_of_canonical
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hcanonical : CanonicalMaterializedValues table context) (index : OtsSecretIndex)
    (hrevealed : index.coordinate ∈ context.state.revealed) :
    context.state.values index.coordinate ≠ none := by
  rw [hcanonical]
  simp only [publicMaterializedValues, if_pos hrevealed]
  simp [resolvedCompletionValue, OtsSecretIndex.coordinate]

theorem not_completable_of_new_chainStartHistoryHit
    (context : DeferredContext) (history : List Probe) (candidate : Option Probe)
    (base : OtsSecretIndex → HashOutput)
    (hpublic : ∀ index : OtsSecretIndex, index.coordinate ∈ context.state.revealed →
      context.state.values index.coordinate ≠ none)
    (hprior : ¬ChainStartHistoryHit context history base)
    (hnew : ChainStartHistoryHit (afterCandidateContext context candidate) (history ++ candidate.toList) base) :
    ¬DeferredCompletable (completedStartTable context.state base) (afterCandidateContext context candidate) := by
  obtain ⟨probe, hprobe, hmissing, hhit⟩ :=
    (chainStartHistoryHit_afterCandidate_append_iff context history candidate base).mp hnew |>.resolve_left hprior
  have hcandidate : candidate = some probe := by simpa only [Option.mem_toList] using hprobe
  subst candidate
  rcases probe with ⟨coordinate, digest⟩
  cases coordinate with
  | position position => simp [ChainStartEntryHit] at hhit
  | chainStart lay tree leafIdx chainIdx =>
      let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
      have hhidden : Coordinate.chainStart lay tree leafIdx chainIdx ∉ context.state.revealed :=
        fun h => hpublic index h hmissing
      simp only [afterCandidateContext, if_neg hhidden]
      intro hcomplete
      apply hcomplete.not_hitAt_chainStart index
      unfold LazyRevealProbe.State.hitAt
      rw [LazyRevealProbe.State.mem_pendingAt_iff]
      have hvalue : completedStartTable context.state base index = base index := by
        change context.state.values index.coordinate = none at hmissing
        simp only [completedStartTable, hmissing, Option.getD_none]
      rw [hvalue]
      have hdigest : truncateHash (base index) = digest := hhit
      rw [hdigest]
      simp [LazyRevealProbe.State.addPending, index, OtsSecretIndex.coordinate]

theorem evalDist_history_filtered_afterCandidate_append
    (context : DeferredContext) (history : List Probe) (candidate : Option Probe)
    (hpublic : ∀ index : OtsSecretIndex, index.coordinate ∈ context.state.revealed →
      context.state.values index.coordinate ≠ none)
    (failure : ProbComp α) (next : (OtsSecretIndex → HashOutput) → ProbComp α)
    (hstop : ∀ base, ¬DeferredCompletable (completedStartTable context.state base) (afterCandidateContext context candidate) →
      evalDist (next (completedStartTable context.state base)) = evalDist failure) :
    evalDist (do
      let base ← sampleOtsHashTable
      if ChainStartHistoryHit context history base then failure
      else next (completedStartTable context.state base)) =
    evalDist (do
      let base ← sampleOtsHashTable
      if ChainStartHistoryHit (afterCandidateContext context candidate) (history ++ candidate.toList) base then failure
      else next (completedStartTable (afterCandidateContext context candidate).state base)) := by
  apply evalDist_bind_congr
  intro base _hbase
  rw [completedStartTable_afterCandidateContext]
  by_cases hprior : ChainStartHistoryHit context history base
  · have hnew := (chainStartHistoryHit_afterCandidate_append_iff context history candidate base).mpr (Or.inl hprior)
    simp only [if_pos hprior, if_pos hnew]
  · simp only [if_neg hprior]
    by_cases hnew : ChainStartHistoryHit (afterCandidateContext context candidate) (history ++ candidate.toList) base
    · rw [if_pos hnew]
      exact hstop base (not_completable_of_new_chainStartHistoryHit context history candidate base hpublic hprior hnew)
    · rw [if_neg hnew]

theorem evalDist_runResolved_observe_of_not_completable
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (failure : ProbComp β) (observe : Option (ResolvedRunResult α) → ProbComp β)
    (hnone : evalDist (observe none) = evalDist failure)
    (hobserve : ∀ result, result.context.ValuesConsistent → StartTableAgrees result.context.state result.table →
      ¬DeferredCompletable result.table result.context →
      evalDist (observe (some result)) = evalDist failure)
    (hconsistent : context.ValuesConsistent) (hstarts : StartTableAgrees context.state table)
    (hdoomed : ¬DeferredCompletable table context) :
    evalDist (runResolvedFromTable context fuel table computation >>= observe) = evalDist failure := by
  calc
    _ = evalDist (runResolvedFromTable context fuel table computation >>= fun _ => failure) := by
      apply evalDist_bind_congr
      intro option hoption
      cases option with
      | none => exact hnone
      | some result =>
          have hcore := resolvedCore_of_mem_runResolvedFromTable computation context fuel table result
            hconsistent hstarts hoption
          apply hobserve result hcore.2.1 (hcore.1 ▸ hcore.2.2)
          rw [hcore.1]
          exact not_deferredCompletable_of_mem_runResolvedFromTable computation context fuel table result
            hconsistent hstarts hoption hdoomed
    _ = _ := OracleComp.DeferredSampling.evalDist_bind_const_neverFails _ (by simp [runResolvedFromTable]) failure

theorem evalDist_history_filtered_executeCandidate_probeFree
    (context : DeferredContext) (history : List Probe) (candidate : Option Probe)
    (fuel : Nat) (cache : SplitHashCache)
    (next : Unit × SplitHashCache → OracleComp (LazyRevealProbe.World Coordinate) α)
    (failure : ProbComp β) (observe : Option (ResolvedRunResult α) → ProbComp β)
    (hnone : evalDist (observe none) = evalDist failure)
    (hobserve : ∀ result, result.context.ValuesConsistent → StartTableAgrees result.context.state result.table →
      ¬DeferredCompletable result.table result.context →
      evalDist (observe (some result)) = evalDist failure)
    (hconsistent : context.ValuesConsistent)
    (hpublic : ∀ index : OtsSecretIndex, index.coordinate ∈ context.state.revealed →
      context.state.values index.coordinate ≠ none)
    (hcovered : PendingCoveredBy history context)
    (hcard : context.state.pending.card + 1 < Fintype.card Digest)
    (hbound : (next ((), cache)).IsQueryBoundP LazyRevealProbe.IsProbe 0) :
    evalDist (do
      let base ← sampleOtsHashTable
      if ChainStartHistoryHit context history base then failure
      else
        runResolvedFromTable context (fuel + 1) (completedStartTable context.state base)
          (((executeCandidate? candidate).run cache) >>= next) >>= observe) =
    evalDist (runResolvedHistoryCompletion (history ++ candidate.toList) (next ((), cache))
      (afterCandidateContext context candidate) (if candidate.isSome then fuel else fuel + 1) >>= observe) := by
  let after := afterCandidateContext context candidate
  let remaining := if candidate.isSome then fuel else fuel + 1
  let continuation := fun table => runResolvedFromTable after remaining table (next ((), cache)) >>= observe
  have hafter := afterCandidateContext_valuesConsistent context candidate hconsistent
  have hstop : ∀ base, ¬DeferredCompletable (completedStartTable context.state base) after →
      evalDist (continuation (completedStartTable context.state base)) = evalDist failure := by
    intro base hdoomed
    exact evalDist_runResolved_observe_of_not_completable after remaining _ _ failure observe hnone hobserve hafter
      (afterCandidateContext_startTableAgrees _ context candidate (startTableAgrees_completedStartTable context.state base))
      hdoomed
  have hsample := evalDist_history_filtered_runResolved_eq_completion_of_probeFree
    (history ++ candidate.toList) (next ((), cache)) after remaining
    (hcovered.afterCandidate candidate) ((afterCandidateContext_pending_card_le context candidate).trans_lt hcard) hbound
  calc
    _ = evalDist (do
        let base ← sampleOtsHashTable
        if ChainStartHistoryHit context history base then failure
        else continuation (completedStartTable context.state base)) := by
      apply evalDist_bind_congr
      intro base _hbase
      split_ifs
      · rfl
      · simp only [runResolvedFromTable_bind, runResolvedFromTable_executeCandidate_positive, pure_bind]
        rfl
    _ = evalDist (do
        let base ← sampleOtsHashTable
        if ChainStartHistoryHit after (history ++ candidate.toList) base then failure
        else continuation (completedStartTable after.state base)) :=
      evalDist_history_filtered_afterCandidate_append context history candidate hpublic failure continuation hstop
    _ = evalDist ((do
        let base ← sampleOtsHashTable
        if ChainStartHistoryHit after (history ++ candidate.toList) base then pure none
        else runResolvedFromTable after remaining (completedStartTable after.state base) (next ((), cache))) >>= observe) := by
      rw [bind_assoc]
      apply evalDist_bind_congr
      intro base _hbase
      split_ifs
      · simpa only [pure_bind] using hnone.symm
      · rfl
    _ = _ := by rw [evalDist_bind, hsample, ← evalDist_bind]

noncomputable def runHistoryHashQueryCompletion
    (parameter : PublicParameter) (input : HashInput) (context : DeferredContext)
    (history : List Probe) (fuel : Nat) (cache : SplitHashCache) :
    ProbComp (Option (ResolvedRunResult (HashOutput × SplitHashCache))) :=
  let plan := purePlanProbingHashQuery parameter input context.state
  runResolvedHistoryCompletion (history ++ plan.candidate?.toList)
    ((match plan.action with
      | .ordinary => splitHashQuery (.ordinary input)
      | .resolve coordinate => resolveKnownInput parameter coordinate input).run cache)
    (afterCandidateContext context plan.candidate?) (if plan.candidate?.isSome then fuel else fuel + 1)

theorem evalDist_history_filtered_probingHashQuery_observe
    (parameter : PublicParameter) (input : HashInput) (context : DeferredContext)
    (history : List Probe) (fuel : Nat) (cache : SplitHashCache)
    (failure : ProbComp α) (observe : Option (ResolvedRunResult (HashOutput × SplitHashCache)) → ProbComp α)
    (hnone : evalDist (observe none) = evalDist failure)
    (hobserve : ∀ result, result.context.ValuesConsistent → StartTableAgrees result.context.state result.table →
      ¬DeferredCompletable result.table result.context →
      evalDist (observe (some result)) = evalDist failure)
    (hconsistent : context.ValuesConsistent)
    (hpublic : ∀ index : OtsSecretIndex, index.coordinate ∈ context.state.revealed →
      context.state.values index.coordinate ≠ none)
    (hcovered : PendingCoveredBy history context)
    (hcard : context.state.pending.card + 1 < Fintype.card Digest) :
    evalDist (do
      let base ← sampleOtsHashTable
      if ChainStartHistoryHit context history base then failure
      else
        runResolvedFromTable context (fuel + 1) (completedStartTable context.state base)
          ((probingHashQuery parameter input).run cache) >>= observe) =
    evalDist (runHistoryHashQueryCompletion parameter input context history fuel cache >>= observe) := by
  let plan := purePlanProbingHashQuery parameter input context.state
  let next := fun result : Unit × SplitHashCache =>
    (match plan.action with
      | .ordinary => splitHashQuery (.ordinary input)
      | .resolve coordinate => resolveKnownInput parameter coordinate input).run result.2
  have hbound : (next ((), cache)).IsQueryBoundP LazyRevealProbe.IsProbe 0 := by
    dsimp only [next]
    cases plan.action with
    | ordinary => exact splitHashQuery_probeFree _ cache
    | resolve coordinate => exact resolveKnownInput_probeFree parameter coordinate input cache
  calc
    _ = evalDist (do
        let base ← sampleOtsHashTable
        if ChainStartHistoryHit context history base then failure
        else
          runResolvedFromTable context (fuel + 1) (completedStartTable context.state base)
            (((executeCandidate? plan.candidate?).run cache) >>= next) >>= observe) := by
      apply evalDist_bind_congr
      intro base _hbase
      split_ifs
      · rfl
      · rw [runResolved_probingHashQuery_eq_afterPlan]
        unfold probingHashQueryAfterPlan executePlannedHashQuery
        rw [StateT.run_bind]
        rfl
    _ = _ := evalDist_history_filtered_executeCandidate_probeFree context history plan.candidate? fuel cache next
      failure observe hnone hobserve hconsistent hpublic hcovered hcard hbound

theorem evalDist_history_filtered_canonicalHashQuery_observe
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : HashInput) (context : DeferredContext) (history : List Probe) (fuel : Nat) (cache : SplitHashCache)
    (failure : ProbComp α) (observe : Option (ResolvedRunResult (HashOutput × SplitHashCache)) → ProbComp α)
    (hnone : evalDist (observe none) = evalDist failure)
    (hobserve : ∀ result, result.context.ValuesConsistent → StartTableAgrees result.context.state result.table →
      ¬DeferredCompletable result.table result.context →
      evalDist (observe (some result)) = evalDist failure)
    (hconsistent : context.ValuesConsistent)
    (hpublic : ∀ index : OtsSecretIndex, index.coordinate ∈ context.state.revealed →
      context.state.values index.coordinate ≠ none)
    (hcovered : PendingCoveredBy history context)
    (hcard : context.state.pending.card + 1 < Fintype.card Digest) :
    evalDist (do
      let base ← sampleOtsHashTable
      let table := completedStartTable context.state base
      if ChainStartHistoryHit context history base then failure
      else
        canonicalChronologicalAdversaryImpl parameter root table ftsSecret (.inl (.inr input))
          context (fuel + 1) table cache >>= observe) =
    evalDist (runHistoryHashQueryCompletion parameter input context history fuel cache >>= fun option =>
      match option with
      | none => observe none
      | some result => observe (canonicalizeResolvedRun result.table (some result))) := by
  let rawObserve := fun option : Option (ResolvedRunResult (HashOutput × SplitHashCache)) =>
    match option with
    | none => observe none
    | some result => observe (canonicalizeResolvedRun result.table (some result))
  have hraw : ∀ result, result.context.ValuesConsistent → StartTableAgrees result.context.state result.table →
      ¬DeferredCompletable result.table result.context →
      evalDist (rawObserve (some result)) = evalDist failure := by
    intro result hvalues hstarts hdoomed
    have hcanonical := doomedResolvedContext_canonicalizeMaterializedValues ⟨hvalues, hstarts, hdoomed⟩
    exact hobserve { result with context := canonicalizeMaterializedValues result.table result.context }
      hcanonical.1 hcanonical.2.1 hcanonical.2.2
  calc
    _ = evalDist (do
        let base ← sampleOtsHashTable
        if ChainStartHistoryHit context history base then failure
        else
          runResolvedFromTable context (fuel + 1) (completedStartTable context.state base)
            ((probingHashQuery parameter input).run cache) >>= rawObserve) := by
      apply evalDist_bind_congr
      intro base _hbase
      dsimp only
      split_ifs
      · rfl
      · rw [canonicalChronologicalAdversaryImpl_eq_raw_then_canonicalize, bind_assoc]
        apply evalDist_bind_congr
        intro option hoption
        simp only [pure_bind]
        cases option with
        | none => rfl
        | some result =>
            have hcore := resolvedCore_of_mem_runResolvedFromTable _ context (fuel + 1) _ result hconsistent
              (startTableAgrees_completedStartTable context.state base) hoption
            simp only [rawObserve, hcore.1]
    _ = _ := evalDist_history_filtered_probingHashQuery_observe parameter input context history fuel cache
      failure rawObserve hnone hraw hconsistent hpublic hcovered hcard

theorem evalDist_history_filtered_canonicalHashQuery_finished
    (parameter : PublicParameter) (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (input : HashInput) (context : DeferredContext) (history : List Probe) (fuel : Nat) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent)
    (hpublic : ∀ index : OtsSecretIndex, index.coordinate ∈ context.state.revealed →
      context.state.values index.coordinate ≠ none)
    (hcovered : PendingCoveredBy history context)
    (hcard : context.state.pending.card + 1 < Fintype.card Digest) :
    evalDist (do
      let base ← sampleOtsHashTable
      let table := completedStartTable context.state base
      if ChainStartHistoryHit context history base then pure true
      else
        canonicalChronologicalAdversaryImpl parameter root table ftsSecret (.inl (.inr input))
          context (fuel + 1) table cache >>= finishResolvedRunIsNone) =
    evalDist (runHistoryHashQueryCompletion parameter input context history fuel cache >>= fun option =>
      match option with
      | none => finishResolvedRunIsNone (none : Option (ResolvedRunResult (HashOutput × SplitHashCache)))
      | some result => finishResolvedRunIsNone (canonicalizeResolvedRun result.table (some result))) := by
  apply evalDist_history_filtered_canonicalHashQuery_observe parameter root ftsSecret input context history fuel cache
    (pure true) finishResolvedRunIsNone
  · rfl
  · intro result _hvalues _hstarts hdoomed
    simp [finishResolvedRunIsNone, finishResolvedRun, hdoomed]
  · exact hconsistent
  · exact hpublic
  · exact hcovered
  · exact hcard

end SphincsSecurity.Concrete.OtsProbeSimulation
