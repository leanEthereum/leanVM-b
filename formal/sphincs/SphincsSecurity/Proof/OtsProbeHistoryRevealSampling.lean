import SphincsSecurity.Proof.OtsProbeStartHistorySampling

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

noncomputable def startTableAvoidingPending (context : DeferredContext) (index : OtsSecretIndex) : HashOutput :=
  if h : ∃ digest : Digest, digest ∉ context.state.pendingAt index.coordinate then hashOutputOfDigest (Classical.choose h)
  else 0

theorem startTableAvoidingPending_no_missingHit (context : DeferredContext)
    (hcard : context.state.pending.card < Fintype.card Digest) :
    ¬MissingChainStartHit (startTableAvoidingPending context) context := by
  rintro ⟨index, _hmissing, hhit⟩
  have hex := exists_digest_not_mem_pendingAt context.state index.coordinate hcard
  unfold LazyRevealProbe.State.hitAt startTableAvoidingPending at hhit
  rw [dif_pos hex, truncateHash_hashOutputOfDigest] at hhit
  exact Classical.choose_spec hex hhit

theorem chainStartHistoryHit_eq_of_start_values_eq
    (before after : DeferredContext) (history : List Probe) (base : OtsSecretIndex → HashOutput)
    (hvalues : ∀ index : OtsSecretIndex, after.state.values index.coordinate = before.state.values index.coordinate) :
    ChainStartHistoryHit after history base = ChainStartHistoryHit before history base := by
  apply propext
  unfold ChainStartHistoryHit
  apply exists_congr
  rintro ⟨coordinate, digest⟩
  cases coordinate with
  | position position => simp [ChainStartEntryHit]
  | chainStart lay tree leafIdx chainIdx =>
      have heq := hvalues ⟨lay, tree, leafIdx, chainIdx⟩
      change after.state.values (.chainStart lay tree leafIdx chainIdx) =
        before.state.values (.chainStart lay tree leafIdx chainIdx) at heq
      rw [heq]

theorem chainStartHistoryHit_materialize_position
    (context : DeferredContext) (history : List Probe) (base : OtsSecretIndex → HashOutput)
    (position : Position) (output : HashOutput) (values : DeferredStructuralValues) :
    ChainStartHistoryHit { state := context.state.materialize (.position position) output, values := values } history base =
      ChainStartHistoryHit context history base := by
  apply chainStartHistoryHit_eq_of_start_values_eq
  intro index
  simp [LazyRevealProbe.State.materialize, OtsSecretIndex.coordinate]

theorem evalDist_history_filtered_resolve_position_swap
    (context : DeferredContext) (history : List Probe) (position : Position)
    (reference : OtsSecretIndex → HashOutput) (hreference : ¬MissingChainStartHit reference context)
    (hcovered : PendingCoveredBy history context)
    (failure : ProbComp α) (next : (OtsSecretIndex → HashOutput) → Option DeferredResolution → ProbComp α) :
    evalDist (do
      let base ← sampleOtsHashTable
      if ChainStartHistoryHit context history base then failure
      else do
        let resolved ← resolveDeferredReveal (completedStartTable context.state base) position context
        next (completedStartTable context.state base) resolved) =
    evalDist (do
      let resolved ← resolveDeferredReveal reference position context
      let base ← sampleOtsHashTable
      if ChainStartHistoryHit context history base then failure
      else next (completedStartTable context.state base) resolved) := by
  calc
    _ = evalDist (do
        let base ← sampleOtsHashTable
        let resolved ← resolveDeferredReveal reference position context
        if ChainStartHistoryHit context history base then failure
        else next (completedStartTable context.state base) resolved) := by
      apply evalDist_bind_congr
      intro base _hbase
      by_cases hhit : ChainStartHistoryHit context history base
      · simp only [if_pos hhit]
        exact (OracleComp.DeferredSampling.evalDist_bind_const_neverFails _ (by simp) failure).symm
      · simp only [if_neg hhit]
        rw [evalDist_bind, evalDist_bind,
          evalDist_resolveDeferredReveal_eq_of_no_missingChainStartHit _ reference position context
            (no_missingChainStartHit_of_history_clean context history base hcovered hhit) hreference]
    _ = _ := evalDist_bind_bind_swap _ _ _

theorem evalDist_history_filtered_runResolved_revealPosition
    (context : DeferredContext) (history : List Probe) (fuel : Nat) (position : Position)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) α)
    (hcovered : PendingCoveredBy history context) (hcard : context.state.pending.card < Fintype.card Digest) :
    evalDist (do
      let base ← sampleOtsHashTable
      if ChainStartHistoryHit context history base then pure none
      else
        runResolvedFromTable context fuel (completedStartTable context.state base)
          (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) (.reveal (.position position)) >>= next)) =
    evalDist (do
      let resolved ← resolveDeferredReveal (startTableAvoidingPending context) position context
      match resolved with
      | none => pure none
      | some resolved => do
          let after : DeferredContext :=
            { state := context.state.materialize (.position position) resolved.output, values := resolved.values }
          let base ← sampleOtsHashTable
          if ChainStartHistoryHit after history base then pure none
          else runResolvedFromTable after fuel (completedStartTable after.state base) (next resolved.output)) := by
  let continuation : (OtsSecretIndex → HashOutput) → Option DeferredResolution → ProbComp (Option (ResolvedRunResult α)) :=
    fun table option => match option with
      | none => pure none
      | some resolved => runResolvedFromTable
          { state := context.state.materialize (.position position) resolved.output, values := resolved.values }
          fuel table (next resolved.output)
  have hswap := evalDist_history_filtered_resolve_position_swap context history position (startTableAvoidingPending context)
    (startTableAvoidingPending_no_missingHit context hcard) hcovered (pure none) continuation
  simp_rw [runResolvedFromTable_reveal_query_bind]
  change evalDist (do
    let base ← sampleOtsHashTable
    if ChainStartHistoryHit context history base then pure none
    else resolveDeferredReveal (completedStartTable context.state base) position context >>=
      continuation (completedStartTable context.state base)) = _
  rw [hswap]
  apply evalDist_bind_congr
  intro option _hoption
  cases option with
  | none =>
      simp only [continuation, ite_self]
      exact evalDist_sampleOtsHashTable_bind_const (pure none)
  | some resolved =>
      apply evalDist_bind_congr
      intro base _hbase
      simp only [continuation, chainStartHistoryHit_materialize_position, completedStartTable_materialize_position]

theorem evalDist_history_filtered_runResolved_revealStart_missing
    (context : DeferredContext) (history : List Probe) (fuel : Nat) (index : OtsSecretIndex)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) α)
    (hcovered : PendingCoveredBy history context) (hmissing : context.state.values index.coordinate = none) :
    evalDist (do
      let base ← sampleOtsHashTable
      if ChainStartHistoryHit context history base then pure none
      else
        runResolvedFromTable context fuel (completedStartTable context.state base)
          (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) (.reveal index.coordinate) >>= next)) =
    evalDist (do
      let output ← LazyRevealProbe.sampleHashOutput
      if ChainStartHistoryOutputHit history index output then pure none
      else do
        let after : DeferredContext := { context with state := context.state.materialize index.coordinate output }
        let base ← sampleOtsHashTable
        if ChainStartHistoryHit after history base then pure none
        else runResolvedFromTable after fuel (completedStartTable after.state base) (next output)) := by
  let continuation : (OtsSecretIndex → HashOutput) → HashOutput → ProbComp (Option (ResolvedRunResult α)) :=
    fun table output => runResolvedFromTable
      { context with state := context.state.materialize index.coordinate output } fuel table (next output)
  have hread := evalDist_history_filtered_completionTable_read context history index hmissing (pure none) continuation
  calc
    _ = evalDist (do
        let base ← sampleOtsHashTable
        if ChainStartHistoryHit context history base then pure none
        else continuation (completedStartTable context.state base) (base index)) := by
      apply evalDist_bind_congr
      intro base _hbase
      by_cases hhit : ChainStartHistoryHit context history base
      · simp only [if_pos hhit]
      · have hclean := no_missingChainStartHit_of_history_clean context history base hcovered hhit
        have hlookup : completedStartTable context.state base index = base index := by
          simp [completedStartTable, hmissing]
        have hnot : ¬context.state.hitAt index.coordinate (base index) := by
          intro hbad
          exact hclean ⟨index, hmissing, by rwa [hlookup]⟩
        simp only [if_neg hhit, runResolvedFromTable_reveal_query_bind]
        rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
        simp only [OtsSecretIndex.coordinate] at hmissing hnot ⊢
        simp [resolveDeferredChainStart, OtsSecretIndex.coordinate, hmissing, hlookup, hnot, continuation]
    _ = _ := hread

theorem evalDist_history_filtered_runResolved_revealStart_known
    (context : DeferredContext) (history : List Probe) (fuel : Nat) (index : OtsSecretIndex) (output : HashOutput)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) α)
    (hknown : context.state.values index.coordinate = some output) :
    evalDist (do
      let base ← sampleOtsHashTable
      if ChainStartHistoryHit context history base then pure none
      else
        runResolvedFromTable context fuel (completedStartTable context.state base)
          (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) (.reveal index.coordinate) >>= next)) =
    evalDist (if context.state.hitAt index.coordinate output then pure none else do
      let after : DeferredContext := { context with state := context.state.materialize index.coordinate output }
      let base ← sampleOtsHashTable
      if ChainStartHistoryHit after history base then pure none
      else runResolvedFromTable after fuel (completedStartTable after.state base) (next output)) := by
  have hvalues : Function.update context.state.values index.coordinate (some output) = context.state.values := by
    rw [← hknown, Function.update_eq_self]
  have hhistory (base : OtsSecretIndex → HashOutput) :
      ChainStartHistoryHit { context with state := context.state.materialize index.coordinate output } history base =
        ChainStartHistoryHit context history base := by
    apply chainStartHistoryHit_eq_of_start_values_eq
    intro other
    simp only [LazyRevealProbe.State.materialize, hvalues]
  have htable (base : OtsSecretIndex → HashOutput) :
      completedStartTable (context.state.materialize index.coordinate output) base = completedStartTable context.state base := by
    funext other
    simp only [completedStartTable, LazyRevealProbe.State.materialize, hvalues]
  by_cases hhit : context.state.hitAt index.coordinate output
  · rw [if_pos hhit]
    calc
      _ = evalDist (do let _base ← sampleOtsHashTable; pure (none : Option (ResolvedRunResult α))) := by
        apply evalDist_bind_congr
        intro base _hbase
        by_cases hbad : ChainStartHistoryHit context history base
        · simp only [if_pos hbad]
        · simp only [if_neg hbad, runResolvedFromTable_reveal_query_bind]
          rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
          simp only [OtsSecretIndex.coordinate] at hknown hhit ⊢
          simp [resolveDeferredChainStart, OtsSecretIndex.coordinate, hknown, hhit]
      _ = _ := evalDist_sampleOtsHashTable_bind_const _
  · rw [if_neg hhit]
    apply evalDist_bind_congr
    intro base _hbase
    simp only [hhistory, htable]
    by_cases hbad : ChainStartHistoryHit context history base
    · simp only [if_pos hbad]
    · simp only [if_neg hbad, runResolvedFromTable_reveal_query_bind]
      rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
      simp only [OtsSecretIndex.coordinate] at hknown hhit ⊢
      simp [resolveDeferredChainStart, OtsSecretIndex.coordinate, hknown, hhit]

end SphincsSecurity.Concrete.OtsProbeSimulation
