import SphincsSecurity.Proof.OtsProbeHistoryRevealSampling

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
attribute [local irreducible] sampleOtsHashTable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

noncomputable def historyCompletionQueryStep (history : List Probe)
    (input : (LazyRevealProbe.World Coordinate).Domain)
    (next : (LazyRevealProbe.World Coordinate).Range input → DeferredContext → Nat → ProbComp (Option α))
    (context : DeferredContext) (fuel : Nat) : ProbComp (Option α) :=
  match input with
  | .uniform n => do
      let output ← (liftM (unifSpec.query n) : ProbComp _)
      next output context fuel
  | .hashOutput => do
      let output ← LazyRevealProbe.sampleHashOutput
      next output context fuel
  | .ensure coordinate => next () { context with state := context.state.ensure coordinate } fuel
  | .peek coordinate => next (context.state.values coordinate) context fuel
  | .publish coordinate => next () { context with state := context.state.publish coordinate } fuel
  | .probe _ _ => pure none
  | .reveal (.chainStart lay tree leafIdx chainIdx) =>
      let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
      match context.state.values index.coordinate with
      | some output =>
          if context.state.hitAt index.coordinate output then pure none
          else next output { context with state := context.state.materialize index.coordinate output } fuel
      | none => do
          let output ← LazyRevealProbe.sampleHashOutput
          if ChainStartHistoryOutputHit history index output then pure none
          else next output { context with state := context.state.materialize index.coordinate output } fuel
  | .reveal (.position position) => do
      let option ← resolveDeferredReveal (startTableAvoidingPending context) position context
      match option with
      | none => pure none
      | some resolved =>
          next resolved.output
            { state := context.state.materialize (.position position) resolved.output, values := resolved.values } fuel

noncomputable def runResolvedHistoryCompletion (history : List Probe)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    DeferredContext → Nat → ProbComp (Option (ResolvedRunResult α)) :=
  OracleComp.construct
    (fun value context fuel => do
      let base ← sampleOtsHashTable
      if ChainStartHistoryHit context history base then pure none
      else pure (some ⟨context, fuel, value, completedStartTable context.state base⟩))
    (fun input _ next => historyCompletionQueryStep history input next) computation

theorem runResolvedHistoryCompletion_query_bind
    (history : List Probe) (input : (LazyRevealProbe.World Coordinate).Domain)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) :
    runResolvedHistoryCompletion history (OracleSpec.query input >>= next) context fuel =
      historyCompletionQueryStep history input (fun output => runResolvedHistoryCompletion history (next output)) context fuel := rfl

theorem evalDist_history_filtered_draw_swap
    (context : DeferredContext) (history : List Probe) (draw : ProbComp α)
    (next : (OtsSecretIndex → HashOutput) → α → ProbComp β) (failure : ProbComp β) :
    evalDist (do
      let base ← sampleOtsHashTable
      if ChainStartHistoryHit context history base then failure
      else do let output ← draw; next base output) =
    evalDist (do
      let output ← draw
      let base ← sampleOtsHashTable
      if ChainStartHistoryHit context history base then failure else next base output) := by
  calc
    _ = evalDist (do
        let base ← sampleOtsHashTable
        let output ← draw
        if ChainStartHistoryHit context history base then failure else next base output) := by
      apply evalDist_bind_congr
      intro base _hbase
      by_cases hhit : ChainStartHistoryHit context history base
      · simp only [if_pos hhit]
        exact (OracleComp.DeferredSampling.evalDist_bind_const_neverFails draw (by simp) failure).symm
      · simp only [if_neg hhit]
    _ = _ := evalDist_bind_bind_swap _ _ _

set_option maxRecDepth 1000 in
theorem evalDist_history_filtered_runResolved_eq_completion_of_probeFree
    (history : List Probe) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (hcovered : PendingCoveredBy history context)
    (hcard : context.state.pending.card < Fintype.card Digest)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe 0) :
    evalDist (do
      let base ← sampleOtsHashTable
      if ChainStartHistoryHit context history base then pure none
      else runResolvedFromTable context fuel (completedStartTable context.state base) computation) =
    evalDist (runResolvedHistoryCompletion history computation context fuel) := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      rw [runResolvedHistoryCompletion, OracleComp.construct_pure]
      apply evalDist_bind_congr
      intro base _hbase
      split_ifs
      · rfl
      · simp only [runResolvedFromTable, OracleComp.construct_pure]
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [runResolvedHistoryCompletion_query_bind]
      cases input with
      | probe coordinate digest => simpa [LazyRevealProbe.IsProbe] using hbound.1
      | uniform n =>
          simp only [historyCompletionQueryStep]
          simp_rw [runResolvedFromTable_uniform_query_bind]
          rw [evalDist_history_filtered_draw_swap]
          apply evalDist_bind_congr
          intro output _houtput
          exact ih output context fuel hcovered hcard (hbound.2 output)
      | hashOutput =>
          simp only [historyCompletionQueryStep]
          simp_rw [runResolvedFromTable_hashOutput_query_bind]
          rw [evalDist_history_filtered_draw_swap]
          apply evalDist_bind_congr
          intro output _houtput
          exact ih output context fuel hcovered hcard (hbound.2 output)
      | ensure coordinate =>
          simp only [historyCompletionQueryStep]
          simp_rw [runResolvedFromTable_ensure_query_bind]
          exact ih () { context with state := context.state.ensure coordinate } fuel hcovered hcard (hbound.2 ())
      | peek coordinate =>
          simp only [historyCompletionQueryStep]
          simp_rw [runResolvedFromTable_peek_query_bind]
          exact ih (context.state.values coordinate) context fuel hcovered hcard (hbound.2 _)
      | publish coordinate =>
          simp only [historyCompletionQueryStep]
          simp_rw [runResolvedFromTable_publish_query_bind]
          exact ih () { context with state := context.state.publish coordinate } fuel hcovered hcard (hbound.2 ())
      | reveal coordinate =>
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
              cases hknown : context.state.values index.coordinate with
              | some output =>
                  have hstep := evalDist_history_filtered_runResolved_revealStart_known context history fuel index output next hknown
                  dsimp only [index, OtsSecretIndex.coordinate] at hstep
                  rw [hstep]
                  have hknown' := hknown
                  dsimp only [index, OtsSecretIndex.coordinate] at hknown'
                  simp only [historyCompletionQueryStep, OtsSecretIndex.coordinate, hknown']
                  change _ = evalDist (if context.state.hitAt (.chainStart lay tree leafIdx chainIdx) output then pure none else
                    runResolvedHistoryCompletion history (next output)
                      { context with state := context.state.materialize (.chainStart lay tree leafIdx chainIdx) output } fuel)
                  by_cases hhit : context.state.hitAt (.chainStart lay tree leafIdx chainIdx) output
                  · simp only [if_pos hhit]
                  · simp only [if_neg hhit]
                    exact ih output
                      { context with state := context.state.materialize (.chainStart lay tree leafIdx chainIdx) output }
                      fuel (hcovered.of_subset (Finset.filter_subset _ _))
                      ((Finset.card_le_card (Finset.filter_subset _ _)).trans_lt hcard) (hbound.2 output)
              | none =>
                  have hstep := evalDist_history_filtered_runResolved_revealStart_missing context history fuel index next hcovered hknown
                  dsimp only [index, OtsSecretIndex.coordinate] at hstep
                  rw [hstep]
                  have hknown' := hknown
                  dsimp only [index, OtsSecretIndex.coordinate] at hknown'
                  simp only [historyCompletionQueryStep, OtsSecretIndex.coordinate, hknown']
                  change _ = evalDist (do
                    let output ← LazyRevealProbe.sampleHashOutput
                    if ChainStartHistoryOutputHit history ⟨lay, tree, leafIdx, chainIdx⟩ output then pure none else
                      runResolvedHistoryCompletion history (next output)
                        { context with state := context.state.materialize (.chainStart lay tree leafIdx chainIdx) output } fuel)
                  apply evalDist_bind_congr
                  intro output _houtput
                  by_cases hhit : ChainStartHistoryOutputHit history ⟨lay, tree, leafIdx, chainIdx⟩ output
                  · simp only [if_pos hhit]
                  · simp only [if_neg hhit]
                    exact ih output
                      { context with state := context.state.materialize (.chainStart lay tree leafIdx chainIdx) output }
                      fuel (hcovered.of_subset (Finset.filter_subset _ _))
                      ((Finset.card_le_card (Finset.filter_subset _ _)).trans_lt hcard) (hbound.2 output)
          | position position =>
              simp only [historyCompletionQueryStep]
              rw [evalDist_history_filtered_runResolved_revealPosition context history fuel position next hcovered hcard]
              change _ = evalDist (do
                let option ← resolveDeferredReveal (startTableAvoidingPending context) position context
                match option with
                | none => pure none
                | some resolved =>
                    runResolvedHistoryCompletion history (next resolved.output)
                      { state := context.state.materialize (.position position) resolved.output, values := resolved.values } fuel)
              apply evalDist_bind_congr
              intro option _hoption
              cases option with
              | none => rfl
              | some resolved =>
                  exact ih resolved.output
                    { state := context.state.materialize (.position position) resolved.output, values := resolved.values }
                    fuel (hcovered.of_subset (Finset.filter_subset _ _))
                    ((Finset.card_le_card (Finset.filter_subset _ _)).trans_lt hcard) (hbound.2 resolved.output)

end SphincsSecurity.Concrete.OtsProbeSimulation
