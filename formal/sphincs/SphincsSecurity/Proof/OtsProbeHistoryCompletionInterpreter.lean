import SphincsSecurity.Proof.Prelude
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

end SphincsSecurity.Concrete.OtsProbeSimulation
