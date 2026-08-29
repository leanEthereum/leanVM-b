import SphincsSecurity.Proof.OtsProbeResolvedCleanTerminal

/-! Direct structural sampling with resolved contexts, projecting exactly to the clean interpreter. -/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def directDeferredValues (state : LazyRevealProbe.State Coordinate) :
    DeferredStructuralValues := fun position => state.values (.position position)

def directDeferredContext (state : LazyRevealProbe.State Coordinate) : DeferredContext :=
  { state := state, values := directDeferredValues state }

noncomputable def runDirectResolvedFromTable
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    ProbComp (Option (ResolvedRunResult α)) :=
  OracleComp.construct
    (C := fun _ : OracleComp (LazyRevealProbe.World Coordinate) α =>
      DeferredContext → Nat → (OtsSecretIndex → HashOutput) →
        ProbComp (Option (ResolvedRunResult α)))
    (fun value context remaining table =>
      pure (some ⟨context, remaining, value, table⟩))
    (fun input _next recursivelyRun context fuel table =>
      match input with
      | .uniform n => do
          let output ← liftM (unifSpec.query n)
          recursivelyRun output context fuel table
      | .hashOutput => do
          let output ← LazyRevealProbe.sampleHashOutput
          recursivelyRun output context fuel table
      | .ensure coordinate =>
          recursivelyRun ()
            { context with state := context.state.ensure coordinate } fuel table
      | .probe coordinate candidate =>
          match fuel with
          | 0 => pure none
          | remaining + 1 =>
              if coordinate ∈ context.state.revealed then
                recursivelyRun () context remaining table
              else
                recursivelyRun ()
                  { context with
                    state := context.state.addPending coordinate candidate }
                  remaining table
      | .peek coordinate =>
          recursivelyRun (context.state.values coordinate) context fuel table
      | .publish coordinate =>
          recursivelyRun ()
            { context with state := context.state.publish coordinate } fuel table
      | .reveal coordinate =>
          match context.state.values coordinate with
          | some output => recursivelyRun output context fuel table
          | none =>
              match coordinate with
              | .chainStart lay tree leafIdx chainIdx =>
                  let output := table ⟨lay, tree, leafIdx, chainIdx⟩
                  if context.state.hitAt coordinate output then
                    pure none
                  else
                    recursivelyRun output
                      { state := context.state.materialize coordinate output
                        values := context.values }
                      fuel table
              | .position position => do
                  let output ← LazyRevealProbe.sampleHashOutput
                  if context.state.hitAt coordinate output then
                    pure none
                  else
                    recursivelyRun output
                      { state := context.state.materialize coordinate output
                        values := context.values.install position output }
                      fuel table)
    computation context fuel table

theorem runDirectResolvedFromTable_uniform_query_bind
    (context : DeferredContext) (fuel n : Nat)
    (table : OtsSecretIndex → HashOutput)
    (next : Fin (n + 1) → OracleComp (LazyRevealProbe.World Coordinate) α) :
    runDirectResolvedFromTable context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.uniform n)) :
            OracleComp (LazyRevealProbe.World Coordinate) (Fin (n + 1))) >>= next) = (do
      let output ← liftM (unifSpec.query n)
      runDirectResolvedFromTable context fuel table (next output)) := by
  rfl

theorem runDirectResolvedFromTable_hashOutput_query_bind
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) α) :
    runDirectResolvedFromTable context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          .hashOutput) :
            OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next) = (do
      let output ← LazyRevealProbe.sampleHashOutput
      runDirectResolvedFromTable context fuel table (next output)) := by
  rfl

theorem runDirectResolvedFromTable_ensure_query_bind
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) α) :
    runDirectResolvedFromTable context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.ensure coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      runDirectResolvedFromTable
        { context with state := context.state.ensure coordinate }
        fuel table (next ()) := by
  rfl

theorem runDirectResolvedFromTable_probe_query_bind
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (candidate : Digest)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) α) :
    runDirectResolvedFromTable context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.probe coordinate candidate)) :
            OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      match fuel with
      | 0 => pure none
      | remaining + 1 =>
          if coordinate ∈ context.state.revealed then
            runDirectResolvedFromTable context remaining table (next ())
          else
            runDirectResolvedFromTable
              { context with
                state := context.state.addPending coordinate candidate }
              remaining table (next ()) := by
  rfl

theorem runDirectResolvedFromTable_peek_query_bind
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (next : Option HashOutput →
      OracleComp (LazyRevealProbe.World Coordinate) α) :
    runDirectResolvedFromTable context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.peek coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) (Option HashOutput)) >>= next) =
      runDirectResolvedFromTable context fuel table
        (next (context.state.values coordinate)) := by
  rfl

theorem runDirectResolvedFromTable_publish_query_bind
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) α) :
    runDirectResolvedFromTable context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.publish coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      runDirectResolvedFromTable
        { context with state := context.state.publish coordinate }
        fuel table (next ()) := by
  rfl

theorem runDirectResolvedFromTable_reveal_query_bind
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) α) :
    runDirectResolvedFromTable context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.reveal coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next) = (do
      match context.state.values coordinate with
      | some output => runDirectResolvedFromTable context fuel table (next output)
      | none =>
          match coordinate with
          | .chainStart lay tree leafIdx chainIdx =>
              let output := table ⟨lay, tree, leafIdx, chainIdx⟩
              if context.state.hitAt coordinate output then
                pure none
              else
                runDirectResolvedFromTable
                  { state := context.state.materialize coordinate output
                    values := context.values }
                  fuel table (next output)
          | .position position => do
              let output ← LazyRevealProbe.sampleHashOutput
              if context.state.hitAt coordinate output then
                pure none
              else
                runDirectResolvedFromTable
                  { state := context.state.materialize coordinate output
                    values := context.values.install position output }
                  fuel table (next output)) := by
  cases coordinate <;> rfl

theorem directDeferredValues_ensure
    (state : LazyRevealProbe.State Coordinate) (coordinate : Coordinate) :
    directDeferredValues (state.ensure coordinate) = directDeferredValues state := rfl

theorem directDeferredValues_addPending
    (state : LazyRevealProbe.State Coordinate) (coordinate : Coordinate)
    (candidate : Digest) :
    directDeferredValues (state.addPending coordinate candidate) =
      directDeferredValues state := rfl

theorem directDeferredValues_publish
    (state : LazyRevealProbe.State Coordinate) (coordinate : Coordinate) :
    directDeferredValues (state.publish coordinate) = directDeferredValues state := rfl

theorem directDeferredValues_materialize_chainStart
    (state : LazyRevealProbe.State Coordinate) (index : OtsSecretIndex)
    (output : HashOutput) :
    directDeferredValues (state.materialize index.coordinate output) =
      directDeferredValues state := by
  funext position
  simp [directDeferredValues, LazyRevealProbe.State.materialize,
    OtsSecretIndex.coordinate]

theorem directDeferredValues_materialize_position
    (state : LazyRevealProbe.State Coordinate) (position : Position)
    (output : HashOutput) :
    directDeferredValues (state.materialize (.position position) output) =
      (directDeferredValues state).install position output := by
  funext other
  by_cases heq : other = position
  · subst other
    simp [directDeferredValues, DeferredStructuralValues.install,
      LazyRevealProbe.State.materialize]
  · simp [directDeferredValues, DeferredStructuralValues.install,
      LazyRevealProbe.State.materialize, heq]

set_option maxRecDepth 100000 in
theorem map_projectResolvedRunResult_runDirect_eq_runClean
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) :
    projectResolvedRunResult <$>
        runDirectResolvedFromTable (directDeferredContext state) fuel table computation =
      runCleanFromTable state fuel table computation := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure value => simp [runDirectResolvedFromTable, runCleanFromTable,
      projectResolvedRunResult, directDeferredContext]
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runDirectResolvedFromTable_uniform_query_bind,
            runCleanFromTable_uniform_query_bind, map_bind]
          apply bind_congr
          intro output
          exact ih output state fuel
      | hashOutput =>
          rw [runDirectResolvedFromTable_hashOutput_query_bind,
            runCleanFromTable_hashOutput_query_bind, map_bind]
          apply bind_congr
          intro output
          exact ih output state fuel
      | ensure coordinate =>
          rw [runDirectResolvedFromTable_ensure_query_bind,
            runCleanFromTable_ensure_query_bind]
          simpa [directDeferredContext, directDeferredValues_ensure] using
            ih () (state.ensure coordinate) fuel
      | probe coordinate candidate =>
          rw [runDirectResolvedFromTable_probe_query_bind,
            runCleanFromTable_probe_query_bind]
          cases fuel with
          | zero => simp [projectResolvedRunResult]
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · simp only [directDeferredContext, hrevealed, ↓reduceIte]
                exact ih () state remaining
              · simp only [directDeferredContext, hrevealed, ↓reduceIte]
                simpa [directDeferredContext, directDeferredValues_addPending] using
                  ih () (state.addPending coordinate candidate) remaining
      | peek coordinate =>
          rw [runDirectResolvedFromTable_peek_query_bind,
            runCleanFromTable_peek_query_bind]
          exact ih (state.values coordinate) state fuel
      | publish coordinate =>
          rw [runDirectResolvedFromTable_publish_query_bind,
            runCleanFromTable_publish_query_bind]
          simpa [directDeferredContext, directDeferredValues_publish] using
            ih () (state.publish coordinate) fuel
      | reveal coordinate =>
          rw [runDirectResolvedFromTable_reveal_query_bind,
            runCleanFromTable_reveal_query_bind]
          cases hvalue : state.values coordinate with
          | some output =>
              simp only [directDeferredContext, hvalue]
              exact ih output state fuel
          | none =>
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
                  let output := table index
                  by_cases hhit : state.hitAt index.coordinate output
                  · change state.hitAt (.chainStart lay tree leafIdx chainIdx)
                        (table ⟨lay, tree, leafIdx, chainIdx⟩) at hhit
                    simp [directDeferredContext, hvalue, hhit,
                      projectResolvedRunResult]
                  · change ¬state.hitAt (.chainStart lay tree leafIdx chainIdx)
                        (table ⟨lay, tree, leafIdx, chainIdx⟩) at hhit
                    simp only [directDeferredContext, hvalue, hhit, ↓reduceIte]
                    have hcontext :
                        { state := state.materialize index.coordinate output,
                          values := directDeferredValues state } =
                          directDeferredContext
                            (state.materialize index.coordinate output) := by
                      simp [directDeferredContext,
                        directDeferredValues_materialize_chainStart]
                    simpa [index, output] using
                      (hcontext ▸ ih output
                        (state.materialize index.coordinate output) fuel)
              | position position =>
                  simp only [directDeferredContext, hvalue, map_bind]
                  apply bind_congr
                  intro output
                  by_cases hhit : state.hitAt (.position position) output
                  · simp [hhit, projectResolvedRunResult]
                  · simp only [hhit, ↓reduceIte]
                    have hcontext :
                        { state := state.materialize (.position position) output,
                          values := (directDeferredValues state).install position output } =
                          directDeferredContext
                            (state.materialize (.position position) output) := by
                      simp [directDeferredContext,
                        directDeferredValues_materialize_position]
                    rw [hcontext]
                    exact ih output (state.materialize (.position position) output) fuel

end SphincsSecurity.Concrete.OtsProbeSimulation
