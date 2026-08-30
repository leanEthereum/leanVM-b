import SphincsSecurity.Proof.OtsProbeResolvedAdaptiveClean

/-!
# Structural boundary first fire

Canonical signer boundaries hide materialized values that were not published while retaining their
private structural copy. A later probe can make such a context impossible only by naming the
truncated private value. This file isolates that exact discrepancy from ordinary clean execution.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

def PrivateStructuralHit (context : DeferredContext) : Prop :=
  ∃ position output,
    context.state.values (.position position) = none ∧
      context.values position = some output ∧
      context.state.hitAt (.position position) output

theorem DeferredCompletion.not_privateStructuralHit
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput}
    (hcompletion : DeferredCompletion table context completion) :
    ¬PrivateStructuralHit context := by
  rintro ⟨position, output, _hhidden, hprivate, hhit⟩
  have hcompletionOutput : completion (.position position) = output :=
    hcompletion.2.1 position output hprivate
  have hpending :
      (Coordinate.position position, truncateHash output) ∈ context.state.pending := by
    rw [← LazyRevealProbe.State.mem_pendingAt_iff]
    exact hhit
  have havoids := hcompletion.2.2.1 (.position position) (truncateHash output) hpending
  rw [hcompletionOutput] at havoids
  exact havoids rfl

theorem not_privateStructuralHit_of_deferredCompletable
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hcompletable : DeferredCompletable table context) :
    ¬PrivateStructuralHit context := by
  obtain ⟨completion, hcompletion⟩ := hcompletable
  exact hcompletion.not_privateStructuralHit

theorem privateStructuralHit_addPending_iff
    (context : DeferredContext) (position : Position) (output : HashOutput)
    (candidate : Digest)
    (hclean : ¬PrivateStructuralHit context)
    (hhidden : context.state.values (.position position) = none)
    (hprivate : context.values position = some output) :
    PrivateStructuralHit
        { context with
          state := context.state.addPending (.position position) candidate } ↔
      truncateHash output = candidate := by
  constructor
  · rintro ⟨other, otherOutput, hotherHidden, hotherPrivate, hotherHit⟩
    by_cases heq : other = position
    · subst other
      have houtput : otherOutput = output := by
        rw [hprivate] at hotherPrivate
        exact Option.some.inj hotherPrivate.symm
      subst otherOutput
      rw [hitAt_addPending_self_iff] at hotherHit
      exact hotherHit.resolve_left fun hold =>
        hclean ⟨position, output, hhidden, hprivate, hold⟩
    · have hcoordinate : Coordinate.position position ≠ .position other := by
        intro hcoordinate
        exact heq (Coordinate.position.inj hcoordinate).symm
      have holdHit : context.state.hitAt (.position other) otherOutput := by
        simpa only [hitAt_addPending_of_ne context.state (.position position)
          (.position other) candidate otherOutput hcoordinate] using hotherHit
      exact False.elim (hclean ⟨other, otherOutput, hotherHidden, hotherPrivate, holdHit⟩)
  · intro hcandidate
    refine ⟨position, output, hhidden, hprivate, ?_⟩
    exact (hitAt_addPending_self_iff context.state (.position position) candidate output).2
      (Or.inr hcandidate)

theorem deferredCompletable_addPending_position_iff
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput}
    (position : Position) (output : HashOutput) (candidate : Digest)
    (hcompletion : DeferredCompletion table context completion)
    (hprivate : context.values position = some output) :
    DeferredCompletable table
        { context with
          state := context.state.addPending (.position position) candidate } ↔
      truncateHash output ≠ candidate := by
  constructor
  · rintro ⟨nextCompletion, hnextCompletion⟩
    have hnextOutput : nextCompletion (.position position) = output :=
      hnextCompletion.2.1 position output hprivate
    have hpending : (Coordinate.position position, candidate) ∈
        (context.state.addPending (.position position) candidate).pending := by
      simp [LazyRevealProbe.State.addPending]
    have havoids :=
      hnextCompletion.2.2.1 (.position position) candidate hpending
    rwa [hnextOutput] at havoids
  · intro havoids
    refine ⟨completion, hcompletion.addPending_of_avoids (.position position) candidate ?_⟩
    have hcompletionOutput : completion (.position position) = output :=
      hcompletion.2.1 position output hprivate
    rwa [hcompletionOutput]

theorem not_deferredCompletable_addPending_position_iff_privateStructuralHit
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    {completion : Coordinate → HashOutput}
    (position : Position) (output : HashOutput) (candidate : Digest)
    (hcompletion : DeferredCompletion table context completion)
    (hhidden : context.state.values (.position position) = none)
    (hprivate : context.values position = some output) :
    ¬DeferredCompletable table
        { context with
          state := context.state.addPending (.position position) candidate } ↔
      PrivateStructuralHit
        { context with
          state := context.state.addPending (.position position) candidate } := by
  rw [deferredCompletable_addPending_position_iff position output candidate hcompletion hprivate,
    privateStructuralHit_addPending_iff context position output candidate
      hcompletion.not_privateStructuralHit hhidden hprivate]
  simp

theorem privateStructuralHit_addPending_of_truncateHash_eq
    (context : DeferredContext) (position : Position) (output : HashOutput)
    (candidate : Digest)
    (hhidden : context.state.values (.position position) = none)
    (hprivate : context.values position = some output)
    (hcandidate : truncateHash output = candidate) :
    PrivateStructuralHit
      { context with
        state := context.state.addPending (.position position) candidate } := by
  refine ⟨position, output, hhidden, hprivate, ?_⟩
  exact (hitAt_addPending_self_iff context.state (.position position) candidate output).2
    (Or.inr hcandidate)

inductive DirectStopReason where
  | fuelExhausted
  | ordinaryHit
  | privateStructuralHit
deriving DecidableEq

inductive DirectDetailedResult (alpha : Type) where
  | stopped (reason : DirectStopReason)
  | done (result : ResolvedRunResult alpha)

def DirectDetailedResult.toOption : DirectDetailedResult alpha → Option (ResolvedRunResult alpha)
  | .stopped _ => none
  | .done result => some result

noncomputable def runDirectResolvedDetailedFromTable
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    ProbComp (DirectDetailedResult alpha) :=
  OracleComp.construct
    (C := fun _ : OracleComp (LazyRevealProbe.World Coordinate) alpha =>
      DeferredContext → Nat → (OtsSecretIndex → HashOutput) →
        ProbComp (DirectDetailedResult alpha))
    (fun value context remaining table =>
      pure (.done ⟨context, remaining, value, table⟩))
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
          | 0 => pure (.stopped .fuelExhausted)
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
                    pure (.stopped .ordinaryHit)
                  else
                    recursivelyRun output
                      { state := context.state.materialize coordinate output
                        values := context.values }
                      fuel table
              | .position position =>
                  match context.values position with
                  | some output =>
                      if context.state.hitAt coordinate output then
                        pure (.stopped .privateStructuralHit)
                      else
                        recursivelyRun output
                          { state := context.state.materialize coordinate output
                            values := context.values }
                          fuel table
                  | none => do
                      let output ← LazyRevealProbe.sampleHashOutput
                      if context.state.hitAt coordinate output then
                        pure (.stopped .ordinaryHit)
                      else
                        recursivelyRun output
                          { state := context.state.materialize coordinate output
                            values := context.values.install position output }
                          fuel table)
    computation context fuel table

theorem runDirectResolvedDetailedFromTable_uniform_query_bind
    (context : DeferredContext) (fuel n : Nat)
    (table : OtsSecretIndex → HashOutput)
    (next : Fin (n + 1) → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectResolvedDetailedFromTable context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.uniform n)) :
            OracleComp (LazyRevealProbe.World Coordinate) (Fin (n + 1))) >>= next) = (do
      let output ← liftM (unifSpec.query n)
      runDirectResolvedDetailedFromTable context fuel table (next output)) := by
  rfl

theorem runDirectResolvedDetailedFromTable_hashOutput_query_bind
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectResolvedDetailedFromTable context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          .hashOutput) :
            OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next) = (do
      let output ← LazyRevealProbe.sampleHashOutput
      runDirectResolvedDetailedFromTable context fuel table (next output)) := by
  rfl

theorem runDirectResolvedDetailedFromTable_ensure_query_bind
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectResolvedDetailedFromTable context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.ensure coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      runDirectResolvedDetailedFromTable
        { context with state := context.state.ensure coordinate }
        fuel table (next ()) := by
  rfl

theorem runDirectResolvedDetailedFromTable_probe_query_bind
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (candidate : Digest)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectResolvedDetailedFromTable context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.probe coordinate candidate)) :
            OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      match fuel with
      | 0 => pure (.stopped .fuelExhausted)
      | remaining + 1 =>
          if coordinate ∈ context.state.revealed then
            runDirectResolvedDetailedFromTable context remaining table (next ())
                      else
                    runDirectResolvedDetailedFromTable
              { context with
                state := context.state.addPending coordinate candidate }
              remaining table (next ()) := by
  rfl

theorem runDirectResolvedDetailedFromTable_peek_query_bind
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (next : Option HashOutput →
      OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectResolvedDetailedFromTable context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.peek coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) (Option HashOutput)) >>= next) =
      runDirectResolvedDetailedFromTable context fuel table
        (next (context.state.values coordinate)) := by
  rfl

theorem runDirectResolvedDetailedFromTable_publish_query_bind
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectResolvedDetailedFromTable context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.publish coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      runDirectResolvedDetailedFromTable
        { context with state := context.state.publish coordinate }
        fuel table (next ()) := by
  rfl

theorem runDirectResolvedDetailedFromTable_reveal_query_bind
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectResolvedDetailedFromTable context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.reveal coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next) =
      (match context.state.values coordinate with
      | some output =>
          runDirectResolvedDetailedFromTable context fuel table (next output)
      | none =>
          match coordinate with
          | .chainStart lay tree leafIdx chainIdx =>
              let output := table ⟨lay, tree, leafIdx, chainIdx⟩
              if context.state.hitAt coordinate output then
                pure (.stopped .ordinaryHit)
              else
                runDirectResolvedDetailedFromTable
                  { state := context.state.materialize coordinate output
                    values := context.values }
                  fuel table (next output)
          | .position position =>
              match context.values position with
              | some output =>
                  if context.state.hitAt coordinate output then
                    pure (.stopped .privateStructuralHit)
                  else
                    runDirectResolvedDetailedFromTable
                      { state := context.state.materialize coordinate output
                        values := context.values }
                      fuel table (next output)
              | none => do
                  let output ← LazyRevealProbe.sampleHashOutput
                  if context.state.hitAt coordinate output then
                    pure (.stopped .ordinaryHit)
                  else
                    runDirectResolvedDetailedFromTable
                      { state := context.state.materialize coordinate output
                        values := context.values.install position output }
                      fuel table (next output)) := by
  cases coordinate <;> rfl

set_option maxRecDepth 100000 in
theorem map_toOption_runDirectResolvedDetailedFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) :
    DirectDetailedResult.toOption <$>
        runDirectResolvedDetailedFromTable context fuel table computation =
      runDirectResolvedFromTable context fuel table computation := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      simp [runDirectResolvedDetailedFromTable, runDirectResolvedFromTable,
        DirectDetailedResult.toOption]
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runDirectResolvedDetailedFromTable_uniform_query_bind,
            runDirectResolvedFromTable_uniform_query_bind, map_bind]
          apply bind_congr
          intro output
          exact ih output context fuel
      | hashOutput =>
          rw [runDirectResolvedDetailedFromTable_hashOutput_query_bind,
            runDirectResolvedFromTable_hashOutput_query_bind, map_bind]
          apply bind_congr
          intro output
          exact ih output context fuel
      | ensure coordinate =>
          rw [runDirectResolvedDetailedFromTable_ensure_query_bind,
            runDirectResolvedFromTable_ensure_query_bind]
          exact ih () { context with state := context.state.ensure coordinate } fuel
      | probe coordinate candidate =>
          rw [runDirectResolvedDetailedFromTable_probe_query_bind,
            runDirectResolvedFromTable_probe_query_bind]
          cases fuel with
          | zero => simp [DirectDetailedResult.toOption]
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · simp only [hrevealed, ↓reduceIte]
                exact ih () context remaining
              · simp only [hrevealed, ↓reduceIte]
                exact ih ()
                  { context with
                    state := context.state.addPending coordinate candidate }
                  remaining
      | peek coordinate =>
          rw [runDirectResolvedDetailedFromTable_peek_query_bind,
            runDirectResolvedFromTable_peek_query_bind]
          exact ih (context.state.values coordinate) context fuel
      | publish coordinate =>
          rw [runDirectResolvedDetailedFromTable_publish_query_bind,
            runDirectResolvedFromTable_publish_query_bind]
          exact ih () { context with state := context.state.publish coordinate } fuel
      | reveal coordinate =>
          rw [runDirectResolvedDetailedFromTable_reveal_query_bind,
            runDirectResolvedFromTable_reveal_query_bind]
          cases hstate : context.state.values coordinate with
          | some output =>
              simp only
              exact ih output context fuel
          | none =>
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let output := table ⟨lay, tree, leafIdx, chainIdx⟩
                  by_cases hhit : context.state.hitAt
                      (.chainStart lay tree leafIdx chainIdx) output
                  · simp [output, hhit, DirectDetailedResult.toOption]
                  · simp only [output, hhit, ↓reduceIte]
                    exact ih output
                      { state := context.state.materialize
                          (.chainStart lay tree leafIdx chainIdx) output
                        values := context.values }
                      fuel
              | position position =>
                  cases hprivate : context.values position with
                  | some output =>
                      by_cases hhit : context.state.hitAt (.position position) output
                      · simp [hprivate, hhit, DirectDetailedResult.toOption,
                          resolveDeferredPositionValue, hstate]
                      · simp only [hprivate, hhit, ↓reduceIte]
                        rw [resolveDeferredPositionValue_of_deferred_value position context
                          output hstate hprivate, if_neg hhit]
                        simp only [pure_bind]
                        exact ih output
                          { state := context.state.materialize (.position position) output
                            values := context.values }
                          fuel
                  | none =>
                      simp only [hprivate]
                      rw [resolveDeferredPositionValue_fresh position context hstate hprivate,
                        map_bind, bind_assoc]
                      apply bind_congr
                      intro output
                      by_cases hhit : context.state.hitAt (.position position) output
                      · simp [hhit, DirectDetailedResult.toOption]
                      · simp only [hhit, ↓reduceIte, pure_bind]
                        exact ih output
                          { state := context.state.materialize (.position position) output
                            values := context.values.install position output }
                          fuel

end SphincsSecurity.Concrete.OtsProbeSimulation
