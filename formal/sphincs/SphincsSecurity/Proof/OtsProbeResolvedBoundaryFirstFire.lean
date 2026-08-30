import SphincsSecurity.Proof.OtsProbeResolvedAdaptiveClean

/-!
# Structural boundary first fire

Canonical signer boundaries hide materialized values that were not published while retaining their
private structural copy. A later probe can make such a context impossible only by naming the
truncated private value. This file isolates that exact discrepancy from ordinary clean execution.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local irreducible] maskedPublishedTreeRoot

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

theorem mem_support_runDirectResolvedFromTable_of_done_detailed
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult alpha)
    (hresult : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table computation)) :
    some result ∈ support
      (runDirectResolvedFromTable context fuel table computation) := by
  rw [← map_toOption_runDirectResolvedDetailedFromTable computation context fuel table,
    support_map]
  exact ⟨.done result, hresult, rfl⟩

inductive DirectBoundaryOutcome where
  | success
  | ordinaryFailure
  | privateStructuralFailure
deriving DecidableEq

def DirectBoundaryOutcome.failed : DirectBoundaryOutcome → Bool
  | .success => false
  | .ordinaryFailure => true
  | .privateStructuralFailure => true

def DirectBoundaryOutcome.privateStructural : DirectBoundaryOutcome → Bool
  | .privateStructuralFailure => true
  | _ => false

def DirectBoundaryOutcome.ofFailed : Bool → DirectBoundaryOutcome
  | false => .success
  | true => .ordinaryFailure

@[simp] theorem DirectBoundaryOutcome.failed_ofFailed (failed : Bool) :
    (DirectBoundaryOutcome.ofFailed failed).failed = failed := by
  cases failed <;> rfl

theorem DirectBoundaryOutcome.failed_eq_true_iff
    (outcome : DirectBoundaryOutcome) :
    outcome.failed = true ↔
      outcome = .ordinaryFailure ∨ outcome = .privateStructuralFailure := by
  cases outcome <;> simp [DirectBoundaryOutcome.failed]

theorem probEvent_failed_le_ordinary_add_private
    (run : ProbComp DirectBoundaryOutcome) :
    Pr[fun outcome => outcome.failed = true | run] ≤
      Pr[= .ordinaryFailure | run] + Pr[= .privateStructuralFailure | run] := by
  have heq : Pr[fun outcome => outcome.failed = true | run] =
      Pr[fun outcome => outcome = .ordinaryFailure ∨
        outcome = .privateStructuralFailure | run] :=
    OracleComp.probEvent_congr'
      (fun outcome _ => DirectBoundaryOutcome.failed_eq_true_iff outcome) rfl
  rw [heq]
  simpa only [probEvent_eq_eq_probOutput] using
    (probEvent_or_le run
      (fun outcome => outcome = .ordinaryFailure)
      (fun outcome => outcome = .privateStructuralFailure))

noncomputable def classifyDirectObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → alpha → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (value : alpha) :
    ProbComp DirectBoundaryOutcome := by
  classical
  exact if PrivateStructuralHit context then
      pure .privateStructuralFailure
    else if DeferredCompletable table context then
      DirectBoundaryOutcome.ofFailed <$> observe context fuel value
    else
      pure .ordinaryFailure

theorem evalDist_failed_classifyDirectObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → alpha → ProbComp Bool)
    [ObserverDooms table observe]
    (context : DeferredContext) (fuel : Nat) (value : alpha)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table) :
    evalDist (DirectBoundaryOutcome.failed <$>
        classifyDirectObserve table observe context fuel value) =
      evalDist (observe context fuel value) := by
  unfold classifyDirectObserve
  by_cases hprivate : PrivateStructuralHit context
  · simp only [hprivate, ↓reduceIte, map_pure, DirectBoundaryOutcome.failed]
    exact (ObserverDooms.eq_true (table := table) (observe := observe)
      context fuel value hconsistent hstarts
        (fun hcompletable =>
          (not_privateStructuralHit_of_deferredCompletable hcompletable) hprivate)).symm
  · simp only [hprivate, ↓reduceIte]
    by_cases hcompletable : DeferredCompletable table context
    · simp [hcompletable, Functor.map_map]
    · simp only [hcompletable, ↓reduceIte, map_pure, DirectBoundaryOutcome.failed]
      exact (ObserverDooms.eq_true (table := table) (observe := observe)
        context fuel value hconsistent hstarts hcompletable).symm

noncomputable def finishDirectDetailedObserve
    (observe : DeferredContext → Nat → alpha → ProbComp DirectBoundaryOutcome) :
    DirectDetailedResult alpha → ProbComp DirectBoundaryOutcome
  | .stopped .privateStructuralHit => pure .privateStructuralFailure
  | .stopped _ => pure .ordinaryFailure
  | .done result => observe result.context result.remaining result.value

noncomputable def classifyDirectDetailedObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → alpha → ProbComp DirectBoundaryOutcome)
    (context : DeferredContext) (fuel : Nat) (value : alpha) :
    ProbComp DirectBoundaryOutcome := by
  classical
  exact if PrivateStructuralHit context then
      pure .privateStructuralFailure
    else if DeferredCompletable table context then
      observe context fuel value
    else
      pure .ordinaryFailure

theorem evalDist_failed_classifyDirectDetailedObserve
    (table : OtsSecretIndex → HashOutput)
    (detailedObserve : DeferredContext → Nat → alpha → ProbComp DirectBoundaryOutcome)
    (observe : DeferredContext → Nat → alpha → ProbComp Bool)
    [ObserverDooms table observe]
    (context : DeferredContext) (fuel : Nat) (value : alpha)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hproject : evalDist (DirectBoundaryOutcome.failed <$>
        detailedObserve context fuel value) =
      evalDist (observe context fuel value)) :
    evalDist (DirectBoundaryOutcome.failed <$>
        classifyDirectDetailedObserve table detailedObserve context fuel value) =
      evalDist (observe context fuel value) := by
  unfold classifyDirectDetailedObserve
  by_cases hprivate : PrivateStructuralHit context
  · simp only [hprivate, ↓reduceIte, map_pure, DirectBoundaryOutcome.failed]
    exact (ObserverDooms.eq_true (table := table) (observe := observe)
      context fuel value hconsistent hstarts
        (fun hcompletable =>
          (not_privateStructuralHit_of_deferredCompletable hcompletable) hprivate)).symm
  · simp only [hprivate, ↓reduceIte]
    by_cases hcompletable : DeferredCompletable table context
    · simpa only [hcompletable, ↓reduceIte] using hproject
    · simp only [hcompletable, ↓reduceIte, map_pure, DirectBoundaryOutcome.failed]
      exact (ObserverDooms.eq_true (table := table) (observe := observe)
        context fuel value hconsistent hstarts hcompletable).symm

noncomputable def canonicalizeDirectDetailedObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → alpha → ProbComp DirectBoundaryOutcome)
    (context : DeferredContext) (fuel : Nat) (value : alpha) :
    ProbComp DirectBoundaryOutcome := by
  classical
  exact if PrivateStructuralHit (canonicalizeMaterializedValues table context) then
      pure .privateStructuralFailure
    else if PublishedValues context.state then
      classifyDirectDetailedObserve table observe
        (canonicalizeMaterializedValues table context) fuel value
    else
      pure .ordinaryFailure

theorem evalDist_failed_canonicalizeDirectDetailedObserve
    (table : OtsSecretIndex → HashOutput)
    (detailedObserve : DeferredContext → Nat → alpha → ProbComp DirectBoundaryOutcome)
    (observe : DeferredContext → Nat → alpha → ProbComp Bool)
    [ObserverDooms table observe]
    (context : DeferredContext) (fuel : Nat) (value : alpha)
    (hconsistent : context.ValuesConsistent)
    (hproject : evalDist (DirectBoundaryOutcome.failed <$>
        detailedObserve (canonicalizeMaterializedValues table context) fuel value) =
      evalDist (observe (canonicalizeMaterializedValues table context) fuel value)) :
    evalDist (DirectBoundaryOutcome.failed <$>
        canonicalizeDirectDetailedObserve table detailedObserve context fuel value) =
      evalDist (canonicalizeObserve table observe context fuel value) := by
  unfold canonicalizeDirectDetailedObserve canonicalizeObserve
  by_cases hprivate : PrivateStructuralHit (canonicalizeMaterializedValues table context)
  · simp only [hprivate, ↓reduceIte, map_pure, DirectBoundaryOutcome.failed]
    by_cases hpublished : PublishedValues context.state
    · simp only [hpublished, ↓reduceIte]
      exact (ObserverDooms.eq_true (table := table) (observe := observe)
        (canonicalizeMaterializedValues table context) fuel value
          (canonicalizeMaterializedValues_valuesConsistent table context hconsistent)
          (canonicalizeMaterializedValues_startTableAgrees table context)
          (fun hcompletable =>
            (not_privateStructuralHit_of_deferredCompletable hcompletable) hprivate)).symm
    · simp [hpublished]
  · simp only [hprivate, ↓reduceIte]
    by_cases hpublished : PublishedValues context.state
    · simp only [hpublished, ↓reduceIte]
      exact evalDist_failed_classifyDirectDetailedObserve table detailedObserve observe
        (canonicalizeMaterializedValues table context) fuel value
          (canonicalizeMaterializedValues_valuesConsistent table context hconsistent)
          (canonicalizeMaterializedValues_startTableAgrees table context) hproject
    · simp [hpublished, DirectBoundaryOutcome.failed]

noncomputable def runDirectDetailedObserve
    (observe : DeferredContext → Nat → alpha → ProbComp DirectBoundaryOutcome)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    ProbComp DirectBoundaryOutcome :=
  runDirectResolvedDetailedFromTable context fuel table computation >>=
    finishDirectDetailedObserve observe

theorem evalDist_failed_runDirectDetailedObserve
    (detailedObserve : DeferredContext → Nat → alpha → ProbComp DirectBoundaryOutcome)
    (observe : DeferredContext → Nat → alpha → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (hproject : ∀ result,
      DirectDetailedResult.done result ∈ support
          (runDirectResolvedDetailedFromTable context fuel table computation) →
        evalDist (DirectBoundaryOutcome.failed <$>
            detailedObserve result.context result.remaining result.value) =
          evalDist (observe result.context result.remaining result.value)) :
    evalDist (DirectBoundaryOutcome.failed <$>
        runDirectDetailedObserve detailedObserve context fuel table computation) =
      evalDist (runDirectResolvedObserve observe context fuel table computation) := by
  unfold runDirectDetailedObserve runDirectResolvedObserve
  rw [map_bind]
  calc
    _ = evalDist (runDirectResolvedDetailedFromTable context fuel table computation >>=
          fun result => finishObserve observe (DirectDetailedResult.toOption result)) := by
      apply evalDist_bind_congr
      intro result hresult
      cases result with
      | stopped reason =>
          cases reason <;> rfl
      | done result =>
          exact hproject result hresult
    _ = evalDist ((DirectDetailedResult.toOption <$>
          runDirectResolvedDetailedFromTable context fuel table computation) >>=
            finishObserve observe) := by
      apply congrArg evalDist
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    _ = _ := by
      rw [map_toOption_runDirectResolvedDetailedFromTable]

noncomputable def directDetailedBoundaryObserve
    (impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (computation : OracleComp spec alpha)
    (observe : DeferredContext → Nat → (alpha × SplitHashCache) →
      ProbComp DirectBoundaryOutcome)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ProbComp DirectBoundaryOutcome := by
  classical
  exact OracleComp.construct
    (C := fun _ : OracleComp spec alpha =>
      (DeferredContext → Nat → (alpha × SplitHashCache) →
          ProbComp DirectBoundaryOutcome) →
        DeferredContext → Nat → (OtsSecretIndex → HashOutput) → SplitHashCache →
          ProbComp DirectBoundaryOutcome)
    (fun value observe context fuel _table cache => observe context fuel (value, cache))
    (fun query _next recursivelyRun observe context fuel table cache =>
      runDirectDetailedObserve
        (canonicalizeDirectDetailedObserve table
          (fun nextContext remaining value =>
            recursivelyRun value.1 observe nextContext remaining table value.2))
        context fuel table ((impl query).run cache))
    computation observe context fuel table cache

set_option maxRecDepth 100000 in
theorem evalDist_failed_directDetailedBoundaryObserve
    (impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (computation : OracleComp spec alpha)
    (detailedObserve : DeferredContext → Nat → (alpha × SplitHashCache) →
      ProbComp DirectBoundaryOutcome)
    (observe : DeferredContext → Nat → (alpha × SplitHashCache) → ProbComp Bool)
    [ObserverDooms table observe]
    (hobserve : ∀ context fuel value,
      context.ValuesConsistent → StartTableAgrees context.state table →
      evalDist (DirectBoundaryOutcome.failed <$>
          detailedObserve context fuel value) =
        evalDist (observe context fuel value))
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table) :
    evalDist (DirectBoundaryOutcome.failed <$>
        directDetailedBoundaryObserve impl computation detailedObserve context fuel table cache) =
      evalDist (directBoundaryObserve impl computation observe context fuel table cache) := by
  induction computation using OracleComp.inductionOn generalizing context fuel cache with
  | pure value =>
      rw [directDetailedBoundaryObserve, OracleComp.construct_pure,
        directBoundaryObserve, OracleComp.construct_pure]
      exact hobserve context fuel (value, cache) hconsistent hstarts
  | query_bind query next ih =>
      rw [directDetailedBoundaryObserve, OracleComp.construct_query_bind,
        directBoundaryObserve, OracleComp.construct_query_bind]
      let detailedNext : DeferredContext → Nat →
          ((spec.Range query) × SplitHashCache) → ProbComp DirectBoundaryOutcome :=
        fun nextContext remaining value =>
          directDetailedBoundaryObserve impl (next value.1) detailedObserve
            nextContext remaining table value.2
      let nextObserve : DeferredContext → Nat →
          ((spec.Range query) × SplitHashCache) → ProbComp Bool :=
        fun nextContext remaining value =>
          directBoundaryObserve impl (next value.1) observe
            nextContext remaining table value.2
      letI : ObserverDooms table nextObserve := ⟨by
        intro nextContext remaining value hnextConsistent hnextStarts hnextDoomed
        exact directBoundaryObserve_dooms impl (next value.1) observe nextContext remaining
          value.2 hnextConsistent hnextStarts hnextDoomed⟩
      apply evalDist_failed_runDirectDetailedObserve
      intro result hresult
      have hdirect := mem_support_runDirectResolvedFromTable_of_done_detailed
        ((impl query).run cache) context fuel table result hresult
      have hcore := resolvedCore_of_mem_runDirectResolvedFromTable
        ((impl query).run cache) context fuel table result hconsistent hstarts hdirect
      apply evalDist_failed_canonicalizeDirectDetailedObserve
        table detailedNext nextObserve result.context result.remaining result.value hcore.2.1
      exact ih result.value.1 (canonicalizeMaterializedValues table result.context)
        result.remaining result.value.2
          (canonicalizeMaterializedValues_valuesConsistent table result.context hcore.2.1)
          (canonicalizeMaterializedValues_startTableAgrees table result.context)

noncomputable def directDetailedVerifierFinishObserve
    (table : OtsSecretIndex → HashOutput)
    (parameter : PublicParameter) (root : Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : (Forgery × QueryLog SigningSpec) × SplitHashCache) :
    ProbComp DirectBoundaryOutcome :=
  runDirectDetailedObserve
    (classifyDirectObserve table (resolvedFinalizationObserve table))
    context fuel table ((canonicalVerifierFinish parameter root value.1).run value.2)

instance directVerifierFinishObserve_observerDooms
    (table : OtsSecretIndex → HashOutput)
    (parameter : PublicParameter) (root : Digest) :
    ObserverDooms table (directVerifierFinishObserve table parameter root) where
  eq_true context fuel value hconsistent hstarts hdoomed := by
    unfold directVerifierFinishObserve
    exact evalDist_runDirectResolvedObserve_eq_true_of_not_completable_auto
      (observe := resolvedFinalizationObserve table) context fuel table
        ((canonicalVerifierFinish parameter root value.1).run value.2)
          hconsistent hstarts hdoomed

theorem evalDist_failed_directDetailedVerifierFinishObserve
    (table : OtsSecretIndex → HashOutput)
    (parameter : PublicParameter) (root : Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : (Forgery × QueryLog SigningSpec) × SplitHashCache)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table) :
    evalDist (DirectBoundaryOutcome.failed <$>
        directDetailedVerifierFinishObserve table parameter root context fuel value) =
      evalDist (directVerifierFinishObserve table parameter root context fuel value) := by
  unfold directDetailedVerifierFinishObserve directVerifierFinishObserve
  apply evalDist_failed_runDirectDetailedObserve
  intro result hresult
  have hdirect := mem_support_runDirectResolvedFromTable_of_done_detailed
    ((canonicalVerifierFinish parameter root value.1).run value.2)
      context fuel table result hresult
  have hcore := resolvedCore_of_mem_runDirectResolvedFromTable
    ((canonicalVerifierFinish parameter root value.1).run value.2)
      context fuel table result hconsistent hstarts hdirect
  exact evalDist_failed_classifyDirectObserve table (resolvedFinalizationObserve table)
    result.context result.remaining result.value hcore.2.1 hcore.2.2

noncomputable def allDirectDetailedRetainedRestObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) : ProbComp DirectBoundaryOutcome :=
  directDetailedBoundaryObserve
    (maskedExpandedAdversaryImpl parameter value.1 ftsSecret)
    (signingTraceComputation (adversary.main ⟨value.1, parameter⟩))
    (directDetailedVerifierFinishObserve table parameter value.1)
    context fuel table value.2

theorem evalDist_failed_allDirectDetailedRetainedRestObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table) :
    evalDist (DirectBoundaryOutcome.failed <$>
        allDirectDetailedRetainedRestObserve adversary parameter table ftsSecret
          context fuel value) =
      evalDist (allDirectRetainedRestObserve adversary parameter table ftsSecret
        context fuel value) := by
  unfold allDirectDetailedRetainedRestObserve allDirectRetainedRestObserve
  apply evalDist_failed_directDetailedBoundaryObserve
  intro nextContext remaining nextValue hnextConsistent hnextStarts
  exact evalDist_failed_directDetailedVerifierFinishObserve table parameter value.1
    nextContext remaining nextValue hnextConsistent hnextStarts
  exact hconsistent
  exact hstarts

noncomputable def allDirectBoundaryDetailedRetainedOutcome
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp DirectBoundaryOutcome :=
  runDirectDetailedObserve
    (allDirectDetailedRetainedRestObserve adversary parameter table ftsSecret)
    { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
      values := emptyDeferredStructuralValues }
    fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem evalDist_failed_allDirectBoundaryDetailedRetainedOutcome
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (DirectBoundaryOutcome.failed <$>
        allDirectBoundaryDetailedRetainedOutcome adversary parameter table ftsSecret fuel) =
      evalDist (allDirectBoundaryDeferredRetainedFinishIsNone adversary parameter table
        ftsSecret fuel) := by
  let initial : DeferredContext :=
    { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
      values := emptyDeferredStructuralValues }
  unfold allDirectBoundaryDetailedRetainedOutcome
    allDirectBoundaryDeferredRetainedFinishIsNone
  apply evalDist_failed_runDirectDetailedObserve
  intro result hresult
  have hdirect := mem_support_runDirectResolvedFromTable_of_done_detailed
    (maskedPublishedTreeRoot.run emptySplitHashCache) initial fuel table result hresult
  have hcore := resolvedCore_of_mem_runDirectResolvedFromTable
    (maskedPublishedTreeRoot.run emptySplitHashCache) initial fuel table result
      DeferredContext.valid_empty.valuesConsistent (startTableAgrees_empty table) hdirect
  exact evalDist_failed_allDirectDetailedRetainedRestObserve adversary parameter table ftsSecret
    result.context result.remaining result.value hcore.2.1 hcore.2.2

noncomputable def sampledAllDirectBoundaryDetailedRetainedOutcome
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp DirectBoundaryOutcome := do
  let table ← sampleOtsHashTable
  allDirectBoundaryDetailedRetainedOutcome adversary parameter table ftsSecret fuel

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
theorem evalDist_failed_sampledAllDirectBoundaryDetailedRetainedOutcome
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (DirectBoundaryOutcome.failed <$>
        sampledAllDirectBoundaryDetailedRetainedOutcome adversary parameter ftsSecret fuel) =
      evalDist (sampledAllDirectBoundaryFinishIsNone adversary parameter ftsSecret fuel) := by
  unfold sampledAllDirectBoundaryDetailedRetainedOutcome sampledAllDirectBoundaryFinishIsNone
  rw [map_bind]
  apply evalDist_bind_congr
  intro table _htable
  exact evalDist_failed_allDirectBoundaryDetailedRetainedOutcome adversary parameter table
    ftsSecret fuel

end SphincsSecurity.Concrete.OtsProbeSimulation
