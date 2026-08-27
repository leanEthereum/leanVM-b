import SphincsSecurity.Proof.OtsProbeCompletionSampling

/-!
# Finite-table deferral through one-time probing runs

The clean eager interpreter reads missing chain starts from one finite table. All uniform draws and
all ordinary or structural random-oracle outputs remain lazy. Its result retains the hidden state,
probe fuel and table needed by finalization.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

noncomputable local instance runSampleableOtsHashTable :
    SampleableType (OtsSecretIndex → HashOutput) :=
  SampleableType.ofFintype (OtsSecretIndex → HashOutput)

noncomputable def sampleOtsHashTable :
    ProbComp (OtsSecretIndex → HashOutput) :=
  $ᵗ (OtsSecretIndex → HashOutput)

structure CleanRunResult (alpha : Type) where
  state : LazyRevealProbe.State Coordinate
  remaining : Nat
  value : alpha
  table : OtsSecretIndex → HashOutput

noncomputable def runCleanFromTable
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    ProbComp (Option (CleanRunResult alpha)) :=
  OracleComp.construct
    (C := fun _ : OracleComp (LazyRevealProbe.World Coordinate) alpha =>
      LazyRevealProbe.State Coordinate → Nat → (OtsSecretIndex → HashOutput) →
        ProbComp (Option (CleanRunResult alpha)))
    (fun value state remaining table => pure (some ⟨state, remaining, value, table⟩))
    (fun input _next recursivelyRun state fuel table =>
      match input with
      | .uniform n => do
          let output ← liftM (unifSpec.query n)
          recursivelyRun output state fuel table
      | .hashOutput => do
          let output ← LazyRevealProbe.sampleHashOutput
          recursivelyRun output state fuel table
      | .ensure coordinate =>
          recursivelyRun () (state.ensure coordinate) fuel table
      | .probe coordinate candidate =>
          match fuel with
          | 0 => pure none
          | remaining + 1 =>
              if coordinate ∈ state.revealed then
                recursivelyRun () state remaining table
              else
                recursivelyRun () (state.addPending coordinate candidate) remaining table
      | .peek coordinate =>
          recursivelyRun (state.values coordinate) state fuel table
      | .publish coordinate =>
          recursivelyRun () (state.publish coordinate) fuel table
      | .reveal coordinate =>
          match state.values coordinate with
          | some output => recursivelyRun output state fuel table
          | none =>
              match coordinate with
              | .chainStart lay tree leafIdx chainIdx =>
                  let output := table ⟨lay, tree, leafIdx, chainIdx⟩
                  if state.hitAt coordinate output then
                    pure none
                  else
                    recursivelyRun output (state.materialize coordinate output) fuel table
              | .position _ => do
                  let output ← LazyRevealProbe.sampleHashOutput
                  if state.hitAt coordinate output then
                    pure none
                  else
                    recursivelyRun output (state.materialize coordinate output) fuel table)
    computation state fuel table

noncomputable def runRawCleanWithCompletionTable
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    ProbComp (Option (CleanRunResult alpha)) := do
  let result ← LazyRevealProbe.runRaw state fuel computation
  match result with
  | .stopped _ => pure none
  | .done finalState remaining value => do
      let base ← ($ᵗ (OtsSecretIndex → HashOutput) :
        ProbComp (OtsSecretIndex → HashOutput))
      pure (some ⟨finalState, remaining, value,
        completedStartTable finalState base⟩)

theorem runCleanFromTable_uniform_query_bind
    (state : LazyRevealProbe.State Coordinate) (fuel n : Nat)
    (table : OtsSecretIndex → HashOutput)
    (next : Fin (n + 1) → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runCleanFromTable state fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) (.uniform n)) :
          OracleComp (LazyRevealProbe.World Coordinate) (Fin (n + 1))) >>= next) = (do
      let output ← liftM (unifSpec.query n)
      runCleanFromTable state fuel table (next output)) := by
  rw [runCleanFromTable, OracleComp.construct_query_bind]
  rfl

theorem runCleanFromTable_hashOutput_query_bind
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runCleanFromTable state fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) .hashOutput) :
          OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next) = (do
      let output ← LazyRevealProbe.sampleHashOutput
      runCleanFromTable state fuel table (next output)) := by
  rw [runCleanFromTable, OracleComp.construct_query_bind]
  rfl

theorem runCleanFromTable_ensure_query_bind
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runCleanFromTable state fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.ensure coordinate)) : OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      runCleanFromTable (state.ensure coordinate) fuel table (next ()) := by
  rw [runCleanFromTable, OracleComp.construct_query_bind]
  rfl

theorem runCleanFromTable_probe_query_bind
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate) (candidate : Digest)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runCleanFromTable state fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.probe coordinate candidate)) :
            OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      match fuel with
      | 0 => pure none
      | remaining + 1 =>
          if coordinate ∈ state.revealed then
            runCleanFromTable state remaining table (next ())
          else
            runCleanFromTable (state.addPending coordinate candidate) remaining table (next ()) := by
  rw [runCleanFromTable, OracleComp.construct_query_bind]
  rfl

theorem runCleanFromTable_peek_query_bind
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (next : Option HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runCleanFromTable state fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.peek coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) (Option HashOutput)) >>= next) =
      runCleanFromTable state fuel table (next (state.values coordinate)) := by
  rw [runCleanFromTable, OracleComp.construct_query_bind]
  rfl

theorem runCleanFromTable_publish_query_bind
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runCleanFromTable state fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.publish coordinate)) : OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      runCleanFromTable (state.publish coordinate) fuel table (next ()) := by
  rw [runCleanFromTable, OracleComp.construct_query_bind]
  rfl

theorem runCleanFromTable_reveal_query_bind
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runCleanFromTable state fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.reveal coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next) =
      (match state.values coordinate with
      | some output => runCleanFromTable state fuel table (next output)
      | none =>
          match coordinate with
          | .chainStart lay tree leafIdx chainIdx =>
              let output := table ⟨lay, tree, leafIdx, chainIdx⟩
              if state.hitAt coordinate output then
                pure none
              else
                runCleanFromTable (state.materialize coordinate output) fuel table (next output)
          | .position _ => do
              let output ← LazyRevealProbe.sampleHashOutput
              if state.hitAt coordinate output then
                pure none
              else
                runCleanFromTable (state.materialize coordinate output) fuel table
                  (next output)) := by
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      rw [runCleanFromTable, OracleComp.construct_query_bind]
      rfl
  | position position =>
      rw [runCleanFromTable, OracleComp.construct_query_bind]
      rfl

theorem runRawCleanWithCompletionTable_uniform_query_bind
    (state : LazyRevealProbe.State Coordinate) (fuel n : Nat)
    (next : Fin (n + 1) → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runRawCleanWithCompletionTable state fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) (.uniform n)) :
          OracleComp (LazyRevealProbe.World Coordinate) (Fin (n + 1))) >>= next) = (do
      let output ← liftM (unifSpec.query n)
      runRawCleanWithCompletionTable state fuel (next output)) := by
  unfold runRawCleanWithCompletionTable
  rw [LazyRevealProbe.runRaw_uniform_query_bind, bind_assoc]

theorem runRawCleanWithCompletionTable_hashOutput_query_bind
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runRawCleanWithCompletionTable state fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) .hashOutput) :
          OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next) = (do
      let output ← LazyRevealProbe.sampleHashOutput
      runRawCleanWithCompletionTable state fuel (next output)) := by
  unfold runRawCleanWithCompletionTable
  rw [LazyRevealProbe.runRaw_hashOutput_query_bind, bind_assoc]

theorem runRawCleanWithCompletionTable_ensure_query_bind
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat) (coordinate : Coordinate)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runRawCleanWithCompletionTable state fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.ensure coordinate)) : OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      runRawCleanWithCompletionTable (state.ensure coordinate) fuel (next ()) := by
  unfold runRawCleanWithCompletionTable
  rw [LazyRevealProbe.runRaw_ensure_query_bind]

theorem runRawCleanWithCompletionTable_probe_query_bind
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat) (coordinate : Coordinate)
    (candidate : Digest)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runRawCleanWithCompletionTable state fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.probe coordinate candidate)) :
            OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      match fuel with
      | 0 => pure none
      | remaining + 1 =>
          if coordinate ∈ state.revealed then
            runRawCleanWithCompletionTable state remaining (next ())
          else
            runRawCleanWithCompletionTable (state.addPending coordinate candidate)
              remaining (next ()) := by
  unfold runRawCleanWithCompletionTable
  rw [LazyRevealProbe.runRaw_probe_query_bind]
  cases fuel with
  | zero => rfl
  | succ remaining =>
      by_cases hrevealed : coordinate ∈ state.revealed <;> simp [hrevealed]

theorem runRawCleanWithCompletionTable_peek_query_bind
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat) (coordinate : Coordinate)
    (next : Option HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runRawCleanWithCompletionTable state fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.peek coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) (Option HashOutput)) >>= next) =
      runRawCleanWithCompletionTable state fuel (next (state.values coordinate)) := by
  unfold runRawCleanWithCompletionTable
  rw [LazyRevealProbe.runRaw_peek_query_bind]

theorem runRawCleanWithCompletionTable_publish_query_bind
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat) (coordinate : Coordinate)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runRawCleanWithCompletionTable state fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.publish coordinate)) : OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      runRawCleanWithCompletionTable (state.publish coordinate) fuel (next ()) := by
  unfold runRawCleanWithCompletionTable
  rw [LazyRevealProbe.runRaw_publish_query_bind]

theorem runRawCleanWithCompletionTable_reveal_query_bind
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat) (coordinate : Coordinate)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runRawCleanWithCompletionTable state fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.reveal coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next) =
      (match state.values coordinate with
      | some output => runRawCleanWithCompletionTable state fuel (next output)
      | none => do
          let output ← LazyRevealProbe.sampleHashOutput
          if state.hitAt coordinate output then
            pure none
          else
            runRawCleanWithCompletionTable (state.materialize coordinate output)
              fuel (next output)) := by
  unfold runRawCleanWithCompletionTable
  rw [LazyRevealProbe.runRaw_reveal_query_bind]
  cases hvalue : state.values coordinate with
  | some output => rfl
  | none =>
      simp only [bind_assoc]
      apply bind_congr
      intro output
      by_cases hhit : state.hitAt coordinate output <;> simp [hhit]

set_option maxRecDepth 100000 in
theorem evalDist_runCleanFromTable_eq_lazy
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat) :
    𝒟[do
      let base ← ($ᵗ (OtsSecretIndex → HashOutput) :
        ProbComp (OtsSecretIndex → HashOutput))
      runCleanFromTable state fuel (completedStartTable state base) computation] =
    𝒟[runRawCleanWithCompletionTable state fuel computation] := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure value =>
      simp [runCleanFromTable, runRawCleanWithCompletionTable, LazyRevealProbe.runRaw]
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          simp_rw [runCleanFromTable_uniform_query_bind]
          rw [runRawCleanWithCompletionTable_uniform_query_bind]
          calc
            _ = 𝒟[(liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>=
                fun output =>
                  ($ᵗ (OtsSecretIndex → HashOutput) :
                    ProbComp (OtsSecretIndex → HashOutput)) >>= fun base =>
                    runCleanFromTable state fuel (completedStartTable state base)
                      (next output)] :=
              OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
            _ = _ := by
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro output
              exact ih output state fuel
      | hashOutput =>
          simp_rw [runCleanFromTable_hashOutput_query_bind]
          rw [runRawCleanWithCompletionTable_hashOutput_query_bind]
          calc
            _ = 𝒟[LazyRevealProbe.sampleHashOutput >>= fun output =>
                ($ᵗ (OtsSecretIndex → HashOutput) :
                  ProbComp (OtsSecretIndex → HashOutput)) >>= fun base =>
                  runCleanFromTable state fuel (completedStartTable state base)
                    (next output)] :=
              OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
            _ = _ := by
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro output
              exact ih output state fuel
      | ensure coordinate =>
          simp_rw [runCleanFromTable_ensure_query_bind]
          rw [runRawCleanWithCompletionTable_ensure_query_bind]
          simpa using ih () (state.ensure coordinate) fuel
      | probe coordinate candidate =>
          simp_rw [runCleanFromTable_probe_query_bind]
          rw [runRawCleanWithCompletionTable_probe_query_bind]
          cases fuel with
          | zero =>
              exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
                ($ᵗ (OtsSecretIndex → HashOutput) :
                  ProbComp (OtsSecretIndex → HashOutput))
                (by simp) (pure none)
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · simp only [hrevealed, ↓reduceIte]
                exact ih () state remaining
              · simp only [hrevealed, ↓reduceIte]
                simpa using ih () (state.addPending coordinate candidate) remaining
      | peek coordinate =>
          simp_rw [runCleanFromTable_peek_query_bind]
          rw [runRawCleanWithCompletionTable_peek_query_bind]
          exact ih (state.values coordinate) state fuel
      | publish coordinate =>
          simp_rw [runCleanFromTable_publish_query_bind]
          rw [runRawCleanWithCompletionTable_publish_query_bind]
          simpa using ih () (state.publish coordinate) fuel
      | reveal coordinate =>
          simp_rw [runCleanFromTable_reveal_query_bind]
          rw [runRawCleanWithCompletionTable_reveal_query_bind]
          cases hvalue : state.values coordinate with
          | some output =>
              exact ih output state fuel
          | none =>
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
                  calc
                    _ = 𝒟[do
                        let output ← LazyRevealProbe.sampleHashOutput
                        let base ← ($ᵗ (OtsSecretIndex → HashOutput) :
                          ProbComp (OtsSecretIndex → HashOutput))
                        if state.hitAt index.coordinate output then
                          pure none
                        else
                          runCleanFromTable (state.materialize index.coordinate output) fuel
                            (completedStartTable
                              (state.materialize index.coordinate output) base)
                            (next output)] := by
                        simpa [index, OtsSecretIndex.coordinate, runCleanFromTable, hvalue,
                          completedStartTable, LazyRevealProbe.State.materialize] using
                            evalDist_materialize_missing_start_clean_cont
                              state index hvalue (fun nextState table =>
                                runCleanFromTable nextState fuel table (next (table index)))
                    _ = _ := by
                      simp only [index, OtsSecretIndex.coordinate]
                      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                      intro output
                      by_cases hhit : state.hitAt
                        (.chainStart lay tree leafIdx chainIdx) output
                      · simp only [hhit, ↓reduceIte]
                        exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
                          ($ᵗ (OtsSecretIndex → HashOutput) :
                            ProbComp (OtsSecretIndex → HashOutput))
                          (by simp) (pure none)
                      · simp only [hhit, ↓reduceIte]
                        exact ih output (state.materialize
                          (.chainStart lay tree leafIdx chainIdx) output) fuel
              | position position =>
                  let coordinate : Coordinate := .position position
                  let tableSample := ($ᵗ (OtsSecretIndex → HashOutput) :
                    ProbComp (OtsSecretIndex → HashOutput))
                  let outputSample := LazyRevealProbe.sampleHashOutput
                  calc
                    _ = 𝒟[tableSample >>= fun base => outputSample >>= fun output =>
                        if state.hitAt coordinate output then
                          pure none
                        else
                          runCleanFromTable (state.materialize coordinate output) fuel
                            (completedStartTable state base) (next output)] := by
                        apply congrArg evalDist
                        simp [runCleanFromTable, coordinate, tableSample, outputSample]
                    _ = 𝒟[outputSample >>= fun output => tableSample >>= fun base =>
                        if state.hitAt coordinate output then
                          pure none
                        else
                          runCleanFromTable (state.materialize coordinate output) fuel
                            (completedStartTable state base) (next output)] :=
                      OracleComp.DeferredSampling.evalDist_bind_comm tableSample outputSample _
                    _ = _ := by
                      simp only [coordinate]
                      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                      intro output
                      by_cases hhit : state.hitAt (.position position) output
                      · simp only [hhit, ↓reduceIte]
                        exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
                          tableSample (by simp [tableSample]) (pure none)
                      · simp only [hhit, ↓reduceIte]
                        have hleft :
                            (tableSample >>= fun base =>
                              runCleanFromTable
                                (state.materialize (.position position) output) fuel
                                (completedStartTable state base) (next output)) =
                            (tableSample >>= fun base =>
                              runCleanFromTable
                                (state.materialize (.position position) output) fuel
                                (completedStartTable
                                  (state.materialize (.position position) output) base)
                                (next output)) := by
                          apply bind_congr
                          intro base
                          rw [completedStartTable_materialize_position]
                        rw [congrArg evalDist hleft]
                        exact ih output (state.materialize (.position position) output) fuel

theorem runCleanFromTable_bind
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (left : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (next : alpha → OracleComp (LazyRevealProbe.World Coordinate) beta) :
    runCleanFromTable state fuel table (left >>= next) =
      runCleanFromTable state fuel table left >>= fun result =>
        match result with
        | none => pure none
        | some result =>
            runCleanFromTable result.state result.remaining result.table
              (next result.value) := by
  induction left using OracleComp.inductionOn generalizing state fuel with
  | pure value => simp [runCleanFromTable]
  | query_bind input continuation ih =>
      cases input with
      | uniform n =>
          rw [bind_assoc, runCleanFromTable_uniform_query_bind,
            runCleanFromTable_uniform_query_bind]
          simp only [bind_assoc]
          apply bind_congr
          intro output
          exact ih output state fuel
      | hashOutput =>
          rw [bind_assoc, runCleanFromTable_hashOutput_query_bind,
            runCleanFromTable_hashOutput_query_bind]
          simp only [bind_assoc]
          apply bind_congr
          intro output
          exact ih output state fuel
      | ensure coordinate =>
          rw [bind_assoc, runCleanFromTable_ensure_query_bind,
            runCleanFromTable_ensure_query_bind]
          exact ih () (state.ensure coordinate) fuel
      | probe coordinate candidate =>
          rw [bind_assoc, runCleanFromTable_probe_query_bind,
            runCleanFromTable_probe_query_bind]
          cases fuel with
          | zero => simp
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · simp only [hrevealed, ↓reduceIte]
                exact ih () state remaining
              · simp only [hrevealed, ↓reduceIte]
                exact ih () (state.addPending coordinate candidate) remaining
      | peek coordinate =>
          rw [bind_assoc, runCleanFromTable_peek_query_bind,
            runCleanFromTable_peek_query_bind]
          exact ih (state.values coordinate) state fuel
      | publish coordinate =>
          rw [bind_assoc, runCleanFromTable_publish_query_bind,
            runCleanFromTable_publish_query_bind]
          exact ih () (state.publish coordinate) fuel
      | reveal coordinate =>
          rw [bind_assoc, runCleanFromTable_reveal_query_bind,
            runCleanFromTable_reveal_query_bind]
          cases hvalue : state.values coordinate with
          | some output => exact ih output state fuel
          | none =>
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let output := table ⟨lay, tree, leafIdx, chainIdx⟩
                  by_cases hhit : state.hitAt
                      (.chainStart lay tree leafIdx chainIdx) output
                  · simp [output, hhit]
                  · simp only [output, hhit, ↓reduceIte]
                    exact ih output
                      (state.materialize (.chainStart lay tree leafIdx chainIdx) output) fuel
              | position position =>
                  simp only [bind_assoc]
                  apply bind_congr
                  intro output
                  by_cases hhit : state.hitAt (.position position) output
                  · simp [hhit]
                  · simp only [hhit, ↓reduceIte]
                    exact ih output (state.materialize (.position position) output) fuel

def projectCleanOrdinary :
    Option (CleanRunResult (alpha × SplitHashCache)) →
      Option (alpha × QueryCache HashSpec)
  | none => none
  | some result => some (result.value.1, ordinaryQueryCache result.value.2)

def CleanOrdinaryStepRel :
    Option (CleanRunResult (alpha × SplitHashCache)) →
      (alpha × QueryCache HashSpec) → Prop :=
  fun cleanResult ordinaryResult => cleanResult = none ∨
    projectCleanOrdinary cleanResult = some ordinaryResult

def StartTableAgrees (state : LazyRevealProbe.State Coordinate)
    (table : OtsSecretIndex → HashOutput) : Prop :=
  ∀ index output, state.values index.coordinate = some output → output = table index

theorem startTableAgrees_empty (table : OtsSecretIndex → HashOutput) :
    StartTableAgrees (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) table := by
  intro index output hvalue
  simp [LazyRevealProbe.State.empty] at hvalue

theorem StartTableAgrees.lookup
    {state : LazyRevealProbe.State Coordinate}
    {table : OtsSecretIndex → HashOutput} (hagrees : StartTableAgrees state table)
    (index : OtsSecretIndex) :
    state.values index.coordinate = none ∨
      state.values index.coordinate = some (table index) := by
  cases hvalue : state.values index.coordinate with
  | none => exact Or.inl rfl
  | some output => exact Or.inr (congrArg some (hagrees index output hvalue))

theorem StartTableAgrees.ensure
    {state : LazyRevealProbe.State Coordinate}
    {table : OtsSecretIndex → HashOutput} (hagrees : StartTableAgrees state table)
    (coordinate : Coordinate) : StartTableAgrees (state.ensure coordinate) table := by
  exact hagrees

theorem StartTableAgrees.addPending
    {state : LazyRevealProbe.State Coordinate}
    {table : OtsSecretIndex → HashOutput} (hagrees : StartTableAgrees state table)
    (coordinate : Coordinate) (candidate : Digest) :
    StartTableAgrees (state.addPending coordinate candidate) table := by
  exact hagrees

theorem StartTableAgrees.publish
    {state : LazyRevealProbe.State Coordinate}
    {table : OtsSecretIndex → HashOutput} (hagrees : StartTableAgrees state table)
    (coordinate : Coordinate) : StartTableAgrees (state.publish coordinate) table := by
  exact hagrees

theorem StartTableAgrees.materialize_start
    {state : LazyRevealProbe.State Coordinate}
    {table : OtsSecretIndex → HashOutput} (hagrees : StartTableAgrees state table)
    (index : OtsSecretIndex) :
    StartTableAgrees (state.materialize index.coordinate (table index)) table := by
  intro other output hvalue
  by_cases heq : other = index
  · subst other
    simpa [LazyRevealProbe.State.materialize] using hvalue.symm
  · have hcoordinate : other.coordinate ≠ index.coordinate :=
      fun h => heq (OtsSecretIndex.coordinate_injective h)
    apply hagrees other output
    simpa [LazyRevealProbe.State.materialize, hcoordinate] using hvalue

theorem StartTableAgrees.materialize_position
    {state : LazyRevealProbe.State Coordinate}
    {table : OtsSecretIndex → HashOutput} (hagrees : StartTableAgrees state table)
    (position : Position) (output : HashOutput) :
    StartTableAgrees (state.materialize (.position position) output) table := by
  intro index cached hvalue
  apply hagrees index cached
  simpa [LazyRevealProbe.State.materialize, OtsSecretIndex.coordinate] using hvalue

theorem StartTableAgrees.complete_start
    {state : LazyRevealProbe.State Coordinate}
    {table : OtsSecretIndex → HashOutput} (hagrees : StartTableAgrees state table)
    (index : OtsSecretIndex) :
    StartTableAgrees (state.complete index.coordinate (table index)) table := by
  intro other output hvalue
  by_cases heq : other = index
  · subst other
    simpa [LazyRevealProbe.State.complete] using hvalue.symm
  · have hcoordinate : other.coordinate ≠ index.coordinate :=
      fun h => heq (OtsSecretIndex.coordinate_injective h)
    apply hagrees other output
    simpa [LazyRevealProbe.State.complete, hcoordinate] using hvalue

theorem StartTableAgrees.complete_position
    {state : LazyRevealProbe.State Coordinate}
    {table : OtsSecretIndex → HashOutput} (hagrees : StartTableAgrees state table)
    (position : Position) (output : HashOutput) :
    StartTableAgrees (state.complete (.position position) output) table := by
  intro index cached hvalue
  apply hagrees index cached
  simpa [LazyRevealProbe.State.complete, OtsSecretIndex.coordinate] using hvalue

theorem StartTableAgrees.clearPending
    {state : LazyRevealProbe.State Coordinate}
    {table : OtsSecretIndex → HashOutput} (hagrees : StartTableAgrees state table)
    (coordinate : Coordinate) : StartTableAgrees (state.clearPending coordinate) table := by
  exact hagrees

theorem startTableAgrees_of_mem_runCleanFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (hagrees : StartTableAgrees state table)
    (result : CleanRunResult alpha)
    (hresult : some result ∈ support
      (runCleanFromTable state fuel table computation)) :
    result.table = table ∧ StartTableAgrees result.state table := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure value =>
      simp [runCleanFromTable] at hresult
      subst result
      exact ⟨rfl, hagrees⟩
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runCleanFromTable_uniform_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output state fuel hagrees hrest
      | hashOutput =>
          rw [runCleanFromTable_hashOutput_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output state fuel hagrees hrest
      | ensure coordinate =>
          rw [runCleanFromTable_ensure_query_bind] at hresult
          exact ih () (state.ensure coordinate) fuel (hagrees.ensure coordinate) hresult
      | probe coordinate candidate =>
          rw [runCleanFromTable_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · exact ih () state remaining hagrees (by simpa [hrevealed] using hresult)
              · exact ih () (state.addPending coordinate candidate) remaining
                  (hagrees.addPending coordinate candidate) (by simpa [hrevealed] using hresult)
      | peek coordinate =>
          rw [runCleanFromTable_peek_query_bind] at hresult
          exact ih (state.values coordinate) state fuel hagrees hresult
      | publish coordinate =>
          rw [runCleanFromTable_publish_query_bind] at hresult
          exact ih () (state.publish coordinate) fuel (hagrees.publish coordinate) hresult
      | reveal coordinate =>
          rw [runCleanFromTable_reveal_query_bind] at hresult
          cases hvalue : state.values coordinate with
          | some output =>
              rw [hvalue] at hresult
              exact ih output state fuel hagrees hresult
          | none =>
              rw [hvalue] at hresult
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  simp only at hresult
                  let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
                  by_cases hhit : state.hitAt (.chainStart lay tree leafIdx chainIdx)
                      (table ⟨lay, tree, leafIdx, chainIdx⟩)
                  · rw [if_pos hhit] at hresult
                    simp at hresult
                  · rw [if_neg hhit] at hresult
                    exact ih (table index)
                      (state.materialize (.chainStart lay tree leafIdx chainIdx) (table index))
                      fuel (by simpa [index, OtsSecretIndex.coordinate] using
                        hagrees.materialize_start index) (by simpa [index] using hresult)
              | position position =>
                  rw [mem_support_bind_iff] at hresult
                  obtain ⟨output, _houtput, hrest⟩ := hresult
                  by_cases hhit : state.hitAt (.position position) output
                  · simp [hhit] at hrest
                  · exact ih output (state.materialize (.position position) output) fuel
                      (hagrees.materialize_position position output)
                      (by simpa [hhit] using hrest)

theorem projectCleanOrdinary_splitHashQuery
    (input : HashInput) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    projectCleanOrdinary <$>
        runCleanFromTable state fuel table ((splitHashQuery (.ordinary input)).run cache) =
      some <$>
        (randomOracle (spec := HashSpec) input).run (ordinaryQueryCache cache) := by
  rw [splitHashQuery_run_eq]
  cases hlookup : cache (.ordinary input) with
  | some output =>
      simp only
      have hordinary : ordinaryQueryCache cache input = some output := hlookup
      rw [QueryImpl.withCaching_run_some uniformSampleImpl hordinary]
      simp [runCleanFromTable, projectCleanOrdinary]
  | none =>
      simp only
      have hordinary : ordinaryQueryCache cache input = none := hlookup
      rw [QueryImpl.withCaching_run_none uniformSampleImpl hordinary]
      rw [LazyRevealProbe.hashOutputQuery, runCleanFromTable_hashOutput_query_bind]
      simp only [map_bind, Functor.map_map]
      change (LazyRevealProbe.sampleHashOutput >>= fun output =>
          projectCleanOrdinary <$>
            runCleanFromTable state fuel table
              (pure (output,
                Function.update cache (.ordinary input) (some output)))) =
        (fun output => some
          (output, (ordinaryQueryCache cache).cacheQuery input output)) <$>
            LazyRevealProbe.sampleHashOutput
      rw [map_eq_bind_pure_comp]
      apply bind_congr
      intro output
      simp [runCleanFromTable, projectCleanOrdinary, ordinaryQueryCache_update]

set_option maxRecDepth 10000 in
theorem projectCleanOrdinary_simulateQ_ordinaryHashImpl
    (computation : OracleComp HashSpec alpha)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    projectCleanOrdinary <$>
        runCleanFromTable state fuel table
          ((simulateQ ordinaryHashImpl computation).run cache) =
      some <$>
        (simulateQ (randomOracle : QueryImpl HashSpec _) computation).run
          (ordinaryQueryCache cache) := by
  induction computation using OracleComp.inductionOn generalizing state cache fuel with
  | pure value =>
      simp [runCleanFromTable, projectCleanOrdinary]
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
        OracleQuery.input_query, StateT.run_bind, runCleanFromTable_bind]
      rw [show ordinaryHashImpl input = splitHashQuery (.ordinary input) by rfl]
      rw [splitHashQuery_run_eq]
      cases hlookup : cache (.ordinary input) with
      | some output =>
          simp only
          have hordinary : ordinaryQueryCache cache input = some output := hlookup
          rw [QueryImpl.withCaching_run_some uniformSampleImpl hordinary]
          simp only [runCleanFromTable, pure_bind]
          exact ih output state cache fuel
      | none =>
          simp only
          have hordinary : ordinaryQueryCache cache input = none := hlookup
          rw [QueryImpl.withCaching_run_none uniformSampleImpl hordinary]
          rw [LazyRevealProbe.hashOutputQuery, runCleanFromTable_hashOutput_query_bind]
          simp only [map_bind, bind_assoc]
          change (LazyRevealProbe.sampleHashOutput >>= fun output =>
              projectCleanOrdinary <$>
                runCleanFromTable state fuel table
                  ((simulateQ ordinaryHashImpl (next output)).run
                    (Function.update cache (.ordinary input) (some output)))) =
            (LazyRevealProbe.sampleHashOutput >>= fun output =>
              some <$>
                (simulateQ (randomOracle : QueryImpl HashSpec _) (next output)).run
                  ((ordinaryQueryCache cache).cacheQuery input output))
          apply bind_congr
          intro output
          rw [← ordinaryQueryCache_update]
          exact ih output state (Function.update cache (.ordinary input) (some output)) fuel

theorem relTriple_runCleanFromTable_simulateQ_ordinaryHashImpl
    [Inhabited alpha] (computation : OracleComp HashSpec alpha)
    (state : LazyRevealProbe.State Coordinate) (cache : SplitHashCache)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    RelTriple
      (runCleanFromTable state fuel table
        ((simulateQ ordinaryHashImpl computation).run cache))
      ((simulateQ (randomOracle : QueryImpl HashSpec _) computation).run
        (ordinaryQueryCache cache))
      fun cleanResult ordinaryResult =>
        projectCleanOrdinary cleanResult = some ordinaryResult := by
  exact SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_of_project_eq_some_exact
    projectCleanOrdinary (default, ∅)
    (runCleanFromTable state fuel table
      ((simulateQ ordinaryHashImpl computation).run cache))
    ((simulateQ (randomOracle : QueryImpl HashSpec _) computation).run
      (ordinaryQueryCache cache))
    (projectCleanOrdinary_simulateQ_ordinaryHashImpl computation state cache fuel table)

theorem projectCleanOrdinary_revealChainStart
    (index : OtsSecretIndex) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hagrees : state.values index.coordinate = none ∨
      state.values index.coordinate = some (table index))
    (hclean : ¬state.hitAt index.coordinate (table index)) :
    projectCleanOrdinary <$>
        runCleanFromTable state fuel table
          ((revealChainStart index.lay index.tree index.leafIdx index.chainIdx).run cache) =
      pure (some (truncateHash (table index), ordinaryQueryCache cache)) := by
  rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
  simp only [OtsSecretIndex.coordinate] at hagrees hclean ⊢
  rw [revealChainStart, revealCoordinate_run, LazyRevealProbe.revealQuery,
    runCleanFromTable_reveal_query_bind]
  rcases hagrees with hmissing | hvalue
  · rw [hmissing]
    simp [hclean, runCleanFromTable, projectCleanOrdinary,
      ordinaryQueryCache_update_hidden]
  · rw [hvalue]
    simp [runCleanFromTable, projectCleanOrdinary, ordinaryQueryCache_update_hidden]

theorem relTriple_runCleanFromTable_revealChainStart
    (index : OtsSecretIndex) (state : LazyRevealProbe.State Coordinate)
    (cache : SplitHashCache) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hagrees : state.values index.coordinate = none ∨
      state.values index.coordinate = some (table index)) :
    RelTriple
      (runCleanFromTable state fuel table
        ((revealChainStart index.lay index.tree index.leafIdx index.chainIdx).run cache))
      (pure (truncateHash (table index), ordinaryQueryCache cache) :
        ProbComp (Digest × QueryCache HashSpec))
      CleanOrdinaryStepRel := by
  rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
  simp only [OtsSecretIndex.coordinate] at hagrees ⊢
  rw [revealChainStart, revealCoordinate_run, LazyRevealProbe.revealQuery,
    runCleanFromTable_reveal_query_bind]
  rcases hagrees with hmissing | hvalue
  · rw [hmissing]
    by_cases hhit : state.hitAt (.chainStart lay tree leafIdx chainIdx)
        (table ⟨lay, tree, leafIdx, chainIdx⟩)
    · simp [hhit, CleanOrdinaryStepRel]
    · simp [hhit, runCleanFromTable, CleanOrdinaryStepRel, projectCleanOrdinary,
        ordinaryQueryCache_update_hidden]
  · rw [hvalue]
    simp [runCleanFromTable, CleanOrdinaryStepRel, projectCleanOrdinary,
      ordinaryQueryCache_update_hidden]

noncomputable def finishCleanRunFromTable :
    Option (CleanRunResult alpha) → ProbComp (Option (CleanRunResult alpha))
  | none => pure none
  | some result => do
      let finalized ← finalizeCleanFromTable result.state.coordinates.toList
        result.state result.table
      match finalized with
      | none => pure none
      | some (finalState, finalTable) =>
          pure (some ⟨finalState, result.remaining, result.value, finalTable⟩)

theorem startTableAgrees_of_mem_finalizeCleanFromTable
    (coordinates : List Coordinate) (state : LazyRevealProbe.State Coordinate)
    (table : OtsSecretIndex → HashOutput) (hagrees : StartTableAgrees state table)
    (finalState : LazyRevealProbe.State Coordinate)
    (finalTable : OtsSecretIndex → HashOutput)
    (hresult : some (finalState, finalTable) ∈ support
      (finalizeCleanFromTable coordinates state table)) :
    finalTable = table ∧ StartTableAgrees finalState table := by
  induction coordinates generalizing state with
  | nil =>
      simp [finalizeCleanFromTable] at hresult
      obtain ⟨rfl, rfl⟩ := hresult
      exact ⟨rfl, hagrees⟩
  | cons coordinate remaining ih =>
      cases hvalue : state.values coordinate with
      | some output =>
          rw [finalizeCleanFromTable.eq_def] at hresult
          simp only at hresult
          rw [hvalue] at hresult
          exact ih (state.clearPending coordinate) (hagrees.clearPending coordinate) hresult
      | none =>
          rw [finalizeCleanFromTable.eq_def] at hresult
          simp only at hresult
          rw [hvalue] at hresult
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
              simp only at hresult
              by_cases hhit : state.hitAt (.chainStart lay tree leafIdx chainIdx)
                  (table ⟨lay, tree, leafIdx, chainIdx⟩)
              · rw [if_pos hhit] at hresult
                simp at hresult
              · rw [if_neg hhit] at hresult
                exact ih
                  (state.complete (.chainStart lay tree leafIdx chainIdx) (table index))
                  (by simpa [index, OtsSecretIndex.coordinate] using
                    hagrees.complete_start index)
                  (by simpa [index] using hresult)
          | position position =>
              rw [mem_support_bind_iff] at hresult
              obtain ⟨output, _houtput, hrest⟩ := hresult
              by_cases hhit : state.hitAt (.position position) output
              · simp [hhit] at hrest
              · exact ih (state.complete (.position position) output)
                  (hagrees.complete_position position output) (by simpa [hhit] using hrest)

theorem startTableAgrees_of_mem_finishCleanRunFromTable
    (result finalResult : CleanRunResult alpha)
    (hagrees : StartTableAgrees result.state result.table)
    (hresult : some finalResult ∈ support
      (finishCleanRunFromTable (some result))) :
    finalResult.table = result.table ∧ StartTableAgrees finalResult.state result.table := by
  unfold finishCleanRunFromTable at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨finalized, hfinalized, hreturn⟩ := hresult
  cases finalized with
  | none => simp at hreturn
  | some value =>
      rcases value with ⟨finalState, finalTable⟩
      simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at hreturn
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hreturn
      exact startTableAgrees_of_mem_finalizeCleanFromTable result.state.coordinates.toList
        result.state result.table hagrees finalState finalTable hfinalized

theorem startTableAgrees_of_mem_runThenFinalizeCleanFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (hagrees : StartTableAgrees state table)
    (finalResult : CleanRunResult alpha)
    (hresult : some finalResult ∈ support (do
      let result ← runCleanFromTable state fuel table computation
      finishCleanRunFromTable result)) :
    finalResult.table = table ∧ StartTableAgrees finalResult.state table := by
  rw [mem_support_bind_iff] at hresult
  obtain ⟨result, hrun, hfinish⟩ := hresult
  cases result with
  | none => simp [finishCleanRunFromTable] at hfinish
  | some runResult =>
      obtain ⟨rfl, hrunAgrees⟩ := startTableAgrees_of_mem_runCleanFromTable
        computation state fuel table hagrees runResult hrun
      exact startTableAgrees_of_mem_finishCleanRunFromTable runResult finalResult
        hrunAgrees hfinish

noncomputable def detailedExperimentCleanWithCompletionTable
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    ProbComp (Option (CleanRunResult alpha)) := do
  let result ← LazyRevealProbe.detailedExperiment state fuel computation
  match result with
  | .stopped _ => pure none
  | .done hit finalState remaining value =>
      if hit then
        pure none
      else
        (fun base => some ⟨finalState, remaining, value,
          completedStartTable finalState base⟩) <$> sampleOtsHashTable

set_option maxRecDepth 100000 in
theorem evalDist_runThenFinalizeCleanFromTable_eq_detailed
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat) :
    𝒟[do
      let base ← ($ᵗ (OtsSecretIndex → HashOutput) :
        ProbComp (OtsSecretIndex → HashOutput))
      let result ← runCleanFromTable state fuel (completedStartTable state base) computation
      finishCleanRunFromTable result] =
    𝒟[detailedExperimentCleanWithCompletionTable state fuel computation] := by
  have hrun := evalDist_runCleanFromTable_eq_lazy computation state fuel
  calc
    _ = 𝒟[(do
        let base ← ($ᵗ (OtsSecretIndex → HashOutput) :
          ProbComp (OtsSecretIndex → HashOutput))
        runCleanFromTable state fuel (completedStartTable state base) computation) >>=
          finishCleanRunFromTable] := by
      apply congrArg evalDist
      rw [bind_assoc]
    _ = 𝒟[runRawCleanWithCompletionTable state fuel computation >>=
        finishCleanRunFromTable] := by
      rw [evalDist_bind, hrun, ← evalDist_bind]
    _ = _ := by
      unfold runRawCleanWithCompletionTable detailedExperimentCleanWithCompletionTable
        LazyRevealProbe.detailedExperiment
      rw [bind_assoc, bind_assoc]
      rw [evalDist_bind, evalDist_bind]
      apply congrArg
      funext raw
      cases raw with
      | stopped hit => simp [finishCleanRunFromTable, LazyRevealProbe.RawResult.finishDetailed]
      | done rawState remaining value =>
          simp only [LazyRevealProbe.RawResult.finishDetailed, bind_assoc]
          have hfinalize := evalDist_finalizeCleanFromTable_eq_lazy
            rawState.coordinates.toList rawState
          let finish : Option
              (LazyRevealProbe.State Coordinate × (OtsSecretIndex → HashOutput)) →
                ProbComp (Option (CleanRunResult alpha)) := fun finalized =>
            match finalized with
            | none => pure none
            | some (finalState, finalTable) =>
                pure (some (CleanRunResult.mk finalState remaining value finalTable))
          calc
            _ = 𝒟[(do
                let base ← ($ᵗ (OtsSecretIndex → HashOutput) :
                  ProbComp (OtsSecretIndex → HashOutput))
                finalizeCleanFromTable rawState.coordinates.toList rawState
                  (completedStartTable rawState base)) >>= finish] := by
              apply congrArg evalDist
              simp [finishCleanRunFromTable, finish, bind_assoc]
            _ = 𝒟[finalizeCleanWithCompletionTable rawState.coordinates.toList rawState >>=
                finish] := by
              rw [evalDist_bind, hfinalize, ← evalDist_bind]
            _ = _ := by
              apply congrArg evalDist
              unfold finalizeCleanWithCompletionTable LazyRevealProbe.finalizeDetailed
              rw [bind_assoc]
              apply bind_congr
              intro finalized
              rcases finalized with ⟨hit, finalState⟩
              by_cases hhit : hit
              · simp [hhit, finish, sampleOtsHashTable]
              · simp [hhit, finish, sampleOtsHashTable]

end SphincsSecurity.Concrete.OtsProbeSimulation
