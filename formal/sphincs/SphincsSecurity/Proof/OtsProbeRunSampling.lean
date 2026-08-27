import SphincsSecurity.Proof.OtsProbeCompletionSampling

/-!
# Finite-table deferral through one-time probing runs

The clean eager interpreter reads missing chain starts from one finite table. All uniform draws and
all ordinary or structural random-oracle outputs remain lazy. Its result retains the hidden state,
probe fuel and table needed by finalization.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

noncomputable local instance runSampleableOtsHashTable :
    SampleableType (OtsSecretIndex → HashOutput) :=
  SampleableType.ofFintype (OtsSecretIndex → HashOutput)

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
      else do
        let base ← ($ᵗ (OtsSecretIndex → HashOutput) :
          ProbComp (OtsSecretIndex → HashOutput))
        pure (some ⟨finalState, remaining, value,
          completedStartTable finalState base⟩)

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
              · simp [hhit, finish]
              · simp [hhit, finish]

end SphincsSecurity.Concrete.OtsProbeSimulation
