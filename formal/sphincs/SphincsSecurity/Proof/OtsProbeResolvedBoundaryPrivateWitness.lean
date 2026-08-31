import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateHindsightWeighted

/-!
# Private first-fire witnesses

The existing detailed interpreter records only the cause of a stop. The ordinal first-fire proof
also needs the structural position and full output that caused a private stop. This parallel
interpreter retains those two values and erases exactly to the existing detailed interpreter.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

structure PrivateHitWitness where
  position : Position
  output : HashOutput
deriving DecidableEq

inductive DirectWitnessResult (alpha : Type) where
  | stoppedFuel
  | stoppedOrdinary
  | stoppedPrivate (witness : PrivateHitWitness)
  | done (result : ResolvedRunResult alpha)

def DirectWitnessResult.erase : DirectWitnessResult alpha → DirectDetailedResult alpha
  | .stoppedFuel => .stopped .fuelExhausted
  | .stoppedOrdinary => .stopped .ordinaryHit
  | .stoppedPrivate _ => .stopped .privateStructuralHit
  | .done result => .done result

noncomputable def runDirectResolvedWitnessFromTable
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    ProbComp (DirectWitnessResult alpha) :=
  OracleComp.construct
    (C := fun _ : OracleComp (LazyRevealProbe.World Coordinate) alpha =>
      DeferredContext → Nat → (OtsSecretIndex → HashOutput) →
        ProbComp (DirectWitnessResult alpha))
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
          | 0 => pure .stoppedFuel
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
                    pure .stoppedOrdinary
                  else
                    recursivelyRun output
                      { state := context.state.materialize coordinate output
                        values := context.values }
                      fuel table
              | .position position =>
                  match context.values position with
                  | some output =>
                      if context.state.hitAt coordinate output then
                        pure (.stoppedPrivate ⟨position, output⟩)
                      else
                        recursivelyRun output
                          { state := context.state.materialize coordinate output
                            values := context.values }
                          fuel table
                  | none => do
                      let output ← LazyRevealProbe.sampleHashOutput
                      if context.state.hitAt coordinate output then
                        pure .stoppedOrdinary
                      else
                        recursivelyRun output
                          { state := context.state.materialize coordinate output
                            values := context.values.install position output }
                          fuel table)
    computation context fuel table

theorem runDirectResolvedWitnessFromTable_uniform_query_bind
    (context : DeferredContext) (fuel n : Nat)
    (table : OtsSecretIndex → HashOutput)
    (next : Fin (n + 1) → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectResolvedWitnessFromTable context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.uniform n)) :
            OracleComp (LazyRevealProbe.World Coordinate) (Fin (n + 1))) >>= next) = (do
      let output ← liftM (unifSpec.query n)
      runDirectResolvedWitnessFromTable context fuel table (next output)) := by
  rfl

theorem runDirectResolvedWitnessFromTable_hashOutput_query_bind
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectResolvedWitnessFromTable context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          .hashOutput) :
            OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next) = (do
      let output ← LazyRevealProbe.sampleHashOutput
      runDirectResolvedWitnessFromTable context fuel table (next output)) := by
  rfl

theorem runDirectResolvedWitnessFromTable_ensure_query_bind
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectResolvedWitnessFromTable context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.ensure coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      runDirectResolvedWitnessFromTable
        { context with state := context.state.ensure coordinate }
        fuel table (next ()) := by
  rfl

theorem runDirectResolvedWitnessFromTable_probe_query_bind
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (candidate : Digest)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectResolvedWitnessFromTable context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.probe coordinate candidate)) :
            OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      match fuel with
      | 0 => pure .stoppedFuel
      | remaining + 1 =>
          if coordinate ∈ context.state.revealed then
            runDirectResolvedWitnessFromTable context remaining table (next ())
          else
            runDirectResolvedWitnessFromTable
              { context with
                state := context.state.addPending coordinate candidate }
              remaining table (next ()) := by
  rfl

theorem runDirectResolvedWitnessFromTable_peek_query_bind
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (next : Option HashOutput →
      OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectResolvedWitnessFromTable context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.peek coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) (Option HashOutput)) >>= next) =
      runDirectResolvedWitnessFromTable context fuel table
        (next (context.state.values coordinate)) := by
  rfl

theorem runDirectResolvedWitnessFromTable_publish_query_bind
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectResolvedWitnessFromTable context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.publish coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      runDirectResolvedWitnessFromTable
        { context with state := context.state.publish coordinate }
        fuel table (next ()) := by
  rfl

theorem runDirectResolvedWitnessFromTable_reveal_query_bind
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectResolvedWitnessFromTable context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.reveal coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next) =
      (match context.state.values coordinate with
      | some output =>
          runDirectResolvedWitnessFromTable context fuel table (next output)
      | none =>
          match coordinate with
          | .chainStart lay tree leafIdx chainIdx =>
              let output := table ⟨lay, tree, leafIdx, chainIdx⟩
              if context.state.hitAt coordinate output then
                pure .stoppedOrdinary
              else
                runDirectResolvedWitnessFromTable
                  { state := context.state.materialize coordinate output
                    values := context.values }
                  fuel table (next output)
          | .position position =>
              match context.values position with
              | some output =>
                  if context.state.hitAt coordinate output then
                    pure (.stoppedPrivate ⟨position, output⟩)
                  else
                    runDirectResolvedWitnessFromTable
                      { state := context.state.materialize coordinate output
                        values := context.values }
                      fuel table (next output)
              | none => do
                  let output ← LazyRevealProbe.sampleHashOutput
                  if context.state.hitAt coordinate output then
                    pure .stoppedOrdinary
                  else
                    runDirectResolvedWitnessFromTable
                      { state := context.state.materialize coordinate output
                        values := context.values.install position output }
                      fuel table (next output)) := by
  cases coordinate <;> rfl

set_option maxRecDepth 100000 in
theorem map_erase_runDirectResolvedWitnessFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) :
    DirectWitnessResult.erase <$>
        runDirectResolvedWitnessFromTable context fuel table computation =
      runDirectResolvedDetailedFromTable context fuel table computation := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      simp [runDirectResolvedWitnessFromTable, runDirectResolvedDetailedFromTable,
        DirectWitnessResult.erase]
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runDirectResolvedWitnessFromTable_uniform_query_bind,
            runDirectResolvedDetailedFromTable_uniform_query_bind, map_bind]
          apply bind_congr
          intro output
          exact ih output context fuel
      | hashOutput =>
          rw [runDirectResolvedWitnessFromTable_hashOutput_query_bind,
            runDirectResolvedDetailedFromTable_hashOutput_query_bind, map_bind]
          apply bind_congr
          intro output
          exact ih output context fuel
      | ensure coordinate =>
          rw [runDirectResolvedWitnessFromTable_ensure_query_bind,
            runDirectResolvedDetailedFromTable_ensure_query_bind]
          exact ih () { context with state := context.state.ensure coordinate } fuel
      | probe coordinate candidate =>
          rw [runDirectResolvedWitnessFromTable_probe_query_bind,
            runDirectResolvedDetailedFromTable_probe_query_bind]
          cases fuel with
          | zero => simp [DirectWitnessResult.erase]
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
          rw [runDirectResolvedWitnessFromTable_peek_query_bind,
            runDirectResolvedDetailedFromTable_peek_query_bind]
          exact ih (context.state.values coordinate) context fuel
      | publish coordinate =>
          rw [runDirectResolvedWitnessFromTable_publish_query_bind,
            runDirectResolvedDetailedFromTable_publish_query_bind]
          exact ih () { context with state := context.state.publish coordinate } fuel
      | reveal coordinate =>
          rw [runDirectResolvedWitnessFromTable_reveal_query_bind,
            runDirectResolvedDetailedFromTable_reveal_query_bind]
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
                  · simp [output, hhit, DirectWitnessResult.erase]
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
                      · simp [hprivate, hhit, DirectWitnessResult.erase]
                      · simp only [hprivate, hhit, ↓reduceIte]
                        exact ih output
                          { state := context.state.materialize (.position position) output
                            values := context.values }
                          fuel
                  | none =>
                      simp only [hprivate, map_bind]
                      apply bind_congr
                      intro output
                      by_cases hhit : context.state.hitAt (.position position) output
                      · simp [hhit, DirectWitnessResult.erase]
                      · simp only [hhit, ↓reduceIte]
                        exact ih output
                          { state := context.state.materialize (.position position) output
                            values := context.values.install position output }
                          fuel

set_option maxRecDepth 100000 in
theorem candidateListHits_of_stoppedPrivate_mem_runDirectResolvedWitnessFromTable
    (candidates : List Probe)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (witness : PrivateHitWitness)
    (hcovered : PendingCoveredBy candidates context)
    (hbound : computation.IsQueryBoundP (IsUncoveredProbe candidates) 0)
    (hresult : DirectWitnessResult.stoppedPrivate witness ∈ support
      (runDirectResolvedWitnessFromTable context fuel table computation)) :
    candidateListHits witness.position candidates witness.output := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      simp [runDirectResolvedWitnessFromTable] at hresult
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      cases input with
      | uniform n =>
          rw [runDirectResolvedWitnessFromTable_uniform_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, htail⟩ := hresult
          exact ih output context fuel hcovered (hbound.2 output) htail
      | hashOutput =>
          rw [runDirectResolvedWitnessFromTable_hashOutput_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, htail⟩ := hresult
          exact ih output context fuel hcovered (hbound.2 output) htail
      | ensure coordinate =>
          rw [runDirectResolvedWitnessFromTable_ensure_query_bind] at hresult
          exact ih () { context with state := context.state.ensure coordinate } fuel hcovered
            (hbound.2 ()) hresult
      | probe coordinate digest =>
          have hmem : (⟨coordinate, digest⟩ : Probe) ∈ candidates := by
            simpa [IsUncoveredProbe] using hbound.1
          have htail : (next ()).IsQueryBoundP (IsUncoveredProbe candidates) 0 := by
            simpa [IsUncoveredProbe] using hbound.2 ()
          cases fuel with
          | zero => simp [runDirectResolvedWitnessFromTable_probe_query_bind] at hresult
          | succ remaining =>
              rw [runDirectResolvedWitnessFromTable_probe_query_bind] at hresult
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · simp only [hrevealed, ↓reduceIte] at hresult
                exact ih () context remaining hcovered htail hresult
              · simp only [hrevealed, ↓reduceIte] at hresult
                exact ih ()
                  { context with state := context.state.addPending coordinate digest }
                  remaining (hcovered.addPending_of_mem ⟨coordinate, digest⟩ hmem) htail
                  hresult
      | peek coordinate =>
          rw [runDirectResolvedWitnessFromTable_peek_query_bind] at hresult
          exact ih (context.state.values coordinate) context fuel hcovered (hbound.2 _) hresult
      | publish coordinate =>
          rw [runDirectResolvedWitnessFromTable_publish_query_bind] at hresult
          exact ih () { context with state := context.state.publish coordinate } fuel hcovered
            (hbound.2 ()) hresult
      | reveal coordinate =>
          rw [runDirectResolvedWitnessFromTable_reveal_query_bind] at hresult
          cases hstate : context.state.values coordinate with
          | some output =>
              simp only [hstate] at hresult
              exact ih output context fuel hcovered (hbound.2 output) hresult
          | none =>
              simp only [hstate] at hresult
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let output := table ⟨lay, tree, leafIdx, chainIdx⟩
                  by_cases hhit : context.state.hitAt
                      (.chainStart lay tree leafIdx chainIdx) output
                  · simp [output, hhit] at hresult
                  · simp only [output, hhit, ↓reduceIte] at hresult
                    exact ih output
                      { state := context.state.materialize
                          (.chainStart lay tree leafIdx chainIdx) output
                        values := context.values }
                      fuel (hcovered.clearPending (.chainStart lay tree leafIdx chainIdx))
                        (hbound.2 output) hresult
              | position position =>
                  cases hprivate : context.values position with
                  | some output =>
                      by_cases hhit : context.state.hitAt (.position position) output
                      · simp [hprivate, hhit] at hresult
                        subst witness
                        have hpending :
                            (Coordinate.position position, truncateHash output) ∈
                              context.state.pending := by
                          rw [← LazyRevealProbe.State.mem_pendingAt_iff]
                          exact hhit
                        obtain ⟨candidate, hcandidate, hcoordinate, hdigest⟩ :=
                          hcovered (Coordinate.position position, truncateHash output) hpending
                        exact candidateListHits_of_mem position output candidate candidates
                          hcandidate hcoordinate hdigest
                      · simp only [hprivate, hhit, ↓reduceIte] at hresult
                        exact ih output
                          { state := context.state.materialize (.position position) output
                            values := context.values }
                          fuel (hcovered.clearPending (.position position)) (hbound.2 output)
                            hresult
                  | none =>
                      simp only [hprivate, mem_support_bind_iff] at hresult
                      obtain ⟨output, _houtput, htailResult⟩ := hresult
                      by_cases hhit : context.state.hitAt (.position position) output
                      · simp [hhit] at htailResult
                      · simp only [hhit, ↓reduceIte] at htailResult
                        exact ih output
                          { state := context.state.materialize (.position position) output
                            values := context.values.install position output }
                          fuel (hcovered.clearPending (.position position)) (hbound.2 output)
                            htailResult

end SphincsSecurity.Concrete.OtsProbeSimulation
