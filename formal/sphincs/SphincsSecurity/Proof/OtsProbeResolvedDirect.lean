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
                  let resolved ← resolveDeferredPositionValue position context
                  match resolved with
                  | none => pure none
                  | some resolved =>
                      recursivelyRun resolved.output
                        { state := context.state.materialize coordinate resolved.output
                          values := resolved.values }
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
              let resolved ← resolveDeferredPositionValue position context
              match resolved with
              | none => pure none
              | some resolved =>
                  runDirectResolvedFromTable
                    { state := context.state.materialize coordinate resolved.output
                      values := resolved.values }
                    fuel table (next resolved.output)) := by
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

theorem resolveDeferredPositionValue_direct_values
    (position : Position) (state : LazyRevealProbe.State Coordinate)
    (result : DeferredResolution)
    (hstate : state.values (.position position) = none)
    (hresult : some result ∈ support
      (resolveDeferredPositionValue position (directDeferredContext state))) :
    result.values = (directDeferredValues state).install position result.output := by
  have hprivate : (directDeferredContext state).values position = none := by
    simpa [directDeferredContext, directDeferredValues] using hstate
  rw [resolveDeferredPositionValue_fresh position (directDeferredContext state)
    (by simpa [directDeferredContext] using hstate) hprivate,
    mem_support_bind_iff] at hresult
  obtain ⟨output, _houtput, hreturn⟩ := hresult
  by_cases hhit : state.hitAt (.position position) output
  · simp [directDeferredContext, hhit] at hreturn
  · simp [directDeferredContext, hhit] at hreturn
    subst result
    rfl

set_option maxRecDepth 100000 in
theorem direct_context_of_mem_runDirectResolvedFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult α)
    (hresult : some result ∈ support
      (runDirectResolvedFromTable (directDeferredContext state) fuel table computation)) :
    result.context = directDeferredContext result.context.state := by
  induction computation using OracleComp.inductionOn generalizing state fuel result with
  | pure value =>
      simp [runDirectResolvedFromTable] at hresult
      subst result
      rfl
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runDirectResolvedFromTable_uniform_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output state fuel result hrest
      | hashOutput =>
          rw [runDirectResolvedFromTable_hashOutput_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output state fuel result hrest
      | ensure coordinate =>
          rw [runDirectResolvedFromTable_ensure_query_bind] at hresult
          have hcontext :
              { directDeferredContext state with state := state.ensure coordinate } =
                directDeferredContext (state.ensure coordinate) := by
            simp [directDeferredContext, directDeferredValues_ensure]
          exact ih () (state.ensure coordinate) fuel result (hcontext ▸ hresult)
      | probe coordinate candidate =>
          rw [runDirectResolvedFromTable_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · exact ih () state remaining result (by
                  simpa [directDeferredContext, hrevealed] using hresult)
              · simp only [directDeferredContext, hrevealed, ↓reduceIte] at hresult
                have hcontext :
                    { directDeferredContext state with
                      state := state.addPending coordinate candidate } =
                      directDeferredContext (state.addPending coordinate candidate) := by
                  simp [directDeferredContext, directDeferredValues_addPending]
                exact ih () (state.addPending coordinate candidate) remaining result
                  (hcontext ▸ hresult)
      | peek coordinate =>
          rw [runDirectResolvedFromTable_peek_query_bind] at hresult
          exact ih (state.values coordinate) state fuel result hresult
      | publish coordinate =>
          rw [runDirectResolvedFromTable_publish_query_bind] at hresult
          exact ih () (state.publish coordinate) fuel result (by
            simpa [directDeferredContext, directDeferredValues_publish] using hresult)
      | reveal coordinate =>
          rw [runDirectResolvedFromTable_reveal_query_bind] at hresult
          cases hvalue : state.values coordinate with
          | some output =>
              exact ih output state fuel result (by
                simpa only [directDeferredContext, hvalue] using hresult)
          | none =>
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
                  let output := table index
                  by_cases hhit : state.hitAt index.coordinate output
                  · change state.hitAt (.chainStart lay tree leafIdx chainIdx)
                        (table ⟨lay, tree, leafIdx, chainIdx⟩) at hhit
                    simp only [directDeferredContext, hvalue, hhit, ↓reduceIte] at hresult
                    simp at hresult
                  · have hcontext :
                        { state := state.materialize index.coordinate output
                          values := directDeferredValues state } =
                          directDeferredContext (state.materialize index.coordinate output) := by
                      simp [directDeferredContext,
                        directDeferredValues_materialize_chainStart]
                    change ¬state.hitAt (.chainStart lay tree leafIdx chainIdx)
                      (table ⟨lay, tree, leafIdx, chainIdx⟩) at hhit
                    simp only [directDeferredContext, hvalue, hhit, ↓reduceIte] at hresult
                    exact ih output (state.materialize index.coordinate output) fuel result
                      (hcontext ▸ hresult)
              | position position =>
                  simp only [directDeferredContext] at hresult
                  rw [hvalue, mem_support_bind_iff] at hresult
                  obtain ⟨resolvedOption, hresolved, hrest⟩ := hresult
                  cases resolvedOption with
                  | none => simp at hrest
                  | some resolved =>
                      simp only at hrest
                      have hvalues := resolveDeferredPositionValue_direct_values position state
                        resolved hvalue hresolved
                      have hcontext :
                          { state := state.materialize (.position position) resolved.output
                            values := resolved.values } =
                            directDeferredContext
                              (state.materialize (.position position) resolved.output) := by
                        rw [hvalues]
                        simp [directDeferredContext,
                          directDeferredValues_materialize_position]
                      exact ih resolved.output
                        (state.materialize (.position position) resolved.output) fuel result
                        (hcontext ▸ hrest)

def ChainValuesMirrored (context : DeferredContext) : Prop :=
  ∀ lay tree leafIdx chainIdx step,
    context.values (.chain lay tree leafIdx chainIdx step) =
      context.state.values (.position (.chain lay tree leafIdx chainIdx step))

theorem chainValuesMirrored_directDeferredContext
    (state : LazyRevealProbe.State Coordinate) :
    ChainValuesMirrored (directDeferredContext state) := by
  intro lay tree leafIdx chainIdx step
  rfl

theorem ChainValuesMirrored.resolve_materialize
    {context : DeferredContext} (hmirror : ChainValuesMirrored context)
    (position : Position) (resolved : DeferredResolution)
    (hresolved : some resolved ∈ support
      (resolveDeferredPositionValue position context)) :
    ChainValuesMirrored
      { state := context.state.materialize (.position position) resolved.output
        values := resolved.values } := by
  intro lay tree leafIdx chainIdx step
  let chainPosition : Position := .chain lay tree leafIdx chainIdx step
  by_cases heq : chainPosition = position
  · subst position
    rw [resolveDeferredPositionValue_installs chainPosition context resolved hresolved]
    change some resolved.output = Function.update context.state.values
      (.position chainPosition) (some resolved.output) (.position chainPosition)
    simp [Function.update]
  · rw [resolveDeferredPositionValue_preserves_other position chainPosition context resolved
        heq hresolved,
      hmirror lay tree leafIdx chainIdx step]
    have hcoordinate : Coordinate.position chainPosition ≠ .position position := by
      intro h
      injection h with h
      exact heq h
    dsimp [chainPosition] at hcoordinate ⊢
    simp [LazyRevealProbe.State.materialize, Function.update, hcoordinate]

set_option maxRecDepth 100000 in
theorem chainValuesMirrored_of_mem_runDirectResolvedFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult α)
    (hmirror : ChainValuesMirrored context)
    (hresult : some result ∈ support
      (runDirectResolvedFromTable context fuel table computation)) :
    ChainValuesMirrored result.context := by
  induction computation using OracleComp.inductionOn generalizing context fuel result with
  | pure value =>
      simp [runDirectResolvedFromTable] at hresult
      subst result
      exact hmirror
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runDirectResolvedFromTable_uniform_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output context fuel result hmirror hrest
      | hashOutput =>
          rw [runDirectResolvedFromTable_hashOutput_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output context fuel result hmirror hrest
      | ensure coordinate =>
          rw [runDirectResolvedFromTable_ensure_query_bind] at hresult
          apply ih () { context with state := context.state.ensure coordinate } fuel result
          · intro lay tree leafIdx chainIdx step
            exact hmirror lay tree leafIdx chainIdx step
          · exact hresult
      | probe coordinate candidate =>
          rw [runDirectResolvedFromTable_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · exact ih () context remaining result hmirror (by
                  simpa [hrevealed] using hresult)
              · apply ih () { context with
                    state := context.state.addPending coordinate candidate } remaining result
                · intro lay tree leafIdx chainIdx step
                  exact hmirror lay tree leafIdx chainIdx step
                · simpa [hrevealed] using hresult
      | peek coordinate =>
          rw [runDirectResolvedFromTable_peek_query_bind] at hresult
          exact ih (context.state.values coordinate) context fuel result hmirror hresult
      | publish coordinate =>
          rw [runDirectResolvedFromTable_publish_query_bind] at hresult
          apply ih () { context with state := context.state.publish coordinate } fuel result
          · intro lay tree leafIdx chainIdx step
            exact hmirror lay tree leafIdx chainIdx step
          · exact hresult
      | reveal coordinate =>
          rw [runDirectResolvedFromTable_reveal_query_bind] at hresult
          cases hvalue : context.state.values coordinate with
          | some output =>
              exact ih output context fuel result hmirror (by simpa [hvalue] using hresult)
          | none =>
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
                  let output := table index
                  by_cases hhit : context.state.hitAt index.coordinate output
                  · change context.state.hitAt (.chainStart lay tree leafIdx chainIdx)
                        (table ⟨lay, tree, leafIdx, chainIdx⟩) at hhit
                    simp [hvalue, hhit] at hresult
                  · change ¬context.state.hitAt (.chainStart lay tree leafIdx chainIdx)
                        (table ⟨lay, tree, leafIdx, chainIdx⟩) at hhit
                    simp only [hvalue, hhit, ↓reduceIte] at hresult
                    apply ih output
                      { state := context.state.materialize index.coordinate output
                        values := context.values }
                      fuel result
                    · intro otherLay otherTree otherLeaf otherChain otherStep
                      simpa [LazyRevealProbe.State.materialize, index,
                        OtsSecretIndex.coordinate] using
                        hmirror otherLay otherTree otherLeaf otherChain otherStep
                    · simpa [index, output, OtsSecretIndex.coordinate] using hresult
              | position position =>
                  rw [hvalue, mem_support_bind_iff] at hresult
                  obtain ⟨resolvedOption, hresolved, hrest⟩ := hresult
                  cases resolvedOption with
                  | none => simp at hrest
                  | some resolved =>
                      simp only at hrest
                      exact ih resolved.output
                        { state := context.state.materialize (.position position) resolved.output
                          values := resolved.values }
                        fuel result (hmirror.resolve_materialize position resolved hresolved) hrest

set_option maxRecDepth 100000 in
theorem raw_done_of_mem_runDirectResolvedFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult α)
    (hresult : some result ∈ support
      (runDirectResolvedFromTable context fuel table computation)) :
    LazyRevealProbe.RawResult.done result.context.state result.remaining result.value ∈
      support (LazyRevealProbe.runRaw context.state fuel computation) := by
  induction computation using OracleComp.inductionOn generalizing context fuel result with
  | pure value =>
      simp [runDirectResolvedFromTable] at hresult
      subst result
      simp [LazyRevealProbe.runRaw]
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runDirectResolvedFromTable_uniform_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, houtput, hrest⟩ := hresult
          rw [LazyRevealProbe.runRaw_uniform_query_bind, mem_support_bind_iff]
          exact ⟨output, houtput, ih output context fuel result hrest⟩
      | hashOutput =>
          rw [runDirectResolvedFromTable_hashOutput_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, houtput, hrest⟩ := hresult
          rw [LazyRevealProbe.runRaw_hashOutput_query_bind, mem_support_bind_iff]
          exact ⟨output, houtput, ih output context fuel result hrest⟩
      | ensure coordinate =>
          rw [runDirectResolvedFromTable_ensure_query_bind] at hresult
          rw [LazyRevealProbe.runRaw_ensure_query_bind]
          exact ih () { context with state := context.state.ensure coordinate } fuel result hresult
      | probe coordinate candidate =>
          rw [runDirectResolvedFromTable_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              rw [LazyRevealProbe.runRaw_probe_query_bind]
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · simp only [hrevealed, ↓reduceIte]
                exact ih () context remaining result (by simpa [hrevealed] using hresult)
              · simp only [hrevealed, ↓reduceIte]
                exact ih () { context with
                  state := context.state.addPending coordinate candidate } remaining result
                    (by simpa [hrevealed] using hresult)
      | peek coordinate =>
          rw [runDirectResolvedFromTable_peek_query_bind] at hresult
          rw [LazyRevealProbe.runRaw_peek_query_bind]
          exact ih (context.state.values coordinate) context fuel result hresult
      | publish coordinate =>
          rw [runDirectResolvedFromTable_publish_query_bind] at hresult
          rw [LazyRevealProbe.runRaw_publish_query_bind]
          exact ih () { context with state := context.state.publish coordinate } fuel result hresult
      | reveal coordinate =>
          rw [runDirectResolvedFromTable_reveal_query_bind] at hresult
          rw [LazyRevealProbe.runRaw_reveal_query_bind]
          cases hvalue : context.state.values coordinate with
          | some output =>
              exact ih output context fuel result (by simpa [hvalue] using hresult)
          | none =>
              simp only
              rw [mem_support_bind_iff]
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
                  let output := table index
                  by_cases hhit : context.state.hitAt index.coordinate output
                  · change context.state.hitAt (.chainStart lay tree leafIdx chainIdx)
                        (table ⟨lay, tree, leafIdx, chainIdx⟩) at hhit
                    simp [hvalue, hhit] at hresult
                  · change ¬context.state.hitAt (.chainStart lay tree leafIdx chainIdx)
                        (table ⟨lay, tree, leafIdx, chainIdx⟩) at hhit
                    simp only [hvalue, hhit, ↓reduceIte] at hresult
                    refine ⟨output, ?_, ?_⟩
                    · simp [LazyRevealProbe.sampleHashOutput]
                    · simp only [index, output, hhit, ↓reduceIte]
                      exact ih output
                        { state := context.state.materialize index.coordinate output
                          values := context.values }
                        fuel result (by
                          simpa [index, output, OtsSecretIndex.coordinate] using hresult)
              | position position =>
                  rw [hvalue, mem_support_bind_iff] at hresult
                  obtain ⟨resolvedOption, hresolved, hrest⟩ := hresult
                  cases resolvedOption with
                  | none => simp at hrest
                  | some resolved =>
                      simp only at hrest
                      refine ⟨resolved.output, ?_, ?_⟩
                      · simp [LazyRevealProbe.sampleHashOutput]
                      · have hnotHit := resolveDeferredPositionValue_not_hit position context
                            resolved hresolved
                        simp only [hnotHit, ↓reduceIte]
                        exact ih resolved.output
                          { state := context.state.materialize (.position position) resolved.output
                            values := resolved.values }
                          fuel result hrest

theorem chainInvariant_of_mem_runDirectResolvedFromTable
    (parameter : PublicParameter) (allowed : Coordinate → Prop)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ResolvedRunResult (α × SplitHashCache))
    (hpreserves : PreservesChainInvariant parameter allowed computation)
    (hinvariant : ChainInvariant parameter allowed context.state cache)
    (hresult : some result ∈ support
      (runDirectResolvedFromTable context fuel table (computation.run cache))) :
    ChainInvariant parameter allowed result.context.state result.value.2 := by
  apply hpreserves context.state cache fuel result.context.state result.remaining
    result.value.1 result.value.2 hinvariant
  exact raw_done_of_mem_runDirectResolvedFromTable
    (computation.run cache) context fuel table result hresult

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
                  have hstate : (directDeferredContext state).state = state := rfl
                  simp only [hstate, hvalue]
                  have hprivate :
                      (directDeferredContext state).values position = none := by
                    simpa [directDeferredContext, directDeferredValues] using hvalue
                  rw [resolveDeferredPositionValue_fresh position
                    (directDeferredContext state) hvalue hprivate]
                  · simp only [map_bind, bind_assoc]
                    apply bind_congr
                    intro output
                    by_cases hhit : state.hitAt (.position position) output
                    · simp [hstate, hhit, projectResolvedRunResult]
                    · simp only [hhit, ↓reduceIte, pure_bind,
                        directDeferredContext]
                      have hcontext :
                          { state := state.materialize (.position position) output,
                            values := (directDeferredValues state).install position output } =
                            directDeferredContext
                              (state.materialize (.position position) output) := by
                        simp [directDeferredContext,
                          directDeferredValues_materialize_position]
                      rw [hcontext]
                      exact ih output (state.materialize (.position position) output) fuel

noncomputable def finishDirectRunIsNone :
    Option (ResolvedRunResult α) → ProbComp Bool := fun result =>
  finishCleanRunIsNone (projectResolvedRunResult result)

set_option maxRecDepth 100000 in
theorem evalDist_runDirectFinishIsNone_eq_runCleanFinishIsNone
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) :
    evalDist (runDirectResolvedFromTable (directDeferredContext state) fuel table computation >>=
        finishDirectRunIsNone) =
      evalDist (runCleanFromTable state fuel table computation >>= finishCleanRunIsNone) := by
  have hprojection := map_projectResolvedRunResult_runDirect_eq_runClean computation state
    fuel table
  unfold finishDirectRunIsNone
  rw [← hprojection, map_eq_bind_pure_comp, bind_assoc]
  rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
