import SphincsSecurity.Proof.OtsProbePrivateValueProbeRecords

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def runPrivateErasedPrefix
    (target : Position)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    ProbComp (Option (ResolvedRunResult alpha)) :=
  OracleComp.construct
    (C := fun _ : OracleComp (LazyRevealProbe.World Coordinate) alpha =>
      DeferredContext → Nat → (OtsSecretIndex → HashOutput) →
        ProbComp (Option (ResolvedRunResult alpha)))
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
              if coordinate = .position target ∨ coordinate ∈ context.state.revealed then
                recursivelyRun () context remaining table
              else
                recursivelyRun ()
                  { context with state := context.state.addPending coordinate candidate }
                  remaining table
      | .peek coordinate =>
          recursivelyRun (context.state.values coordinate) context fuel table
      | .publish coordinate =>
          recursivelyRun ()
            { context with state := context.state.publish coordinate } fuel table
      | .reveal coordinate => do
          let resolved ← match coordinate with
            | .chainStart lay tree leafIdx chainIdx =>
                pure (resolveDeferredChainStart table ⟨lay, tree, leafIdx, chainIdx⟩ context)
            | .position position => resolveDeferredReveal table position context
          match resolved with
          | none => pure none
          | some resolved =>
              recursivelyRun resolved.output
                { state := context.state.materialize coordinate resolved.output
                  values := resolved.values }
                fuel table)
    computation context fuel table

theorem runPrivateErasedPrefix_uniform_query_bind
    (target : Position) (context : DeferredContext) (fuel n : Nat)
    (table : OtsSecretIndex → HashOutput)
    (next : Fin (n + 1) → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runPrivateErasedPrefix target context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) (.uniform n)) :
          OracleComp (LazyRevealProbe.World Coordinate) (Fin (n + 1))) >>= next) = (do
      let output ← liftM (unifSpec.query n)
      runPrivateErasedPrefix target context fuel table (next output)) := by
  rw [runPrivateErasedPrefix, OracleComp.construct_query_bind]
  rfl

theorem runPrivateErasedPrefix_hashOutput_query_bind
    (target : Position) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runPrivateErasedPrefix target context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) .hashOutput) :
          OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next) = (do
      let output ← LazyRevealProbe.sampleHashOutput
      runPrivateErasedPrefix target context fuel table (next output)) := by
  rw [runPrivateErasedPrefix, OracleComp.construct_query_bind]
  rfl

theorem runPrivateErasedPrefix_ensure_query_bind
    (target : Position) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runPrivateErasedPrefix target context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.ensure coordinate)) : OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      runPrivateErasedPrefix target
        { context with state := context.state.ensure coordinate } fuel table (next ()) := by
  rw [runPrivateErasedPrefix, OracleComp.construct_query_bind]
  rfl

theorem runPrivateErasedPrefix_probe_query_bind
    (target : Position) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate) (candidate : Digest)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runPrivateErasedPrefix target context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.probe coordinate candidate)) :
            OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      match fuel with
      | 0 => pure none
      | remaining + 1 =>
          if coordinate = .position target ∨ coordinate ∈ context.state.revealed then
            runPrivateErasedPrefix target context remaining table (next ())
          else
            runPrivateErasedPrefix target
              { context with state := context.state.addPending coordinate candidate }
              remaining table (next ()) := by
  rw [runPrivateErasedPrefix, OracleComp.construct_query_bind]
  rfl

theorem runPrivateErasedPrefix_peek_query_bind
    (target : Position) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (next : Option HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runPrivateErasedPrefix target context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.peek coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) (Option HashOutput)) >>= next) =
      runPrivateErasedPrefix target context fuel table
        (next (context.state.values coordinate)) := by
  rw [runPrivateErasedPrefix, OracleComp.construct_query_bind]
  rfl

theorem runPrivateErasedPrefix_publish_query_bind
    (target : Position) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runPrivateErasedPrefix target context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.publish coordinate)) : OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      runPrivateErasedPrefix target
        { context with state := context.state.publish coordinate } fuel table (next ()) := by
  rw [runPrivateErasedPrefix, OracleComp.construct_query_bind]
  rfl

theorem runPrivateErasedPrefix_reveal_query_bind
    (target : Position) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runPrivateErasedPrefix target context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.reveal coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next) = (do
      let resolved ← match coordinate with
        | .chainStart lay tree leafIdx chainIdx =>
            pure (resolveDeferredChainStart table ⟨lay, tree, leafIdx, chainIdx⟩ context)
        | .position position => resolveDeferredReveal table position context
      match resolved with
      | none => pure none
      | some resolved =>
          runPrivateErasedPrefix target
            { state := context.state.materialize coordinate resolved.output
              values := resolved.values }
            fuel table (next resolved.output)) := by
  cases coordinate <;> rw [runPrivateErasedPrefix, OracleComp.construct_query_bind] <;> rfl

theorem evalDist_runPrivateErasedPrefix_replacePrivatePosition
    (target : Position) (before after : HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (h : PrivatePositionReplaceable target before after context)
    (hsafe : computation.IsQueryBoundP (IsPrivatePositionDisclosure target) 0) :
    evalDist (runPrivateErasedPrefix target (replacePrivatePosition target after context) fuel table computation) =
      evalDist (Option.map (replacePrivateRunResult target after) <$> runPrivateErasedPrefix target context fuel table computation) := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value => simp [runPrivateErasedPrefix, replacePrivateRunResult]
  | query_bind query next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hsafe
      have hquery : ¬IsPrivatePositionDisclosure target query := by simpa using hsafe.1
      have hnext : ∀ output, (next output).IsQueryBoundP (IsPrivatePositionDisclosure target) 0 := by
        intro output
        simpa using hsafe.2 output
      cases query with
      | uniform n =>
          rw [runPrivateErasedPrefix_uniform_query_bind, runPrivateErasedPrefix_uniform_query_bind, map_bind]
          apply evalDist_bind_congr
          intro output _
          exact ih output context fuel h (hnext output)
      | hashOutput =>
          rw [runPrivateErasedPrefix_hashOutput_query_bind, runPrivateErasedPrefix_hashOutput_query_bind, map_bind]
          apply evalDist_bind_congr
          intro output _
          exact ih output context fuel h (hnext output)
      | ensure coordinate =>
          rw [runPrivateErasedPrefix_ensure_query_bind, runPrivateErasedPrefix_ensure_query_bind]
          exact ih () { context with state := context.state.ensure coordinate } fuel h (hnext ())
      | peek coordinate =>
          rw [runPrivateErasedPrefix_peek_query_bind, runPrivateErasedPrefix_peek_query_bind]
          exact ih _ context fuel h (hnext _)
      | publish coordinate =>
          rw [runPrivateErasedPrefix_publish_query_bind, runPrivateErasedPrefix_publish_query_bind]
          exact ih () { context with state := context.state.publish coordinate } fuel h (hnext ())
      | probe coordinate digest =>
          rw [runPrivateErasedPrefix_probe_query_bind, runPrivateErasedPrefix_probe_query_bind]
          cases fuel with
          | zero => simp
          | succ remaining =>
              dsimp only [replacePrivatePosition]
              split_ifs with hrevealed
              · exact ih () context remaining h (hnext ())
              · exact ih () { context with state := context.state.addPending coordinate digest } remaining
                  (h.addPending coordinate digest (by
                    intro hexpose
                    exact hrevealed (Or.inl hexpose.1))) (hnext ())
      | reveal coordinate =>
          rw [runPrivateErasedPrefix_reveal_query_bind, runPrivateErasedPrefix_reveal_query_bind]
          have hne : coordinate ≠ .position target := hquery
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              simp only [resolveDeferredChainStart_replacePrivatePosition, pure_bind]
              cases hresolved : resolveDeferredChainStart table ⟨lay, tree, leafIdx, chainIdx⟩ context with
              | none => simp
              | some result =>
                  have hvalues : result.values = context.values := by
                    unfold resolveDeferredChainStart at hresolved
                    dsimp only at hresolved
                    split at hresolved <;> split_ifs at hresolved <;> simp_all
                    all_goals rw [← hresolved]
                  have hcontinue := h.materialize_other (.chainStart lay tree leafIdx chainIdx) result.output result.values
                    (by simp) (hvalues ▸ h.2.1)
                  exact ih result.output _ fuel hcontinue (hnext result.output)
          | position position =>
              have hposition : position ≠ target := fun heq => hne (congrArg Coordinate.position heq)
              rw [evalDist_bind, evalDist_resolveDeferredReveal_replacePrivatePosition target position before after table
                context h, ← evalDist_bind, bind_map_left, map_bind]
              apply evalDist_bind_congr
              intro option hoption
              cases option with
              | none => simp
              | some result =>
                  have hvalue := privateValue_preserved_by_resolveDeferredReveal target position before table context result
                    h.1 h.2.1 hoption
                  have hcontinue := h.materialize_other (.position position) result.output result.values hne hvalue
                  simpa only [Option.map, replacePrivateResolution, replacePrivatePosition, Option.some.injEq, hposition, ↓reduceIte] using
                    ih result.output _ fuel hcontinue (hnext result.output)

noncomputable def privateErasedPrefixValue
    (target : Position) (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) : ProbComp (Option (Nat × α)) :=
  (fun result => result.map (fun result => (result.remaining, result.value))) <$>
    runPrivateErasedPrefix target context fuel table computation

theorem evalDist_privateErasedPrefixValue_replace
    (target : Position) (before after : HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hstate : context.state.values (.position target) = none)
    (hpending : context.state.pendingAt (.position target) = ∅)
    (hsafe : computation.IsQueryBoundP (IsPrivatePositionDisclosure target) 0) :
    evalDist (privateErasedPrefixValue target (replacePrivatePosition target before context) fuel table computation) =
      evalDist (privateErasedPrefixValue target (replacePrivatePosition target after context) fuel table computation) := by
  have h : PrivatePositionReplaceable target before after (replacePrivatePosition target before context) := by
    refine ⟨hstate, ?_, ?_, ?_⟩
    · simp [replacePrivatePosition, DeferredStructuralValues.install]
    all_goals simp [replacePrivatePosition, LazyRevealProbe.State.hitAt, hpending]
  have hdist := evalDist_runPrivateErasedPrefix_replacePrivatePosition target before after computation
    (replacePrivatePosition target before context) fuel table h hsafe
  have hdist' : evalDist (runPrivateErasedPrefix target (replacePrivatePosition target after context) fuel table computation) =
      evalDist (Option.map (replacePrivateRunResult target after) <$>
        runPrivateErasedPrefix target (replacePrivatePosition target before context) fuel table computation) := by
    simpa [replacePrivatePosition, DeferredStructuralValues.install] using hdist
  unfold privateErasedPrefixValue
  rw [evalDist_map, evalDist_map, hdist', evalDist_map, Functor.map_map]
  congr 1
  funext result
  cases result <;> rfl

theorem runPrivateErasedPrefix_query_bind_of_not_target_probe
    (target : Position) (input : LazyRevealProbe.Query Coordinate)
    (next : (LazyRevealProbe.World Coordinate).Range input → OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hprobe : ¬IsPrivatePositionProbe target input) :
    runPrivateErasedPrefix target context fuel table ((liftM (OracleSpec.query input) : OracleComp (LazyRevealProbe.World Coordinate) _) >>= next) =
      (runResolvedFromTable context fuel table (liftM (OracleSpec.query input)) >>= fun result =>
        match result with
        | none => pure none
        | some result => runPrivateErasedPrefix target result.context result.remaining result.table (next result.value)) := by
  cases input with
  | probe coordinate digest =>
      have hne : coordinate ≠ .position target := hprobe
      simp only [runPrivateErasedPrefix_probe_query_bind, runResolvedFromTable, OracleComp.construct_query]
      cases fuel with
      | zero => rfl
      | succ fuel =>
          simp only [hne, false_or]
          split_ifs <;> rfl
  | reveal coordinate =>
      rw [runPrivateErasedPrefix_reveal_query_bind]
      cases coordinate <;>
        simp only [runResolvedFromTable, OracleComp.construct_query, bind_assoc] <;>
        apply bind_congr <;> intro result <;> cases result <;> rfl
  | uniform n => simp [runPrivateErasedPrefix_uniform_query_bind, runResolvedFromTable]
  | hashOutput => simp [runPrivateErasedPrefix_hashOutput_query_bind, runResolvedFromTable]
  | ensure coordinate => rfl
  | peek coordinate => rfl
  | publish coordinate => rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
