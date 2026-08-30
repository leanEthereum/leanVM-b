import SphincsSecurity.Proof.OtsProbeResolvedBoundaryProbability

/-!
# Ordinary boundary failures

The fixed-table detailed interpreter is averaged by drawing each missing chain start only when it
is revealed. Structural values remain lazy. This is the sampling-order bridge needed by the
ordinary first-fire bound.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

set_option maxHeartbeats 20000

noncomputable def runDirectResolvedDetailedWithCompletionTable
    (context : DeferredContext) (fuel : Nat)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    ProbComp (DirectDetailedResult alpha) :=
  OracleComp.construct
    (C := fun _ : OracleComp (LazyRevealProbe.World Coordinate) alpha =>
      DeferredContext → Nat → ProbComp (DirectDetailedResult alpha))
    (fun value context remaining => do
      let base ← sampleOtsHashTable
      pure (.done ⟨context, remaining, value, completedStartTable context.state base⟩))
    (fun input _next recursivelyRun context fuel =>
      match input with
      | .uniform n => do
          let output ← liftM (unifSpec.query n)
          recursivelyRun output context fuel
      | .hashOutput => do
          let output ← LazyRevealProbe.sampleHashOutput
          recursivelyRun output context fuel
      | .ensure coordinate =>
          recursivelyRun () { context with state := context.state.ensure coordinate } fuel
      | .probe coordinate candidate =>
          match fuel with
          | 0 => pure (.stopped .fuelExhausted)
          | remaining + 1 =>
              if coordinate ∈ context.state.revealed then
                recursivelyRun () context remaining
              else
                recursivelyRun ()
                  { context with state := context.state.addPending coordinate candidate }
                  remaining
      | .peek coordinate =>
          recursivelyRun (context.state.values coordinate) context fuel
      | .publish coordinate =>
          recursivelyRun () { context with state := context.state.publish coordinate } fuel
      | .reveal coordinate =>
          match context.state.values coordinate with
          | some output => recursivelyRun output context fuel
          | none =>
              match coordinate with
              | .chainStart _ _ _ _ => do
                  let output ← LazyRevealProbe.sampleHashOutput
                  if context.state.hitAt coordinate output then
                    pure (.stopped .ordinaryHit)
                  else
                    recursivelyRun output
                      { state := context.state.materialize coordinate output
                        values := context.values }
                      fuel
              | .position position =>
                  match context.values position with
                  | some output =>
                      if context.state.hitAt coordinate output then
                        pure (.stopped .privateStructuralHit)
                      else
                        recursivelyRun output
                          { state := context.state.materialize coordinate output
                            values := context.values }
                          fuel
                  | none => do
                      let output ← LazyRevealProbe.sampleHashOutput
                      if context.state.hitAt coordinate output then
                        pure (.stopped .ordinaryHit)
                      else
                        recursivelyRun output
                          { state := context.state.materialize coordinate output
                            values := context.values.install position output }
                          fuel)
    computation context fuel

theorem runDirectResolvedDetailedFromTable_pure
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (value : alpha) :
    runDirectResolvedDetailedFromTable context fuel table
        (pure value : OracleComp (LazyRevealProbe.World Coordinate) alpha) =
      pure (.done ⟨context, fuel, value, table⟩) := by
  rfl

theorem runDirectResolvedDetailedWithCompletionTable_pure
    (context : DeferredContext) (fuel : Nat) (value : alpha) :
    runDirectResolvedDetailedWithCompletionTable context fuel
        (pure value : OracleComp (LazyRevealProbe.World Coordinate) alpha) = (do
      let base ← sampleOtsHashTable
      pure (.done ⟨context, fuel, value, completedStartTable context.state base⟩)) := by
  rw [runDirectResolvedDetailedWithCompletionTable, OracleComp.construct_pure]

theorem runDirectResolvedDetailedWithCompletionTable_uniform_query_bind
    (context : DeferredContext) (fuel n : Nat)
    (next : Fin (n + 1) → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectResolvedDetailedWithCompletionTable context fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) (.uniform n)) :
          OracleComp (LazyRevealProbe.World Coordinate) (Fin (n + 1))) >>= next) = (do
      let output ← liftM (unifSpec.query n)
      runDirectResolvedDetailedWithCompletionTable context fuel (next output)) := by
  rfl

theorem runDirectResolvedDetailedWithCompletionTable_hashOutput_query_bind
    (context : DeferredContext) (fuel : Nat)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectResolvedDetailedWithCompletionTable context fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) .hashOutput) :
          OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next) = (do
      let output ← LazyRevealProbe.sampleHashOutput
      runDirectResolvedDetailedWithCompletionTable context fuel (next output)) := by
  rfl

theorem runDirectResolvedDetailedWithCompletionTable_ensure_query_bind
    (context : DeferredContext) (fuel : Nat) (coordinate : Coordinate)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectResolvedDetailedWithCompletionTable context fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.ensure coordinate)) : OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      runDirectResolvedDetailedWithCompletionTable
        { context with state := context.state.ensure coordinate } fuel (next ()) := by
  rfl

theorem runDirectResolvedDetailedWithCompletionTable_probe_query_bind
    (context : DeferredContext) (fuel : Nat) (coordinate : Coordinate) (candidate : Digest)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectResolvedDetailedWithCompletionTable context fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.probe coordinate candidate)) :
            OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      match fuel with
      | 0 => pure (.stopped .fuelExhausted)
      | remaining + 1 =>
          if coordinate ∈ context.state.revealed then
            runDirectResolvedDetailedWithCompletionTable context remaining (next ())
          else
            runDirectResolvedDetailedWithCompletionTable
              { context with state := context.state.addPending coordinate candidate }
              remaining (next ()) := by
  rfl

theorem runDirectResolvedDetailedWithCompletionTable_peek_query_bind
    (context : DeferredContext) (fuel : Nat) (coordinate : Coordinate)
    (next : Option HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectResolvedDetailedWithCompletionTable context fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.peek coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) (Option HashOutput)) >>= next) =
      runDirectResolvedDetailedWithCompletionTable context fuel
        (next (context.state.values coordinate)) := by
  rfl

theorem runDirectResolvedDetailedWithCompletionTable_publish_query_bind
    (context : DeferredContext) (fuel : Nat) (coordinate : Coordinate)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectResolvedDetailedWithCompletionTable context fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.publish coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      runDirectResolvedDetailedWithCompletionTable
        { context with state := context.state.publish coordinate } fuel (next ()) := by
  rfl

theorem runDirectResolvedDetailedWithCompletionTable_reveal_query_bind
    (context : DeferredContext) (fuel : Nat) (coordinate : Coordinate)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectResolvedDetailedWithCompletionTable context fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.reveal coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next) =
      (match context.state.values coordinate with
      | some output =>
          runDirectResolvedDetailedWithCompletionTable context fuel (next output)
      | none =>
          match coordinate with
          | .chainStart _ _ _ _ => do
              let output ← LazyRevealProbe.sampleHashOutput
              if context.state.hitAt coordinate output then
                pure (.stopped .ordinaryHit)
              else
                runDirectResolvedDetailedWithCompletionTable
                  { state := context.state.materialize coordinate output
                    values := context.values }
                  fuel (next output)
          | .position position =>
              match context.values position with
              | some output =>
                  if context.state.hitAt coordinate output then
                    pure (.stopped .privateStructuralHit)
                  else
                    runDirectResolvedDetailedWithCompletionTable
                      { state := context.state.materialize coordinate output
                        values := context.values }
                      fuel (next output)
              | none => do
                  let output ← LazyRevealProbe.sampleHashOutput
                  if context.state.hitAt coordinate output then
                    pure (.stopped .ordinaryHit)
                  else
                    runDirectResolvedDetailedWithCompletionTable
                      { state := context.state.materialize coordinate output
                        values := context.values.install position output }
                      fuel (next output)) := by
  cases coordinate <;> rfl

private theorem evalDist_sampled_runDirectResolvedDetailed_reveal_chainStart_query_bind
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (ih : ∀ output context fuel,
      𝒟[do
        let base ← sampleOtsHashTable
        let table := completedStartTable context.state base
        runDirectResolvedDetailedFromTable context fuel table (next output)] =
        𝒟[runDirectResolvedDetailedWithCompletionTable context fuel (next output)])
    (context : DeferredContext) (fuel : Nat) :
    𝒟[do
      let base ← sampleOtsHashTable
      let table := completedStartTable context.state base
      runDirectResolvedDetailedFromTable context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.reveal (.chainStart lay tree leafIdx chainIdx))) :
            OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next)] =
      𝒟[runDirectResolvedDetailedWithCompletionTable context fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.reveal (.chainStart lay tree leafIdx chainIdx))) :
            OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next)] := by
  simp_rw [runDirectResolvedDetailedFromTable_reveal_query_bind]
  rw [runDirectResolvedDetailedWithCompletionTable_reveal_query_bind]
  cases hstate : context.state.values (.chainStart lay tree leafIdx chainIdx) with
  | some output => exact ih output context fuel
  | none =>
      let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
      let cont := fun base : OtsSecretIndex → HashOutput =>
        fun output : HashOutput =>
          if context.state.hitAt (.chainStart lay tree leafIdx chainIdx) output then
            pure (.stopped .ordinaryHit)
          else
            runDirectResolvedDetailedFromTable
              { state := context.state.materialize
                  (.chainStart lay tree leafIdx chainIdx) output
                values := context.values }
              fuel (completedStartTable context.state base) (next output)
      have hcell := evalDist_completionTable_bind_cell_extract index cont
      have hstate' : context.state.values index.coordinate = none := by
        simpa [index, OtsSecretIndex.coordinate] using hstate
      calc
        _ = 𝒟[do
            let base ← sampleOtsHashTable
            cont base (base index)] := by
          apply congrArg evalDist
          apply bind_congr
          intro base
          have hlookup : completedStartTable context.state base index = base index := by
            change (context.state.values index.coordinate).getD (base index) = base index
            rw [hstate']
            rfl
          simp only [cont]
          rw [hlookup]
        _ = 𝒟[do
            let output ← LazyRevealProbe.sampleHashOutput
            let base ← sampleOtsHashTable
            cont (Function.update base index output) output] := by
          simpa only [sampleOtsHashTable, LazyRevealProbe.sampleHashOutput] using hcell
        _ = _ := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro output
          by_cases hhit : context.state.hitAt
              (.chainStart lay tree leafIdx chainIdx) output
          · simp only [cont, hhit, ↓reduceIte]
            simpa using evalDist_sampleOtsHashTable_bind_const
              (pure (.stopped .ordinaryHit) : ProbComp (DirectDetailedResult alpha))
          · simp only [cont, hhit, ↓reduceIte]
            have hnext := ih output
              { state := context.state.materialize
                  (.chainStart lay tree leafIdx chainIdx) output
                values := context.values }
              fuel
            have htable (base : OtsSecretIndex → HashOutput) :
                completedStartTable context.state (Function.update base index output) =
                  completedStartTable
                    (context.state.materialize
                      (.chainStart lay tree leafIdx chainIdx) output) base := by
              rw [completedStartTable_update_base_of_missing context.state base index
                output hstate']
              simpa [index, OtsSecretIndex.coordinate] using
                (completedStartTable_materialize_coordinate context.state base index output).symm
            calc
              _ = 𝒟[do
                  let base ← sampleOtsHashTable
                  let table := completedStartTable
                    (context.state.materialize
                      (.chainStart lay tree leafIdx chainIdx) output) base
                  runDirectResolvedDetailedFromTable
                    { state := context.state.materialize
                        (.chainStart lay tree leafIdx chainIdx) output
                      values := context.values }
                    fuel table (next output)] := by
                apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                intro base
                rw [htable base]
              _ = _ := hnext

private theorem evalDist_sampled_runDirectResolvedDetailed_reveal_position_query_bind
    (position : Position)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (ih : ∀ output context fuel,
      𝒟[do
        let base ← sampleOtsHashTable
        let table := completedStartTable context.state base
        runDirectResolvedDetailedFromTable context fuel table (next output)] =
        𝒟[runDirectResolvedDetailedWithCompletionTable context fuel (next output)])
    (context : DeferredContext) (fuel : Nat) :
    𝒟[do
      let base ← sampleOtsHashTable
      let table := completedStartTable context.state base
      runDirectResolvedDetailedFromTable context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.reveal (.position position))) :
            OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next)] =
      𝒟[runDirectResolvedDetailedWithCompletionTable context fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.reveal (.position position))) :
            OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next)] := by
  simp_rw [runDirectResolvedDetailedFromTable_reveal_query_bind]
  rw [runDirectResolvedDetailedWithCompletionTable_reveal_query_bind]
  cases hstate : context.state.values (.position position) with
  | some output => exact ih output context fuel
  | none =>
      cases hprivate : context.values position with
      | some output =>
          by_cases hhit : context.state.hitAt (.position position) output
          · simp only [hprivate, hhit, ↓reduceIte]
            simpa using evalDist_sampleOtsHashTable_bind_const
              (pure (.stopped .privateStructuralHit) :
                ProbComp (DirectDetailedResult alpha))
          · simp only [hprivate, hhit, ↓reduceIte]
            have hnext := ih output
              { state := context.state.materialize (.position position) output
                values := context.values }
              fuel
            calc
              _ = 𝒟[do
                  let base ← sampleOtsHashTable
                  runDirectResolvedDetailedFromTable
                    { state := context.state.materialize (.position position) output
                      values := context.values }
                    fuel
                    (completedStartTable
                      (context.state.materialize (.position position) output) base)
                    (next output)] := by
                apply congrArg evalDist
                apply bind_congr
                intro base
                rw [completedStartTable_materialize_position]
              _ = _ := hnext
      | none =>
          simp only [hprivate]
          calc
            _ = 𝒟[LazyRevealProbe.sampleHashOutput >>= fun output =>
                sampleOtsHashTable >>= fun base =>
                  if context.state.hitAt (.position position) output then
                    pure (.stopped .ordinaryHit)
                  else
                    runDirectResolvedDetailedFromTable
                      { state := context.state.materialize (.position position) output
                        values := context.values.install position output }
                      fuel (completedStartTable context.state base) (next output)] :=
              OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
            _ = _ := by
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro output
              by_cases hhit : context.state.hitAt (.position position) output
              · simp only [hhit, ↓reduceIte]
                simpa using evalDist_sampleOtsHashTable_bind_const
                  (pure (.stopped .ordinaryHit) : ProbComp (DirectDetailedResult alpha))
              · simp only [hhit, ↓reduceIte]
                have hnext := ih output
                  { state := context.state.materialize (.position position) output
                    values := context.values.install position output }
                  fuel
                calc
                  _ = 𝒟[do
                      let base ← sampleOtsHashTable
                      runDirectResolvedDetailedFromTable
                        { state := context.state.materialize (.position position) output
                          values := context.values.install position output }
                        fuel
                        (completedStartTable
                          (context.state.materialize (.position position) output) base)
                        (next output)] := by
                    apply congrArg evalDist
                    apply bind_congr
                    intro base
                    rw [completedStartTable_materialize_position]
                  _ = _ := hnext

private theorem evalDist_sampled_runDirectResolvedDetailed_reveal_query_bind
    (coordinate : Coordinate)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (ih : ∀ output context fuel,
      𝒟[do
        let base ← sampleOtsHashTable
        let table := completedStartTable context.state base
        runDirectResolvedDetailedFromTable context fuel table (next output)] =
        𝒟[runDirectResolvedDetailedWithCompletionTable context fuel (next output)])
    (context : DeferredContext) (fuel : Nat) :
    𝒟[do
      let base ← sampleOtsHashTable
      let table := completedStartTable context.state base
      runDirectResolvedDetailedFromTable context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.reveal coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next)] =
      𝒟[runDirectResolvedDetailedWithCompletionTable context fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.reveal coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next)] := by
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      exact evalDist_sampled_runDirectResolvedDetailed_reveal_chainStart_query_bind
        lay tree leafIdx chainIdx next ih context fuel
  | position position =>
      exact evalDist_sampled_runDirectResolvedDetailed_reveal_position_query_bind
        position next ih context fuel

private def DirectDetailedSamplingEq
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (context : DeferredContext) (fuel : Nat) : Prop :=
  𝒟[do
    let base ← sampleOtsHashTable
    let table := completedStartTable context.state base
    runDirectResolvedDetailedFromTable context fuel table computation] =
    𝒟[runDirectResolvedDetailedWithCompletionTable context fuel computation]

private theorem directDetailedSamplingEq_pure
    (value : alpha) (context : DeferredContext) (fuel : Nat) :
    DirectDetailedSamplingEq
      (pure value : OracleComp (LazyRevealProbe.World Coordinate) alpha) context fuel := by
  unfold DirectDetailedSamplingEq
  simp_rw [runDirectResolvedDetailedFromTable_pure]
  rw [runDirectResolvedDetailedWithCompletionTable_pure]

private theorem directDetailedSamplingEq_uniform_query_bind
    (n : Nat)
    (next : Fin (n + 1) → OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (ih : ∀ output context fuel, DirectDetailedSamplingEq (next output) context fuel)
    (context : DeferredContext) (fuel : Nat) :
    DirectDetailedSamplingEq
      ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) (.uniform n)) :
        OracleComp (LazyRevealProbe.World Coordinate) (Fin (n + 1))) >>= next)
      context fuel := by
  unfold DirectDetailedSamplingEq at ih ⊢
  simp_rw [runDirectResolvedDetailedFromTable_uniform_query_bind]
  rw [runDirectResolvedDetailedWithCompletionTable_uniform_query_bind]
  calc
    _ = 𝒟[(liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>= fun output =>
        sampleOtsHashTable >>= fun base =>
          runDirectResolvedDetailedFromTable context fuel
            (completedStartTable context.state base) (next output)] :=
      OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    _ = _ := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro output
      exact ih output context fuel

private theorem directDetailedSamplingEq_hashOutput_query_bind
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (ih : ∀ output context fuel, DirectDetailedSamplingEq (next output) context fuel)
    (context : DeferredContext) (fuel : Nat) :
    DirectDetailedSamplingEq
      ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) .hashOutput) :
        OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next)
      context fuel := by
  unfold DirectDetailedSamplingEq at ih ⊢
  simp_rw [runDirectResolvedDetailedFromTable_hashOutput_query_bind]
  rw [runDirectResolvedDetailedWithCompletionTable_hashOutput_query_bind]
  calc
    _ = 𝒟[LazyRevealProbe.sampleHashOutput >>= fun output =>
        sampleOtsHashTable >>= fun base =>
          runDirectResolvedDetailedFromTable context fuel
            (completedStartTable context.state base) (next output)] :=
      OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    _ = _ := by
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro output
      exact ih output context fuel

private theorem directDetailedSamplingEq_ensure_query_bind
    (coordinate : Coordinate)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (ih : ∀ output context fuel, DirectDetailedSamplingEq (next output) context fuel)
    (context : DeferredContext) (fuel : Nat) :
    DirectDetailedSamplingEq
      ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
        (.ensure coordinate)) : OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next)
      context fuel := by
  unfold DirectDetailedSamplingEq at ih ⊢
  simp_rw [runDirectResolvedDetailedFromTable_ensure_query_bind]
  rw [runDirectResolvedDetailedWithCompletionTable_ensure_query_bind]
  have hnext := ih () { context with state := context.state.ensure coordinate } fuel
  calc
    _ = 𝒟[do
        let base ← sampleOtsHashTable
        runDirectResolvedDetailedFromTable
          { context with state := context.state.ensure coordinate } fuel
          (completedStartTable (context.state.ensure coordinate) base) (next ())] := by
      apply congrArg evalDist
      apply bind_congr
      intro base
      rw [completedStartTable_ensure]
    _ = _ := hnext

private theorem directDetailedSamplingEq_probe_query_bind
    (coordinate : Coordinate) (candidate : Digest)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (ih : ∀ output context fuel, DirectDetailedSamplingEq (next output) context fuel)
    (context : DeferredContext) (fuel : Nat) :
    DirectDetailedSamplingEq
      ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
        (.probe coordinate candidate)) :
          OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next)
      context fuel := by
  unfold DirectDetailedSamplingEq at ih ⊢
  simp_rw [runDirectResolvedDetailedFromTable_probe_query_bind]
  rw [runDirectResolvedDetailedWithCompletionTable_probe_query_bind]
  cases fuel with
  | zero =>
      simpa using evalDist_sampleOtsHashTable_bind_const
        (pure (.stopped .fuelExhausted) : ProbComp (DirectDetailedResult alpha))
  | succ remaining =>
      by_cases hrevealed : coordinate ∈ context.state.revealed
      · simp only [hrevealed, ↓reduceIte]
        exact ih () context remaining
      · simp only [hrevealed, ↓reduceIte]
        have hnext := ih ()
          { context with state := context.state.addPending coordinate candidate } remaining
        calc
          _ = 𝒟[do
              let base ← sampleOtsHashTable
              runDirectResolvedDetailedFromTable
                { context with state := context.state.addPending coordinate candidate }
                remaining
                (completedStartTable
                  (context.state.addPending coordinate candidate) base) (next ())] := by
            apply congrArg evalDist
            apply bind_congr
            intro base
            rw [completedStartTable_addPending]
          _ = _ := hnext

private theorem directDetailedSamplingEq_peek_query_bind
    (coordinate : Coordinate)
    (next : Option HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (ih : ∀ output context fuel, DirectDetailedSamplingEq (next output) context fuel)
    (context : DeferredContext) (fuel : Nat) :
    DirectDetailedSamplingEq
      ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
        (.peek coordinate)) :
          OracleComp (LazyRevealProbe.World Coordinate) (Option HashOutput)) >>= next)
      context fuel := by
  unfold DirectDetailedSamplingEq at ih ⊢
  simp_rw [runDirectResolvedDetailedFromTable_peek_query_bind]
  rw [runDirectResolvedDetailedWithCompletionTable_peek_query_bind]
  exact ih (context.state.values coordinate) context fuel

private theorem directDetailedSamplingEq_publish_query_bind
    (coordinate : Coordinate)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (ih : ∀ output context fuel, DirectDetailedSamplingEq (next output) context fuel)
    (context : DeferredContext) (fuel : Nat) :
    DirectDetailedSamplingEq
      ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
        (.publish coordinate)) :
          OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next)
      context fuel := by
  unfold DirectDetailedSamplingEq at ih ⊢
  simp_rw [runDirectResolvedDetailedFromTable_publish_query_bind]
  rw [runDirectResolvedDetailedWithCompletionTable_publish_query_bind]
  have hnext := ih () { context with state := context.state.publish coordinate } fuel
  calc
    _ = 𝒟[do
        let base ← sampleOtsHashTable
        runDirectResolvedDetailedFromTable
          { context with state := context.state.publish coordinate } fuel
          (completedStartTable (context.state.publish coordinate) base) (next ())] := by
      apply congrArg evalDist
      apply bind_congr
      intro base
      rw [completedStartTable_publish]
    _ = _ := hnext

private theorem directDetailedSamplingEq_reveal_query_bind
    (coordinate : Coordinate)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (ih : ∀ output context fuel, DirectDetailedSamplingEq (next output) context fuel)
    (context : DeferredContext) (fuel : Nat) :
    DirectDetailedSamplingEq
      ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
        (.reveal coordinate)) :
          OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next)
      context fuel := by
  unfold DirectDetailedSamplingEq at ih ⊢
  exact evalDist_sampled_runDirectResolvedDetailed_reveal_query_bind
    coordinate next ih context fuel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000 in
theorem evalDist_sampled_runDirectResolvedDetailed_eq_completionTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (context : DeferredContext) (fuel : Nat) :
    𝒟[do
      let base ← sampleOtsHashTable
      let table := completedStartTable context.state base
      runDirectResolvedDetailedFromTable context fuel table computation] =
      𝒟[runDirectResolvedDetailedWithCompletionTable context fuel computation] := by
  change DirectDetailedSamplingEq computation context fuel
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value => exact directDetailedSamplingEq_pure value context fuel
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          exact directDetailedSamplingEq_uniform_query_bind n next ih context fuel
      | hashOutput =>
          exact directDetailedSamplingEq_hashOutput_query_bind next ih context fuel
      | ensure coordinate =>
          exact directDetailedSamplingEq_ensure_query_bind coordinate next ih context fuel
      | probe coordinate candidate =>
          exact directDetailedSamplingEq_probe_query_bind coordinate candidate next ih context fuel
      | peek coordinate =>
          exact directDetailedSamplingEq_peek_query_bind coordinate next ih context fuel
      | publish coordinate =>
          exact directDetailedSamplingEq_publish_query_bind coordinate next ih context fuel
      | reveal coordinate =>
          exact directDetailedSamplingEq_reveal_query_bind coordinate next ih context fuel

noncomputable def finishDirectDetailedSafeOrdinaryObserve
    (observe : (OtsSecretIndex → HashOutput) →
      DeferredContext → Nat → alpha → ProbComp Bool) :
    DirectDetailedResult alpha → ProbComp Bool
  | .stopped .ordinaryHit => pure true
  | .stopped _ => pure false
  | .done result => observe result.table result.context result.remaining result.value

noncomputable def runDirectDetailedSafeOrdinaryWithCompletionTable
    (observe : (OtsSecretIndex → HashOutput) →
      DeferredContext → Nat → alpha → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha) : ProbComp Bool :=
  runDirectResolvedDetailedWithCompletionTable context fuel computation >>=
    finishDirectDetailedSafeOrdinaryObserve observe

theorem evalDist_sampled_runDirectDetailedSafeOrdinary_eq_completionTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (observe : (OtsSecretIndex → HashOutput) →
      DeferredContext → Nat → alpha → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) :
    𝒟[(do
        let base ← sampleOtsHashTable
        let table := completedStartTable context.state base
        runDirectResolvedDetailedFromTable context fuel table computation) >>=
          finishDirectDetailedSafeOrdinaryObserve observe] =
      𝒟[runDirectDetailedSafeOrdinaryWithCompletionTable observe context fuel computation] := by
  unfold runDirectDetailedSafeOrdinaryWithCompletionTable
  exact evalDist_bind_eq_of_evalDist_eq
    (evalDist_sampled_runDirectResolvedDetailed_eq_completionTable computation context fuel)
    (finishDirectDetailedSafeOrdinaryObserve observe)

theorem runDirectDetailedSafeOrdinaryWithCompletionTable_pure
    (observe : (OtsSecretIndex → HashOutput) →
      DeferredContext → Nat → alpha → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (value : alpha) :
    runDirectDetailedSafeOrdinaryWithCompletionTable observe context fuel
        (pure value : OracleComp (LazyRevealProbe.World Coordinate) alpha) = (do
      let base ← sampleOtsHashTable
      observe (completedStartTable context.state base) context fuel value) := by
  rw [runDirectDetailedSafeOrdinaryWithCompletionTable,
    runDirectResolvedDetailedWithCompletionTable_pure]
  simp only [bind_assoc, pure_bind, finishDirectDetailedSafeOrdinaryObserve]

theorem runDirectDetailedSafeOrdinaryWithCompletionTable_uniform_query_bind
    (observe : (OtsSecretIndex → HashOutput) →
      DeferredContext → Nat → alpha → ProbComp Bool)
    (context : DeferredContext) (fuel n : Nat)
    (next : Fin (n + 1) → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectDetailedSafeOrdinaryWithCompletionTable observe context fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) (.uniform n)) :
          OracleComp (LazyRevealProbe.World Coordinate) (Fin (n + 1))) >>= next) = (do
      let output ← liftM (unifSpec.query n)
      runDirectDetailedSafeOrdinaryWithCompletionTable observe context fuel (next output)) := by
  rw [runDirectDetailedSafeOrdinaryWithCompletionTable,
    runDirectResolvedDetailedWithCompletionTable_uniform_query_bind, bind_assoc]
  rfl

theorem runDirectDetailedSafeOrdinaryWithCompletionTable_hashOutput_query_bind
    (observe : (OtsSecretIndex → HashOutput) →
      DeferredContext → Nat → alpha → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectDetailedSafeOrdinaryWithCompletionTable observe context fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) .hashOutput) :
          OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next) = (do
      let output ← LazyRevealProbe.sampleHashOutput
      runDirectDetailedSafeOrdinaryWithCompletionTable observe context fuel (next output)) := by
  rw [runDirectDetailedSafeOrdinaryWithCompletionTable,
    runDirectResolvedDetailedWithCompletionTable_hashOutput_query_bind, bind_assoc]
  rfl

theorem runDirectDetailedSafeOrdinaryWithCompletionTable_ensure_query_bind
    (observe : (OtsSecretIndex → HashOutput) →
      DeferredContext → Nat → alpha → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (coordinate : Coordinate)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectDetailedSafeOrdinaryWithCompletionTable observe context fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.ensure coordinate)) : OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      runDirectDetailedSafeOrdinaryWithCompletionTable observe
        { context with state := context.state.ensure coordinate } fuel (next ()) := by
  rw [runDirectDetailedSafeOrdinaryWithCompletionTable,
    runDirectResolvedDetailedWithCompletionTable_ensure_query_bind]
  rfl

theorem runDirectDetailedSafeOrdinaryWithCompletionTable_probe_query_bind
    (observe : (OtsSecretIndex → HashOutput) →
      DeferredContext → Nat → alpha → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (coordinate : Coordinate) (candidate : Digest)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectDetailedSafeOrdinaryWithCompletionTable observe context fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.probe coordinate candidate)) :
            OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      match fuel with
      | 0 => pure false
      | remaining + 1 =>
          if coordinate ∈ context.state.revealed then
            runDirectDetailedSafeOrdinaryWithCompletionTable observe context remaining (next ())
          else
            runDirectDetailedSafeOrdinaryWithCompletionTable observe
              { context with state := context.state.addPending coordinate candidate }
              remaining (next ()) := by
  rw [runDirectDetailedSafeOrdinaryWithCompletionTable,
    runDirectResolvedDetailedWithCompletionTable_probe_query_bind]
  cases fuel with
  | zero => rfl
  | succ remaining =>
      by_cases hrevealed : coordinate ∈ context.state.revealed <;>
        simp only [hrevealed, ↓reduceIte] <;> rfl

theorem runDirectDetailedSafeOrdinaryWithCompletionTable_peek_query_bind
    (observe : (OtsSecretIndex → HashOutput) →
      DeferredContext → Nat → alpha → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (coordinate : Coordinate)
    (next : Option HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectDetailedSafeOrdinaryWithCompletionTable observe context fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.peek coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) (Option HashOutput)) >>= next) =
      runDirectDetailedSafeOrdinaryWithCompletionTable observe context fuel
        (next (context.state.values coordinate)) := by
  rw [runDirectDetailedSafeOrdinaryWithCompletionTable,
    runDirectResolvedDetailedWithCompletionTable_peek_query_bind]
  rfl

theorem runDirectDetailedSafeOrdinaryWithCompletionTable_publish_query_bind
    (observe : (OtsSecretIndex → HashOutput) →
      DeferredContext → Nat → alpha → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (coordinate : Coordinate)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectDetailedSafeOrdinaryWithCompletionTable observe context fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.publish coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      runDirectDetailedSafeOrdinaryWithCompletionTable observe
        { context with state := context.state.publish coordinate } fuel (next ()) := by
  rw [runDirectDetailedSafeOrdinaryWithCompletionTable,
    runDirectResolvedDetailedWithCompletionTable_publish_query_bind]
  rfl

theorem runDirectDetailedSafeOrdinaryWithCompletionTable_reveal_query_bind
    (observe : (OtsSecretIndex → HashOutput) →
      DeferredContext → Nat → alpha → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (coordinate : Coordinate)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) alpha) :
    runDirectDetailedSafeOrdinaryWithCompletionTable observe context fuel
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.reveal coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next) =
      (match context.state.values coordinate with
      | some output =>
          runDirectDetailedSafeOrdinaryWithCompletionTable observe context fuel (next output)
      | none =>
          match coordinate with
          | .chainStart _ _ _ _ => do
              let output ← LazyRevealProbe.sampleHashOutput
              if context.state.hitAt coordinate output then pure true
              else
                runDirectDetailedSafeOrdinaryWithCompletionTable observe
                  { state := context.state.materialize coordinate output
                    values := context.values }
                  fuel (next output)
          | .position position =>
              match context.values position with
              | some output =>
                  if context.state.hitAt coordinate output then pure false
                  else
                    runDirectDetailedSafeOrdinaryWithCompletionTable observe
                      { state := context.state.materialize coordinate output
                        values := context.values }
                      fuel (next output)
              | none => do
                  let output ← LazyRevealProbe.sampleHashOutput
                  if context.state.hitAt coordinate output then pure true
                  else
                    runDirectDetailedSafeOrdinaryWithCompletionTable observe
                      { state := context.state.materialize coordinate output
                        values := context.values.install position output }
                      fuel (next output)) := by
  rw [runDirectDetailedSafeOrdinaryWithCompletionTable,
    runDirectResolvedDetailedWithCompletionTable_reveal_query_bind]
  cases hstate : context.state.values coordinate with
  | some output => rfl
  | none =>
      cases coordinate with
      | chainStart lay tree leafIdx chainIdx =>
          simp only [bind_assoc]
          apply bind_congr
          intro output
          by_cases hhit : context.state.hitAt
              (.chainStart lay tree leafIdx chainIdx) output <;>
            simp only [hhit, ↓reduceIte] <;> rfl
      | position position =>
          cases hprivate : context.values position with
          | some output =>
              by_cases hhit : context.state.hitAt (.position position) output <;>
                simp only [hprivate, hhit, ↓reduceIte] <;> rfl
          | none =>
              simp only [hprivate, bind_assoc]
              apply bind_congr
              intro output
              by_cases hhit : context.state.hitAt (.position position) output <;>
                simp only [hhit, ↓reduceIte] <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 200000 in
set_option linter.constructorNameAsVariable false in
theorem probEvent_runDirectDetailedSafeOrdinaryWithCompletionTable_le
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (observe : (OtsSecretIndex → HashOutput) →
      DeferredContext → Nat → alpha → ProbComp Bool)
    (hobserve : ∀ (context : DeferredContext) (fuel : Nat) (value : alpha),
      Pr[fun hit : Bool => hit = true | do
        let base ← sampleOtsHashTable
        observe (completedStartTable context.state base) context fuel value] ≤
        ((fuel + context.state.pending.card : Nat) : ℝ≥0∞) *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹)
    (context : DeferredContext) (fuel : Nat) :
    Pr[fun hit : Bool => hit = true |
        runDirectDetailedSafeOrdinaryWithCompletionTable observe context fuel computation] ≤
      ((fuel + context.state.pending.card : Nat) : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      rw [runDirectDetailedSafeOrdinaryWithCompletionTable_pure]
      exact hobserve context fuel value
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runDirectDetailedSafeOrdinaryWithCompletionTable_uniform_query_bind]
          exact probEvent_bind_le_of_forall_le fun output _ => ih output context fuel
      | hashOutput =>
          rw [runDirectDetailedSafeOrdinaryWithCompletionTable_hashOutput_query_bind]
          exact probEvent_bind_le_of_forall_le fun output _ => ih output context fuel
      | ensure coordinate =>
          rw [runDirectDetailedSafeOrdinaryWithCompletionTable_ensure_query_bind]
          simpa only [LazyRevealProbe.State.pending_card_ensure] using
            ih () { context with state := context.state.ensure coordinate } fuel
      | probe coordinate candidate =>
          rw [runDirectDetailedSafeOrdinaryWithCompletionTable_probe_query_bind]
          cases fuel with
          | zero => simp
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · simp only [hrevealed, ↓reduceIte]
                refine (ih () context remaining).trans ?_
                have hnat : remaining + context.state.pending.card ≤
                    remaining + 1 + context.state.pending.card := by omega
                exact mul_le_mul_of_nonneg_right (by exact_mod_cast hnat) zero_le
              · simp only [hrevealed, ↓reduceIte]
                refine (ih ()
                  { context with state := context.state.addPending coordinate candidate }
                  remaining).trans ?_
                have hnat : remaining +
                    (context.state.addPending coordinate candidate).pending.card ≤
                    remaining + 1 + context.state.pending.card := by
                  have := context.state.pending_card_addPending_le coordinate candidate
                  omega
                exact mul_le_mul_of_nonneg_right (by exact_mod_cast hnat) zero_le
      | peek coordinate =>
          rw [runDirectDetailedSafeOrdinaryWithCompletionTable_peek_query_bind]
          exact ih (context.state.values coordinate) context fuel
      | publish coordinate =>
          rw [runDirectDetailedSafeOrdinaryWithCompletionTable_publish_query_bind]
          exact ih () { context with state := context.state.publish coordinate } fuel
      | reveal coordinate =>
          rw [runDirectDetailedSafeOrdinaryWithCompletionTable_reveal_query_bind]
          cases hstate : context.state.values coordinate with
          | some output => exact ih output context fuel
          | none =>
              simp only
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  refine (probEvent_bind_le_probEvent_add
                    (mx := LazyRevealProbe.sampleHashOutput)
                    (my := fun output =>
                      if context.state.hitAt
                          (.chainStart lay tree leafIdx chainIdx) output then
                        pure true
                      else
                        runDirectDetailedSafeOrdinaryWithCompletionTable observe
                          { state := context.state.materialize
                              (.chainStart lay tree leafIdx chainIdx) output
                            values := context.values }
                          fuel (next output))
                    (q := fun hit : Bool => hit = true)
                    (p := context.state.hitAt (.chainStart lay tree leafIdx chainIdx))
                    (ε := ((fuel + (context.state.pendingAway
                      (.chainStart lay tree leafIdx chainIdx)).card : Nat) : ℝ≥0∞) *
                        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ?_).trans ?_
                  · intro output _houtput hmiss
                    simp only [hmiss, ↓reduceIte]
                    simpa only [LazyRevealProbe.State.pending_card_materialize] using
                      ih output
                        { state := context.state.materialize
                            (.chainStart lay tree leafIdx chainIdx) output
                          values := context.values }
                        fuel
                  · refine add_le_add
                      (LazyRevealProbe.probEvent_sampleHashOutput_hitAt_le context.state
                        (.chainStart lay tree leafIdx chainIdx)) le_rfl |>.trans ?_
                    calc
                      ((context.state.pendingAt
                            (.chainStart lay tree leafIdx chainIdx)).card : ℝ≥0∞) *
                            ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
                          ((fuel + (context.state.pendingAway
                            (.chainStart lay tree leafIdx chainIdx)).card : Nat) : ℝ≥0∞) *
                            ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ =
                        (((context.state.pendingAt
                            (.chainStart lay tree leafIdx chainIdx)).card + fuel +
                            (context.state.pendingAway
                              (.chainStart lay tree leafIdx chainIdx)).card : Nat) : ℝ≥0∞) *
                            ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
                              push_cast
                              ring
                      _ ≤ ((fuel + context.state.pending.card : Nat) : ℝ≥0∞) *
                            ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
                        have hsplit := context.state.pendingAway_card_add_pendingAt_card_le
                          (.chainStart lay tree leafIdx chainIdx)
                        have hnat :
                            (context.state.pendingAt
                              (.chainStart lay tree leafIdx chainIdx)).card + fuel +
                                (context.state.pendingAway
                                  (.chainStart lay tree leafIdx chainIdx)).card ≤
                              fuel + context.state.pending.card := by omega
                        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hnat) zero_le
              | position position =>
                  simp only
                  cases hprivate : context.values position with
                  | some output =>
                      by_cases hhit : context.state.hitAt (.position position) output
                      · simp [hhit]
                      · simp only [hhit, ↓reduceIte]
                        refine (ih output
                          { state := context.state.materialize (.position position) output
                            values := context.values }
                          fuel).trans ?_
                        have hsplit := context.state.pendingAway_card_add_pendingAt_card_le
                          (.position position)
                        have hnat : fuel +
                            (context.state.pendingAway (.position position)).card ≤
                              fuel + context.state.pending.card := by omega
                        simpa only [LazyRevealProbe.State.pending_card_materialize] using
                          mul_le_mul_of_nonneg_right (by exact_mod_cast hnat) zero_le
                  | none =>
                      refine (probEvent_bind_le_probEvent_add
                        (mx := LazyRevealProbe.sampleHashOutput)
                        (my := fun output =>
                          if context.state.hitAt (.position position) output then
                            pure true
                          else
                            runDirectDetailedSafeOrdinaryWithCompletionTable observe
                              { state := context.state.materialize
                                  (.position position) output
                                values := context.values.install position output }
                              fuel (next output))
                        (q := fun hit : Bool => hit = true)
                        (p := context.state.hitAt (.position position))
                        (ε := ((fuel + (context.state.pendingAway
                          (.position position)).card : Nat) : ℝ≥0∞) *
                            ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ?_).trans ?_
                      · intro output _houtput hmiss
                        simp only [hmiss, ↓reduceIte]
                        simpa only [LazyRevealProbe.State.pending_card_materialize] using
                          ih output
                            { state := context.state.materialize
                                (.position position) output
                              values := context.values.install position output }
                            fuel
                      · refine add_le_add
                          (LazyRevealProbe.probEvent_sampleHashOutput_hitAt_le context.state
                            (.position position)) le_rfl |>.trans ?_
                        calc
                          ((context.state.pendingAt (.position position)).card : ℝ≥0∞) *
                                ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
                              ((fuel + (context.state.pendingAway
                                (.position position)).card : Nat) : ℝ≥0∞) *
                                ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ =
                            (((context.state.pendingAt (.position position)).card + fuel +
                                (context.state.pendingAway
                                  (.position position)).card : Nat) : ℝ≥0∞) *
                                ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
                                  push_cast
                                  ring
                          _ ≤ ((fuel + context.state.pending.card : Nat) : ℝ≥0∞) *
                                ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
                            have hsplit := context.state.pendingAway_card_add_pendingAt_card_le
                              (.position position)
                            have hnat :
                                (context.state.pendingAt (.position position)).card + fuel +
                                    (context.state.pendingAway
                                      (.position position)).card ≤
                                  fuel + context.state.pending.card := by omega
                            exact mul_le_mul_of_nonneg_right
                              (by exact_mod_cast hnat) zero_le

theorem probEvent_runDirectDetailedSafeOrdinaryFinalize_le
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (context : DeferredContext) (fuel : Nat) :
    Pr[fun hit : Bool => hit = true |
        runDirectDetailedSafeOrdinaryWithCompletionTable
          (fun _ nextContext _ _ => LazyRevealProbe.finalize nextContext.state)
          context fuel computation] ≤
      ((fuel + context.state.pending.card : Nat) : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  apply probEvent_runDirectDetailedSafeOrdinaryWithCompletionTable_le
  intro nextContext remaining value
  have hdist :
      𝒟[do
        let _base ← sampleOtsHashTable
        LazyRevealProbe.finalize nextContext.state] =
        𝒟[LazyRevealProbe.finalize nextContext.state] :=
    evalDist_sampleOtsHashTable_bind_const _
  refine (OracleComp.probEvent_congr' (fun _ _ => Iff.rfl) hdist).le.trans ?_
  refine (LazyRevealProbe.finalize_probability_le nextContext.state).trans ?_
  have hnat : nextContext.state.pending.card ≤
      remaining + nextContext.state.pending.card := by omega
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hnat) zero_le

def DirectDetailedResult.toRawResult :
    DirectDetailedResult alpha → LazyRevealProbe.RawResult Coordinate alpha
  | .stopped .ordinaryHit => .stopped true
  | .stopped _ => .stopped false
  | .done result => .done result.context.state result.remaining result.value

set_option maxRecDepth 100000 in
set_option maxHeartbeats 200000 in
theorem evalDist_toRawResult_runDirectResolvedDetailedWithCompletionTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat) :
    𝒟[DirectDetailedResult.toRawResult <$>
        runDirectResolvedDetailedWithCompletionTable
          (directDeferredContext state) fuel computation] =
      𝒟[LazyRevealProbe.runRaw state fuel computation] := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure value =>
      rw [runDirectResolvedDetailedWithCompletionTable_pure]
      calc
        _ = 𝒟[sampleOtsHashTable >>= fun _ =>
            (pure (.done state fuel value) :
              ProbComp (LazyRevealProbe.RawResult Coordinate alpha))] := by
          apply congrArg evalDist
          rw [map_bind]
          apply bind_congr
          intro base
          rfl
        _ = 𝒟[pure (.done state fuel value)] :=
          evalDist_sampleOtsHashTable_bind_const _
        _ = _ := rfl
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runDirectResolvedDetailedWithCompletionTable_uniform_query_bind,
            LazyRevealProbe.runRaw_uniform_query_bind, map_bind]
          apply evalDist_bind_congr
          intro output _houtput
          exact ih output state fuel
      | hashOutput =>
          rw [runDirectResolvedDetailedWithCompletionTable_hashOutput_query_bind,
            LazyRevealProbe.runRaw_hashOutput_query_bind, map_bind]
          apply evalDist_bind_congr
          intro output _houtput
          exact ih output state fuel
      | ensure coordinate =>
          rw [runDirectResolvedDetailedWithCompletionTable_ensure_query_bind,
            LazyRevealProbe.runRaw_ensure_query_bind]
          simpa [directDeferredContext, directDeferredValues_ensure] using
            ih () (state.ensure coordinate) fuel
      | probe coordinate candidate =>
          rw [runDirectResolvedDetailedWithCompletionTable_probe_query_bind,
            LazyRevealProbe.runRaw_probe_query_bind]
          cases fuel with
          | zero => simp [DirectDetailedResult.toRawResult]
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · simp only [directDeferredContext, hrevealed, ↓reduceIte]
                exact ih () state remaining
              · simp only [directDeferredContext, hrevealed, ↓reduceIte]
                simpa [directDeferredContext, directDeferredValues_addPending] using
                  ih () (state.addPending coordinate candidate) remaining
      | peek coordinate =>
          rw [runDirectResolvedDetailedWithCompletionTable_peek_query_bind,
            LazyRevealProbe.runRaw_peek_query_bind]
          exact ih (state.values coordinate) state fuel
      | publish coordinate =>
          rw [runDirectResolvedDetailedWithCompletionTable_publish_query_bind,
            LazyRevealProbe.runRaw_publish_query_bind]
          simpa [directDeferredContext, directDeferredValues_publish] using
            ih () (state.publish coordinate) fuel
      | reveal coordinate =>
          rw [runDirectResolvedDetailedWithCompletionTable_reveal_query_bind,
            LazyRevealProbe.runRaw_reveal_query_bind]
          cases hstate : state.values coordinate with
          | some output =>
              simp only [directDeferredContext, hstate]
              exact ih output state fuel
          | none =>
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  simp only [directDeferredContext, hstate, map_bind]
                  apply evalDist_bind_congr
                  intro output _houtput
                  by_cases hhit : state.hitAt
                      (.chainStart lay tree leafIdx chainIdx) output
                  · simp [hhit, DirectDetailedResult.toRawResult]
                  · simp only [hhit, ↓reduceIte]
                    have hcontext :
                        { state := state.materialize
                            (.chainStart lay tree leafIdx chainIdx) output
                          values := directDeferredValues state } =
                          directDeferredContext
                            (state.materialize
                              (.chainStart lay tree leafIdx chainIdx) output) := by
                      congr 1
                    rw [hcontext]
                    exact ih output
                      (state.materialize
                        (.chainStart lay tree leafIdx chainIdx) output) fuel
              | position position =>
                  simp only [directDeferredContext, directDeferredValues, hstate,
                    map_bind]
                  apply evalDist_bind_congr
                  intro output _houtput
                  by_cases hhit : state.hitAt (.position position) output
                  · simp [hhit, DirectDetailedResult.toRawResult]
                  · simp only [hhit, ↓reduceIte]
                    have hcontext :
                        { state := state.materialize (.position position) output
                          values := (directDeferredValues state).install position output } =
                          directDeferredContext
                            (state.materialize (.position position) output) := by
                      simp [directDeferredContext,
                        directDeferredValues_materialize_position]
                    rw [hcontext]
                    exact ih output (state.materialize (.position position) output) fuel

theorem finishDirectDetailedSafeOrdinaryFinalize_eq_rawFinish
    (result : DirectDetailedResult alpha) :
    finishDirectDetailedSafeOrdinaryObserve
        (fun _ context _ _ => LazyRevealProbe.finalize context.state) result =
      result.toRawResult.finish := by
  cases result with
  | stopped reason => cases reason <;> rfl
  | done result => rfl

theorem evalDist_runDirectDetailedSafeOrdinaryFinalize_eq_runRawFinish
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat) :
    𝒟[runDirectDetailedSafeOrdinaryWithCompletionTable
        (fun _ context _ _ => LazyRevealProbe.finalize context.state)
        (directDeferredContext state) fuel computation] =
      𝒟[LazyRevealProbe.runRaw state fuel computation >>=
        LazyRevealProbe.RawResult.finish] := by
  unfold runDirectDetailedSafeOrdinaryWithCompletionTable
  calc
    _ = 𝒟[(DirectDetailedResult.toRawResult <$>
          runDirectResolvedDetailedWithCompletionTable
            (directDeferredContext state) fuel computation) >>=
        LazyRevealProbe.RawResult.finish] := by
      apply congrArg evalDist
      rw [map_eq_bind_pure_comp, bind_assoc]
      apply bind_congr
      intro result
      exact finishDirectDetailedSafeOrdinaryFinalize_eq_rawFinish result
    _ = _ := evalDist_bind_eq_of_evalDist_eq
      (evalDist_toRawResult_runDirectResolvedDetailedWithCompletionTable computation state fuel)
      LazyRevealProbe.RawResult.finish

theorem stopped_false_mem_support_runRaw_of_fuelExhausted_detailed
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (hresult : DirectDetailedResult.stopped .fuelExhausted ∈ support
      (runDirectResolvedDetailedWithCompletionTable
        (directDeferredContext state) fuel computation)) :
    LazyRevealProbe.RawResult.stopped false ∈ support
      (LazyRevealProbe.runRaw state fuel computation) := by
  have hmapped : LazyRevealProbe.RawResult.stopped false ∈ support
      (DirectDetailedResult.toRawResult <$>
        runDirectResolvedDetailedWithCompletionTable
          (directDeferredContext state) fuel computation) := by
    rw [support_map]
    exact ⟨.stopped .fuelExhausted, hresult, rfl⟩
  exact (mem_support_iff_of_evalDist_eq
    (evalDist_toRawResult_runDirectResolvedDetailedWithCompletionTable computation state fuel)
    (.stopped false)).mp hmapped

theorem fuelExhausted_not_mem_support_detailed_of_runRaw
    (computation : OracleComp (LazyRevealProbe.World Coordinate) alpha)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (hnotStopped : LazyRevealProbe.RawResult.stopped false ∉ support
      (LazyRevealProbe.runRaw state fuel computation)) :
    DirectDetailedResult.stopped .fuelExhausted ∉ support
      (runDirectResolvedDetailedWithCompletionTable
        (directDeferredContext state) fuel computation) := by
  intro hresult
  exact hnotStopped
    (stopped_false_mem_support_runRaw_of_fuelExhausted_detailed computation state fuel hresult)

end SphincsSecurity.Concrete.OtsProbeSimulation
