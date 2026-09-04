import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivatePreparationLift

/-!
# Guarded preparation through the direct interpreter

The direct interpreter's private-stop projection is dominated by the guarded finite preparation observer whenever every probe issued by the computation is present in the fixed candidate list.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local instance] Classical.propDecidable

def IsUncoveredProbe (candidates : List Probe) :
    (LazyRevealProbe.World Coordinate).Domain → Prop
  | .probe coordinate digest => ⟨coordinate, digest⟩ ∉ candidates
  | _ => False

instance (candidates : List Probe) : DecidablePred (IsUncoveredProbe candidates)
  | .probe coordinate digest => inferInstanceAs (Decidable (⟨coordinate, digest⟩ ∉ candidates))
  | .uniform _ | .hashOutput | .ensure _ | .peek _ | .publish _ | .reveal _ => isFalse id

noncomputable def runPrivatePreparation
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) : ProbComp Bool :=
  runDirectDetailedPrivateObserve
    (fun nextContext _remaining _value => guardedPreparationObserve candidates nextContext)
    context fuel table computation

theorem runPrivatePreparation_pure
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (value : α) :
    runPrivatePreparation candidates context fuel table (pure value) =
      guardedPreparationObserve candidates context := by
  simp [runPrivatePreparation, runDirectDetailedPrivateObserve,
    runDirectResolvedDetailedFromTable, finishDirectDetailedPrivateObserve]

theorem runPrivatePreparation_uniform_query_bind
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (n : Nat)
    (next : Fin (n + 1) → OracleComp (LazyRevealProbe.World Coordinate) α) :
    runPrivatePreparation candidates context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) (.uniform n)) :
          OracleComp (LazyRevealProbe.World Coordinate) (Fin (n + 1))) >>= next) = (do
      let output ← liftM (unifSpec.query n)
      runPrivatePreparation candidates context fuel table (next output)) := by
  unfold runPrivatePreparation runDirectDetailedPrivateObserve
  rw [runDirectResolvedDetailedFromTable_uniform_query_bind, bind_assoc]

theorem runPrivatePreparation_hashOutput_query_bind
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) α) :
    runPrivatePreparation candidates context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) .hashOutput) :
          OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next) = (do
      let output ← LazyRevealProbe.sampleHashOutput
      runPrivatePreparation candidates context fuel table (next output)) := by
  unfold runPrivatePreparation runDirectDetailedPrivateObserve
  rw [runDirectResolvedDetailedFromTable_hashOutput_query_bind, bind_assoc]

theorem runPrivatePreparation_ensure_query_bind
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) α) :
    runPrivatePreparation candidates context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.ensure coordinate)) :
          OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      runPrivatePreparation candidates
        { context with state := context.state.ensure coordinate }
        fuel table (next ()) := by
  unfold runPrivatePreparation runDirectDetailedPrivateObserve
  rw [runDirectResolvedDetailedFromTable_ensure_query_bind]

theorem runPrivatePreparation_probe_query_bind
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate) (digest : Digest)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) α) :
    runPrivatePreparation candidates context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.probe coordinate digest)) :
          OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      match fuel with
      | 0 => pure false
      | remaining + 1 =>
          if coordinate ∈ context.state.revealed then
            runPrivatePreparation candidates context remaining table (next ())
          else
            runPrivatePreparation candidates
              { context with state := context.state.addPending coordinate digest }
              remaining table (next ()) := by
  unfold runPrivatePreparation runDirectDetailedPrivateObserve
  rw [runDirectResolvedDetailedFromTable_probe_query_bind]
  cases fuel with
  | zero => rfl
  | succ remaining =>
      by_cases hrevealed : coordinate ∈ context.state.revealed <;>
        simp [hrevealed]

theorem runPrivatePreparation_peek_query_bind
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (next : Option HashOutput → OracleComp (LazyRevealProbe.World Coordinate) α) :
    runPrivatePreparation candidates context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.peek coordinate)) :
          OracleComp (LazyRevealProbe.World Coordinate) (Option HashOutput)) >>= next) =
      runPrivatePreparation candidates context fuel table
        (next (context.state.values coordinate)) := by
  unfold runPrivatePreparation runDirectDetailedPrivateObserve
  rw [runDirectResolvedDetailedFromTable_peek_query_bind]

theorem runPrivatePreparation_publish_query_bind
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) α) :
    runPrivatePreparation candidates context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.publish coordinate)) :
          OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      runPrivatePreparation candidates
        { context with state := context.state.publish coordinate }
        fuel table (next ()) := by
  unfold runPrivatePreparation runDirectDetailedPrivateObserve
  rw [runDirectResolvedDetailedFromTable_publish_query_bind]

theorem runPrivatePreparation_reveal_query_bind
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) α) :
    runPrivatePreparation candidates context fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.reveal coordinate)) :
          OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next) =
      (match context.state.values coordinate with
      | some output => runPrivatePreparation candidates context fuel table (next output)
      | none =>
          match coordinate with
          | .chainStart lay tree leafIdx chainIdx =>
              let output := table ⟨lay, tree, leafIdx, chainIdx⟩
              if context.state.hitAt coordinate output then
                pure false
              else
                runPrivatePreparation candidates
                  { state := context.state.materialize coordinate output
                    values := context.values }
                  fuel table (next output)
          | .position position =>
              match context.values position with
              | some output =>
                  if context.state.hitAt coordinate output then
                    pure true
                  else
                    runPrivatePreparation candidates
                      { state := context.state.materialize coordinate output
                        values := context.values }
                      fuel table (next output)
              | none => do
                  let output ← LazyRevealProbe.sampleHashOutput
                  if context.state.hitAt coordinate output then
                    pure false
                  else
                    runPrivatePreparation candidates
                      { state := context.state.materialize coordinate output
                        values := context.values.install position output }
                      fuel table (next output)) := by
  unfold runPrivatePreparation runDirectDetailedPrivateObserve
  rw [runDirectResolvedDetailedFromTable_reveal_query_bind]
  cases hstate : context.state.values coordinate with
  | some output => rfl
  | none =>
      cases coordinate with
      | chainStart lay tree leafIdx chainIdx =>
          by_cases hhit : context.state.hitAt
              (.chainStart lay tree leafIdx chainIdx) (table ⟨lay, tree, leafIdx, chainIdx⟩) <;>
            simp [hhit, finishDirectDetailedPrivateObserve]
      | position position =>
          cases hprivate : context.values position with
          | some output =>
              by_cases hhit : context.state.hitAt (.position position) output <;>
                simp [hprivate, hhit, finishDirectDetailedPrivateObserve]
          | none =>
              simp only [hprivate, bind_assoc]
              apply bind_congr
              intro output
              by_cases hhit : context.state.hitAt (.position position) output <;>
                simp [hhit, finishDirectDetailedPrivateObserve]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_runPrivatePreparation_le_guarded
    (candidates : List Probe)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hcovered : PendingCoveredBy candidates context)
    (hbound : computation.IsQueryBoundP (IsUncoveredProbe candidates) 0) :
    Pr[= true | runPrivatePreparation candidates context fuel table computation] ≤
      Pr[= true | guardedPreparationObserve candidates context] := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      rw [runPrivatePreparation_pure]
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      cases input with
      | uniform n =>
          rw [runPrivatePreparation_uniform_query_bind, ← probEvent_eq_eq_probOutput]
          apply probEvent_bind_le_of_forall_le
          intro output _houtput
          rw [probEvent_eq_eq_probOutput]
          exact ih output context fuel hcovered (hbound.2 output)
      | hashOutput =>
          rw [runPrivatePreparation_hashOutput_query_bind, ← probEvent_eq_eq_probOutput]
          apply probEvent_bind_le_of_forall_le
          intro output _houtput
          rw [probEvent_eq_eq_probOutput]
          exact ih output context fuel hcovered (hbound.2 output)
      | ensure coordinate =>
          rw [runPrivatePreparation_ensure_query_bind]
          calc
            _ ≤ Pr[= true | guardedPreparationObserve candidates
                  { context with state := context.state.ensure coordinate }] :=
              ih () { context with state := context.state.ensure coordinate } fuel
                ((pendingCoveredBy_ensure candidates context coordinate).2 hcovered)
                (hbound.2 ())
            _ = _ := OracleComp.probOutput_congr rfl
              (evalDist_guardedPreparationObserve_ensure candidates context coordinate)
      | probe coordinate digest =>
          rw [runPrivatePreparation_probe_query_bind]
          have hmem : (⟨coordinate, digest⟩ : Probe) ∈ candidates := by
            simpa [IsUncoveredProbe] using hbound.1
          have htail : (next ()).IsQueryBoundP (IsUncoveredProbe candidates) 0 := by
            simpa [IsUncoveredProbe] using hbound.2 ()
          cases fuel with
          | zero => simp
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · simp [hrevealed]
                exact ih () context remaining hcovered htail
              · simp [hrevealed]
                let candidate : Probe := ⟨coordinate, digest⟩
                have hnextCovered := hcovered.addPending_of_mem candidate hmem
                calc
                  _ ≤ Pr[= true | guardedPreparationObserve candidates
                        { context with state := context.state.addPending coordinate digest }] :=
                    ih () { context with state := context.state.addPending coordinate digest }
                      remaining hnextCovered htail
                  _ = _ := OracleComp.probOutput_congr rfl
                    (evalDist_guardedPreparationObserve_addPending_of_mem candidates context
                      candidate hmem)
      | peek coordinate =>
          rw [runPrivatePreparation_peek_query_bind]
          exact ih (context.state.values coordinate) context fuel hcovered (hbound.2 _)
      | publish coordinate =>
          rw [runPrivatePreparation_publish_query_bind]
          calc
            _ ≤ Pr[= true | guardedPreparationObserve candidates
                  { context with state := context.state.publish coordinate }] :=
              ih () { context with state := context.state.publish coordinate } fuel
                ((pendingCoveredBy_publish candidates context coordinate).2 hcovered)
                (hbound.2 ())
            _ = _ := OracleComp.probOutput_congr rfl
              (evalDist_guardedPreparationObserve_publish candidates context coordinate)
      | reveal coordinate =>
          rw [runPrivatePreparation_reveal_query_bind]
          cases hstate : context.state.values coordinate with
          | some output =>
              exact ih output context fuel hcovered (hbound.2 output)
          | none =>
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
                  let output := table index
                  change Pr[= true |
                      if context.state.hitAt index.coordinate output then
                        pure false
                      else
                        runPrivatePreparation candidates
                          { state := context.state.materialize index.coordinate output
                            values := context.values }
                          fuel table (next output)] ≤ _
                  by_cases hhit : context.state.hitAt index.coordinate output
                  · simp [hhit]
                  · simp only [hhit, ↓reduceIte]
                    have hnextCovered : PendingCoveredBy candidates
                        { state := context.state.materialize index.coordinate output
                          values := context.values } :=
                      hcovered.clearPending index.coordinate
                    calc
                      _ ≤ Pr[= true | guardedPreparationObserve candidates
                            { state := context.state.materialize index.coordinate output
                              values := context.values }] :=
                        ih output
                          { state := context.state.materialize index.coordinate output
                            values := context.values }
                          fuel hnextCovered (hbound.2 output)
                      _ ≤ _ := probEvent_guardedPreparationObserve_materializeChainStart_le
                        candidates context index output
              | position position =>
                  cases hprivate : context.values position with
                  | some output =>
                      by_cases hhit : context.state.hitAt (.position position) output
                      · simp only [hprivate, hhit, ↓reduceIte]
                        have hprivateHit : PrivateStructuralHit context :=
                          ⟨position, output, hstate, hprivate, hhit⟩
                        have hguarded := evalDist_guardedPreparationObserve_eq_true_of_privateStructuralHit
                          candidates context hcovered hprivateHit
                        exact le_of_eq (OracleComp.probOutput_congr rfl hguarded.symm)
                      · simp only [hprivate, hhit, ↓reduceIte]
                        have hnextCovered : PendingCoveredBy candidates
                            { state := context.state.materialize (.position position) output
                              values := context.values } :=
                          hcovered.clearPending (.position position)
                        calc
                          _ ≤ Pr[= true | guardedPreparationObserve candidates
                                { state := context.state.materialize (.position position) output
                                  values := context.values }] :=
                            ih output
                              { state := context.state.materialize (.position position) output
                                values := context.values }
                              fuel hnextCovered (hbound.2 output)
                          _ = _ := OracleComp.probOutput_congr rfl
                            (evalDist_guardedPreparationObserve_materializePrivate_eq_of_miss
                              candidates context position output hstate hprivate hhit hcovered)
                  | none =>
                      simp only [hprivate]
                      let resolvedContext : HashOutput → DeferredContext := fun output =>
                        { state := context.state.clearPending (.position position)
                          values := context.values.install position output }
                      let materializedContext : HashOutput → DeferredContext := fun output =>
                        { state := context.state.materialize (.position position) output
                          values := context.values.install position output }
                      let left : HashOutput → ProbComp Bool := fun output =>
                        if context.state.hitAt (.position position) output then
                          pure false
                        else
                          runPrivatePreparation candidates (materializedContext output) fuel table
                            (next output)
                      let right : HashOutput → ProbComp Bool := fun output =>
                        if context.state.hitAt (.position position) output then
                          pure true
                        else
                          guardedPreparationObserve candidates (resolvedContext output)
                      have hbind : Pr[= true | LazyRevealProbe.sampleHashOutput >>= left] ≤
                          Pr[= true | LazyRevealProbe.sampleHashOutput >>= right] := by
                        rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
                        apply probEvent_bind_le_bind_of_forall_le
                        intro output _houtput
                        by_cases hhit : context.state.hitAt (.position position) output
                        · simp [left, right, hhit]
                        · simp only [left, right, hhit, ↓reduceIte]
                          have hresolvedCovered : PendingCoveredBy candidates
                              (resolvedContext output) :=
                            hcovered.clearPending (.position position)
                          have hmaterializedCovered : PendingCoveredBy candidates
                              (materializedContext output) := hresolvedCovered
                          have htail := ih output (materializedContext output) fuel
                            hmaterializedCovered (hbound.2 output)
                          have hresolvedState :
                              (resolvedContext output).state.values (.position position) = none :=
                            hstate
                          have hresolvedPrivate :
                              (resolvedContext output).values position = some output := by
                            simp [resolvedContext, DeferredStructuralValues.install]
                          have hresolvedMiss :
                              ¬(resolvedContext output).state.hitAt (.position position) output :=
                            not_hitAt_clearPending_self context.state (.position position) output
                          have hmaterializedEq :=
                            evalDist_guardedPreparationObserve_materializePrivate_eq_of_miss
                              candidates (resolvedContext output) position output hresolvedState
                              hresolvedPrivate hresolvedMiss hresolvedCovered
                          have hmaterializedContextEq :
                              { state := (resolvedContext output).state.materialize
                                  (.position position) output
                                values := (resolvedContext output).values } =
                                materializedContext output := by
                            simp [resolvedContext, materializedContext,
                              LazyRevealProbe.State.clearPending,
                              LazyRevealProbe.State.materialize,
                              LazyRevealProbe.State.pendingAway]
                          rw [hmaterializedContextEq] at hmaterializedEq
                          rw [probEvent_eq_eq_probOutput, probEvent_eq_eq_probOutput]
                          exact htail.trans (le_of_eq
                            (OracleComp.probOutput_congr rfl hmaterializedEq))
                      have hright : Pr[= true |
                            LazyRevealProbe.sampleHashOutput >>= right] ≤
                          Pr[= true | guardedPreparationObserve candidates context] := by
                        let resolvedRun : ProbComp Bool :=
                          resolveDeferredPositionValue position context >>= fun resolved =>
                            match resolved with
                            | none => pure true
                            | some resolved =>
                                guardedPreparationObserve candidates resolved.toDeferredContext
                        have heq : evalDist (LazyRevealProbe.sampleHashOutput >>= right) =
                            evalDist resolvedRun := by
                          unfold resolvedRun
                          rw [resolveDeferredPositionValue_fresh position context hstate hprivate]
                          simp only [bind_assoc]
                          apply evalDist_bind_congr
                          intro output _houtput
                          by_cases hhit : context.state.hitAt (.position position) output <;>
                            simp [right, resolvedContext, hhit]
                        calc
                          _ = Pr[= true | resolvedRun] :=
                            OracleComp.probOutput_congr rfl heq
                          _ ≤ _ := probEvent_resolve_then_guardedPreparationObserve_le position
                            candidates context
                      exact hbind.trans hright

set_option maxRecDepth 100000 in
theorem pendingCoveredBy_of_done_runDirectResolvedDetailedFromTable
    (candidates : List Probe)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult α)
    (hcovered : PendingCoveredBy candidates context)
    (hbound : computation.IsQueryBoundP (IsUncoveredProbe candidates) 0)
    (hresult : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table computation)) :
    PendingCoveredBy candidates result.context := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      simp [runDirectResolvedDetailedFromTable] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      exact hcovered
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      cases input with
      | uniform n =>
          rw [runDirectResolvedDetailedFromTable_uniform_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, htail⟩ := hresult
          exact ih output context fuel hcovered (hbound.2 output) htail
      | hashOutput =>
          rw [runDirectResolvedDetailedFromTable_hashOutput_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, htail⟩ := hresult
          exact ih output context fuel hcovered (hbound.2 output) htail
      | ensure coordinate =>
          rw [runDirectResolvedDetailedFromTable_ensure_query_bind] at hresult
          exact ih () { context with state := context.state.ensure coordinate } fuel hcovered
            (hbound.2 ()) hresult
      | probe coordinate digest =>
          have hmem : (⟨coordinate, digest⟩ : Probe) ∈ candidates := by
            simpa [IsUncoveredProbe] using hbound.1
          have htail : (next ()).IsQueryBoundP (IsUncoveredProbe candidates) 0 := by
            simpa [IsUncoveredProbe] using hbound.2 ()
          cases fuel with
          | zero => simp [runDirectResolvedDetailedFromTable_probe_query_bind] at hresult
          | succ remaining =>
              rw [runDirectResolvedDetailedFromTable_probe_query_bind] at hresult
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · simp only [hrevealed, ↓reduceIte] at hresult
                exact ih () context remaining hcovered htail hresult
              · simp only [hrevealed, ↓reduceIte] at hresult
                exact ih () { context with state := context.state.addPending coordinate digest }
                  remaining (hcovered.addPending_of_mem ⟨coordinate, digest⟩ hmem) htail hresult
      | peek coordinate =>
          rw [runDirectResolvedDetailedFromTable_peek_query_bind] at hresult
          exact ih (context.state.values coordinate) context fuel hcovered (hbound.2 _) hresult
      | publish coordinate =>
          rw [runDirectResolvedDetailedFromTable_publish_query_bind] at hresult
          exact ih () { context with state := context.state.publish coordinate } fuel hcovered
            (hbound.2 ()) hresult
      | reveal coordinate =>
          rw [runDirectResolvedDetailedFromTable_reveal_query_bind] at hresult
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
