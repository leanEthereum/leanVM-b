import SphincsSecurity.Proof.OtsProbeResolvedDirectRecursive

/-! Fixed-position resolution commutation for the direct interpreter. -/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

theorem evalDist_resolveDeferredPositionValue_then_runDirectResolvedObserve_eq_true_of_not_completable_auto
    {observe : DeferredContext → Nat → α → ProbComp Bool}
    (position : Position) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) [ObserverDooms table observe]
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hdoomed : ¬DeferredCompletable table context) :
    evalDist (do
      let resolved ← resolveDeferredPositionValue position context
      match resolved with
      | none => pure true
      | some resolved =>
          runDirectResolvedObserve observe resolved.toDeferredContext fuel table computation) =
      evalDist (pure true : ProbComp Bool) := by
  calc
    _ = evalDist (resolveDeferredPositionValue position context >>= fun _ => pure true) := by
      apply evalDist_bind_congr
      intro resolved hresolved
      cases resolved with
      | none => rfl
      | some resolved =>
          have hresolvedNotCompletable :
              ¬DeferredCompletable table resolved.toDeferredContext := by
            intro hresolvedCompletable
            obtain ⟨completion, hcompletion⟩ := hresolvedCompletable
            have hback :=
              (deferredCompletion_resolveDeferredPositionValue_iff position resolved
                hconsistent hresolved completion).mp hcompletion
            exact hdoomed ⟨completion, hback.1⟩
          exact evalDist_runDirectResolvedObserve_eq_true_of_not_completable_auto
            resolved.toDeferredContext fuel table computation
            (hconsistent.of_resolveDeferredPositionValue position resolved hresolved)
            (hstarts.of_state_values_eq
              (resolveDeferredPositionValue_preserves_state_values position context resolved
                hresolved))
            hresolvedNotCompletable
    _ = _ := OracleComp.DeferredSampling.evalDist_bind_const_neverFails
      (resolveDeferredPositionValue position context) (by
        simp [resolveDeferredPositionValue, LazyRevealProbe.sampleHashOutput])
      (pure true)

theorem evalDist_resolveDeferredPositionValue_after_materialized_reveal_runDirectResolvedObserve
    (target revealed : Position) (context : DeferredContext)
    (revealedResult : DeferredResolution) (table : OtsSecretIndex → HashOutput)
    (fuel : Nat) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (observe : DeferredContext → Nat → α → ProbComp Bool)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hrevealed : some revealedResult ∈ support
      (resolveDeferredReveal table revealed context)) :
    evalDist (resolveDeferredPositionValue target revealedResult.toDeferredContext >>=
      fun targetResult =>
        match targetResult with
        | none => pure true
        | some targetResult =>
            runDirectResolvedObserve observe
              { state := (context.state.clearPending (.position target)).materialize
                  (.position revealed) revealedResult.output
                values := targetResult.values }
              fuel table computation) =
      evalDist (resolveDeferredPositionValue target
        (materializeResolvedPosition context revealed revealedResult) >>= fun targetResult =>
          match targetResult with
          | none => pure true
          | some targetResult =>
              runDirectResolvedObserve observe targetResult.toDeferredContext fuel table
                computation) :=
  evalDist_resolveDeferredPositionValue_after_materialized_reveal_observe
    (fun nextContext => runDirectResolvedObserve observe nextContext fuel table computation)
    target revealed context revealedResult table hvalid hcompletable hrevealed

theorem evalDist_resolveDeferredPositionValue_after_materialized_chainStart_runDirectResolvedObserve
    (target : Position) (index : OtsSecretIndex) (context : DeferredContext)
    (revealedResult : DeferredResolution) (table : OtsSecretIndex → HashOutput)
    (fuel : Nat) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (observe : DeferredContext → Nat → α → ProbComp Bool)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hrevealed : resolveDeferredChainStart table index context = some revealedResult) :
    evalDist (resolveDeferredPositionValue target revealedResult.toDeferredContext >>=
      fun targetResult =>
        match targetResult with
        | none => pure true
        | some targetResult =>
            runDirectResolvedObserve observe
              { state := (context.state.clearPending (.position target)).materialize
                  index.coordinate revealedResult.output
                values := targetResult.values }
              fuel table computation) =
      evalDist (resolveDeferredPositionValue target
        (materializeResolvedChainStart context index revealedResult) >>= fun targetResult =>
          match targetResult with
          | none => pure true
          | some targetResult =>
              runDirectResolvedObserve observe targetResult.toDeferredContext fuel table
                computation) :=
  evalDist_resolveDeferredPositionValue_after_materialized_chainStart_observe
    (fun nextContext => runDirectResolvedObserve observe nextContext fuel table computation)
    target index context revealedResult table hvalid hcompletable hrevealed

theorem evalDist_resolveDeferredPositionValue_after_materialized_positionValue_runDirectResolvedObserve
    (target revealed : Position) (context : DeferredContext)
    (revealedResult : DeferredResolution) (table : OtsSecretIndex → HashOutput)
    (fuel : Nat) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (observe : DeferredContext → Nat → α → ProbComp Bool)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hrevealed : some revealedResult ∈ support
      (resolveDeferredPositionValue revealed context)) :
    evalDist (resolveDeferredPositionValue target revealedResult.toDeferredContext >>=
      fun targetResult =>
        match targetResult with
        | none => pure true
        | some targetResult =>
            runDirectResolvedObserve observe
              { state := (context.state.clearPending (.position target)).materialize
                  (.position revealed) revealedResult.output
                values := targetResult.values }
              fuel table computation) =
      evalDist (resolveDeferredPositionValue target
        (materializeResolvedPosition context revealed revealedResult) >>= fun targetResult =>
          match targetResult with
          | none => pure true
          | some targetResult =>
              runDirectResolvedObserve observe targetResult.toDeferredContext fuel table
                computation) :=
  evalDist_resolveDeferredPositionValue_after_materialized_positionValue_observe
    (fun nextContext => runDirectResolvedObserve observe nextContext fuel table computation)
    target revealed context revealedResult table hvalid hcompletable hrevealed

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredPositionValue_then_runDirectResolvedObserve
    (position : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    {observe : DeferredContext → Nat → α → ProbComp Bool}
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hensured : Coordinate.position position ∈ context.state.ensured)
    (hbase : ∀ nextContext remaining value,
      nextContext.Valid → DeferredCompletable table nextContext →
      Coordinate.position position ∈ nextContext.state.ensured →
      evalDist (resolveDeferredPositionValue position nextContext >>= fun resolved =>
        match resolved with
        | none => pure true
        | some resolved => observe resolved.toDeferredContext remaining value) =
        evalDist (observe nextContext remaining value))
    [ObserverDooms table observe] :
    evalDist (do
      let resolved ← resolveDeferredPositionValue position context
      match resolved with
      | none => pure true
      | some resolved =>
          runDirectResolvedObserve observe resolved.toDeferredContext fuel table computation) =
      evalDist (runDirectResolvedObserve observe context fuel table computation) := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      unfold runDirectResolvedObserve
      simp only [runDirectResolvedFromTable, pure_bind]
      exact hbase context fuel value hvalid hcompletable hensured
  | query_bind query next ih =>
      cases query with
      | uniform n =>
          unfold runDirectResolvedObserve
          simp only [runDirectResolvedFromTable_uniform_query_bind, bind_assoc]
          calc
            _ = evalDist (resolveDeferredPositionValue position context >>= fun resolved =>
                (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>= fun output =>
                  match resolved with
                  | none => pure true
                  | some resolved =>
                      runDirectResolvedFromTable resolved.toDeferredContext fuel table
                          (next output) >>=
                        finishObserve observe) := by
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro resolved
              cases resolved with
              | none =>
                  exact (OracleComp.DeferredSampling.evalDist_bind_const_neverFails
                    (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))
                    (by simp) (pure true)).symm
              | some resolved => rfl
            _ = evalDist ((liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>= fun output =>
                resolveDeferredPositionValue position context >>= fun resolved =>
                  match resolved with
                  | none => pure true
                  | some resolved =>
                      runDirectResolvedFromTable resolved.toDeferredContext fuel table
                          (next output) >>=
                        finishObserve observe) :=
              OracleComp.DeferredSampling.evalDist_bind_comm
                (resolveDeferredPositionValue position context)
                (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) _
            _ = _ := by
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro output
              exact ih output context fuel hvalid hcompletable hensured
      | hashOutput =>
          unfold runDirectResolvedObserve
          simp only [runDirectResolvedFromTable_hashOutput_query_bind, bind_assoc]
          calc
            _ = evalDist (resolveDeferredPositionValue position context >>= fun resolved =>
                LazyRevealProbe.sampleHashOutput >>= fun output =>
                  match resolved with
                  | none => pure true
                  | some resolved =>
                      runDirectResolvedFromTable resolved.toDeferredContext fuel table
                          (next output) >>=
                        finishObserve observe) := by
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro resolved
              cases resolved with
              | none =>
                  exact (OracleComp.DeferredSampling.evalDist_bind_const_neverFails
                    LazyRevealProbe.sampleHashOutput (by
                      simp [LazyRevealProbe.sampleHashOutput]) (pure true)).symm
              | some resolved => rfl
            _ = evalDist (LazyRevealProbe.sampleHashOutput >>= fun output =>
                resolveDeferredPositionValue position context >>= fun resolved =>
                  match resolved with
                  | none => pure true
                  | some resolved =>
                      runDirectResolvedFromTable resolved.toDeferredContext fuel table
                          (next output) >>=
                        finishObserve observe) :=
              OracleComp.DeferredSampling.evalDist_bind_comm
                (resolveDeferredPositionValue position context)
                LazyRevealProbe.sampleHashOutput _
            _ = _ := by
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro output
              exact ih output context fuel hvalid hcompletable hensured
      | ensure coordinate =>
          unfold runDirectResolvedObserve
          simp_rw [runDirectResolvedFromTable_ensure_query_bind]
          calc
            _ = evalDist (resolveDeferredPositionValue position
                  { context with state := context.state.ensure coordinate } >>= fun resolved =>
                match resolved with
                | none => pure true
                | some resolved =>
                    runDirectResolvedFromTable resolved.toDeferredContext fuel table (next ()) >>=
                      finishObserve observe) := by
              rw [resolveDeferredPositionValue_ensure]
              simp only [map_eq_bind_pure_comp, bind_assoc]
              apply congrArg evalDist
              apply bind_congr
              intro resolved
              cases resolved <;> rfl
            _ = _ := ih () { context with state := context.state.ensure coordinate } fuel
              (hvalid.ensure coordinate) (hcompletable.ensure coordinate) (by
                exact Finset.mem_insert.mpr (Or.inr hensured))
      | probe coordinate candidate =>
          unfold runDirectResolvedObserve
          simp_rw [runDirectResolvedFromTable_probe_query_bind]
          cases fuel with
          | zero =>
              simp only [pure_bind]
              have hnone : finishObserve observe
                  (none : Option (ResolvedRunResult α)) = pure true := by
                simp [finishObserve]
              simp_rw [hnone]
              calc
                _ = evalDist (resolveDeferredPositionValue position context >>= fun _ =>
                      pure true) := by
                  apply congrArg evalDist
                  apply bind_congr
                  intro resolved
                  cases resolved <;> rfl
                _ = _ := OracleComp.DeferredSampling.evalDist_bind_const_neverFails
                  (resolveDeferredPositionValue position context) (by
                    simp [resolveDeferredPositionValue, LazyRevealProbe.sampleHashOutput])
                  (pure true)
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · calc
                  _ = evalDist (resolveDeferredPositionValue position context >>= fun resolved =>
                        match resolved with
                        | none => pure true
                        | some resolved =>
                            runDirectResolvedFromTable resolved.toDeferredContext remaining table
                                (next ()) >>=
                              finishObserve observe) := by
                      apply evalDist_bind_congr
                      intro resolved hresolved
                      cases resolved with
                      | none => rfl
                      | some resolved =>
                          have hstate := resolveDeferredPositionValue_state_eq_clearPending
                            position context resolved hresolved
                          simp [hstate, LazyRevealProbe.State.clearPending, hrevealed]
                  _ = _ := by
                    simpa [runDirectResolvedObserve, hrevealed] using
                      ih () context remaining hvalid hcompletable hensured
              · by_cases heq : coordinate = .position position
                · subst coordinate
                  let nextContext : DeferredContext :=
                    { context with
                      state := context.state.addPending (.position position) candidate }
                  let continuation : Option DeferredResolution → ProbComp Bool
                    | none => pure true
                    | some resolved =>
                        runDirectResolvedFromTable resolved.toDeferredContext remaining table
                            (next ()) >>=
                          finishObserve observe
                  calc
                    _ = evalDist (resolveDeferredPositionValue position context >>=
                          fun first =>
                            match first with
                            | none => pure true
                            | some first =>
                                resolveDeferredPositionValue position
                                    { first.toDeferredContext with
                                      state := first.state.addPending (.position position)
                                        candidate } >>=
                                  continuation) := by
                        apply evalDist_bind_congr
                        intro first hfirst
                        cases first with
                        | none => rfl
                        | some first =>
                            let added : DeferredContext :=
                              { first.toDeferredContext with
                                state := first.state.addPending (.position position) candidate }
                            have hfirstValid :=
                              hvalid.of_resolveDeferredPositionValue position first hfirst
                            have hfirstCompletable :=
                              hcompletable.of_resolveDeferredPositionValue hvalid position first
                                hfirst
                            have hfirstState := resolveDeferredPositionValue_state_eq_clearPending
                              position context first hfirst
                            have hnotRevealed :
                                Coordinate.position position ∉ first.state.revealed := by
                              simpa [hfirstState, LazyRevealProbe.State.clearPending] using
                                hrevealed
                            have haddedEnsured :
                                Coordinate.position position ∈ added.state.ensured := by
                              simpa [added, hfirstState, LazyRevealProbe.State.clearPending,
                                LazyRevealProbe.State.addPending] using hensured
                            by_cases haddedCompletable : DeferredCompletable table added
                            · simpa [added, continuation, DeferredResolution.addPending,
                                hnotRevealed, runDirectResolvedObserve] using
                                (ih () added remaining
                                  (hfirstValid.addPending_of_completable
                                    (.position position) candidate haddedCompletable)
                                  haddedCompletable haddedEnsured).symm
                            · have haddedConsistent : added.ValuesConsistent :=
                                hfirstValid.valuesConsistent.addPending (.position position)
                                  candidate
                              have hfirstStarts : StartTableAgrees first.state table :=
                                startTableAgrees_of_deferredCompletable hfirstCompletable
                              have haddedStarts : StartTableAgrees added.state table := by
                                exact hfirstStarts
                              calc
                                _ = evalDist (pure true : ProbComp Bool) := by
                                  simpa [added, hnotRevealed, runDirectResolvedObserve] using
                                    evalDist_runDirectResolvedObserve_eq_true_of_not_completable_auto
                                      (observe := observe)
                                      added remaining table (next ()) haddedConsistent haddedStarts
                                      haddedCompletable
                                _ = _ := by
                                  symm
                                  exact
                                    evalDist_resolveDeferredPositionValue_then_runDirectResolvedObserve_eq_true_of_not_completable_auto
                                      position added remaining table (next ()) haddedConsistent
                                      haddedStarts haddedCompletable
                    _ = evalDist ((do
                          let first ← resolveDeferredPositionValue position context
                          match first with
                          | none => (pure none : ProbComp (Option DeferredResolution))
                          | some first =>
                              resolveDeferredPositionValue position
                                { first.toDeferredContext with
                                  state := first.state.addPending (.position position)
                                    candidate }) >>= continuation) := by
                        simp only [bind_assoc]
                        apply congrArg evalDist
                        apply bind_congr
                        intro first
                        cases first <;> rfl
                    _ = evalDist (resolveDeferredPositionValue position nextContext >>=
                          continuation) := by
                        dsimp only [nextContext]
                        exact congrArg evalDist (congrArg (fun resolver => resolver >>= continuation)
                          (resolveDeferredPositionValue_then_addPending_self_resolve position
                            context candidate))
                    _ = _ := by
                        have hnextConsistent : nextContext.ValuesConsistent :=
                          hvalid.valuesConsistent.addPending (.position position) candidate
                        have hstarts : StartTableAgrees context.state table :=
                          startTableAgrees_of_deferredCompletable hcompletable
                        have hnextStarts : StartTableAgrees nextContext.state table := by
                          exact hstarts
                        have hnextEnsured :
                            Coordinate.position position ∈ nextContext.state.ensured := hensured
                        by_cases hnextCompletable : DeferredCompletable table nextContext
                        · simpa [nextContext, continuation, hrevealed,
                              runDirectResolvedObserve] using
                            ih () nextContext remaining
                              (hvalid.addPending_of_completable (.position position) candidate
                                hnextCompletable)
                              hnextCompletable hnextEnsured
                        · calc
                            _ = evalDist (pure true : ProbComp Bool) :=
                              evalDist_resolveDeferredPositionValue_then_runDirectResolvedObserve_eq_true_of_not_completable_auto
                                position nextContext remaining table (next ()) hnextConsistent
                                hnextStarts hnextCompletable
                            _ = _ := by
                              symm
                              simpa [nextContext, hrevealed, runDirectResolvedObserve] using
                                evalDist_runDirectResolvedObserve_eq_true_of_not_completable_auto
                                  (observe := observe)
                                  nextContext remaining table (next ()) hnextConsistent hnextStarts
                                  hnextCompletable
                · let nextContext : DeferredContext :=
                    { context with state := context.state.addPending coordinate candidate }
                  by_cases hnextCompletable : DeferredCompletable table nextContext
                  · calc
                      _ = evalDist (resolveDeferredPositionValue position nextContext >>=
                            fun resolved =>
                              match resolved with
                              | none => pure true
                              | some resolved =>
                                  runDirectResolvedFromTable resolved.toDeferredContext remaining table
                                      (next ()) >>=
                                    finishObserve observe) := by
                          dsimp only [nextContext]
                          rw [resolveDeferredPositionValue_addPending_of_ne position context
                            coordinate candidate heq]
                          simp only [map_eq_bind_pure_comp, bind_assoc]
                          apply evalDist_bind_congr
                          intro resolved hresolved
                          cases resolved with
                          | none => rfl
                          | some resolved =>
                              have hstate := resolveDeferredPositionValue_state_eq_clearPending
                                position context resolved hresolved
                              have hnotRevealed : coordinate ∉ resolved.state.revealed := by
                                simpa [hstate, LazyRevealProbe.State.clearPending] using hrevealed
                              simp [DeferredResolution.addPending, hnotRevealed]
                      _ = _ := by
                        simpa [nextContext, hrevealed, runDirectResolvedObserve] using
                          ih () nextContext remaining
                            (hvalid.addPending_of_completable coordinate candidate
                              hnextCompletable)
                            hnextCompletable (by exact hensured)
                  · have hnextConsistent : nextContext.ValuesConsistent :=
                      hvalid.valuesConsistent.addPending coordinate candidate
                    have hstarts : StartTableAgrees context.state table :=
                      startTableAgrees_of_deferredCompletable hcompletable
                    have hnextStarts : StartTableAgrees nextContext.state table := by
                      exact hstarts
                    calc
                      _ = evalDist (resolveDeferredPositionValue position nextContext >>=
                            fun resolved =>
                              match resolved with
                              | none => pure true
                              | some resolved =>
                                  runDirectResolvedFromTable resolved.toDeferredContext remaining table
                                      (next ()) >>=
                                    finishObserve observe) := by
                          dsimp only [nextContext]
                          rw [resolveDeferredPositionValue_addPending_of_ne position context
                            coordinate candidate heq]
                          simp only [map_eq_bind_pure_comp, bind_assoc]
                          apply evalDist_bind_congr
                          intro resolved hresolved
                          cases resolved with
                          | none => rfl
                          | some resolved =>
                              have hstate := resolveDeferredPositionValue_state_eq_clearPending
                                position context resolved hresolved
                              have hnotRevealed : coordinate ∉ resolved.state.revealed := by
                                simpa [hstate, LazyRevealProbe.State.clearPending] using hrevealed
                              simp [DeferredResolution.addPending, hnotRevealed]
                      _ = evalDist (pure true : ProbComp Bool) := by
                        calc
                          _ = evalDist (resolveDeferredPositionValue position nextContext >>=
                                fun _ => pure true) := by
                            apply evalDist_bind_congr
                            intro resolved hresolved
                            cases resolved with
                            | none => rfl
                            | some resolved =>
                                have hresolvedNotCompletable :
                                    ¬DeferredCompletable table resolved.toDeferredContext := by
                                  intro hresolvedCompletable
                                  obtain ⟨completion, hcompletion⟩ := hresolvedCompletable
                                  have hback :=
                                    (deferredCompletion_resolveDeferredPositionValue_iff position
                                      resolved hnextConsistent hresolved completion).mp hcompletion
                                  exact hnextCompletable ⟨completion, hback.1⟩
                                exact
                                  evalDist_runDirectResolvedObserve_eq_true_of_not_completable_auto
                                    resolved.toDeferredContext remaining table (next ())
                                    (hnextConsistent.of_resolveDeferredPositionValue position
                                      resolved hresolved)
                                    (hnextStarts.of_state_values_eq
                                      (resolveDeferredPositionValue_preserves_state_values position
                                        nextContext resolved hresolved))
                                    hresolvedNotCompletable
                          _ = _ :=
                            OracleComp.DeferredSampling.evalDist_bind_const_neverFails
                              (resolveDeferredPositionValue position nextContext) (by
                                simp [resolveDeferredPositionValue,
                                  LazyRevealProbe.sampleHashOutput])
                              (pure true)
                      _ = _ := by
                        symm
                        simpa [nextContext, hrevealed, runDirectResolvedObserve] using
                          evalDist_runDirectResolvedObserve_eq_true_of_not_completable_auto
                            (observe := observe)
                            nextContext remaining table (next ()) hnextConsistent hnextStarts
                            hnextCompletable
      | peek coordinate =>
          unfold runDirectResolvedObserve
          simp_rw [runDirectResolvedFromTable_peek_query_bind]
          calc
            _ = evalDist (resolveDeferredPositionValue position context >>= fun resolved =>
                match resolved with
                | none => pure true
                | some resolved =>
                    runDirectResolvedFromTable resolved.toDeferredContext fuel table
                        (next (context.state.values coordinate)) >>=
                      finishObserve observe) := by
              apply evalDist_bind_congr
              intro resolved hresolved
              cases resolved with
              | none => rfl
              | some resolved =>
                  have hvalues := resolveDeferredPositionValue_preserves_state_values position
                    context resolved hresolved
                  simp [hvalues]
            _ = _ := ih (context.state.values coordinate) context fuel hvalid hcompletable
              hensured
      | publish coordinate =>
          unfold runDirectResolvedObserve
          simp_rw [runDirectResolvedFromTable_publish_query_bind]
          calc
            _ = evalDist (resolveDeferredPositionValue position
                  { context with state := context.state.publish coordinate } >>= fun resolved =>
                match resolved with
                | none => pure true
                | some resolved =>
                    runDirectResolvedFromTable resolved.toDeferredContext fuel table (next ()) >>=
                      finishObserve observe) := by
              rw [resolveDeferredPositionValue_publish]
              simp only [map_eq_bind_pure_comp, bind_assoc]
              apply congrArg evalDist
              apply bind_congr
              intro resolved
              cases resolved <;> rfl
            _ = _ := ih () { context with state := context.state.publish coordinate } fuel
              (hvalid.publish coordinate) (hcompletable.publish coordinate) hensured
      | reveal coordinate =>
          unfold runDirectResolvedObserve
          simp_rw [runDirectResolvedFromTable_reveal_query_bind]
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
              have hstarts := startTableAgrees_of_deferredCompletable hcompletable
              have hclean := hcompletable.not_hitAt_chainStart index
              cases hstate : context.state.values index.coordinate with
              | some output =>
                  have houtput : output = table index := hstarts index output hstate
                  subst output
                  calc
                    _ = evalDist (resolveDeferredPositionValue position context >>= fun resolved =>
                          match resolved with
                          | none => pure true
                          | some resolved =>
                              runDirectResolvedObserve observe resolved.toDeferredContext fuel table
                                (next (table index))) := by
                        apply evalDist_bind_congr
                        intro resolved hresolved
                        cases resolved with
                        | none => rfl
                        | some resolved =>
                            have hvalues := resolveDeferredPositionValue_preserves_state_values
                              position context resolved hresolved
                            have hcached : resolved.state.values index.coordinate =
                                some (table index) := by simpa [hvalues] using hstate
                            simp only [show resolved.state.values
                              (.chainStart lay tree leafIdx chainIdx) = some (table index) by
                                simpa [index, OtsSecretIndex.coordinate] using hcached]
                            unfold runDirectResolvedObserve
                            rfl
                    _ = evalDist (runDirectResolvedObserve observe context fuel table
                          (next (table index))) :=
                        ih (table index) context fuel hvalid hcompletable hensured
                    _ = _ := by
                        have hstate' : context.state.values
                            (.chainStart lay tree leafIdx chainIdx) =
                              some (table ⟨lay, tree, leafIdx, chainIdx⟩) := by
                          simpa [index, OtsSecretIndex.coordinate] using hstate
                        unfold runDirectResolvedObserve
                        rw [hstate']
              | none =>
                  let continuation : Option RevealedResolution → ProbComp Bool
                    | none => pure true
                    | some resolved =>
                        runDirectResolvedObserve observe
                          { state := (context.state.clearPending (.position position)).materialize
                              index.coordinate resolved.output
                            values := resolved.context.values }
                          fuel table (next resolved.output)
                  calc
                    _ = evalDist (resolvePositionThenChainStart position table index context >>=
                          continuation) := by
                        unfold resolvePositionThenChainStart continuation
                        simp only [bind_assoc]
                        apply evalDist_bind_congr
                        intro positionResult hpositionResult
                        cases positionResult with
                        | none => rfl
                        | some positionResult =>
                            have hpositionState :=
                              resolveDeferredPositionValue_state_eq_clearPending position context
                                positionResult hpositionResult
                            have hpositionValues :=
                              resolveDeferredPositionValue_preserves_state_values position context
                                positionResult hpositionResult
                            have hpositionStarts := hstarts.of_state_values_eq hpositionValues
                            have hpositionClean :
                                ¬positionResult.state.hitAt index.coordinate (table index) := by
                              rw [hpositionState]
                              exact (hitAt_clearPending_of_ne context.state (.position position)
                                index.coordinate (table index) (by cases index <;> simp
                                  [OtsSecretIndex.coordinate])).not.mpr hclean
                            have hmissing : positionResult.state.values index.coordinate = none := by
                              simpa [hpositionValues] using hstate
                            simp only
                            rw [show positionResult.state.values
                              (.chainStart lay tree leafIdx chainIdx) = none by
                                simpa [index, OtsSecretIndex.coordinate] using hmissing]
                            simp only
                            rw [if_neg (show ¬positionResult.state.hitAt
                              (.chainStart lay tree leafIdx chainIdx) (table index) by
                                simpa [index, OtsSecretIndex.coordinate] using hpositionClean)]
                            rw [resolveDeferredChainStart_of_agrees table index
                              positionResult.toDeferredContext hpositionStarts hpositionClean]
                            simp only [pure_bind]
                            rw [hpositionState]
                            rfl
                    _ = evalDist (resolveChainStartThenPosition position table index context >>=
                          continuation) :=
                        evalDist_bind_eq_of_evalDist_eq
                          (evalDist_resolvePosition_chainStart_comm position table index context
                            hcompletable)
                          continuation
                    _ = evalDist (match resolveDeferredChainStart table index context with
                          | none => pure true
                          | some revealedResult =>
                              resolveDeferredPositionValue position
                                  revealedResult.toDeferredContext >>=
                                fun targetResult =>
                                  match targetResult with
                                  | none => pure true
                                  | some targetResult =>
                                      runDirectResolvedObserve observe
                                        { state := (context.state.clearPending
                                              (.position position)).materialize
                                            index.coordinate revealedResult.output
                                          values := targetResult.values }
                                        fuel table (next revealedResult.output)) := by
                        unfold resolveChainStartThenPosition continuation
                        cases resolveDeferredChainStart table index context with
                        | none => rfl
                        | some revealedResult =>
                            simp only [bind_assoc]
                            apply congrArg evalDist
                            apply bind_congr
                            intro targetResult
                            cases targetResult <;> rfl
                    _ = evalDist (match resolveDeferredChainStart table index context with
                          | none => pure true
                          | some revealedResult =>
                              runDirectResolvedObserve observe
                                (materializeResolvedChainStart context index revealedResult)
                                fuel table (next revealedResult.output)) := by
                        cases hrevealedResult : resolveDeferredChainStart table index context with
                        | none => rfl
                        | some revealedResult =>
                            have htransport :=
                              evalDist_resolveDeferredPositionValue_after_materialized_chainStart_runDirectResolvedObserve
                                position index context revealedResult table fuel
                                  (next revealedResult.output) observe hvalid hcompletable
                                    hrevealedResult
                            have hdeferredValues :=
                              resolveDeferredChainStart_deferred_values_eq table index context
                                revealedResult hrevealedResult
                            have hrevealedCompletable :=
                              hcompletable.of_resolveDeferredChainStart index revealedResult
                                hrevealedResult
                            have hstateValues := resolveDeferredChainStart_state_values_eq table index
                              context revealedResult hrevealedResult
                            have houtput := resolveDeferredChainStart_output_of_agrees table index
                              context revealedResult hstarts hrevealedResult
                            have hmaterializedValid :
                                (materializeResolvedChainStart context index revealedResult).Valid := by
                              rw [materializeResolvedChainStart, hdeferredValues]
                              exact hvalid.materialize_chainStart lay tree leafIdx chainIdx
                                revealedResult.output
                            have hmaterializedCompletable : DeferredCompletable table
                                (materializeResolvedChainStart context index revealedResult) := by
                              obtain ⟨completion, hcompletion⟩ := hrevealedCompletable
                              refine ⟨completion, ?_⟩
                              exact (deferredCompletion_materializeResolvedChainStart_iff index
                                revealedResult hstarts houtput hstateValues hdeferredValues
                                  (resolveDeferredChainStart_pending_eq table index context
                                    revealedResult hrevealedResult)).2 hcompletion
                            have hmaterializedEnsured : Coordinate.position position ∈
                                (materializeResolvedChainStart context index
                                  revealedResult).state.ensured := by
                              change Coordinate.position position ∈
                                insert index.coordinate context.state.ensured
                              exact Finset.mem_insert.mpr (Or.inr hensured)
                            exact htransport.trans
                              (ih revealedResult.output
                                (materializeResolvedChainStart context index revealedResult) fuel
                                hmaterializedValid hmaterializedCompletable
                                  hmaterializedEnsured)
                    _ = _ := by
                        rw [resolveDeferredChainStart_of_agrees table index context hstarts hclean]
                        have hstate' : context.state.values
                            (.chainStart lay tree leafIdx chainIdx) = none := by
                          simpa [index, OtsSecretIndex.coordinate] using hstate
                        have hclean' : ¬context.state.hitAt
                            (.chainStart lay tree leafIdx chainIdx)
                              (table ⟨lay, tree, leafIdx, chainIdx⟩) := by
                          simpa [index, OtsSecretIndex.coordinate] using hclean
                        unfold runDirectResolvedObserve materializeResolvedChainStart
                        rw [hstate']
                        simp only
                        rw [if_neg hclean']
                        rfl
          | position revealed =>
              cases hstate : context.state.values (.position revealed) with
              | some output =>
                  calc
                    _ = evalDist (resolveDeferredPositionValue position context >>= fun resolved =>
                          match resolved with
                          | none => pure true
                          | some resolved =>
                              runDirectResolvedObserve observe resolved.toDeferredContext fuel table
                                (next output)) := by
                        apply evalDist_bind_congr
                        intro resolved hresolved
                        cases resolved with
                        | none => rfl
                        | some resolved =>
                            have hvalues := resolveDeferredPositionValue_preserves_state_values
                              position context resolved hresolved
                            have hcached : resolved.state.values (.position revealed) =
                                some output := by simpa [hvalues] using hstate
                            simp only [hcached]
                            unfold runDirectResolvedObserve
                            rfl
                    _ = evalDist (runDirectResolvedObserve observe context fuel table
                          (next output)) := ih output context fuel hvalid hcompletable hensured
                    _ = _ := by rfl
              | none =>
                  let continuation : Option RevealedResolution → ProbComp Bool
                    | none => pure true
                    | some resolved =>
                        runDirectResolvedObserve observe
                          { state := (context.state.clearPending (.position position)).materialize
                              (.position revealed) resolved.output
                            values := resolved.context.values }
                          fuel table (next resolved.output)
                  calc
                    _ = evalDist (resolvePositionValuesInOrder position revealed context >>=
                          continuation) := by
                        unfold resolvePositionValuesInOrder continuation
                        simp only [bind_assoc]
                        apply evalDist_bind_congr
                        intro positionResult hpositionResult
                        cases positionResult with
                        | none => rfl
                        | some positionResult =>
                            have hpositionState :=
                              resolveDeferredPositionValue_state_eq_clearPending position context
                                positionResult hpositionResult
                            have hpositionValues :=
                              resolveDeferredPositionValue_preserves_state_values position context
                                positionResult hpositionResult
                            have hmissing : positionResult.state.values (.position revealed) = none :=
                              by simpa [hpositionValues] using hstate
                            simp only [hmissing, bind_assoc]
                            apply evalDist_bind_congr
                            intro revealedResult _hrevealedResult
                            cases revealedResult with
                            | none => rfl
                            | some revealedResult =>
                                simp only [pure_bind]
                                rw [hpositionState]
                                rfl
                    _ = evalDist (resolvePositionValuesSwapped position revealed context >>=
                          continuation) := by
                        apply evalDist_bind_eq_of_evalDist_eq
                        by_cases heq : position = revealed
                        · subst revealed
                          exact evalDist_resolvePositionValues_comm_self position context
                        · exact evalDist_resolvePositionValues_comm_of_ne position revealed
                            context heq
                    _ = evalDist (resolveDeferredPositionValue revealed context >>=
                          fun revealedResult =>
                            match revealedResult with
                            | none => pure true
                            | some revealedResult =>
                                resolveDeferredPositionValue position
                                    revealedResult.toDeferredContext >>=
                                  fun targetResult =>
                                    match targetResult with
                                    | none => pure true
                                    | some targetResult =>
                                        runDirectResolvedObserve observe
                                          { state := (context.state.clearPending
                                                (.position position)).materialize
                                              (.position revealed) revealedResult.output
                                            values := targetResult.values }
                                          fuel table (next revealedResult.output)) := by
                        unfold resolvePositionValuesSwapped continuation
                        simp only [bind_assoc]
                        apply congrArg evalDist
                        apply bind_congr
                        intro revealedResult
                        cases revealedResult with
                        | none => rfl
                        | some revealedResult =>
                            simp only [bind_assoc]
                            apply bind_congr
                            intro targetResult
                            cases targetResult <;> rfl
                    _ = evalDist (resolveDeferredPositionValue revealed context >>=
                          fun revealedResult =>
                            match revealedResult with
                            | none => pure true
                            | some revealedResult =>
                                runDirectResolvedObserve observe
                                  (materializeResolvedPosition context revealed revealedResult)
                                  fuel table (next revealedResult.output)) := by
                        apply evalDist_bind_congr
                        intro revealedResult hrevealedResult
                        cases revealedResult with
                        | none => rfl
                        | some revealedResult =>
                            have htransport :=
                              evalDist_resolveDeferredPositionValue_after_materialized_positionValue_runDirectResolvedObserve
                                position revealed context revealedResult table fuel
                                  (next revealedResult.output) observe hvalid hcompletable
                                    hrevealedResult
                            have hrevealedValid := hvalid.of_resolveDeferredPositionValue revealed
                              revealedResult hrevealedResult
                            have hstateValues :=
                              resolveDeferredPositionValue_preserves_state_values revealed context
                                revealedResult hrevealedResult
                            have hpending := resolveDeferredPositionValue_pending revealed context
                              revealedResult hrevealedResult
                            have hresolved := resolveDeferredPositionValue_resolves revealed context
                              revealedResult hrevealedResult
                            have hmaterializedValid := hvalid.materializeResolvedPosition_of revealed
                              revealedResult hrevealedValid hstateValues hresolved
                            have hrevealedCompletable :=
                              hcompletable.of_resolveDeferredPositionValue hvalid revealed
                                revealedResult hrevealedResult
                            have hmaterializedCompletable : DeferredCompletable table
                                (materializeResolvedPosition context revealed revealedResult) := by
                              obtain ⟨completion, hcompletion⟩ := hrevealedCompletable
                              exact ⟨completion,
                                (deferredCompletion_materializeResolvedPosition_iff revealed
                                  revealedResult hstateValues hpending hresolved).2 hcompletion⟩
                            have hmaterializedEnsured : Coordinate.position position ∈
                                (materializeResolvedPosition context revealed
                                  revealedResult).state.ensured := by
                              change Coordinate.position position ∈
                                insert (.position revealed) context.state.ensured
                              exact Finset.mem_insert.mpr (Or.inr hensured)
                            exact htransport.trans
                              (ih revealedResult.output
                                (materializeResolvedPosition context revealed revealedResult) fuel
                                hmaterializedValid hmaterializedCompletable
                                  hmaterializedEnsured)
                    _ = _ := by
                        simp only [bind_assoc]
                        apply congrArg evalDist
                        apply bind_congr
                        intro revealedResult
                        cases revealedResult <;> rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
