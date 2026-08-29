import SphincsSecurity.Proof.OtsProbeResolvedPrivateRecursive

/-!
# Private structural sample deferral through the resolved interpreter

Resolving one ensured private structural position before an arbitrary probing computation leaves
the terminal completion-failure distribution unchanged. The reveal case uses recursive resolution
commutation while retaining every pending probe through the public materialization boundary.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

theorem DeferredCompletable.of_resolveDeferredReveal
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hcompletable : DeferredCompletable table context) (hvalid : context.Valid)
    (position : Position) (result : DeferredResolution)
    (hresult : some result ∈ support (resolveDeferredReveal table position context)) :
    DeferredCompletable table result.toDeferredContext := by
  classical
  by_cases hresolvable : ResolvableOtsPosition position
  · exact hcompletable.of_resolveDeferredPosition hvalid (by
      simpa [resolveDeferredReveal, hresolvable] using hresult)
  · exact hcompletable.of_resolveDeferredPositionValue hvalid position result (by
      simpa [resolveDeferredReveal, hresolvable] using hresult)

theorem resolveDeferredPositionValue_values_eq_of_values_eq
    (position : Position) (left right : DeferredContext)
    (leftResult rightResult : DeferredResolution)
    (hleft : some leftResult ∈ support (resolveDeferredPositionValue position left))
    (hright : some rightResult ∈ support (resolveDeferredPositionValue position right))
    (hvalues : left.values = right.values)
    (houtput : leftResult.output = rightResult.output) :
    leftResult.values = rightResult.values := by
  funext other
  by_cases heq : other = position
  · subst other
    rw [resolveDeferredPositionValue_installs position left leftResult hleft,
      resolveDeferredPositionValue_installs position right rightResult hright, houtput]
  · rw [resolveDeferredPositionValue_preserves_other position other left leftResult heq hleft,
      resolveDeferredPositionValue_preserves_other position other right rightResult heq hright,
      hvalues]

theorem clearPending_materialize_comm
    (state : LazyRevealProbe.State Coordinate) (cleared materialized : Coordinate)
    (output : HashOutput) :
    (state.clearPending cleared).materialize materialized output =
      (state.materialize materialized output).clearPending cleared := by
  rcases state with ⟨pending, values, revealed, ensured⟩
  simp [LazyRevealProbe.State.clearPending, LazyRevealProbe.State.materialize,
    LazyRevealProbe.State.pendingAway, and_comm]
  exact Finset.filter_comm (fun x : Coordinate × Digest => ¬x.1 = cleared)
    (fun x => ¬x.1 = materialized) pending

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredPositionValue_after_materialized_reveal
    (target revealed : Position) (context : DeferredContext)
    (revealedResult : DeferredResolution) (table : OtsSecretIndex → HashOutput)
    (fuel : Nat) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hrevealed : some revealedResult ∈ support
      (resolveDeferredReveal table revealed context)) :
    evalDist (resolveDeferredPositionValue target revealedResult.toDeferredContext >>=
      fun targetResult =>
        match targetResult with
        | none => pure true
        | some targetResult =>
            runResolvedFinishIsNone
              { state := (context.state.clearPending (.position target)).materialize
                  (.position revealed) revealedResult.output
                values := targetResult.values }
              fuel table computation) =
      evalDist (resolveDeferredPositionValue target
        (materializeResolvedPosition context revealed revealedResult) >>= fun targetResult =>
          match targetResult with
          | none => pure true
          | some targetResult =>
              runResolvedFinishIsNone targetResult.toDeferredContext fuel table computation) := by
  let materialized := materializeResolvedPosition context revealed revealedResult
  have hstarts := startTableAgrees_of_deferredCompletable hcompletable
  have hrevealedValid := hvalid.of_resolveDeferredReveal table revealed revealedResult hrevealed
  have hstateValues := resolveDeferredReveal_preserves_state_values table revealed context
    revealedResult hrevealed
  have hresolved := resolveDeferredReveal_resolves table revealed context revealedResult
    hrevealed
  have hmaterializedValid := hvalid.materializeResolvedPosition_of revealed revealedResult
    hrevealedValid hstateValues hresolved
  have hrevealedCompletable := hcompletable.of_resolveDeferredReveal hvalid revealed
    revealedResult hrevealed
  have hmaterializedCompletable : DeferredCompletable table materialized := by
    obtain ⟨completion, hcompletion⟩ := hrevealedCompletable
    refine ⟨completion, ?_⟩
    exact (deferredCompletion_materializeResolvedReveal_iff revealed revealedResult hvalid
      hstarts hrevealed).2 hcompletion
  have hview : FinalizationViewEq table materialized revealedResult.toDeferredContext :=
    finalizationViewEq_materializeResolvedReveal revealed revealedResult hvalid hstarts
      hrevealed hmaterializedCompletable
  have hbase := relTriple_resolveDeferredPositionValue_of_finalizationViewEq table target
    revealedResult.toDeferredContext materialized hview.symm hrevealedValid
      hmaterializedValid hrevealedCompletable
  have hleft := SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
    (fun result => result ∈ support
      (resolveDeferredPositionValue target revealedResult.toDeferredContext))
    (fun result hresult => hresult)
  have hboth :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleft
  apply evalDist_eq_of_relTriple_eqRel
  apply relTriple_bind hboth
  intro leftResult rightResult hrelation
  rcases hrelation with ⟨⟨hrelation, hleftSupport⟩, hrightSupport⟩
  cases leftResult with
  | none =>
      cases rightResult with
      | none => exact relTriple_pure_pure rfl
      | some rightResult => simp [FinalizationResolutionEq] at hrelation
  | some leftResult =>
      cases rightResult with
      | none => simp [FinalizationResolutionEq] at hrelation
      | some rightResult =>
          simp only
          have hvalues : leftResult.values = rightResult.values :=
            resolveDeferredPositionValue_values_eq_of_values_eq target
              revealedResult.toDeferredContext materialized leftResult rightResult
              hleftSupport hrightSupport (by rfl) hrelation.1
          have hrightState := resolveDeferredPositionValue_state_eq_clearPending target
            materialized rightResult hrightSupport
          have hstate :
              (context.state.clearPending (.position target)).materialize
                  (.position revealed) revealedResult.output = rightResult.state := by
            rw [hrightState]
            exact clearPending_materialize_comm context.state (.position target)
              (.position revealed) revealedResult.output
          apply relTriple_eqRel_of_evalDist_eq
          rw [hstate, hvalues]

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredPositionValue_after_materialized_chainStart
    (target : Position) (index : OtsSecretIndex) (context : DeferredContext)
    (revealedResult : DeferredResolution) (table : OtsSecretIndex → HashOutput)
    (fuel : Nat) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hrevealed : resolveDeferredChainStart table index context = some revealedResult) :
    evalDist (resolveDeferredPositionValue target revealedResult.toDeferredContext >>=
      fun targetResult =>
        match targetResult with
        | none => pure true
        | some targetResult =>
            runResolvedFinishIsNone
              { state := (context.state.clearPending (.position target)).materialize
                  index.coordinate revealedResult.output
                values := targetResult.values }
              fuel table computation) =
      evalDist (resolveDeferredPositionValue target
        (materializeResolvedChainStart context index revealedResult) >>= fun targetResult =>
          match targetResult with
          | none => pure true
          | some targetResult =>
              runResolvedFinishIsNone targetResult.toDeferredContext fuel table computation) := by
  let materialized := materializeResolvedChainStart context index revealedResult
  have hstarts := startTableAgrees_of_deferredCompletable hcompletable
  have hrevealedValid := hvalid.of_resolveDeferredChainStart table index revealedResult hrevealed
  have hstateValues := resolveDeferredChainStart_state_values_eq table index context
    revealedResult hrevealed
  have hdeferredValues := resolveDeferredChainStart_deferred_values_eq table index context
    revealedResult hrevealed
  have hrevealedCompletable := hcompletable.of_resolveDeferredChainStart index revealedResult
    hrevealed
  have houtput := resolveDeferredChainStart_output_of_agrees table index context revealedResult
    hstarts hrevealed
  have hmaterializedValid : materialized.Valid := by
    dsimp only [materialized]
    rw [materializeResolvedChainStart, hdeferredValues]
    rcases index with ⟨lay, tree, leafIdx, chainIdx⟩
    exact hvalid.materialize_chainStart lay tree leafIdx chainIdx revealedResult.output
  have hmaterializedCompletable : DeferredCompletable table materialized := by
    obtain ⟨completion, hcompletion⟩ := hrevealedCompletable
    refine ⟨completion, ?_⟩
    exact (deferredCompletion_materializeResolvedChainStart_iff index revealedResult hstarts
      houtput hstateValues hdeferredValues
      (resolveDeferredChainStart_pending_eq table index context revealedResult hrevealed)).2
        hcompletion
  have hview : FinalizationViewEq table materialized revealedResult.toDeferredContext :=
    finalizationViewEq_materializeResolvedChainStart index revealedResult hvalid hstarts
      hrevealed hmaterializedCompletable
  have hbase := relTriple_resolveDeferredPositionValue_of_finalizationViewEq table target
    revealedResult.toDeferredContext materialized hview.symm hrevealedValid
      hmaterializedValid hrevealedCompletable
  have hleft := SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
    (fun result => result ∈ support
      (resolveDeferredPositionValue target revealedResult.toDeferredContext))
    (fun result hresult => hresult)
  have hboth :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleft
  apply evalDist_eq_of_relTriple_eqRel
  apply relTriple_bind hboth
  intro leftResult rightResult hrelation
  rcases hrelation with ⟨⟨hrelation, hleftSupport⟩, hrightSupport⟩
  cases leftResult with
  | none =>
      cases rightResult with
      | none => exact relTriple_pure_pure rfl
      | some rightResult => simp [FinalizationResolutionEq] at hrelation
  | some leftResult =>
      cases rightResult with
      | none => simp [FinalizationResolutionEq] at hrelation
      | some rightResult =>
          simp only
          have hvalues : leftResult.values = rightResult.values :=
            resolveDeferredPositionValue_values_eq_of_values_eq target
              revealedResult.toDeferredContext materialized leftResult rightResult
              hleftSupport hrightSupport (by rfl) hrelation.1
          have hrightState := resolveDeferredPositionValue_state_eq_clearPending target
            materialized rightResult hrightSupport
          have hstate :
              (context.state.clearPending (.position target)).materialize
                  index.coordinate revealedResult.output = rightResult.state := by
            rw [hrightState]
            exact clearPending_materialize_comm context.state (.position target)
              index.coordinate revealedResult.output
          apply relTriple_eqRel_of_evalDist_eq
          rw [hstate, hvalues]

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredPositionValue_then_runResolvedFinishIsNone
    (position : Position) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hensured : Coordinate.position position ∈ context.state.ensured) :
    evalDist (do
      let resolved ← resolveDeferredPositionValue position context
      match resolved with
      | none => pure true
      | some resolved =>
          runResolvedFinishIsNone resolved.toDeferredContext fuel table computation) =
      evalDist (runResolvedFinishIsNone context fuel table computation) := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      unfold runResolvedFinishIsNone
      simp only [runResolvedFromTable, pure_bind]
      exact evalDist_resolveDeferredPositionValue_then_finish_isNone position context table
        fuel value hvalid hcompletable hensured
  | query_bind query next ih =>
      cases query with
      | uniform n =>
          unfold runResolvedFinishIsNone
          simp only [runResolvedFromTable_uniform_query_bind, bind_assoc]
          calc
            _ = evalDist (resolveDeferredPositionValue position context >>= fun resolved =>
                (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>= fun output =>
                  match resolved with
                  | none => pure true
                  | some resolved =>
                      runResolvedFromTable resolved.toDeferredContext fuel table
                          (next output) >>=
                        finishResolvedRunIsNone) := by
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
                      runResolvedFromTable resolved.toDeferredContext fuel table
                          (next output) >>=
                        finishResolvedRunIsNone) :=
              OracleComp.DeferredSampling.evalDist_bind_comm
                (resolveDeferredPositionValue position context)
                (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) _
            _ = _ := by
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro output
              exact ih output context fuel hvalid hcompletable hensured
      | hashOutput =>
          unfold runResolvedFinishIsNone
          simp only [runResolvedFromTable_hashOutput_query_bind, bind_assoc]
          calc
            _ = evalDist (resolveDeferredPositionValue position context >>= fun resolved =>
                LazyRevealProbe.sampleHashOutput >>= fun output =>
                  match resolved with
                  | none => pure true
                  | some resolved =>
                      runResolvedFromTable resolved.toDeferredContext fuel table
                          (next output) >>=
                        finishResolvedRunIsNone) := by
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
                      runResolvedFromTable resolved.toDeferredContext fuel table
                          (next output) >>=
                        finishResolvedRunIsNone) :=
              OracleComp.DeferredSampling.evalDist_bind_comm
                (resolveDeferredPositionValue position context)
                LazyRevealProbe.sampleHashOutput _
            _ = _ := by
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro output
              exact ih output context fuel hvalid hcompletable hensured
      | ensure coordinate =>
          unfold runResolvedFinishIsNone
          simp_rw [runResolvedFromTable_ensure_query_bind]
          calc
            _ = evalDist (resolveDeferredPositionValue position
                  { context with state := context.state.ensure coordinate } >>= fun resolved =>
                match resolved with
                | none => pure true
                | some resolved =>
                    runResolvedFromTable resolved.toDeferredContext fuel table (next ()) >>=
                      finishResolvedRunIsNone) := by
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
          unfold runResolvedFinishIsNone
          simp_rw [runResolvedFromTable_probe_query_bind]
          cases fuel with
          | zero =>
              simp only [pure_bind]
              have hnone : finishResolvedRunIsNone
                  (none : Option (ResolvedRunResult α)) = pure true := by
                simp [finishResolvedRunIsNone, finishResolvedRun]
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
                            runResolvedFromTable resolved.toDeferredContext remaining table
                                (next ()) >>=
                              finishResolvedRunIsNone) := by
                      apply evalDist_bind_congr
                      intro resolved hresolved
                      cases resolved with
                      | none => rfl
                      | some resolved =>
                          have hstate := resolveDeferredPositionValue_state_eq_clearPending
                            position context resolved hresolved
                          simp [hstate, LazyRevealProbe.State.clearPending, hrevealed]
                  _ = _ := by
                    simpa [runResolvedFinishIsNone, hrevealed] using
                      ih () context remaining hvalid hcompletable hensured
              · by_cases heq : coordinate = .position position
                · subst coordinate
                  let nextContext : DeferredContext :=
                    { context with
                      state := context.state.addPending (.position position) candidate }
                  let continuation : Option DeferredResolution → ProbComp Bool
                    | none => pure true
                    | some resolved =>
                        runResolvedFromTable resolved.toDeferredContext remaining table
                            (next ()) >>=
                          finishResolvedRunIsNone
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
                                hnotRevealed, runResolvedFinishIsNone] using
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
                                  simpa [added, hnotRevealed] using
                                    evalDist_runResolvedFinishIsNone_eq_true_of_not_completable
                                      added remaining table (next ()) haddedConsistent haddedStarts
                                      haddedCompletable
                                _ = _ := by
                                  symm
                                  exact
                                    evalDist_resolveDeferredPositionValue_then_run_eq_true_of_not_completable
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
                              runResolvedFinishIsNone] using
                            ih () nextContext remaining
                              (hvalid.addPending_of_completable (.position position) candidate
                                hnextCompletable)
                              hnextCompletable hnextEnsured
                        · calc
                            _ = evalDist (pure true : ProbComp Bool) :=
                              evalDist_resolveDeferredPositionValue_then_run_eq_true_of_not_completable
                                position nextContext remaining table (next ()) hnextConsistent
                                hnextStarts hnextCompletable
                            _ = _ := by
                              symm
                              simpa [nextContext, hrevealed] using
                                evalDist_runResolvedFinishIsNone_eq_true_of_not_completable
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
                                  runResolvedFromTable resolved.toDeferredContext remaining table
                                      (next ()) >>=
                                    finishResolvedRunIsNone) := by
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
                        simpa [nextContext, hrevealed, runResolvedFinishIsNone] using
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
                                  runResolvedFromTable resolved.toDeferredContext remaining table
                                      (next ()) >>=
                                    finishResolvedRunIsNone) := by
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
                                  evalDist_runResolvedFinishIsNone_eq_true_of_not_completable
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
                        simpa [nextContext, hrevealed] using
                          evalDist_runResolvedFinishIsNone_eq_true_of_not_completable
                            nextContext remaining table (next ()) hnextConsistent hnextStarts
                            hnextCompletable
      | peek coordinate =>
          unfold runResolvedFinishIsNone
          simp_rw [runResolvedFromTable_peek_query_bind]
          calc
            _ = evalDist (resolveDeferredPositionValue position context >>= fun resolved =>
                match resolved with
                | none => pure true
                | some resolved =>
                    runResolvedFromTable resolved.toDeferredContext fuel table
                        (next (context.state.values coordinate)) >>=
                      finishResolvedRunIsNone) := by
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
          unfold runResolvedFinishIsNone
          simp_rw [runResolvedFromTable_publish_query_bind]
          calc
            _ = evalDist (resolveDeferredPositionValue position
                  { context with state := context.state.publish coordinate } >>= fun resolved =>
                match resolved with
                | none => pure true
                | some resolved =>
                    runResolvedFromTable resolved.toDeferredContext fuel table (next ()) >>=
                      finishResolvedRunIsNone) := by
              rw [resolveDeferredPositionValue_publish]
              simp only [map_eq_bind_pure_comp, bind_assoc]
              apply congrArg evalDist
              apply bind_congr
              intro resolved
              cases resolved <;> rfl
            _ = _ := ih () { context with state := context.state.publish coordinate } fuel
              (hvalid.publish coordinate) (hcompletable.publish coordinate) hensured
      | reveal coordinate =>
          unfold runResolvedFinishIsNone
          simp_rw [runResolvedFromTable_reveal_query_bind]
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
              let continuation : Option RevealedResolution → ProbComp Bool
                | none => pure true
                | some resolved =>
                    runResolvedFinishIsNone
                      { state := (context.state.clearPending (.position position)).materialize
                          index.coordinate resolved.output
                        values := resolved.context.values }
                      fuel table (next resolved.output)
              simp only
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
                        have hstate := resolveDeferredPositionValue_state_eq_clearPending
                          position context positionResult hpositionResult
                        cases hrevealedResult : resolveDeferredChainStart table index
                          positionResult.toDeferredContext with
                        | none =>
                            dsimp only [index] at hrevealedResult ⊢
                            simp [hrevealedResult, finishResolvedRunIsNone, finishResolvedRun]
                        | some revealedResult =>
                            dsimp only [index] at hrevealedResult ⊢
                            simp only [hrevealedResult, pure_bind]
                            rw [hstate]
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
                                  runResolvedFinishIsNone
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
                          runResolvedFinishIsNone
                            (materializeResolvedChainStart context index revealedResult)
                            fuel table (next revealedResult.output)) := by
                    cases hrevealedResult : resolveDeferredChainStart table index context with
                    | none => rfl
                    | some revealedResult =>
                        have htransport :=
                          evalDist_resolveDeferredPositionValue_after_materialized_chainStart
                            position index context revealedResult table fuel
                              (next revealedResult.output) hvalid hcompletable hrevealedResult
                        have hstarts := startTableAgrees_of_deferredCompletable hcompletable
                        have hdeferredValues :=
                          resolveDeferredChainStart_deferred_values_eq table index context
                            revealedResult hrevealedResult
                        have hrevealedValid := hvalid.of_resolveDeferredChainStart table index
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
                    cases hrevealedResult : resolveDeferredChainStart table index context with
                    | none =>
                        simp [finishResolvedRunIsNone, finishResolvedRun]
                    | some revealedResult =>
                        simp only [pure_bind, materializeResolvedChainStart]
                        rfl
          | position revealed =>
              let resolver : PrivateResolver := fun nextContext =>
                resolveDeferredReveal table revealed nextContext
              let continuation : Option RevealedResolution → ProbComp Bool
                | none => pure true
                | some resolved =>
                    runResolvedFinishIsNone
                      { state := (context.state.clearPending (.position position)).materialize
                          (.position revealed) resolved.output
                        values := resolved.context.values }
                      fuel table (next resolved.output)
              simp only
              calc
                _ = evalDist (resolvePositionThenResolver position resolver context >>=
                      continuation) := by
                    unfold resolvePositionThenResolver resolver continuation
                    simp only [bind_assoc]
                    apply evalDist_bind_congr
                    intro positionResult hpositionResult
                    cases positionResult with
                    | none => rfl
                    | some positionResult =>
                        simp only [bind_assoc]
                        apply evalDist_bind_congr
                        intro revealedResult _hrevealedResult
                        cases revealedResult with
                        | none => rfl
                        | some revealedResult =>
                            have hstate := resolveDeferredPositionValue_state_eq_clearPending
                              position context positionResult hpositionResult
                            simp only
                            rw [hstate]
                            simp only [pure_bind]
                            rfl
                _ = evalDist (resolveResolverThenPosition position resolver context >>=
                      continuation) :=
                    evalDist_bind_eq_of_evalDist_eq
                      (positionResolutionCommutes_reveal position table revealed context hvalid
                        hcompletable)
                      continuation
                _ = evalDist (resolveDeferredReveal table revealed context >>=
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
                                    runResolvedFinishIsNone
                                      { state := (context.state.clearPending
                                            (.position position)).materialize
                                          (.position revealed) revealedResult.output
                                        values := targetResult.values }
                                      fuel table (next revealedResult.output)) := by
                    unfold resolveResolverThenPosition resolver continuation
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
                _ = evalDist (resolveDeferredReveal table revealed context >>=
                      fun revealedResult =>
                        match revealedResult with
                        | none => pure true
                        | some revealedResult =>
                            runResolvedFinishIsNone
                              (materializeResolvedPosition context revealed revealedResult)
                              fuel table (next revealedResult.output)) := by
                    apply evalDist_bind_congr
                    intro revealedResult hrevealedResult
                    cases revealedResult with
                    | none => rfl
                    | some revealedResult =>
                        have htransport :=
                          evalDist_resolveDeferredPositionValue_after_materialized_reveal
                            position revealed context revealedResult table fuel
                              (next revealedResult.output) hvalid hcompletable hrevealedResult
                        have hstarts := startTableAgrees_of_deferredCompletable hcompletable
                        have hrevealedValid := hvalid.of_resolveDeferredReveal table revealed
                          revealedResult hrevealedResult
                        have hstateValues := resolveDeferredReveal_preserves_state_values table
                          revealed context revealedResult hrevealedResult
                        have hresolved := resolveDeferredReveal_resolves table revealed context
                          revealedResult hrevealedResult
                        have hmaterializedValid :=
                          hvalid.materializeResolvedPosition_of revealed revealedResult
                            hrevealedValid hstateValues hresolved
                        have hrevealedCompletable :=
                          hcompletable.of_resolveDeferredReveal hvalid revealed revealedResult
                            hrevealedResult
                        have hmaterializedCompletable : DeferredCompletable table
                            (materializeResolvedPosition context revealed revealedResult) := by
                          obtain ⟨completion, hcompletion⟩ := hrevealedCompletable
                          refine ⟨completion, ?_⟩
                          exact (deferredCompletion_materializeResolvedReveal_iff revealed
                            revealedResult hvalid hstarts hrevealedResult).2 hcompletion
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
                    simp only [materializeResolvedPosition, bind_assoc]
                    apply congrArg evalDist
                    apply bind_congr
                    intro revealedResult
                    cases revealedResult <;> rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
