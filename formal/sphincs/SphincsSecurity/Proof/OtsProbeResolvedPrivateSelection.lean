import SphincsSecurity.Proof.OtsProbeResolvedPrivateInterpreter

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option maxRecDepth 100000 in
theorem evalDist_finishResolvedRunIsNone_eq_of_finalizationContextEq
    (table : OtsSecretIndex → HashOutput) (left right : DeferredContext)
    (fuel : Nat) (value : α)
    (hcontext : FinalizationContextEq table (some left) (some right)) :
    evalDist (finishResolvedRunIsNone
        (some (ResolvedRunResult.mk left fuel value table))) =
      evalDist (finishResolvedRunIsNone
        (some (ResolvedRunResult.mk right fuel value table))) := by
  rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
  have hrightCompletable : DeferredCompletable table right := by
    rcases hleftCompletable with ⟨completion, hcompletion⟩
    exact ⟨completion, (hview.deferredCompletion_iff completion).mp hcompletion⟩
  rw [finishResolvedRunIsNone_some_eq_finalize _ hleftCompletable,
    finishResolvedRunIsNone_some_eq_finalize _ hrightCompletable]
  exact evalDist_map_isNone_finalizeResolvedCoordinates_congr_covered table
    left.state.coordinates.toList right.state.coordinates.toList left right hview
    left.state.coordinates.nodup_toList right.state.coordinates.nodup_toList
    (pendingCovered_coordinates_toList left) (pendingCovered_coordinates_toList right)

set_option maxRecDepth 100000 in
theorem evalDist_runResolvedFinishIsNone_eq_of_finalizationSynchronized
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (left right : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hcontext : FinalizationContextEq table (some left) (some right))
    (hvalues : left.state.values = right.state.values)
    (hrevealed : left.state.revealed = right.state.revealed) :
    evalDist (runResolvedFinishIsNone left fuel table computation) =
      evalDist (runResolvedFinishIsNone right fuel table computation) := by
  induction computation using OracleComp.inductionOn generalizing left right fuel with
  | pure value =>
      unfold runResolvedFinishIsNone
      simp only [runResolvedFromTable, pure_bind]
      exact evalDist_finishResolvedRunIsNone_eq_of_finalizationContextEq table left right
        fuel value hcontext
  | query_bind query next ih =>
      cases query with
      | uniform n =>
          unfold runResolvedFinishIsNone
          simp only [runResolvedFromTable_uniform_query_bind, bind_assoc]
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro output
          exact ih output left right fuel hcontext hvalues hrevealed
      | hashOutput =>
          unfold runResolvedFinishIsNone
          simp only [runResolvedFromTable_hashOutput_query_bind, bind_assoc]
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro output
          exact ih output left right fuel hcontext hvalues hrevealed
      | ensure coordinate =>
          unfold runResolvedFinishIsNone
          simp only [runResolvedFromTable_ensure_query_bind]
          rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
          apply ih ()
          · exact ⟨hview.ensure coordinate, hleftValid.ensure coordinate,
              hrightValid.ensure coordinate, hleftCompletable.ensure coordinate⟩
          · exact hvalues
          · exact hrevealed
      | peek coordinate =>
          unfold runResolvedFinishIsNone
          simp only [runResolvedFromTable_peek_query_bind]
          rw [hvalues]
          exact ih (right.state.values coordinate) left right fuel hcontext hvalues hrevealed
      | publish coordinate =>
          unfold runResolvedFinishIsNone
          simp only [runResolvedFromTable_publish_query_bind]
          rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
          apply ih ()
          · exact ⟨hview.publish coordinate, hleftValid.publish coordinate,
              hrightValid.publish coordinate, hleftCompletable.publish coordinate⟩
          · exact hvalues
          · simpa [LazyRevealProbe.State.publish] using congrArg (insert coordinate) hrevealed
      | probe coordinate candidate =>
          unfold runResolvedFinishIsNone
          simp only [runResolvedFromTable_probe_query_bind]
          cases fuel with
          | zero => rfl
          | succ remaining =>
              by_cases hleftRevealed : coordinate ∈ left.state.revealed
              · have hrightRevealed : coordinate ∈ right.state.revealed := by
                  rw [← hrevealed]
                  exact hleftRevealed
                simp only [hleftRevealed, hrightRevealed, ↓reduceIte]
                exact ih () left right remaining hcontext hvalues hrevealed
              · have hrightRevealed : coordinate ∉ right.state.revealed := by
                  rwa [← hrevealed]
                simp only [hleftRevealed, hrightRevealed, ↓reduceIte]
                let left' : DeferredContext :=
                  { left with state := left.state.addPending coordinate candidate }
                let right' : DeferredContext :=
                  { right with state := right.state.addPending coordinate candidate }
                have hcompletableIff : DeferredCompletable table left' ↔
                    DeferredCompletable table right' := by
                  exact deferredCompletable_addPending_iff_of_finalizationViewEq
                    hcontext.1 coordinate candidate
                by_cases hleftCompletable : DeferredCompletable table left'
                · have hrightCompletable : DeferredCompletable table right' :=
                    hcompletableIff.mp hleftCompletable
                  apply ih () left' right' remaining
                  · exact ⟨hcontext.1.addPending_of_completable coordinate candidate
                        hleftCompletable hrightCompletable,
                      hcontext.2.1.addPending_of_completable coordinate candidate
                        hleftCompletable,
                      hcontext.2.2.1.addPending_of_completable coordinate candidate
                        hrightCompletable,
                      hleftCompletable⟩
                  · exact hvalues
                  · exact hrevealed
                · have hrightCompletable : ¬DeferredCompletable table right' := by
                    rwa [← hcompletableIff]
                  calc
                    _ = evalDist (pure true : ProbComp Bool) :=
                      evalDist_runResolvedFinishIsNone_eq_true_of_not_completable
                        left' remaining table (next ()) hcontext.2.1.1 hcontext.1.leftStarts
                        hleftCompletable
                    _ = evalDist (runResolvedFinishIsNone right' remaining table
                        (next ())) :=
                      (evalDist_runResolvedFinishIsNone_eq_true_of_not_completable
                        right' remaining table (next ()) hcontext.2.2.1.1 hcontext.1.rightStarts
                        hrightCompletable).symm
      | reveal coordinate =>
          unfold runResolvedFinishIsNone
          simp_rw [runResolvedFromTable_reveal_query_bind]
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
              simp only [bind_assoc]
              rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
              have hresolved := relTriple_resolveDeferredChainStart_of_finalizationViewEq
                table index left right hview hleftValid hrightValid hleftCompletable
              have hresolvedLeft :=
                SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hresolved
                  (fun result => result ∈ support
                    (pure (resolveDeferredChainStart table index left) :
                      ProbComp (Option DeferredResolution)))
                  (fun result hresult => hresult)
              have hresolvedBoth :=
                SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support
                  hresolvedLeft
              apply evalDist_eq_of_relTriple_eqRel
              apply relTriple_bind hresolvedBoth
              intro leftResolved rightResolved hrelation
              rcases hrelation with ⟨⟨hrelation, hleftSupport⟩, hrightSupport⟩
              cases leftResolved with
              | none =>
                  cases rightResolved with
                  | none => simp [EqRel, finishResolvedRunIsNone, finishResolvedRun]
                  | some rightResolved => simp [FinalizationResolutionEq] at hrelation
              | some leftResolved =>
                  cases rightResolved with
                  | none => simp [FinalizationResolutionEq] at hrelation
                  | some rightResolved =>
                      have hleftResult :
                          resolveDeferredChainStart table index left = some leftResolved := by
                        simpa using hleftSupport.symm
                      have hrightResult :
                          resolveDeferredChainStart table index right = some rightResolved := by
                        simpa using hrightSupport.symm
                      have hleftMaterializedCompletable :=
                        hleftCompletable.materializeResolvedChainStart hview.leftStarts index
                          leftResolved hleftResult
                      have hrightCompletable : DeferredCompletable table right := by
                        rcases hleftCompletable with ⟨completion, hcompletion⟩
                        exact ⟨completion,
                          (hview.deferredCompletion_iff completion).mp hcompletion⟩
                      have hrightMaterializedCompletable :=
                        hrightCompletable.materializeResolvedChainStart hview.rightStarts index
                          rightResolved hrightResult
                      have hleftMaterializedView :=
                        finalizationViewEq_materializeResolvedChainStart index leftResolved
                          hleftValid hview.leftStarts hleftResult
                            hleftMaterializedCompletable
                      have hrightMaterializedView :=
                        finalizationViewEq_materializeResolvedChainStart index rightResolved
                          hrightValid hview.rightStarts hrightResult
                            hrightMaterializedCompletable
                      have hleftMaterializedValid :
                          (materializeResolvedChainStart left index leftResolved).Valid := by
                        unfold materializeResolvedChainStart
                        rw [resolveDeferredChainStart_deferred_values_eq table index left
                          leftResolved hleftResult]
                        exact hleftValid.materialize_chainStart lay tree leafIdx chainIdx
                          leftResolved.output
                      have hrightMaterializedValid :
                          (materializeResolvedChainStart right index rightResolved).Valid := by
                        unfold materializeResolvedChainStart
                        rw [resolveDeferredChainStart_deferred_values_eq table index right
                          rightResolved hrightResult]
                        exact hrightValid.materialize_chainStart lay tree leafIdx chainIdx
                          rightResolved.output
                      have hnext := ih leftResolved.output
                        (materializeResolvedChainStart left index leftResolved)
                        (materializeResolvedChainStart right index rightResolved) fuel
                        ⟨hleftMaterializedView.trans
                            (hrelation.2.1.trans hrightMaterializedView.symm),
                          hleftMaterializedValid, hrightMaterializedValid,
                          hleftMaterializedCompletable⟩
                        (by
                          change Function.update left.state.values index.coordinate
                              (some leftResolved.output) =
                            Function.update right.state.values index.coordinate
                              (some rightResolved.output)
                          rw [hrelation.1, hvalues])
                        (by
                          simpa [materializeResolvedChainStart,
                            LazyRevealProbe.State.materialize] using hrevealed)
                      apply relTriple_eqRel_of_evalDist_eq
                      simpa only [runResolvedFinishIsNone, materializeResolvedChainStart,
                        index, OtsSecretIndex.coordinate, hrelation.1] using hnext
          | position position =>
              simp only [bind_assoc]
              rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
              have hresolved := relTriple_resolveDeferredReveal_of_finalizationViewEq table
                position left right hview hleftValid hrightValid hleftCompletable
              have hresolvedLeft :=
                SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hresolved
                  (fun result => result ∈ support
                    (resolveDeferredReveal table position left))
                  (fun result hresult => hresult)
              have hresolvedBoth :=
                SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support
                  hresolvedLeft
              apply evalDist_eq_of_relTriple_eqRel
              apply relTriple_bind hresolvedBoth
              intro leftResolved rightResolved hrelation
              rcases hrelation with ⟨⟨hrelation, hleftSupport⟩, hrightSupport⟩
              cases leftResolved with
              | none =>
                  cases rightResolved with
                  | none => simp [EqRel, finishResolvedRunIsNone, finishResolvedRun]
                  | some rightResolved => simp [FinalizationResolutionEq] at hrelation
              | some leftResolved =>
                  cases rightResolved with
                  | none => simp [FinalizationResolutionEq] at hrelation
                  | some rightResolved =>
                      have hleftMaterializedCompletable : DeferredCompletable table
                          (materializeResolvedPosition left position leftResolved) := by
                        rcases hrelation.2.2.2.2 with ⟨completion, hcompletion⟩
                        exact ⟨completion,
                          (deferredCompletion_materializeResolvedReveal_iff position
                            leftResolved hleftValid hview.leftStarts hleftSupport).mpr
                              hcompletion⟩
                      have hrightRawCompletable :
                          DeferredCompletable table rightResolved.toDeferredContext := by
                        rcases hrelation.2.2.2.2 with ⟨completion, hcompletion⟩
                        exact ⟨completion,
                          (hrelation.2.1.deferredCompletion_iff completion).mp hcompletion⟩
                      have hrightMaterializedCompletable : DeferredCompletable table
                          (materializeResolvedPosition right position rightResolved) := by
                        rcases hrightRawCompletable with ⟨completion, hcompletion⟩
                        exact ⟨completion,
                          (deferredCompletion_materializeResolvedReveal_iff position
                            rightResolved hrightValid hview.rightStarts hrightSupport).mpr
                              hcompletion⟩
                      have hleftMaterializedView :=
                        finalizationViewEq_materializeResolvedReveal position leftResolved
                          hleftValid hview.leftStarts hleftSupport
                            hleftMaterializedCompletable
                      have hrightMaterializedView :=
                        finalizationViewEq_materializeResolvedReveal position rightResolved
                          hrightValid hview.rightStarts hrightSupport
                            hrightMaterializedCompletable
                      have hleftResultValid := hleftValid.of_resolveDeferredReveal table
                        position leftResolved hleftSupport
                      have hrightResultValid := hrightValid.of_resolveDeferredReveal table
                        position rightResolved hrightSupport
                      have hleftStateValues :=
                        resolveDeferredReveal_preserves_state_values table position left
                          leftResolved hleftSupport
                      have hrightStateValues :=
                        resolveDeferredReveal_preserves_state_values table position right
                          rightResolved hrightSupport
                      have hleftResolvedValue := resolveDeferredReveal_resolves table position
                        left leftResolved hleftSupport
                      have hrightResolvedValue := resolveDeferredReveal_resolves table position
                        right rightResolved hrightSupport
                      have hleftMaterializedValid :
                          (materializeResolvedPosition left position leftResolved).Valid :=
                        hleftValid.materializeResolvedPosition_of position leftResolved
                          hleftResultValid hleftStateValues hleftResolvedValue
                      have hrightMaterializedValid :
                          (materializeResolvedPosition right position rightResolved).Valid :=
                        hrightValid.materializeResolvedPosition_of position rightResolved
                          hrightResultValid hrightStateValues hrightResolvedValue
                      have hnext := ih leftResolved.output
                        (materializeResolvedPosition left position leftResolved)
                        (materializeResolvedPosition right position rightResolved) fuel
                        ⟨hleftMaterializedView.trans
                            (hrelation.2.1.trans hrightMaterializedView.symm),
                          hleftMaterializedValid, hrightMaterializedValid,
                          hleftMaterializedCompletable⟩
                        (by
                          change Function.update left.state.values (.position position)
                              (some leftResolved.output) =
                            Function.update right.state.values (.position position)
                              (some rightResolved.output)
                          rw [hrelation.1, hvalues])
                        (by
                          simpa [materializeResolvedPosition,
                            LazyRevealProbe.State.materialize] using hrevealed)
                      apply relTriple_eqRel_of_evalDist_eq
                      simpa only [runResolvedFinishIsNone, materializeResolvedPosition,
                        hrelation.1] using hnext

theorem finalizationContextEq_resolveDeferredChainStart_original
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex)
    (context : DeferredContext) (result : DeferredResolution)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hresult : resolveDeferredChainStart table index context = some result) :
    FinalizationContextEq table (some result.toDeferredContext) (some context) := by
  have hstarts := startTableAgrees_of_deferredCompletable hcompletable
  have hstateValues := resolveDeferredChainStart_state_values_eq table index context result
    hresult
  have hpositionValues := resolveDeferredChainStart_positionValue_eq table index context result
    hresult
  have hresultValid := hvalid.of_resolveDeferredChainStart table index result hresult
  have hresultCompletable := hcompletable.of_resolveDeferredChainStart index result hresult
  refine ⟨finalizationViewEq_of_deferredCompletion_iff hresultValid hvalid
      (hstarts.of_state_values_eq hstateValues) hstarts ?_ hresultCompletable ?_,
    hresultValid, hvalid, hresultCompletable⟩
  · funext coordinate
    cases coordinate with
    | chainStart => rfl
    | position position =>
        exact congrFun hpositionValues position
  · intro completion
    exact deferredCompletion_resolveDeferredChainStart_iff index result hstarts hresult
      completion

theorem evalDist_resolveDeferredChainStart_then_runResolvedFinishIsNone
    (table : OtsSecretIndex → HashOutput) (index : OtsSecretIndex)
    (context : DeferredContext) (fuel : Nat)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context) :
    evalDist (match resolveDeferredChainStart table index context with
      | none => pure true
      | some resolved =>
          runResolvedFinishIsNone resolved.toDeferredContext fuel table computation) =
      evalDist (runResolvedFinishIsNone context fuel table computation) := by
  let result : DeferredResolution :=
    ⟨{ state := context.state.clearPending index.coordinate, values := context.values },
      table index⟩
  have hstarts := startTableAgrees_of_deferredCompletable hcompletable
  have hclean := hcompletable.not_hitAt_chainStart index
  have hresult : resolveDeferredChainStart table index context = some result := by
    cases hstate : context.state.values index.coordinate with
    | some output =>
        have houtput := hstarts index output hstate
        simp [resolveDeferredChainStart, hstate, houtput, hclean, result]
    | none => simp [resolveDeferredChainStart, hstate, hclean, result]
  rw [hresult]
  exact evalDist_runResolvedFinishIsNone_eq_of_finalizationSynchronized computation
    result.toDeferredContext context fuel table
    (finalizationContextEq_resolveDeferredChainStart_original table index context result
      hvalid hcompletable hresult)
    (resolveDeferredChainStart_state_values_eq table index context result hresult)
    (by
      rw [resolveDeferredChainStart_state_eq_clearPending table index context result hresult]
      rfl)

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredChainPrefix_then_runResolvedFinishIsNone
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    ∀ steps hsteps (context : DeferredContext) (fuel : Nat)
      (computation : OracleComp (LazyRevealProbe.World Coordinate) α),
      context.Valid → DeferredCompletable table context →
      (∀ step : ChainStep, step.val < steps →
        Coordinate.position (.chain lay tree leafIdx chainIdx step) ∈
          context.state.ensured) →
      evalDist (do
        let resolved ← resolveDeferredChainPrefix table lay tree leafIdx chainIdx
          steps hsteps context
        match resolved with
        | none => pure true
        | some resolved =>
            runResolvedFinishIsNone resolved.toDeferredContext fuel table computation) =
        evalDist (runResolvedFinishIsNone context fuel table computation)
  | 0, hsteps, context, fuel, computation, hvalid, hcompletable, _hensured => by
      simp only [resolveDeferredChainPrefix, pure_bind]
      exact evalDist_resolveDeferredChainStart_then_runResolvedFinishIsNone table
        ⟨lay, tree, leafIdx, chainIdx⟩ context fuel computation hvalid hcompletable
  | steps + 1, hsteps, context, fuel, computation, hvalid, hcompletable, hensured => by
      rw [resolveDeferredChainPrefix]
      simp only [bind_assoc]
      calc
        _ = evalDist (resolveDeferredChainPrefix table lay tree leafIdx chainIdx steps
              (by omega) context >>= fun previous =>
            match previous with
            | none => pure true
            | some previous =>
                runResolvedFinishIsNone previous.toDeferredContext fuel table computation) := by
          apply evalDist_bind_congr
          intro previous hprevious
          cases previous with
          | none => rfl
          | some previous =>
              let position : Position :=
                .chain lay tree leafIdx chainIdx ⟨steps, by omega⟩
              have hpreviousValid := hvalid.of_resolveDeferredChainPrefix table lay tree
                leafIdx chainIdx steps (by omega) previous hprevious
              have hpreviousCompletable :=
                hcompletable.of_resolveDeferredChainPrefix hvalid hprevious
              have hprivate := privateStateAgrees_resolveDeferredChainPrefix table lay tree
                leafIdx chainIdx steps (by omega) context previous hprevious
              have hpositionEnsured : Coordinate.position position ∈
                  previous.state.ensured := by
                rw [hprivate.2.2]
                exact hensured ⟨steps, by omega⟩ (by simp)
              exact evalDist_resolveDeferredPositionValue_then_runResolvedFinishIsNone
                position computation previous.toDeferredContext fuel table hpreviousValid
                  hpreviousCompletable hpositionEnsured
        _ = _ :=
          evalDist_resolveDeferredChainPrefix_then_runResolvedFinishIsNone table lay tree
            leafIdx chainIdx steps (by omega) context fuel computation hvalid hcompletable
              (fun step hstep => hensured step (by omega))

def FullChainEnsured (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (context : DeferredContext) : Prop :=
  ∀ step : ChainStep,
    Coordinate.position (.chain lay tree leafIdx chainIdx step) ∈ context.state.ensured

def OtsLeafEnsured (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (context : DeferredContext) : Prop :=
  (∀ chainIdx : ChainIndex, FullChainEnsured lay tree leafIdx chainIdx context) ∧
    Coordinate.position (.leaf lay tree leafIdx) ∈ context.state.ensured

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredChains_then_runResolvedFinishIsNone
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) :
    ∀ (chains : List ChainIndex) (context : DeferredContext) (fuel : Nat)
      (computation : OracleComp (LazyRevealProbe.World Coordinate) α),
      context.Valid → DeferredCompletable table context →
      (∀ chainIdx ∈ chains, FullChainEnsured lay tree leafIdx chainIdx context) →
      evalDist (do
        let resolved ← resolveDeferredChains table lay tree leafIdx chains context
        match resolved with
        | none => pure true
        | some resolved => runResolvedFinishIsNone resolved fuel table computation) =
        evalDist (runResolvedFinishIsNone context fuel table computation)
  | [], context, fuel, computation, _hvalid, _hcompletable, _hensured => by
      simp [resolveDeferredChains]
  | chainIdx :: remaining, context, fuel, computation, hvalid, hcompletable,
      hensured => by
      rw [resolveDeferredChains]
      simp only [bind_assoc]
      calc
        _ = evalDist (resolveDeferredChainPrefix table lay tree leafIdx chainIdx
              (chainLength - 1) (by omega) context >>= fun resolved =>
            match resolved with
            | none => pure true
            | some resolved =>
                runResolvedFinishIsNone resolved.toDeferredContext fuel table computation) := by
          apply evalDist_bind_congr
          intro resolved hresolved
          cases resolved with
          | none => rfl
          | some resolved =>
              have hresolvedValid := hvalid.of_resolveDeferredChainPrefix table lay tree
                leafIdx chainIdx (chainLength - 1) (by omega) resolved hresolved
              have hresolvedCompletable :=
                hcompletable.of_resolveDeferredChainPrefix hvalid hresolved
              have hprivate := privateStateAgrees_resolveDeferredChainPrefix table lay tree
                leafIdx chainIdx (chainLength - 1) (by omega) context resolved hresolved
              apply evalDist_resolveDeferredChains_then_runResolvedFinishIsNone table lay tree
                leafIdx remaining resolved.toDeferredContext fuel computation hresolvedValid
                  hresolvedCompletable
              intro other hother step
              rw [hprivate.2.2]
              exact hensured other (by simp [hother]) step
        _ = _ :=
          evalDist_resolveDeferredChainPrefix_then_runResolvedFinishIsNone table lay tree
            leafIdx chainIdx (chainLength - 1) (by omega) context fuel computation hvalid
              hcompletable (fun step _ => hensured chainIdx (by simp) step)

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredOtsLeaf_then_runResolvedFinishIsNone
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (context : DeferredContext) (fuel : Nat)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hensured : OtsLeafEnsured lay tree leafIdx context) :
    evalDist (do
      let resolved ← resolveDeferredOtsLeaf table lay tree leafIdx context
      match resolved with
      | none => pure true
      | some resolved =>
          runResolvedFinishIsNone resolved.toDeferredContext fuel table computation) =
      evalDist (runResolvedFinishIsNone context fuel table computation) := by
  rw [resolveDeferredOtsLeaf]
  simp only [bind_assoc]
  calc
    _ = evalDist (resolveDeferredChains table lay tree leafIdx
          (List.ofFn fun chainIdx : ChainIndex => chainIdx) context >>= fun chains =>
        match chains with
        | none => pure true
        | some chains => runResolvedFinishIsNone chains fuel table computation) := by
      apply evalDist_bind_congr
      intro chains hchains
      cases chains with
      | none => rfl
      | some chains =>
          have hchainsValid := hvalid.of_resolveDeferredChains table lay tree leafIdx
            (List.ofFn fun chainIdx : ChainIndex => chainIdx) chains hchains
          have hchainsCompletable := hcompletable.of_resolveDeferredChains hvalid hchains
          have hprivate := privateStateAgrees_resolveDeferredChains table lay tree leafIdx
            (List.ofFn fun chainIdx : ChainIndex => chainIdx) context chains hchains
          have hleafEnsured : Coordinate.position (.leaf lay tree leafIdx) ∈
              chains.state.ensured := by
            rw [hprivate.2.2]
            exact hensured.2
          exact evalDist_resolveDeferredPositionValue_then_runResolvedFinishIsNone
            (.leaf lay tree leafIdx) computation chains fuel table hchainsValid
              hchainsCompletable hleafEnsured
    _ = _ := evalDist_resolveDeferredChains_then_runResolvedFinishIsNone table lay tree
      leafIdx (List.ofFn fun chainIdx : ChainIndex => chainIdx) context fuel computation
        hvalid hcompletable (by
          intro chainIdx _hmem
          exact hensured.1 chainIdx)

def TreeNodeEnsured (lay : Layer) (tree : TreeIndex) :
    Nat → Nat → DeferredContext → Prop
  | 0, nodeIdx, context => OtsLeafEnsured lay tree (leafOfNat nodeIdx) context
  | level + 1, nodeIdx, context =>
      TreeNodeEnsured lay tree level (2 * nodeIdx) context ∧
        TreeNodeEnsured lay tree level (2 * nodeIdx + 1) context ∧
        ∃ hlevel : level < maxLayerHeight,
          Coordinate.position (.node lay tree ⟨level, hlevel⟩ (leafOfNat nodeIdx)) ∈
            context.state.ensured

theorem treeNodeEnsured_congr_ensured
    (lay : Layer) (tree : TreeIndex) (level nodeIdx : Nat)
    (left right : DeferredContext)
    (hensured : left.state.ensured = right.state.ensured) :
    TreeNodeEnsured lay tree level nodeIdx left ↔
      TreeNodeEnsured lay tree level nodeIdx right := by
  induction level generalizing nodeIdx with
  | zero => simp [TreeNodeEnsured, OtsLeafEnsured, FullChainEnsured, hensured]
  | succ level ih =>
      simp only [TreeNodeEnsured]
      rw [ih (2 * nodeIdx), ih (2 * nodeIdx + 1)]
      simp [hensured]

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredTreeNode_then_runResolvedFinishIsNone
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex) :
    ∀ level nodeIdx hlevel (context : DeferredContext) (fuel : Nat)
      (computation : OracleComp (LazyRevealProbe.World Coordinate) α),
      context.Valid → DeferredCompletable table context →
      TreeNodeEnsured lay tree level nodeIdx context →
      evalDist (do
        let resolved ← resolveDeferredTreeNode table lay tree level nodeIdx hlevel context
        match resolved with
        | none => pure true
        | some resolved =>
            runResolvedFinishIsNone resolved.toDeferredContext fuel table computation) =
        evalDist (runResolvedFinishIsNone context fuel table computation)
  | 0, nodeIdx, hlevel, context, fuel, computation, hvalid, hcompletable, hensured =>
      evalDist_resolveDeferredOtsLeaf_then_runResolvedFinishIsNone table lay tree
        (leafOfNat nodeIdx) context fuel computation hvalid hcompletable hensured
  | level + 1, nodeIdx, hlevel, context, fuel, computation, hvalid, hcompletable,
      hensured => by
      rw [resolveDeferredTreeNode]
      simp only [bind_assoc]
      calc
        _ = evalDist (resolveDeferredTreeNode table lay tree level (2 * nodeIdx)
              (by omega) context >>= fun leftResult =>
            match leftResult with
            | none => pure true
            | some leftResult =>
                runResolvedFinishIsNone leftResult.toDeferredContext fuel table computation) := by
          apply evalDist_bind_congr
          intro leftResult hleft
          cases leftResult with
          | none => rfl
          | some leftResult =>
              have hleftValid := hvalid.of_resolveDeferredTreeNode table lay tree level
                (2 * nodeIdx) (by omega) leftResult hleft
              have hleftCompletable :=
                hcompletable.of_resolveDeferredTreeNode hvalid hleft
              have hleftPrivate := privateStateAgrees_resolveDeferredTreeNode table lay tree
                level (2 * nodeIdx) (by omega) context leftResult hleft
              have hrightEnsured : TreeNodeEnsured lay tree level (2 * nodeIdx + 1)
                  leftResult.toDeferredContext := by
                exact (treeNodeEnsured_congr_ensured lay tree level (2 * nodeIdx + 1)
                  context leftResult.toDeferredContext hleftPrivate.2.2.symm).mp
                    hensured.2.1
              simp only [bind_assoc]
              calc
                _ = evalDist (resolveDeferredTreeNode table lay tree level
                      (2 * nodeIdx + 1) (by omega) leftResult.toDeferredContext >>=
                    fun rightResult =>
                      match rightResult with
                      | none => pure true
                      | some rightResult =>
                          runResolvedFinishIsNone rightResult.toDeferredContext fuel table
                            computation) := by
                  apply evalDist_bind_congr
                  intro rightResult hright
                  cases rightResult with
                  | none => rfl
                  | some rightResult =>
                      have hrightValid := hleftValid.of_resolveDeferredTreeNode table lay tree
                        level (2 * nodeIdx + 1) (by omega) rightResult hright
                      have hrightCompletable :=
                        hleftCompletable.of_resolveDeferredTreeNode hleftValid hright
                      have hrightPrivate := privateStateAgrees_resolveDeferredTreeNode table lay
                        tree level (2 * nodeIdx + 1) (by omega)
                          leftResult.toDeferredContext rightResult hright
                      obtain ⟨hnodeLevel, hnodeBase⟩ := hensured.2.2
                      have hnodeEnsured : Coordinate.position
                          (.node lay tree ⟨level, by omega⟩ (leafOfNat nodeIdx)) ∈
                            rightResult.state.ensured := by
                        rw [hrightPrivate.2.2, hleftPrivate.2.2]
                        simpa using hnodeBase
                      exact
                        evalDist_resolveDeferredPositionValue_then_runResolvedFinishIsNone
                          (.node lay tree ⟨level, by omega⟩ (leafOfNat nodeIdx)) computation
                            rightResult.toDeferredContext fuel table hrightValid
                              hrightCompletable hnodeEnsured
                _ = _ :=
                  evalDist_resolveDeferredTreeNode_then_runResolvedFinishIsNone table lay tree
                    level (2 * nodeIdx + 1) (by omega) leftResult.toDeferredContext fuel
                      computation hleftValid hleftCompletable hrightEnsured
        _ = _ :=
          evalDist_resolveDeferredTreeNode_then_runResolvedFinishIsNone table lay tree level
            (2 * nodeIdx) (by omega) context fuel computation hvalid hcompletable hensured.1

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredSelectedChainFamily_then_runResolvedFinishIsNone
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) :
    ∀ {n : Nat} (family : Fin n → ChainIndex) (digits : Fin n → Digit)
      (context : DeferredContext) (fuel : Nat)
      (computation : OracleComp (LazyRevealProbe.World Coordinate) α),
      context.Valid → DeferredCompletable table context →
      (∀ index (step : ChainStep), step.val < (digits index).val →
        Coordinate.position (.chain lay tree leafIdx (family index) step) ∈
          context.state.ensured) →
      evalDist (do
        let resolved ← resolveDeferredSelectedChainFamily table lay tree leafIdx
          family digits context
        match resolved with
        | none => pure true
        | some (finalContext, _) =>
            runResolvedFinishIsNone finalContext fuel table computation) =
      evalDist (runResolvedFinishIsNone context fuel table computation)
  | 0, family, digits, context, fuel, computation, _hvalid, _hcompletable,
      _hensured => by
      simp [resolveDeferredSelectedChainFamily]
  | n + 1, family, digits, context, fuel, computation, hvalid, hcompletable,
      hensured => by
      rw [resolveDeferredSelectedChainFamily]
      simp only [bind_assoc]
      calc
        _ = evalDist (resolveDeferredChainPrefix table lay tree leafIdx (family 0)
              (digits 0).val (by have := (digits 0).isLt; omega) context >>=
            fun headOption =>
              match headOption with
              | none => pure true
              | some head =>
                  runResolvedFinishIsNone head.toDeferredContext fuel table computation) := by
          apply evalDist_bind_congr
          intro headOption hhead
          cases headOption with
          | none => rfl
          | some head =>
              have hheadValid := hvalid.of_resolveDeferredChainPrefix table lay tree leafIdx
                (family 0) (digits 0).val (by have := (digits 0).isLt; omega) head hhead
              have hheadCompletable :=
                hcompletable.of_resolveDeferredChainPrefix hvalid hhead
              have hprivate := privateStateAgrees_resolveDeferredChainPrefix table lay tree
                leafIdx (family 0) (digits 0).val
                  (by have := (digits 0).isLt; omega) context head hhead
              have htail :=
                evalDist_resolveDeferredSelectedChainFamily_then_runResolvedFinishIsNone
                  table lay tree leafIdx (fun index : Fin n => family index.succ)
                    (fun index : Fin n => digits index.succ) head.toDeferredContext fuel
                      computation hheadValid hheadCompletable (by
                        intro index step hstep
                        rw [hprivate.2.2]
                        exact hensured index.succ step hstep)
              calc
                _ = evalDist (do
                    let tail ← resolveDeferredSelectedChainFamily table lay tree leafIdx
                      (fun index : Fin n => family index.succ)
                      (fun index : Fin n => digits index.succ) head.toDeferredContext
                    match tail with
                    | none => pure true
                    | some (finalContext, _) =>
                        runResolvedFinishIsNone finalContext fuel table computation) := by
                      apply congrArg evalDist
                      simp only [bind_assoc]
                      apply bind_congr
                      intro tailOption
                      cases tailOption <;> simp
                _ = _ := htail
        _ = _ :=
          evalDist_resolveDeferredChainPrefix_then_runResolvedFinishIsNone table lay tree
            leafIdx (family 0) (digits 0).val
              (by have := (digits 0).isLt; omega) context fuel computation hvalid
                hcompletable (fun step hstep => hensured 0 step hstep)

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredLayerPathFamily_then_runResolvedFinishIsNone
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) :
    ∀ {n : Nat} (family : Fin n → Fin maxLayerHeight)
      (context : DeferredContext) (fuel : Nat)
      (computation : OracleComp (LazyRevealProbe.World Coordinate) α),
      context.Valid → DeferredCompletable table context →
      (∀ index, (family index).val < layerHeight lay →
        TreeNodeEnsured lay tree (family index).val
          (Nat.xor (leafIdx.val / 2 ^ (family index).val) 1) context) →
      evalDist (do
        let resolved ← resolveDeferredLayerPathFamily table lay tree leafIdx family context
        match resolved with
        | none => pure true
        | some (finalContext, _) =>
            runResolvedFinishIsNone finalContext fuel table computation) =
      evalDist (runResolvedFinishIsNone context fuel table computation)
  | 0, family, context, fuel, computation, _hvalid, _hcompletable, _hensured => by
      simp [resolveDeferredLayerPathFamily]
  | n + 1, family, context, fuel, computation, hvalid, hcompletable, hensured => by
      rw [resolveDeferredLayerPathFamily]
      by_cases hinLayer : (family 0).val < layerHeight lay
      · simp only [hinLayer, ↓reduceDIte, bind_assoc]
        calc
          _ = evalDist (resolveDeferredTreeNode table lay tree (family 0).val
                (Nat.xor (leafIdx.val / 2 ^ (family 0).val) 1)
                  (by have := (family 0).isLt; omega) context >>= fun headOption =>
              match headOption with
              | none => pure true
              | some head =>
                  runResolvedFinishIsNone head.toDeferredContext fuel table computation) := by
            apply evalDist_bind_congr
            intro headOption hhead
            cases headOption with
            | none => rfl
            | some head =>
                have hheadValid := hvalid.of_resolveDeferredTreeNode table lay tree
                  (family 0).val (Nat.xor (leafIdx.val / 2 ^ (family 0).val) 1)
                    (by have := (family 0).isLt; omega) head hhead
                have hheadCompletable := hcompletable.of_resolveDeferredTreeNode hvalid hhead
                have hprivate := privateStateAgrees_resolveDeferredTreeNode table lay tree
                  (family 0).val (Nat.xor (leafIdx.val / 2 ^ (family 0).val) 1)
                    (by have := (family 0).isLt; omega) context head hhead
                have htail :=
                  evalDist_resolveDeferredLayerPathFamily_then_runResolvedFinishIsNone
                    table lay tree leafIdx (fun index : Fin n => family index.succ)
                      head.toDeferredContext fuel computation hheadValid hheadCompletable (by
                        intro index hindex
                        apply (treeNodeEnsured_congr_ensured lay tree
                          (family index.succ).val
                          (Nat.xor (leafIdx.val / 2 ^ (family index.succ).val) 1)
                            context head.toDeferredContext hprivate.2.2.symm).mp
                        exact hensured index.succ hindex)
                calc
                  _ = evalDist (do
                      let tail ← resolveDeferredLayerPathFamily table lay tree leafIdx
                        (fun index : Fin n => family index.succ) head.toDeferredContext
                      match tail with
                      | none => pure true
                      | some (finalContext, _) =>
                          runResolvedFinishIsNone finalContext fuel table computation) := by
                        apply congrArg evalDist
                        simp only [bind_assoc]
                        apply bind_congr
                        intro tailOption
                        cases tailOption <;> simp
                  _ = _ := htail
          _ = _ := evalDist_resolveDeferredTreeNode_then_runResolvedFinishIsNone table lay tree
            (family 0).val (Nat.xor (leafIdx.val / 2 ^ (family 0).val) 1)
              (by have := (family 0).isLt; omega) context fuel computation hvalid
                hcompletable (hensured 0 hinLayer)
      · simp only [hinLayer, ↓reduceDIte, bind_assoc]
        calc
          _ = evalDist (do
              let tail ← resolveDeferredLayerPathFamily table lay tree leafIdx
                (fun index : Fin n => family index.succ) context
              match tail with
              | none => pure true
              | some (finalContext, _) =>
                  runResolvedFinishIsNone finalContext fuel table computation) := by
                apply congrArg evalDist
                apply bind_congr
                intro tailOption
                cases tailOption <;> simp
          _ = _ :=
            evalDist_resolveDeferredLayerPathFamily_then_runResolvedFinishIsNone table lay tree
              leafIdx (fun index : Fin n => family index.succ) context fuel computation hvalid
                hcompletable (fun index hindex => hensured index.succ hindex)

theorem DeferredCompletable.of_resolveDeferredSelectedChainFamily
    {table : OtsSecretIndex → HashOutput} {lay : Layer} {tree : TreeIndex}
    {leafIdx : LeafIndex} {context : DeferredContext}
    (hcompletable : DeferredCompletable table context) (hvalid : context.Valid) :
    ∀ {n : Nat} (family : Fin n → ChainIndex) (digits : Fin n → Digit)
      (finalContext : DeferredContext) (values : Fin n → Digest),
      some (finalContext, values) ∈ support
        (resolveDeferredSelectedChainFamily table lay tree leafIdx family digits context) →
      DeferredCompletable table finalContext
  | 0, family, digits, finalContext, values, hresult => by
      simp [resolveDeferredSelectedChainFamily] at hresult
      rw [hresult.1]
      exact hcompletable
  | n + 1, family, digits, finalContext, values, hresult => by
      rw [resolveDeferredSelectedChainFamily, mem_support_bind_iff] at hresult
      obtain ⟨headOption, hhead, hrest⟩ := hresult
      cases headOption with
      | none => simp at hrest
      | some head =>
          rw [mem_support_bind_iff] at hrest
          obtain ⟨tailOption, htail, hreturn⟩ := hrest
          cases tailOption with
          | none => simp at hreturn
          | some tail =>
              rcases tail with ⟨tailContext, tailValues⟩
              have hreturn' : finalContext = tailContext ∧
                  values = Fin.cases (truncateHash head.output) tailValues := by
                simpa using hreturn
              rw [hreturn'.1]
              have hheadCompletable := hcompletable.of_resolveDeferredChainPrefix hvalid hhead
              have hheadValid := hvalid.of_resolveDeferredChainPrefix table lay tree leafIdx
                (family 0) (digits 0).val (by have := (digits 0).isLt; omega) head hhead
              exact hheadCompletable.of_resolveDeferredSelectedChainFamily hheadValid
                (fun index : Fin n => family index.succ)
                  (fun index : Fin n => digits index.succ) tailContext tailValues htail

theorem DeferredCompletable.of_resolveDeferredLayerPathFamily
    {table : OtsSecretIndex → HashOutput} {lay : Layer} {tree : TreeIndex}
    {leafIdx : LeafIndex} {context : DeferredContext}
    (hcompletable : DeferredCompletable table context) (hvalid : context.Valid) :
    ∀ {n : Nat} (family : Fin n → Fin maxLayerHeight)
      (finalContext : DeferredContext) (values : Fin n → Digest),
      some (finalContext, values) ∈ support
        (resolveDeferredLayerPathFamily table lay tree leafIdx family context) →
      DeferredCompletable table finalContext
  | 0, family, finalContext, values, hresult => by
      simp [resolveDeferredLayerPathFamily] at hresult
      rw [hresult.1]
      exact hcompletable
  | n + 1, family, finalContext, values, hresult => by
      rw [resolveDeferredLayerPathFamily] at hresult
      by_cases hinLayer : (family 0).val < layerHeight lay
      · simp only [hinLayer, ↓reduceDIte, mem_support_bind_iff] at hresult
        obtain ⟨headOption, hhead, hrest⟩ := hresult
        cases headOption with
        | none => simp at hrest
        | some head =>
            rw [mem_support_bind_iff] at hrest
            obtain ⟨tailOption, htail, hreturn⟩ := hrest
            cases tailOption with
            | none => simp at hreturn
            | some tail =>
                rcases tail with ⟨tailContext, tailValues⟩
                have hreturn' : finalContext = tailContext ∧
                    values = Fin.cases (truncateHash head.output) tailValues := by
                  simpa using hreturn
                rw [hreturn'.1]
                have hheadCompletable := hcompletable.of_resolveDeferredTreeNode hvalid hhead
                have hheadValid := hvalid.of_resolveDeferredTreeNode table lay tree
                  (family 0).val (Nat.xor (leafIdx.val / 2 ^ (family 0).val) 1)
                    (by have := (family 0).isLt; omega) head hhead
                exact hheadCompletable.of_resolveDeferredLayerPathFamily hheadValid
                  (fun index : Fin n => family index.succ) tailContext tailValues htail
      · simp only [hinLayer, ↓reduceDIte, mem_support_bind_iff] at hresult
        obtain ⟨tailOption, htail, hreturn⟩ := hresult
        cases tailOption with
        | none => simp at hreturn
        | some tail =>
            rcases tail with ⟨tailContext, tailValues⟩
            have hreturn' : finalContext = tailContext ∧
                values = Fin.cases 0 tailValues := by
              simpa using hreturn
            rw [hreturn'.1]
            exact hcompletable.of_resolveDeferredLayerPathFamily hvalid
              (fun index : Fin n => family index.succ) tailContext tailValues htail

def LayerValuesEnsured (index : Index) (lay : Layer) (encoding : ChainIndex → Digit)
    (context : DeferredContext) : Prop :=
  (∀ chainIdx (step : ChainStep), step.val < (encoding chainIdx).val →
      Coordinate.position
        (.chain lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx step) ∈
          context.state.ensured) ∧
    ∀ level : Fin maxLayerHeight, level.val < layerHeight lay →
      TreeNodeEnsured lay (treeIndexAt index lay) level.val
        (Nat.xor ((leafIndexAt index lay).val / 2 ^ level.val) 1) context

noncomputable def runResolvedPairFinishIsNone
    (run : ProbComp (Option (DeferredContext × β))) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) : ProbComp Bool := do
  let resolved ← run
  match resolved with
  | none => pure true
  | some (finalContext, _) =>
      runResolvedFinishIsNone finalContext fuel table computation

theorem evalDist_runResolvedPair_selectedChainFamily
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) {n : Nat} (family : Fin n → ChainIndex)
    (digits : Fin n → Digit) (context : DeferredContext) (fuel : Nat)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hensured : ∀ index (step : ChainStep), step.val < (digits index).val →
      Coordinate.position (.chain lay tree leafIdx (family index) step) ∈
        context.state.ensured) :
    evalDist (runResolvedPairFinishIsNone
      (resolveDeferredSelectedChainFamily table lay tree leafIdx family digits context)
        fuel table computation) =
      evalDist (runResolvedFinishIsNone context fuel table computation) := by
  unfold runResolvedPairFinishIsNone
  let hbase :=
    evalDist_resolveDeferredSelectedChainFamily_then_runResolvedFinishIsNone table lay tree
      leafIdx family digits context fuel computation hvalid hcompletable hensured
  apply Eq.trans _ hbase
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro resolved
  cases resolved with
  | none => rfl
  | some resolved =>
      rcases resolved with ⟨finalContext, values⟩
      rfl

theorem evalDist_runResolvedPair_layerPathFamily
    (table : OtsSecretIndex → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) {n : Nat} (family : Fin n → Fin maxLayerHeight)
    (context : DeferredContext) (fuel : Nat)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hensured : ∀ index, (family index).val < layerHeight lay →
      TreeNodeEnsured lay tree (family index).val
        (Nat.xor (leafIdx.val / 2 ^ (family index).val) 1) context) :
    evalDist (runResolvedPairFinishIsNone
      (resolveDeferredLayerPathFamily table lay tree leafIdx family context)
        fuel table computation) =
      evalDist (runResolvedFinishIsNone context fuel table computation) := by
  unfold runResolvedPairFinishIsNone
  let hbase := evalDist_resolveDeferredLayerPathFamily_then_runResolvedFinishIsNone table lay
    tree leafIdx family context fuel computation hvalid hcompletable hensured
  apply Eq.trans _ hbase
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro resolved
  cases resolved with
  | none => rfl
  | some resolved =>
      rcases resolved with ⟨finalContext, values⟩
      rfl

set_option maxRecDepth 100000 in
theorem ensuredLE_of_mem_runResolvedFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (result : ResolvedRunResult α)
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table computation)) :
    LazyRevealProbe.EnsuredLE context.state result.context.state := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      simp [runResolvedFromTable] at hresult
      subst result
      exact LazyRevealProbe.EnsuredLE.refl context.state
  | query_bind query next ih =>
      cases query with
      | uniform n =>
          rw [runResolvedFromTable_uniform_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output context fuel hrest
      | hashOutput =>
          rw [runResolvedFromTable_hashOutput_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output context fuel hrest
      | ensure coordinate =>
          rw [runResolvedFromTable_ensure_query_bind] at hresult
          exact (LazyRevealProbe.ensuredLE_ensure context.state coordinate).trans
            (ih () { context with state := context.state.ensure coordinate } fuel hresult)
      | probe coordinate candidate =>
          rw [runResolvedFromTable_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · exact ih () context remaining (by simpa [hrevealed] using hresult)
              · exact (LazyRevealProbe.ensuredLE_addPending context.state coordinate
                    candidate).trans
                  (ih () { context with state := context.state.addPending coordinate candidate }
                    remaining (by simpa [hrevealed] using hresult))
      | peek coordinate =>
          rw [runResolvedFromTable_peek_query_bind] at hresult
          exact ih (context.state.values coordinate) context fuel hresult
      | publish coordinate =>
          rw [runResolvedFromTable_publish_query_bind] at hresult
          exact (LazyRevealProbe.ensuredLE_publish context.state coordinate).trans
            (ih () { context with state := context.state.publish coordinate } fuel hresult)
      | reveal coordinate =>
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              rw [runResolvedFromTable_reveal_query_bind, mem_support_bind_iff] at hresult
              obtain ⟨resolvedOption, _hresolved, hrest⟩ := hresult
              cases resolvedOption with
              | none => simp at hrest
              | some resolved =>
                  exact (LazyRevealProbe.ensuredLE_materialize context.state
                        (.chainStart lay tree leafIdx chainIdx) resolved.output).trans
                    (ih resolved.output
                      { state := context.state.materialize
                          (.chainStart lay tree leafIdx chainIdx) resolved.output
                        values := resolved.values }
                      fuel hrest)
          | position position =>
              rw [runResolvedFromTable_reveal_query_bind, mem_support_bind_iff] at hresult
              obtain ⟨resolvedOption, _hresolved, hrest⟩ := hresult
              cases resolvedOption with
              | none => simp at hrest
              | some resolved =>
                  exact (LazyRevealProbe.ensuredLE_materialize context.state
                        (.position position) resolved.output).trans
                    (ih resolved.output
                      { state := context.state.materialize (.position position)
                          resolved.output
                        values := resolved.values }
                      fuel hrest)

structure ResolvedEnsuresCoordinate (coordinate : Coordinate)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop where
  of_run : ∀ table context fuel cache result,
    some result ∈ support
      (runResolvedFromTable context fuel table (computation.run cache)) →
    coordinate ∈ result.context.state.ensured

theorem ResolvedEnsuresCoordinate.bind_preserved
    {coordinate : Coordinate}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {next : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hleft : ResolvedEnsuresCoordinate coordinate left) :
    ResolvedEnsuresCoordinate coordinate (left >>= next) := by
  constructor
  intro table context fuel cache result hresult
  rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨middleOption, hmiddle, hrest⟩ := hresult
  cases middleOption with
  | none => simp at hrest
  | some middle =>
      have hcoordinate := hleft.of_run table context fuel cache middle hmiddle
      exact (ensuredLE_of_mem_runResolvedFromTable
        ((next middle.value.1).run middle.value.2) middle.context middle.remaining
          middle.table result hrest) hcoordinate

theorem ResolvedEnsuresCoordinate.bind_right
    {coordinate : Coordinate}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {next : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hnext : ∀ value, ResolvedEnsuresCoordinate coordinate (next value)) :
    ResolvedEnsuresCoordinate coordinate (left >>= next) := by
  constructor
  intro table context fuel cache result hresult
  rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨middleOption, _hmiddle, hrest⟩ := hresult
  cases middleOption with
  | none => simp at hrest
  | some middle =>
      exact (hnext middle.value.1).of_run middle.table middle.context middle.remaining
        middle.value.2 result hrest

theorem resolvedEnsuresCoordinate_ensureCoordinate (coordinate : Coordinate) :
    ResolvedEnsuresCoordinate coordinate (ensureCoordinate coordinate) := by
  constructor
  intro table context fuel cache result hresult
  unfold ensureCoordinate at hresult
  rw [StateT.run_liftM, LazyRevealProbe.ensureQuery,
    runResolvedFromTable_ensure_query_bind] at hresult
  simp [runResolvedFromTable] at hresult
  subst result
  simp [LazyRevealProbe.State.ensure]

theorem ResolvedEnsuresCoordinate.sequenceFin_component {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (index : Fin n)
    (hensures : ResolvedEnsuresCoordinate coordinate (computation index)) :
    ResolvedEnsuresCoordinate coordinate (sequenceFin computation) := by
  induction n with
  | zero => exact index.elim0
  | succ n ih =>
      rw [sequenceFin]
      cases index using Fin.cases with
      | zero => exact hensures.bind_preserved
      | succ index =>
          apply ResolvedEnsuresCoordinate.bind_right
          intro head
          exact (ih (fun current : Fin n => computation current.succ) index
            hensures).bind_preserved

theorem resolvedEnsuresCoordinate_ensureChainPrefix
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (digit : Digit) (step : ChainStep) (hstep : step.val < digit.val) :
    ResolvedEnsuresCoordinate (.position (.chain lay tree leafIdx chainIdx step))
      (ensureChainPrefix lay tree leafIdx chainIdx digit) := by
  unfold ensureChainPrefix
  apply ResolvedEnsuresCoordinate.bind_preserved
  apply ResolvedEnsuresCoordinate.sequenceFin_component
    (fun current : ChainStep =>
      if current.val < digit.val then
        ensureCoordinate (.position (.chain lay tree leafIdx chainIdx current))
      else pure ()) step
  rw [if_pos hstep]
  exact resolvedEnsuresCoordinate_ensureCoordinate _

theorem resolvedEnsuresCoordinate_ensureFullChain
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (step : ChainStep) :
    ResolvedEnsuresCoordinate (.position (.chain lay tree leafIdx chainIdx step))
      (ensureFullChain lay tree leafIdx chainIdx) := by
  unfold ensureFullChain
  exact (ResolvedEnsuresCoordinate.sequenceFin_component
    (fun current : ChainStep =>
      ensureCoordinate (.position (.chain lay tree leafIdx chainIdx current))) step
    (resolvedEnsuresCoordinate_ensureCoordinate _)).bind_preserved

theorem resolvedEnsuresCoordinate_ensureOtsLeaf_chain
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (step : ChainStep) :
    ResolvedEnsuresCoordinate (.position (.chain lay tree leafIdx chainIdx step))
      (ensureOtsLeaf lay tree leafIdx) := by
  unfold ensureOtsLeaf
  exact (ResolvedEnsuresCoordinate.sequenceFin_component
    (fun current : ChainIndex => ensureFullChain lay tree leafIdx current) chainIdx
    (resolvedEnsuresCoordinate_ensureFullChain lay tree leafIdx chainIdx step)).bind_preserved

theorem resolvedEnsuresCoordinate_ensureOtsLeaf_leaf
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    ResolvedEnsuresCoordinate (.position (.leaf lay tree leafIdx))
      (ensureOtsLeaf lay tree leafIdx) := by
  unfold ensureOtsLeaf
  apply ResolvedEnsuresCoordinate.bind_right
  intro values
  exact resolvedEnsuresCoordinate_ensureCoordinate _

theorem TreeNodeEnsured.mono
    {lay : Layer} {tree : TreeIndex} {level nodeIdx : Nat}
    {left right : DeferredContext}
    (htree : TreeNodeEnsured lay tree level nodeIdx left)
    (hle : LazyRevealProbe.EnsuredLE left.state right.state) :
    TreeNodeEnsured lay tree level nodeIdx right := by
  induction level generalizing nodeIdx with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro chainIdx step
        exact hle (htree.1 chainIdx step)
      · exact hle htree.2
  | succ level ih =>
      refine ⟨ih htree.1, ih htree.2.1, ?_⟩
      obtain ⟨hlevel, hcoordinate⟩ := htree.2.2
      exact ⟨hlevel, hle hcoordinate⟩

structure ResolvedEnsuresTreeNode (lay : Layer) (tree : TreeIndex)
    (level nodeIdx : Nat)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop where
  of_run : ∀ table context fuel cache result,
    some result ∈ support
      (runResolvedFromTable context fuel table (computation.run cache)) →
    TreeNodeEnsured lay tree level nodeIdx result.context

theorem ResolvedEnsuresTreeNode.bind_preserved
    {lay : Layer} {tree : TreeIndex} {level nodeIdx : Nat}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {next : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hleft : ResolvedEnsuresTreeNode lay tree level nodeIdx left) :
    ResolvedEnsuresTreeNode lay tree level nodeIdx (left >>= next) := by
  constructor
  intro table context fuel cache result hresult
  rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨middleOption, hmiddle, hrest⟩ := hresult
  cases middleOption with
  | none => simp at hrest
  | some middle =>
      exact (hleft.of_run table context fuel cache middle hmiddle).mono
        (ensuredLE_of_mem_runResolvedFromTable ((next middle.value.1).run middle.value.2)
          middle.context middle.remaining middle.table result hrest)

theorem ResolvedEnsuresTreeNode.bind_right
    {lay : Layer} {tree : TreeIndex} {level nodeIdx : Nat}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {next : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hnext : ∀ value, ResolvedEnsuresTreeNode lay tree level nodeIdx (next value)) :
    ResolvedEnsuresTreeNode lay tree level nodeIdx (left >>= next) := by
  constructor
  intro table context fuel cache result hresult
  rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨middleOption, _hmiddle, hrest⟩ := hresult
  cases middleOption with
  | none => simp at hrest
  | some middle =>
      exact (hnext middle.value.1).of_run middle.table middle.context middle.remaining
        middle.value.2 result hrest

theorem ResolvedEnsuresTreeNode.sequenceFin_component {n : Nat}
    {lay : Layer} {tree : TreeIndex} {level nodeIdx : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (index : Fin n)
    (hensures : ResolvedEnsuresTreeNode lay tree level nodeIdx (computation index)) :
    ResolvedEnsuresTreeNode lay tree level nodeIdx (sequenceFin computation) := by
  induction n with
  | zero => exact index.elim0
  | succ n ih =>
      rw [sequenceFin]
      cases index using Fin.cases with
      | zero => exact hensures.bind_preserved
      | succ index =>
          apply ResolvedEnsuresTreeNode.bind_right
          intro head
          exact (ih (fun current : Fin n => computation current.succ) index
            hensures).bind_preserved

attribute [local irreducible] ensureFullChain ensureOtsLeaf

theorem resolvedEnsuresTreeNode_ensureOtsLeaf
    (lay : Layer) (tree : TreeIndex) (nodeIdx : Nat) :
    ResolvedEnsuresTreeNode lay tree 0 nodeIdx
      (ensureOtsLeaf lay tree (leafOfNat nodeIdx)) := by
  constructor
  intro table context fuel cache result hresult
  refine ⟨?_, ?_⟩
  · intro chainIdx step
    exact (resolvedEnsuresCoordinate_ensureOtsLeaf_chain lay tree (leafOfNat nodeIdx)
      chainIdx step).of_run table context fuel cache result hresult
  · exact (resolvedEnsuresCoordinate_ensureOtsLeaf_leaf lay tree (leafOfNat nodeIdx)).of_run
      table context fuel cache result hresult

theorem resolvedEnsuresTreeNode_ensureTreeNode
    (lay : Layer) (tree : TreeIndex) (level nodeIdx : Nat)
    (hlevel : level ≤ maxLayerHeight) :
    ResolvedEnsuresTreeNode lay tree level nodeIdx
      (ensureTreeNode lay tree level nodeIdx) := by
  induction level generalizing nodeIdx with
  | zero =>
      simpa only [ensureTreeNode] using
        (resolvedEnsuresTreeNode_ensureOtsLeaf lay tree nodeIdx)
  | succ level ih =>
      rw [ensureTreeNode]
      have hleft : ResolvedEnsuresTreeNode lay tree level (2 * nodeIdx)
          (do
            ensureTreeNode lay tree level (2 * nodeIdx)
            ensureTreeNode lay tree level (2 * nodeIdx + 1)
            if h : level < maxLayerHeight then
              ensureCoordinate (.position (.node lay tree ⟨level, h⟩ (leafOfNat nodeIdx)))
            else pure ()) := by
        apply ResolvedEnsuresTreeNode.bind_preserved
        exact ih (2 * nodeIdx) (by omega)
      have hright : ResolvedEnsuresTreeNode lay tree level (2 * nodeIdx + 1)
          (do
            ensureTreeNode lay tree level (2 * nodeIdx)
            ensureTreeNode lay tree level (2 * nodeIdx + 1)
            if h : level < maxLayerHeight then
              ensureCoordinate (.position (.node lay tree ⟨level, h⟩ (leafOfNat nodeIdx)))
            else pure ()) := by
        apply ResolvedEnsuresTreeNode.bind_right
        intro leftValue
        apply ResolvedEnsuresTreeNode.bind_preserved
        exact ih (2 * nodeIdx + 1) (by omega)
      have hnode : ResolvedEnsuresCoordinate
          (.position (.node lay tree ⟨level, by omega⟩ (leafOfNat nodeIdx)))
          (do
            ensureTreeNode lay tree level (2 * nodeIdx)
            ensureTreeNode lay tree level (2 * nodeIdx + 1)
            if h : level < maxLayerHeight then
              ensureCoordinate (.position (.node lay tree ⟨level, h⟩ (leafOfNat nodeIdx)))
            else pure ()) := by
        apply ResolvedEnsuresCoordinate.bind_right
        intro leftValue
        apply ResolvedEnsuresCoordinate.bind_right
        intro rightValue
        rw [dif_pos (by omega)]
        exact resolvedEnsuresCoordinate_ensureCoordinate _
      constructor
      intro table context fuel cache result hresult
      refine ⟨hleft.of_run table context fuel cache result hresult,
        hright.of_run table context fuel cache result hresult, ?_⟩
      exact ⟨by omega, hnode.of_run table context fuel cache result hresult⟩

theorem resolvedEnsuresTreeNode_ensureTreePath
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (level : Fin maxLayerHeight) (hinLayer : level.val < layerHeight lay) :
    ResolvedEnsuresTreeNode lay tree level.val
      (Nat.xor (leafIdx.val / 2 ^ level.val) 1)
      (ensureTreePath lay tree leafIdx) := by
  unfold ensureTreePath
  apply ResolvedEnsuresTreeNode.bind_preserved
  apply ResolvedEnsuresTreeNode.sequenceFin_component
    (fun current : Fin maxLayerHeight =>
      if current.val < layerHeight lay then
        ensureTreeNode lay tree current.val
          (Nat.xor (leafIdx.val / 2 ^ current.val) 1)
      else pure ()) level
  rw [if_pos hinLayer]
  exact resolvedEnsuresTreeNode_ensureTreeNode lay tree level.val
    (Nat.xor (leafIdx.val / 2 ^ level.val) 1) (by omega)

set_option maxRecDepth 100000 in
theorem chainPrefixEnsured_of_mem_runResolved_maskedOtsSignFrom
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (message : Digest) :
    ∀ attempts counter (table : OtsSecretIndex → HashOutput)
      (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
      (result : ResolvedRunResult
        (Option (Counter × (ChainIndex → Digit)) × SplitHashCache))
      (selectedCounter : Counter) (encoding : ChainIndex → Digit),
      some result ∈ support (runResolvedFromTable context fuel table
        ((maskedOtsSignFrom parameter lay tree leafIdx message attempts counter).run cache)) →
      result.value.1 = some (selectedCounter, encoding) →
      ∀ chainIdx (step : ChainStep), step.val < (encoding chainIdx).val →
        Coordinate.position (.chain lay tree leafIdx chainIdx step) ∈
          result.context.state.ensured
  | 0, counter, table, context, fuel, cache, result, selectedCounter, encoding,
      hresult, hvalue => by
      simp [maskedOtsSignFrom, runResolvedFromTable] at hresult
      subst result
      simp at hvalue
  | attempts + 1, counter, table, context, fuel, cache, result, selectedCounter,
      encoding, hresult, hvalue => by
      rw [maskedOtsSignFrom, StateT.run_bind, runResolvedFromTable_bind,
        mem_support_bind_iff] at hresult
      obtain ⟨encodedOption, _hencoded, hrest⟩ := hresult
      cases encodedOption with
      | none => simp at hrest
      | some encodedResult =>
          rcases encodedResult with
            ⟨encodedContext, encodedRemaining, ⟨encoded, encodedCache⟩, encodedTable⟩
          simp only at hrest
          cases encoded with
          | none =>
              exact chainPrefixEnsured_of_mem_runResolved_maskedOtsSignFrom parameter lay tree
                leafIdx message attempts (counter + 1) encodedTable encodedContext
                  encodedRemaining encodedCache result
                    selectedCounter encoding hrest hvalue
          | some selectedEncoding =>
              rw [StateT.run_bind, runResolvedFromTable_bind,
                mem_support_bind_iff] at hrest
              obtain ⟨ensureOption, hensure, hfinish⟩ := hrest
              cases ensureOption with
              | none => simp at hfinish
              | some ensureResult =>
                  simp [runResolvedFromTable] at hfinish
                  subst result
                  simp only [Option.some.injEq, Prod.mk.injEq] at hvalue
                  rcases hvalue with ⟨_hcounter, hencoding⟩
                  subst encoding
                  intro chainIdx step hstep
                  exact (ResolvedEnsuresCoordinate.sequenceFin_component
                    (fun current : ChainIndex =>
                      ensureChainPrefix lay tree leafIdx current (selectedEncoding current))
                    chainIdx (resolvedEnsuresCoordinate_ensureChainPrefix lay tree leafIdx
                      chainIdx (selectedEncoding chainIdx) step hstep)).of_run
                        encodedTable encodedContext encodedRemaining encodedCache ensureResult
                          hensure

theorem chainPrefixEnsured_of_mem_runResolved_maskedOtsSign
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (message : Digest) (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (result : ResolvedRunResult
      (Option (Counter × (ChainIndex → Digit)) × SplitHashCache))
    (selectedCounter : Counter) (encoding : ChainIndex → Digit)
    (hresult : some result ∈ support (runResolvedFromTable context fuel table
      ((maskedOtsSign parameter lay tree leafIdx message).run cache)))
    (hvalue : result.value.1 = some (selectedCounter, encoding)) :
    ∀ chainIdx (step : ChainStep), step.val < (encoding chainIdx).val →
      Coordinate.position (.chain lay tree leafIdx chainIdx step) ∈
        result.context.state.ensured := by
  exact chainPrefixEnsured_of_mem_runResolved_maskedOtsSignFrom parameter lay tree leafIdx
    message encodingAttemptLimit 0 table context fuel cache result selectedCounter encoding
      hresult hvalue

set_option maxRecDepth 100000 in
theorem layerValuesEnsured_of_mem_runResolved_maskedSignLayer
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer) (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (result : ResolvedRunResult
      (Option (Counter × (ChainIndex → Digit)) × SplitHashCache))
    (counter : Counter) (encoding : ChainIndex → Digit)
    (hresult : some result ∈ support (runResolvedFromTable context fuel table
      ((maskedSignLayer parameter ftsSecret index lay).run cache)))
    (hvalue : result.value.1 = some (counter, encoding)) :
    LayerValuesEnsured index lay encoding result.context := by
  unfold maskedSignLayer at hresult
  rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨messageOption, _hmessage, hrest⟩ := hresult
  cases messageOption with
  | none => simp at hrest
  | some messageResult =>
      rcases messageResult with
        ⟨messageContext, messageRemaining, ⟨message, messageCache⟩, messageTable⟩
      simp only at hrest
      rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hrest
      obtain ⟨otsOption, hots, hafterOts⟩ := hrest
      cases otsOption with
      | none => simp at hafterOts
      | some otsResult =>
          rcases otsResult with
            ⟨otsContext, otsRemaining, ⟨selected, otsCache⟩, otsTable⟩
          simp only at hafterOts
          cases selected with
          | none =>
              simp [runResolvedFromTable] at hafterOts
              subst result
              simp at hvalue
          | some selected =>
              rcases selected with ⟨selectedCounter, selectedEncoding⟩
              rw [StateT.run_bind, runResolvedFromTable_bind,
                mem_support_bind_iff] at hafterOts
              obtain ⟨pathOption, hpath, hfinish⟩ := hafterOts
              cases pathOption with
              | none => simp at hfinish
              | some pathResult =>
                  simp [runResolvedFromTable] at hfinish
                  subst result
                  simp only [Option.some.injEq, Prod.mk.injEq] at hvalue
                  rcases hvalue with ⟨_hcounter, hencoding⟩
                  subst encoding
                  have hchainBefore :=
                    chainPrefixEnsured_of_mem_runResolved_maskedOtsSign parameter lay
                      (treeIndexAt index lay) (leafIndexAt index lay) message
                        messageTable messageContext messageRemaining messageCache
                          ⟨otsContext, otsRemaining,
                            (some (selectedCounter, selectedEncoding), otsCache), otsTable⟩
                              selectedCounter selectedEncoding hots rfl
                  have hpathMono := ensuredLE_of_mem_runResolvedFromTable
                    ((ensureTreePath lay (treeIndexAt index lay)
                      (leafIndexAt index lay)).run otsCache) otsContext otsRemaining otsTable
                        pathResult hpath
                  refine ⟨?_, ?_⟩
                  · intro chainIdx step hstep
                    exact hpathMono (hchainBefore chainIdx step hstep)
                  · intro level hlevel
                    exact (resolvedEnsuresTreeNode_ensureTreePath lay
                      (treeIndexAt index lay) (leafIndexAt index lay) level hlevel).of_run
                        otsTable otsContext otsRemaining otsCache
                          pathResult hpath

theorem deferredCompletable_of_mem_runResolved_maskedSignLayer
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer) (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (result : ResolvedRunResult
      (Option (Counter × (ChainIndex → Digit)) × SplitHashCache))
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hresult : some result ∈ support (runResolvedFromTable context fuel table
      ((maskedSignLayer parameter ftsSecret index lay).run cache))) :
    DeferredCompletable table result.context := by
  have hstarts := startTableAgrees_of_deferredCompletable hcompletable
  have hview := finalizationViewEq_of_deferredCompletion_iff hvalid hvalid hstarts hstarts
    rfl hcompletable (fun _ => Iff.rfl)
  have hrelation := finalizationMaterializedCouples_maskedSignLayer table parameter ftsSecret
    index lay context context fuel cache cache
      ⟨hview, hvalid, hvalid, hcompletable⟩ rfl rfl
  obtain ⟨rightResult, _hright, hresultRelation⟩ :=
    exists_right_of_relTriple_of_mem_support hrelation hresult
  cases rightResult with
  | none => simp [FinalizationMaterializedRunEq] at hresultRelation
  | some rightResult =>
      rcases hresultRelation with
        ⟨_hvalue, hcontexts, _hfuel, _hleftTable, _hrightTable, _hcache, _hrevealed⟩
      exact hcontexts.2.2.2

theorem selectedLayerValuesEnsured_of_mem_selectDeferredLayer
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (lay : Layer) (input output : ResolvedRunResult DeferredLayerStore)
    (counter : Counter) (encoding : ChainIndex → Digit)
    (houtput : some output ∈ support
      (selectDeferredLayer parameter table ftsSecret index lay input))
    (hselected : output.value.selected lay = some (counter, encoding)) :
    LayerValuesEnsured index lay encoding output.context := by
  unfold selectDeferredLayer at houtput
  rw [mem_support_bind_iff] at houtput
  obtain ⟨selectedOption, hrun, hreturn⟩ := houtput
  cases selectedOption with
  | none => simp at hreturn
  | some selected =>
      simp only [support_pure, Set.mem_singleton_iff] at hreturn
      have houtputEq := Option.some.inj hreturn
      subst output
      have hvalue : selected.value.1 = some (counter, encoding) := by
        simpa using hselected
      exact layerValuesEnsured_of_mem_runResolved_maskedSignLayer parameter ftsSecret index lay
        table input.context input.remaining input.value.cache selected counter encoding hrun hvalue

theorem deferredCompletable_of_mem_selectDeferredLayer
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (lay : Layer) (input output : ResolvedRunResult DeferredLayerStore)
    (hvalid : input.context.Valid)
    (hcompletable : DeferredCompletable table input.context)
    (houtput : some output ∈ support
      (selectDeferredLayer parameter table ftsSecret index lay input)) :
    DeferredCompletable table output.context := by
  unfold selectDeferredLayer at houtput
  rw [mem_support_bind_iff] at houtput
  obtain ⟨selectedOption, hrun, hreturn⟩ := houtput
  cases selectedOption with
  | none => simp at hreturn
  | some selected =>
      simp only [support_pure, Set.mem_singleton_iff] at hreturn
      have houtputEq := Option.some.inj hreturn
      subst output
      exact deferredCompletable_of_mem_runResolved_maskedSignLayer parameter ftsSecret index lay
        table input.context input.remaining input.value.cache selected hvalid hcompletable hrun

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredLayerValues_then_runResolvedFinishIsNone
    (table : OtsSecretIndex → HashOutput) (index : Index) (lay : Layer)
    (encoding : ChainIndex → Digit) (context : DeferredContext) (fuel : Nat)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hensured : LayerValuesEnsured index lay encoding context) :
    evalDist (do
      let resolved ← resolveDeferredLayerValues table index lay encoding context
      match resolved with
      | none => pure true
      | some (finalContext, _) =>
          runResolvedFinishIsNone finalContext fuel table computation) =
    evalDist (runResolvedFinishIsNone context fuel table computation) := by
  let chainFamily : ChainIndex → ChainIndex := fun chainIdx => chainIdx
  let pathFamily : Fin maxLayerHeight → Fin maxLayerHeight := fun level => level
  change evalDist (do
      let resolved ← resolveDeferredLayerValues table index lay encoding context
      match resolved with
      | none => pure true
      | some (finalContext, _) =>
          runResolvedFinishIsNone finalContext fuel table computation) = _
  rw [resolveDeferredLayerValues]
  simp only [bind_assoc]
  calc
    _ = evalDist (resolveDeferredSelectedChainFamily table lay (treeIndexAt index lay)
          (leafIndexAt index lay) chainFamily encoding context >>=
        fun chainsOption =>
          match chainsOption with
          | none => pure true
          | some (afterChains, _) =>
              runResolvedFinishIsNone afterChains fuel table computation) := by
      apply evalDist_bind_congr
      intro chainsOption hchains
      cases chainsOption with
      | none => rfl
      | some chains =>
          rcases chains with ⟨afterChains, chainValues⟩
          have hchainsValid := hvalid.of_resolveDeferredSelectedChainFamily table lay
            (treeIndexAt index lay) (leafIndexAt index lay)
              chainFamily encoding afterChains chainValues hchains
          have hchainsCompletable :=
            hcompletable.of_resolveDeferredSelectedChainFamily hvalid
              chainFamily encoding afterChains chainValues hchains
          have hprivate := privateStateAgrees_resolveDeferredSelectedChainFamily table lay
            (treeIndexAt index lay) (leafIndexAt index lay)
              chainFamily encoding context afterChains chainValues
                hchains
          have hpath := evalDist_resolveDeferredLayerPathFamily_then_runResolvedFinishIsNone
            table lay (treeIndexAt index lay) (leafIndexAt index lay)
              pathFamily afterChains fuel computation
                hchainsValid hchainsCompletable (by
                  intro level hlevel
                  apply (treeNodeEnsured_congr_ensured lay (treeIndexAt index lay) level.val
                    (Nat.xor ((leafIndexAt index lay).val / 2 ^ level.val) 1)
                      context afterChains hprivate.2.2.symm).mp
                  exact hensured.2 level hlevel)
          calc
            _ = evalDist (do
                let path ← resolveDeferredLayerPathFamily table lay (treeIndexAt index lay)
                  (leafIndexAt index lay) (fun level : Fin maxLayerHeight => level) afterChains
                match path with
                | none => pure true
                | some (finalContext, _) =>
                    runResolvedFinishIsNone finalContext fuel table computation) := by
                  apply congrArg evalDist
                  simp only [bind_assoc]
                  apply bind_congr
                  intro pathOption
                  cases pathOption <;> simp
            _ = evalDist (runResolvedFinishIsNone afterChains fuel table computation) := by
              apply Eq.trans _ hpath
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro resolved
              cases resolved with
              | none => rfl
              | some resolved =>
                  rcases resolved with ⟨finalContext, values⟩
                  rfl
            _ = _ := rfl
    _ = evalDist (runResolvedFinishIsNone context fuel table computation) := by
      let hbase :=
        evalDist_resolveDeferredSelectedChainFamily_then_runResolvedFinishIsNone table lay
          (treeIndexAt index lay) (leafIndexAt index lay) chainFamily encoding context fuel
            computation hvalid hcompletable hensured.1
      apply Eq.trans _ hbase
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro resolved
      cases resolved with
      | none => rfl
      | some resolved =>
          rcases resolved with ⟨finalContext, values⟩
          rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
