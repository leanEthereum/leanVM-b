import SphincsSecurity.Proof.OtsProbeResolvedDirectPositionNeutral

/-! Direct interpreter synchronization without a position-neutrality assumption. -/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

theorem evalDist_runDirectResolvedObserve_eq_of_finalizationSynchronized
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (left right : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    {observe : DeferredContext → Nat → α → ProbComp Bool}
    [ObserverDooms table observe] [ObserverSynchronized table observe]
    (hcontext : FinalizationContextEq table (some left) (some right))
    (hvalues : left.state.values = right.state.values)
    (hrevealed : left.state.revealed = right.state.revealed) :
    evalDist (runDirectResolvedObserve observe left fuel table computation) =
      evalDist (runDirectResolvedObserve observe right fuel table computation) := by
  induction computation using OracleComp.inductionOn generalizing left right fuel with
  | pure value =>
      unfold runDirectResolvedObserve
      simp only [runDirectResolvedFromTable]
      exact ObserverSynchronized.eq_of_synchronized left right fuel value hcontext
        hvalues hrevealed
  | query_bind query next ih =>
      cases query with
      | uniform n =>
          unfold runDirectResolvedObserve
          simp only [runDirectResolvedFromTable_uniform_query_bind, bind_assoc]
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro output
          exact ih output left right fuel hcontext hvalues hrevealed
      | hashOutput =>
          unfold runDirectResolvedObserve
          simp only [runDirectResolvedFromTable_hashOutput_query_bind, bind_assoc]
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro output
          exact ih output left right fuel hcontext hvalues hrevealed
      | ensure coordinate =>
          unfold runDirectResolvedObserve
          simp only [runDirectResolvedFromTable_ensure_query_bind]
          rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
          apply ih ()
          · exact ⟨hview.ensure coordinate, hleftValid.ensure coordinate,
              hrightValid.ensure coordinate, hleftCompletable.ensure coordinate⟩
          · exact hvalues
          · exact hrevealed
      | peek coordinate =>
          unfold runDirectResolvedObserve
          simp only [runDirectResolvedFromTable_peek_query_bind]
          rw [hvalues]
          exact ih (right.state.values coordinate) left right fuel hcontext hvalues hrevealed
      | publish coordinate =>
          unfold runDirectResolvedObserve
          simp only [runDirectResolvedFromTable_publish_query_bind]
          rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
          apply ih ()
          · exact ⟨hview.publish coordinate, hleftValid.publish coordinate,
              hrightValid.publish coordinate, hleftCompletable.publish coordinate⟩
          · exact hvalues
          · simpa [LazyRevealProbe.State.publish] using congrArg (insert coordinate) hrevealed
      | probe coordinate candidate =>
          unfold runDirectResolvedObserve
          simp only [runDirectResolvedFromTable_probe_query_bind]
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
                      evalDist_runDirectResolvedObserve_eq_true_of_not_completable_auto (observe := observe)
                        left' remaining table (next ()) hcontext.2.1.1 hcontext.1.leftStarts
                        hleftCompletable
                    _ = evalDist (runDirectResolvedObserve observe right' remaining table
                        (next ())) :=
                      (evalDist_runDirectResolvedObserve_eq_true_of_not_completable_auto (observe := observe)
                        right' remaining table (next ()) hcontext.2.2.1.1 hcontext.1.rightStarts
                        hrightCompletable).symm
      | reveal coordinate =>
          unfold runDirectResolvedObserve
          simp_rw [runDirectResolvedFromTable_reveal_query_bind]
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
              simp only [bind_assoc]
              rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
              have hrightCompletable : DeferredCompletable table right := by
                rcases hleftCompletable with ⟨completion, hcompletion⟩
                exact ⟨completion, (hview.deferredCompletion_iff completion).mp hcompletion⟩
              have hleftClean := hleftCompletable.not_hitAt_chainStart index
              have hrightClean := hrightCompletable.not_hitAt_chainStart index
              cases hleftState : left.state.values index.coordinate with
              | some output =>
                  have hrightState : right.state.values index.coordinate = some output := by
                    rw [← hvalues]
                    exact hleftState
                  have hleftState' : left.state.values
                      (.chainStart lay tree leafIdx chainIdx) = some output := by
                    simpa [index, OtsSecretIndex.coordinate] using hleftState
                  have hrightState' : right.state.values
                      (.chainStart lay tree leafIdx chainIdx) = some output := by
                    simpa [index, OtsSecretIndex.coordinate] using hrightState
                  rw [hleftState', hrightState']
                  simpa only [runDirectResolvedObserve] using
                      ih output left right fuel
                        ⟨hview, hleftValid, hrightValid, hleftCompletable⟩ hvalues hrevealed
              | none =>
                  have hrightState : right.state.values index.coordinate = none := by
                    rw [← hvalues]
                    exact hleftState
                  have hleftState' : left.state.values
                      (.chainStart lay tree leafIdx chainIdx) = none := by
                    simpa [index, OtsSecretIndex.coordinate] using hleftState
                  have hrightState' : right.state.values
                      (.chainStart lay tree leafIdx chainIdx) = none := by
                    simpa [index, OtsSecretIndex.coordinate] using hrightState
                  have hleftClean' : ¬left.state.hitAt
                      (.chainStart lay tree leafIdx chainIdx)
                        (table ⟨lay, tree, leafIdx, chainIdx⟩) := by
                    simpa [index, OtsSecretIndex.coordinate] using hleftClean
                  have hrightClean' : ¬right.state.hitAt
                      (.chainStart lay tree leafIdx chainIdx)
                        (table ⟨lay, tree, leafIdx, chainIdx⟩) := by
                    simpa [index, OtsSecretIndex.coordinate] using hrightClean
                  let leftResolved : DeferredResolution :=
                    ⟨{ state := left.state.clearPending index.coordinate,
                        values := left.values }, table index⟩
                  let rightResolved : DeferredResolution :=
                    ⟨{ state := right.state.clearPending index.coordinate,
                        values := right.values }, table index⟩
                  have hleftResult :
                      resolveDeferredChainStart table index left = some leftResolved :=
                    resolveDeferredChainStart_of_agrees table index left hview.leftStarts
                      hleftClean
                  have hrightResult :
                      resolveDeferredChainStart table index right = some rightResolved :=
                    resolveDeferredChainStart_of_agrees table index right hview.rightStarts
                      hrightClean
                  have hrawView := finalizationViewEq_resolveDeferredChainStart index
                    leftResolved rightResolved hview hleftValid hrightValid hleftCompletable
                    hleftResult hrightResult
                  have hleftRawValid := hleftValid.of_resolveDeferredChainStart table index
                    leftResolved hleftResult
                  have hrightRawValid := hrightValid.of_resolveDeferredChainStart table index
                    rightResolved hrightResult
                  have hleftMaterializedCompletable :=
                    hleftCompletable.materializeResolvedChainStart hview.leftStarts index
                      leftResolved hleftResult
                  have hrightMaterializedCompletable :=
                    hrightCompletable.materializeResolvedChainStart hview.rightStarts index
                      rightResolved hrightResult
                  have hleftMaterializedView :=
                    finalizationViewEq_materializeResolvedChainStart index leftResolved
                      hleftValid hview.leftStarts hleftResult hleftMaterializedCompletable
                  have hrightMaterializedView :=
                    finalizationViewEq_materializeResolvedChainStart index rightResolved
                      hrightValid hview.rightStarts hrightResult hrightMaterializedCompletable
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
                        (hrawView.trans hrightMaterializedView.symm),
                      hleftMaterializedValid, hrightMaterializedValid,
                      hleftMaterializedCompletable⟩
                    (by
                      change Function.update left.state.values index.coordinate
                          (some leftResolved.output) =
                        Function.update right.state.values index.coordinate
                          (some rightResolved.output)
                      rw [hvalues])
                    (by
                      simpa [materializeResolvedChainStart,
                        LazyRevealProbe.State.materialize] using hrevealed)
                  rw [hleftState', hrightState', if_neg hleftClean', if_neg hrightClean']
                  simpa only [runDirectResolvedObserve, index, OtsSecretIndex.coordinate,
                    leftResolved,
                    rightResolved, materializeResolvedChainStart] using hnext
          | position position =>
              simp only [bind_assoc]
              rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
              cases hleftState : left.state.values (.position position) with
              | some output =>
                  have hrightState : right.state.values (.position position) = some output := by
                    rw [← hvalues]
                    exact hleftState
                  simpa only [runDirectResolvedObserve, hleftState, hrightState] using
                    ih output left right fuel
                      ⟨hview, hleftValid, hrightValid, hleftCompletable⟩ hvalues hrevealed
              | none =>
                have hrightState : right.state.values (.position position) = none := by
                  rw [← hvalues]
                  exact hleftState
                rw [hrightState]
                simp only [bind_assoc]
                have hresolved := relTriple_resolveDeferredPositionValue_of_finalizationViewEq
                  table position left right hview hleftValid hrightValid hleftCompletable
                have hresolvedLeft :=
                  SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hresolved
                    (fun result => result ∈ support
                      (resolveDeferredPositionValue position left))
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
                    | none => simp [EqRel]
                    | some rightResolved => simp [FinalizationResolutionEq] at hrelation
                | some leftResolved =>
                    cases rightResolved with
                    | none => simp [FinalizationResolutionEq] at hrelation
                    | some rightResolved =>
                        have hleftRawCompletable := hrelation.2.2.2.2
                        have hleftStateValues :=
                          resolveDeferredPositionValue_preserves_state_values position left
                            leftResolved hleftSupport
                        have hrightStateValues :=
                          resolveDeferredPositionValue_preserves_state_values position right
                            rightResolved hrightSupport
                        have hleftPending := resolveDeferredPositionValue_pending position left
                          leftResolved hleftSupport
                        have hrightPending := resolveDeferredPositionValue_pending position right
                          rightResolved hrightSupport
                        have hleftResolvedValue := resolveDeferredPositionValue_resolves position
                          left leftResolved hleftSupport
                        have hrightResolvedValue := resolveDeferredPositionValue_resolves position
                          right rightResolved hrightSupport
                        have hleftMaterializedCompletable : DeferredCompletable table
                            (materializeResolvedPosition left position leftResolved) := by
                          rcases hleftRawCompletable with ⟨completion, hcompletion⟩
                          exact ⟨completion,
                            (deferredCompletion_materializeResolvedPosition_iff position
                              leftResolved hleftStateValues hleftPending hleftResolvedValue).2
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
                            (deferredCompletion_materializeResolvedPosition_iff position
                              rightResolved hrightStateValues hrightPending hrightResolvedValue).2
                                hcompletion⟩
                        have hleftMaterializedView :=
                          finalizationViewEq_materializeResolvedPositionValue position leftResolved
                            hleftValid hview.leftStarts hleftSupport
                              hleftMaterializedCompletable
                        have hrightMaterializedView :=
                          finalizationViewEq_materializeResolvedPositionValue position rightResolved
                            hrightValid hview.rightStarts hrightSupport
                              hrightMaterializedCompletable
                        have hleftResultValid := hleftValid.of_resolveDeferredPositionValue
                          position leftResolved hleftSupport
                        have hrightResultValid := hrightValid.of_resolveDeferredPositionValue
                          position rightResolved hrightSupport
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
                        simpa only [runDirectResolvedObserve, hleftState, hrightState,
                          materializeResolvedPosition, hrelation.1] using hnext

end SphincsSecurity.Concrete.OtsProbeSimulation
