import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalHiddenRisk

/-!
# Hidden candidate freshness transport

The direct interpreter installs an auxiliary structural value only together with a materialized
state value. Since state values are never removed, absence of the final state value preserves
absence of the initial auxiliary value.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

def ChildValuesPublished (state : LazyRevealProbe.State Coordinate) : Prop :=
  ∀ position parent, Position.parentOf position = some parent →
    state.values (.position position) ≠ none →
    Coordinate.position position ∈ state.revealed

theorem childValuesPublished_empty :
    ChildValuesPublished (LazyRevealProbe.State.empty :
      LazyRevealProbe.State Coordinate) := by
  intro position parent hparent hvalue
  simp [LazyRevealProbe.State.empty] at hvalue

set_option maxRecDepth 100000 in
theorem auxiliaryPositionValue_none_of_done_runDirectResolvedWitnessFromTable
    (position : Position)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult α)
    (hstate : context.state.values (.position position) = none)
    (hprivate : context.values position = none)
    (hresult : DirectWitnessResult.done result ∈ support
      (runDirectResolvedWitnessFromTable context fuel table computation))
    (hfinalState : result.context.state.values (.position position) = none) :
    result.context.values position = none := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      simp [runDirectResolvedWitnessFromTable] at hresult
      subst result
      exact hprivate
  | query_bind query next ih =>
      cases query with
      | uniform n =>
          rw [runDirectResolvedWitnessFromTable_uniform_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨sampled, _hsampled, htail⟩ := hresult
          exact ih sampled context fuel hstate hprivate htail
      | hashOutput =>
          rw [runDirectResolvedWitnessFromTable_hashOutput_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨sampled, _hsampled, htail⟩ := hresult
          exact ih sampled context fuel hstate hprivate htail
      | ensure coordinate =>
          rw [runDirectResolvedWitnessFromTable_ensure_query_bind] at hresult
          exact ih () { context with state := context.state.ensure coordinate } fuel hstate
            hprivate hresult
      | probe coordinate candidate =>
          rw [runDirectResolvedWitnessFromTable_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · simp only [hrevealed, ↓reduceIte] at hresult
                exact ih () context remaining hstate hprivate hresult
              · simp only [hrevealed, ↓reduceIte] at hresult
                exact ih () { context with state := context.state.addPending coordinate candidate }
                  remaining hstate hprivate hresult
      | peek coordinate =>
          rw [runDirectResolvedWitnessFromTable_peek_query_bind] at hresult
          exact ih (context.state.values coordinate) context fuel hstate hprivate hresult
      | publish coordinate =>
          rw [runDirectResolvedWitnessFromTable_publish_query_bind] at hresult
          exact ih () { context with state := context.state.publish coordinate } fuel hstate
            hprivate hresult
      | reveal coordinate =>
          rw [runDirectResolvedWitnessFromTable_reveal_query_bind] at hresult
          cases hvalue : context.state.values coordinate with
          | some output =>
              simp only [hvalue] at hresult
              exact ih output context fuel hstate hprivate hresult
          | none =>
              simp only [hvalue] at hresult
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let output := table ⟨lay, tree, leafIdx, chainIdx⟩
                  by_cases hhit : context.state.hitAt
                      (.chainStart lay tree leafIdx chainIdx) output
                  · simp [output, hhit] at hresult
                  · simp only [output, hhit, ↓reduceIte] at hresult
                    have hnextState :
                        (context.state.materialize
                          (.chainStart lay tree leafIdx chainIdx) output).values
                            (.position position) = none := by
                      simpa [LazyRevealProbe.State.materialize] using hstate
                    exact ih output
                      { state := context.state.materialize
                          (.chainStart lay tree leafIdx chainIdx) output
                        values := context.values }
                      fuel hnextState hprivate hresult
              | position revealed =>
                  by_cases heq : revealed = position
                  · subst revealed
                    cases hprivateValue : context.values position with
                    | some output =>
                        rw [hprivate] at hprivateValue
                        contradiction
                    | none =>
                        simp only [hprivateValue] at hresult
                        rw [mem_support_bind_iff] at hresult
                        obtain ⟨output, _houtput, htail⟩ := hresult
                        by_cases hhit : context.state.hitAt (.position position) output
                        · simp [hhit] at htail
                        · simp only [hhit, ↓reduceIte] at htail
                          have hinstalled :
                              ({ state := context.state.materialize (.position position) output
                                 values := context.values.install position output } :
                                DeferredContext).state.values (.position position) = some output := by
                            simp [LazyRevealProbe.State.materialize]
                          let nextContext : DeferredContext :=
                            { state := context.state.materialize (.position position) output
                              values := context.values.install position output }
                          have hdetailed : DirectDetailedResult.done result ∈ support
                              (runDirectResolvedDetailedFromTable nextContext fuel table
                                (next output)) := by
                            rw [← map_erase_runDirectResolvedWitnessFromTable (next output)
                              nextContext fuel table, support_map]
                            exact ⟨DirectWitnessResult.done result, htail, rfl⟩
                          have hdirect := mem_support_runDirectResolvedFromTable_of_done_detailed
                            (next output) nextContext fuel table result hdetailed
                          have hraw := raw_done_of_mem_runDirectResolvedFromTable
                            (next output) nextContext fuel table result hdirect
                          have hvalues := LazyRevealProbe.valuesLE_of_mem_runRaw_done
                            (next output) nextContext.state result.context.state fuel
                              result.remaining result.value hraw
                          have hfalse : result.context.state.values (.position position) =
                              some output := hvalues (.position position) output hinstalled
                          rw [hfinalState] at hfalse
                          contradiction
                  · cases hprivateValue : context.values revealed with
                    | some output =>
                        simp only [hprivateValue] at hresult
                        by_cases hhit : context.state.hitAt (.position revealed) output
                        · simp [hhit] at hresult
                        · simp only [hhit, ↓reduceIte] at hresult
                          have hnextState :
                              (context.state.materialize (.position revealed) output).values
                                  (.position position) = none := by
                            have hcoordinate : Coordinate.position position ≠
                                .position revealed := by simpa using Ne.symm heq
                            simpa [LazyRevealProbe.State.materialize,
                              Function.update_of_ne hcoordinate] using hstate
                          exact ih output
                            { state := context.state.materialize (.position revealed) output
                              values := context.values }
                            fuel hnextState hprivate hresult
                    | none =>
                        simp only [hprivateValue] at hresult
                        rw [mem_support_bind_iff] at hresult
                        obtain ⟨output, _houtput, htail⟩ := hresult
                        by_cases hhit : context.state.hitAt (.position revealed) output
                        · simp [hhit] at htail
                        · simp only [hhit, ↓reduceIte] at htail
                          have hnextState :
                              (context.state.materialize (.position revealed) output).values
                                  (.position position) = none := by
                            have hcoordinate : Coordinate.position position ≠
                                .position revealed := by simpa using Ne.symm heq
                            simpa [LazyRevealProbe.State.materialize,
                              Function.update_of_ne hcoordinate] using hstate
                          have hnextPrivate :
                              (context.values.install revealed output) position = none := by
                            unfold DeferredStructuralValues.install
                            rw [Function.update_of_ne (Ne.symm heq)]
                            exact hprivate
                          exact ih output
                            { state := context.state.materialize (.position revealed) output
                              values := context.values.install revealed output }
                            fuel hnextState hnextPrivate htail

theorem candidatePositionsFresh_canonicalize_of_done
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult α)
    (hfresh : CandidatePositionsFresh context)
    (hpublished : PublishedValues context.state)
    (hresult : DirectWitnessResult.done result ∈ support
      (runDirectResolvedWitnessFromTable context fuel table computation))
    (hchildren : ChildValuesPublished result.context.state) :
    CandidatePositionsFresh (canonicalizeMaterializedValues table result.context) := by
  intro position parent hparent hcanonicalHidden
  have hfinalHidden : Coordinate.position position ∉ result.context.state.revealed := by
    simpa [canonicalizeMaterializedValues_revealed] using hcanonicalHidden
  have hinitialHidden : Coordinate.position position ∉ context.state.revealed := by
    intro hinitialRevealed
    obtain ⟨output, hvalue⟩ := Option.ne_none_iff_exists'.mp
      (hpublished (.position position) hinitialRevealed)
    have hknown := knownPublishedCoordinateResult_of_mem_runDirectResolvedWitnessFromTable
      (.position position) output computation context fuel table hvalue hinitialRevealed
      (DirectWitnessResult.done result) hresult
    exact hfinalHidden hknown.2
  have hinitialFresh := hfresh position parent hparent hinitialHidden
  have hfinalState : result.context.state.values (.position position) = none := by
    by_contra hvalue
    exact hfinalHidden (hchildren position parent hparent hvalue)
  have hfinalPrivate := auxiliaryPositionValue_none_of_done_runDirectResolvedWitnessFromTable
    position computation context fuel table result hinitialFresh.1 hinitialFresh.2 hresult
      hfinalState
  constructor
  · unfold canonicalizeMaterializedValues publicMaterializedValues
    simp [hfinalHidden]
  · exact hfinalPrivate

end SphincsSecurity.Concrete.OtsProbeSimulation
