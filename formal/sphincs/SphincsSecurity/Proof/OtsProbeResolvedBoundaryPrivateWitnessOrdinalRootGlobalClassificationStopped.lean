import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationProjection

/-!
# Successful stopped hidden-hit classification

A missing chain-start obstruction cannot disappear along a successful materialized run. This is the
unrecoverable half of the stopped coupling: once it has been separated from a matched private stop,
successful finalization rules it out.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

theorem MissingChainStartHit.ensure
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hmissing : MissingChainStartHit table context) (coordinate : Coordinate) :
    MissingChainStartHit table
      { context with state := context.state.ensure coordinate } := by
  obtain ⟨index, hvalue, hhit⟩ := hmissing
  exact ⟨index, by simpa using hvalue, by simpa using hhit⟩

theorem MissingChainStartHit.publish
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hmissing : MissingChainStartHit table context) (coordinate : Coordinate) :
    MissingChainStartHit table
      { context with state := context.state.publish coordinate } := by
  obtain ⟨index, hvalue, hhit⟩ := hmissing
  exact ⟨index, by simpa using hvalue, by simpa using hhit⟩

theorem MissingChainStartHit.addPending
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (hmissing : MissingChainStartHit table context)
    (coordinate : Coordinate) (candidate : Digest) :
    MissingChainStartHit table
      { context with state := context.state.addPending coordinate candidate } := by
  obtain ⟨index, hvalue, hhit⟩ := hmissing
  refine ⟨index, by simpa using hvalue, ?_⟩
  unfold LazyRevealProbe.State.hitAt at hhit ⊢
  rw [LazyRevealProbe.State.mem_pendingAt_iff] at hhit ⊢
  exact Finset.mem_insert_of_mem hhit

theorem missingChainStartHit_materialize_of_ne
    {table : OtsSecretIndex → HashOutput} {context : DeferredContext}
    (index : OtsSecretIndex)
    (hvalue : context.state.values index.coordinate = none)
    (hhit : context.state.hitAt index.coordinate (table index))
    (coordinate : Coordinate) (output : HashOutput)
    (hne : coordinate ≠ index.coordinate) :
    MissingChainStartHit table
      { context with state := context.state.materialize coordinate output } := by
  refine ⟨index, ?_, ?_⟩
  · simpa [LazyRevealProbe.State.materialize, Function.update_of_ne hne.symm] using hvalue
  · unfold LazyRevealProbe.State.hitAt at hhit ⊢
    rw [LazyRevealProbe.State.mem_pendingAt_iff] at hhit ⊢
    exact Finset.mem_filter.mpr ⟨hhit, hne.symm⟩

set_option maxRecDepth 100000 in
theorem missingChainStartHit_of_mem_runObservedCleanFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (result : ObservedCleanRunResult α)
    (hmissing : MissingChainStartHit table (directDeferredContext state))
    (hresult : some result ∈ support
      (runObservedCleanFromTable observations state fuel table computation)) :
    result.table = table ∧
      MissingChainStartHit table (directDeferredContext result.state) := by
  induction computation using OracleComp.inductionOn generalizing
      observations state fuel table with
  | pure value =>
      simp [runObservedCleanFromTable] at hresult
      subst result
      exact ⟨rfl, hmissing⟩
  | query_bind query next ih =>
      cases query with
      | uniform n =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output observations state fuel table hmissing hrest
      | hashOutput =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output observations state fuel table hmissing hrest
      | ensure coordinate =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind] at hresult
          exact ih () observations (state.ensure coordinate) fuel table
            (hmissing.ensure coordinate) hresult
      | probe coordinate candidate =>
          rw [runObservedCleanFromTable_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · exact ih ()
                  (observations ++ [cleanProbeObservation state coordinate candidate])
                  state remaining table hmissing (by simpa [hrevealed] using hresult)
              · exact ih ()
                  (observations ++ [cleanProbeObservation state coordinate candidate])
                  (state.addPending coordinate candidate) remaining table
                  (hmissing.addPending coordinate candidate)
                  (by simpa [hrevealed] using hresult)
      | peek coordinate =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind] at hresult
          exact ih (state.values coordinate) observations state fuel table hmissing hresult
      | publish coordinate =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind] at hresult
          exact ih () observations (state.publish coordinate) fuel table
            (hmissing.publish coordinate) hresult
      | reveal coordinate =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind] at hresult
          obtain ⟨index, hvalue, hhit⟩ := hmissing
          cases hstored : state.values coordinate with
          | some output =>
              simp only [hstored] at hresult
              exact ih output observations state fuel table ⟨index, hvalue, hhit⟩ hresult
          | none =>
              simp only [hstored] at hresult
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let revealedIndex : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
                  let output := table revealedIndex
                  by_cases hcoordinate :
                      Coordinate.chainStart lay tree leafIdx chainIdx = index.coordinate
                  · have heq : revealedIndex = index :=
                      OtsSecretIndex.coordinate_injective (by
                        simpa [revealedIndex, OtsSecretIndex.coordinate] using hcoordinate)
                    have hhit' : state.hitAt
                        (.chainStart lay tree leafIdx chainIdx) output := by
                      have hhitState : state.hitAt index.coordinate (table index) := by
                        simpa only [directDeferredContext] using hhit
                      simpa [output, heq, hcoordinate] using hhitState
                    have hhitLiteral : state.hitAt
                        (.chainStart lay tree leafIdx chainIdx)
                        (table ⟨lay, tree, leafIdx, chainIdx⟩) := by
                      simpa [output, revealedIndex] using hhit'
                    simp [hhitLiteral] at hresult
                  ·
                    by_cases hrevealedHit : state.hitAt
                        (.chainStart lay tree leafIdx chainIdx) output
                    · have hhitLiteral : state.hitAt
                          (.chainStart lay tree leafIdx chainIdx)
                          (table ⟨lay, tree, leafIdx, chainIdx⟩) := by
                        simpa [output, revealedIndex] using hrevealedHit
                      simp [hhitLiteral] at hresult
                    · have hnotHitLiteral : ¬state.hitAt
                          (.chainStart lay tree leafIdx chainIdx)
                          (table ⟨lay, tree, leafIdx, chainIdx⟩) := by
                        simpa [output, revealedIndex] using hrevealedHit
                      simp only [if_neg hnotHitLiteral] at hresult
                      have hrest : some result ∈ support
                          (runObservedCleanFromTable observations
                            (state.materialize
                              (.chainStart lay tree leafIdx chainIdx) output)
                            fuel table (next output)) := by
                        rw [runObservedCleanFromTable]
                        simpa [output, revealedIndex] using hresult
                      exact ih output observations
                        (state.materialize (.chainStart lay tree leafIdx chainIdx) output)
                        fuel table
                        (missingChainStartHit_materialize_of_ne index hvalue hhit
                          (.chainStart lay tree leafIdx chainIdx) output hcoordinate)
                        hrest
              | position position =>
                  rw [mem_support_bind_iff] at hresult
                  obtain ⟨output, _houtput, hrest⟩ := hresult
                  by_cases hpositionHit : state.hitAt (.position position) output
                  · simp [hpositionHit] at hrest
                  · simp only [hpositionHit, ↓reduceIte] at hrest
                    have hcoordinate : Coordinate.position position ≠ index.coordinate := by
                      cases index
                      simp [OtsSecretIndex.coordinate]
                    exact ih output observations (state.materialize (.position position) output)
                      fuel table
                      (missingChainStartHit_materialize_of_ne index hvalue hhit
                        (.position position) output hcoordinate)
                      hrest

set_option maxRecDepth 100000 in
theorem missingChainStartHit_of_mem_observedMaterializedBoundary
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ObservedCleanRunResult (α × SplitHashCache))
    (hmissing : MissingChainStartHit table (directDeferredContext state))
    (hresult : some result ∈ support
      (observedMaterializedBoundary parameter root ftsSecret computation observations state fuel
        table cache)) :
    result.table = table ∧
      MissingChainStartHit table (directDeferredContext result.state) := by
  induction computation using OracleComp.inductionOn generalizing
      observations state fuel table cache with
  | pure value =>
      simp [observedMaterializedBoundary] at hresult
      obtain rfl := hresult
      exact ⟨rfl, hmissing⟩
  | query_bind query next ih =>
      rw [observedMaterializedBoundary, OracleComp.construct_query_bind] at hresult
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              rw [mem_support_bind_iff] at hresult
              obtain ⟨step?, hstep, hrest⟩ := hresult
              cases step? with
              | none => simp at hrest
              | some step =>
                  have hnext := missingChainStartHit_of_mem_runObservedCleanFromTable
                    ((splitUniformImpl n).run cache) observations state fuel table step hmissing hstep
                  exact ih step.value.1 step.observations step.state step.remaining table
                    step.value.2 hnext.2 (by
                      simpa only [observedMaterializedBoundary] using hrest)
          | inr input =>
              rw [mem_support_bind_iff] at hresult
              obtain ⟨step?, hstep, hrest⟩ := hresult
              cases step? with
              | none => simp at hrest
              | some step =>
                  let publicContext := materializedCanonicalContext table state
                  let plan := purePlanProbingHashQuery parameter input publicContext.state
                  have hnext := missingChainStartHit_of_mem_runObservedCleanFromTable
                    ((probingHashQueryAfterRootAwarePublicPlan parameter input publicContext.state
                      plan).run cache) observations state fuel table step hmissing hstep
                  exact ih step.value.1 step.observations step.state step.remaining table
                    step.value.2 hnext.2 (by
                      simpa only [observedMaterializedBoundary] using hrest)
      | inr message =>
          rw [mem_support_bind_iff] at hresult
          obtain ⟨step?, hstep, hrest⟩ := hresult
          cases step? with
          | none => simp at hrest
          | some step =>
              have hnext := missingChainStartHit_of_mem_runObservedCleanFromTable
                ((maskedSign parameter root ftsSecret message).run cache) observations state fuel
                  table step hmissing hstep
              exact ih step.value.1 step.observations step.state step.remaining table
                step.value.2 hnext.2 (by
                  simpa only [observedMaterializedBoundary] using hrest)

theorem not_missingChainStartHit_of_successful_observedMaterializedBoundary
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ObservedCleanRunResult (α × SplitHashCache))
    (finalResult : ObservedCleanRunResult (α × SplitHashCache))
    (hrun : some result ∈ support
      (observedMaterializedBoundary parameter root ftsSecret computation observations state fuel
        table cache))
    (hfinish : some finalResult ∈ support
      (finishObservedCleanRunFromTable (some result))) :
    ¬MissingChainStartHit table (directDeferredContext state) := by
  intro hmissing
  have hpersist := missingChainStartHit_of_mem_observedMaterializedBoundary parameter root
    ftsSecret computation observations state fuel table cache result hmissing hrun
  have hfinalMissing := hpersist.2
  rw [← hpersist.1] at hfinalMissing
  exact not_missingChainStartHit_of_mem_finishObservedCleanRunFromTable result finalResult hfinish
    hfinalMissing

end SphincsSecurity.Concrete.OtsProbeSimulation
