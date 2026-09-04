import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalOperational

/-!
# Adaptive materialized observation lift

The local source-to-observation coupling is lifted through the complete retained computation while
keeping the shared clean-failure alternative outside every root position and ordinal.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option maxRecDepth 100000 in
theorem valuesLE_of_mem_runObservedCleanFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (result : ObservedCleanRunResult α)
    (hresult : some result ∈ support
      (runObservedCleanFromTable observations state fuel table computation)) :
    LazyRevealProbe.ValuesLE state result.state := by
  have hclean : some result.toClean ∈ support
      (runCleanFromTable state fuel table computation) := by
    rw [← map_projectObservedCleanRun_runObservedCleanFromTable computation observations
      state fuel table, support_map]
    exact ⟨some result, hresult, rfl⟩
  rw [← map_projectDirectDetailedClean_run_eq_clean computation state fuel table,
    support_map] at hclean
  obtain ⟨detailed, hdetailed, hproject⟩ := hclean
  cases detailed with
  | stopped reason =>
      simp [projectDirectDetailedClean, DirectDetailedResult.toOption,
        projectResolvedRunResult] at hproject
  | done detailed =>
      have heq : result.toClean =
          ⟨detailed.context.state, detailed.remaining, detailed.value, detailed.table⟩ := by
        exact Option.some.inj (by simpa [projectDirectDetailedClean,
          DirectDetailedResult.toOption, projectResolvedRunResult] using hproject.symm)
      have hstate : result.state = detailed.context.state := congrArg CleanRunResult.state heq
      rw [hstate]
      exact valuesLE_of_done_runDirectResolvedDetailedFromTable computation
        (directDeferredContext state) fuel table detailed hdetailed

theorem LazyRevealProbe.valuesLE_clearPending
    (state : LazyRevealProbe.State Coordinate) (coordinate : Coordinate) :
    LazyRevealProbe.ValuesLE state (state.clearPending coordinate) := by
  intro other output hvalue
  exact hvalue

theorem LazyRevealProbe.valuesLE_complete_of_none
    (state : LazyRevealProbe.State Coordinate) (coordinate : Coordinate)
    (output : HashOutput) (hnone : state.values coordinate = none) :
    LazyRevealProbe.ValuesLE state (state.complete coordinate output) := by
  intro other stored hvalue
  by_cases heq : other = coordinate
  · subst other
    rw [hnone] at hvalue
    simp at hvalue
  · simpa [LazyRevealProbe.State.complete, Function.update_of_ne heq] using hvalue

set_option maxRecDepth 100000 in
theorem valuesLE_of_mem_finalizeCleanFromTable :
    ∀ (coordinates : List Coordinate)
      (state : LazyRevealProbe.State Coordinate)
      (table : OtsSecretIndex → HashOutput)
      (finalState : LazyRevealProbe.State Coordinate)
      (finalTable : OtsSecretIndex → HashOutput),
      some (finalState, finalTable) ∈ support
          (finalizeCleanFromTable coordinates state table) →
        LazyRevealProbe.ValuesLE state finalState
  | [], state, table, finalState, finalTable, hresult => by
      simp [finalizeCleanFromTable] at hresult
      obtain ⟨rfl, rfl⟩ := hresult
      exact fun _ _ hvalue => hvalue
  | coordinate :: remaining, state, table, finalState, finalTable, hresult => by
      rw [finalizeCleanFromTable.eq_def] at hresult
      cases hvalue : state.values coordinate with
      | some output =>
          simp only [hvalue] at hresult
          exact (LazyRevealProbe.valuesLE_clearPending state coordinate).trans
            (valuesLE_of_mem_finalizeCleanFromTable remaining
              (state.clearPending coordinate) table finalState finalTable hresult)
      | none =>
          simp only [hvalue] at hresult
          cases coordinate with
          | chainStart lay tree leafIdx chainIdx =>
              let output := table ⟨lay, tree, leafIdx, chainIdx⟩
              by_cases hhit : state.hitAt (.chainStart lay tree leafIdx chainIdx) output
              · simp [output, hhit] at hresult
              · simp only [output, hhit, ↓reduceIte] at hresult
                exact (LazyRevealProbe.valuesLE_complete_of_none state
                  (.chainStart lay tree leafIdx chainIdx) output hvalue).trans
                    (valuesLE_of_mem_finalizeCleanFromTable remaining
                      (state.complete (.chainStart lay tree leafIdx chainIdx) output) table
                      finalState finalTable hresult)
          | position position =>
              rw [mem_support_bind_iff] at hresult
              obtain ⟨output, _houtput, hrest⟩ := hresult
              by_cases hhit : state.hitAt (.position position) output
              · simp [hhit] at hrest
              · simp only [hhit, ↓reduceIte] at hrest
                exact (LazyRevealProbe.valuesLE_complete_of_none state (.position position)
                  output hvalue).trans
                    (valuesLE_of_mem_finalizeCleanFromTable remaining
                      (state.complete (.position position) output) table finalState finalTable
                      hrest)

theorem valuesLE_of_mem_finishObservedCleanRunFromTable
    (result finalResult : ObservedCleanRunResult α)
    (hresult : some finalResult ∈ support
      (finishObservedCleanRunFromTable (some result))) :
    LazyRevealProbe.ValuesLE result.state finalResult.state := by
  unfold finishObservedCleanRunFromTable at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨finalized, hfinalized, hreturn⟩ := hresult
  cases finalized with
  | none => simp at hreturn
  | some value =>
      rcases value with ⟨finalState, finalTable⟩
      simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at hreturn
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hreturn
      exact valuesLE_of_mem_finalizeCleanFromTable result.state.coordinates.toList result.state
        result.table finalState finalTable hfinalized

set_option maxRecDepth 100000 in
theorem observations_prefix_of_mem_runObservedCleanFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (result : ObservedCleanRunResult α)
    (hresult : some result ∈ support
      (runObservedCleanFromTable observations state fuel table computation)) :
    observations <+: result.observations := by
  induction computation using OracleComp.inductionOn generalizing
      observations state fuel table with
  | pure value =>
      simp [runObservedCleanFromTable] at hresult
      subst result
      exact List.prefix_rfl
  | query_bind query next ih =>
      cases query with
      | uniform n =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output observations state fuel table hrest
      | hashOutput =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output observations state fuel table hrest
      | ensure coordinate =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind] at hresult
          exact ih () observations (state.ensure coordinate) fuel table hresult
      | probe coordinate candidate =>
          rw [runObservedCleanFromTable_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · exact List.prefix_append observations
                  [cleanProbeObservation state coordinate candidate] |>.trans
                    (ih () (observations ++ [cleanProbeObservation state coordinate candidate])
                      state remaining table (by simpa [hrevealed] using hresult))
              · exact List.prefix_append observations
                  [cleanProbeObservation state coordinate candidate] |>.trans
                    (ih () (observations ++ [cleanProbeObservation state coordinate candidate])
                      (state.addPending coordinate candidate) remaining table
                      (by simpa [hrevealed] using hresult))
      | peek coordinate =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind] at hresult
          exact ih (state.values coordinate) observations state fuel table hresult
      | publish coordinate =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind] at hresult
          exact ih () observations (state.publish coordinate) fuel table hresult
      | reveal coordinate =>
          rw [runObservedCleanFromTable, OracleComp.construct_query_bind] at hresult
          cases hvalue : state.values coordinate with
          | some output =>
              simp only [hvalue] at hresult
              exact ih output observations state fuel table hresult
          | none =>
              simp only [hvalue] at hresult
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let output := table ⟨lay, tree, leafIdx, chainIdx⟩
                  by_cases hhit : state.hitAt (.chainStart lay tree leafIdx chainIdx) output
                  · simp [output, hhit] at hresult
                  · simp only [output, hhit, ↓reduceIte] at hresult
                    exact ih output observations
                      (state.materialize (.chainStart lay tree leafIdx chainIdx) output) fuel table
                      hresult
              | position position =>
                  rw [mem_support_bind_iff] at hresult
                  obtain ⟨output, _houtput, hrest⟩ := hresult
                  by_cases hhit : state.hitAt (.position position) output
                  · simp [hhit] at hrest
                  · simp only [hhit, ↓reduceIte] at hrest
                    exact ih output observations (state.materialize (.position position) output)
                      fuel table hrest

set_option maxRecDepth 100000 in
theorem remaining_le_of_mem_runObservedCleanFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (result : ObservedCleanRunResult α)
    (hresult : some result ∈ support
      (runObservedCleanFromTable observations state fuel table computation)) :
    result.remaining ≤ fuel := by
  have hclean : some result.toClean ∈ support
      (runCleanFromTable state fuel table computation) := by
    rw [← map_projectObservedCleanRun_runObservedCleanFromTable computation observations
      state fuel table, support_map]
    exact ⟨some result, hresult, rfl⟩
  rw [← map_projectDirectDetailedClean_run_eq_clean computation state fuel table,
    support_map] at hclean
  obtain ⟨detailed, hdetailed, hproject⟩ := hclean
  cases detailed with
  | stopped reason =>
      simp [projectDirectDetailedClean, DirectDetailedResult.toOption,
        projectResolvedRunResult] at hproject
  | done detailed =>
      have heq : result.toClean =
          ⟨detailed.context.state, detailed.remaining, detailed.value, detailed.table⟩ := by
        exact Option.some.inj (by simpa [projectDirectDetailedClean,
          DirectDetailedResult.toOption, projectResolvedRunResult] using hproject.symm)
      have hremaining : result.remaining = detailed.remaining :=
        congrArg CleanRunResult.remaining heq
      rw [hremaining]
      exact remaining_le_fuel_of_done_runDirectResolvedDetailedFromTable computation
        (directDeferredContext state) fuel table detailed hdetailed

set_option maxRecDepth 100000 in
theorem fuel_le_remaining_add_of_mem_runObservedCleanFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (result : ObservedCleanRunResult α) (bound : Nat)
    (hbound : computation.IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) bound)
    (hresult : some result ∈ support
      (runObservedCleanFromTable observations state fuel table computation)) :
    fuel ≤ result.remaining + bound := by
  have hclean : some result.toClean ∈ support
      (runCleanFromTable state fuel table computation) := by
    rw [← map_projectObservedCleanRun_runObservedCleanFromTable computation observations
      state fuel table, support_map]
    exact ⟨some result, hresult, rfl⟩
  rw [← map_projectDirectDetailedClean_run_eq_clean computation state fuel table,
    support_map] at hclean
  obtain ⟨detailed, hdetailed, hproject⟩ := hclean
  cases detailed with
  | stopped reason =>
      simp [projectDirectDetailedClean, DirectDetailedResult.toOption,
        projectResolvedRunResult] at hproject
  | done detailed =>
      have heq : result.toClean =
          ⟨detailed.context.state, detailed.remaining, detailed.value, detailed.table⟩ := by
        exact Option.some.inj (by simpa [projectDirectDetailedClean,
          DirectDetailedResult.toOption, projectResolvedRunResult] using hproject.symm)
      have hremaining : result.remaining = detailed.remaining :=
        congrArg CleanRunResult.remaining heq
      rw [hremaining]
      exact fuel_le_remaining_add_of_done_runDirectResolvedDetailedFromTable computation
        (directDeferredContext state) fuel table detailed bound hbound hdetailed

set_option maxRecDepth 100000 in
theorem materializedDoomed_of_mem_runObservedCleanFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (result : ObservedCleanRunResult α)
    (hdoomed : DoomedResolvedContext table (directDeferredContext state))
    (hresult : some result ∈ support
      (runObservedCleanFromTable observations state fuel table computation)) :
    result.table = table ∧
      DoomedResolvedContext table (directDeferredContext result.state) := by
  have hclean : some result.toClean ∈ support
      (runCleanFromTable state fuel table computation) := by
    rw [← map_projectObservedCleanRun_runObservedCleanFromTable computation observations
      state fuel table, support_map]
    exact ⟨some result, hresult, rfl⟩
  rw [← map_projectDirectDetailedClean_run_eq_clean computation state fuel table,
    support_map] at hclean
  obtain ⟨detailed, hdetailed, hproject⟩ := hclean
  cases detailed with
  | stopped reason =>
      simp [projectDirectDetailedClean, DirectDetailedResult.toOption,
        projectResolvedRunResult] at hproject
  | done detailed =>
      have heq : result.toClean =
          ⟨detailed.context.state, detailed.remaining, detailed.value, detailed.table⟩ := by
        exact Option.some.inj (by simpa [projectDirectDetailedClean,
          DirectDetailedResult.toOption, projectResolvedRunResult] using hproject.symm)
      have hstate : result.state = detailed.context.state := congrArg CleanRunResult.state heq
      have htable : result.table = detailed.table := congrArg CleanRunResult.table heq
      have hdoom := finalizationDoomedRun_of_mem_runDirectResolvedDetailedFromTable table
        computation (directDeferredContext state) fuel detailed hdoomed hdetailed
      have hmaterialized := directDetailedMaterialized_of_mem_runDirectResolvedDetailedFromTable
        computation state fuel table (.done detailed) hdetailed
      rw [hstate, htable, hdoom.1, ← hmaterialized]
      exact ⟨rfl, hdoom.2⟩

set_option maxRecDepth 100000 in
theorem valuesLE_of_mem_observedMaterializedBoundary
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ObservedCleanRunResult (α × SplitHashCache))
    (hresult : some result ∈ support
      (observedMaterializedBoundary parameter root ftsSecret computation observations state fuel
        table cache)) :
    LazyRevealProbe.ValuesLE state result.state := by
  induction computation using OracleComp.inductionOn generalizing
      observations state fuel table cache with
  | pure value =>
      simp [observedMaterializedBoundary] at hresult
      obtain rfl := hresult
      exact LazyRevealProbe.ValuesLE.refl state
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
                  exact (valuesLE_of_mem_runObservedCleanFromTable
                    ((splitUniformImpl n).run cache) observations state fuel table step hstep).trans
                    (ih step.value.1 step.observations step.state step.remaining table
                      step.value.2 (by simpa only [observedMaterializedBoundary] using hrest))
          | inr input =>
              rw [mem_support_bind_iff] at hresult
              obtain ⟨step?, hstep, hrest⟩ := hresult
              cases step? with
              | none => simp at hrest
              | some step =>
                  let publicContext := materializedCanonicalContext table state
                  let plan := purePlanProbingHashQuery parameter input publicContext.state
                  exact (valuesLE_of_mem_runObservedCleanFromTable
                    ((probingHashQueryAfterRootAwarePublicPlan parameter input publicContext.state
                      plan).run cache) observations state fuel table step hstep).trans
                    (ih step.value.1 step.observations step.state step.remaining table
                      step.value.2 (by simpa only [observedMaterializedBoundary] using hrest))
      | inr message =>
          rw [mem_support_bind_iff] at hresult
          obtain ⟨step?, hstep, hrest⟩ := hresult
          cases step? with
          | none => simp at hrest
          | some step =>
              exact (valuesLE_of_mem_runObservedCleanFromTable
                ((maskedSign parameter root ftsSecret message).run cache) observations state fuel
                  table step hstep).trans
                (ih step.value.1 step.observations step.state step.remaining table
                  step.value.2 (by simpa only [observedMaterializedBoundary] using hrest))

set_option maxRecDepth 100000 in
theorem observations_prefix_of_mem_observedMaterializedBoundary
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ObservedCleanRunResult (α × SplitHashCache))
    (hresult : some result ∈ support
      (observedMaterializedBoundary parameter root ftsSecret computation observations state fuel
        table cache)) :
    observations <+: result.observations := by
  induction computation using OracleComp.inductionOn generalizing
      observations state fuel table cache with
  | pure value =>
      simp [observedMaterializedBoundary] at hresult
      obtain rfl := hresult
      exact List.prefix_rfl
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
                  exact (observations_prefix_of_mem_runObservedCleanFromTable
                    ((splitUniformImpl n).run cache) observations state fuel table step hstep).trans
                    (ih step.value.1 step.observations step.state step.remaining table
                      step.value.2 (by simpa only [observedMaterializedBoundary] using hrest))
          | inr input =>
              rw [mem_support_bind_iff] at hresult
              obtain ⟨step?, hstep, hrest⟩ := hresult
              cases step? with
              | none => simp at hrest
              | some step =>
                  let publicContext := materializedCanonicalContext table state
                  let plan := purePlanProbingHashQuery parameter input publicContext.state
                  exact (observations_prefix_of_mem_runObservedCleanFromTable
                    ((probingHashQueryAfterRootAwarePublicPlan parameter input publicContext.state
                      plan).run cache) observations state fuel table step hstep).trans
                    (ih step.value.1 step.observations step.state step.remaining table
                      step.value.2 (by simpa only [observedMaterializedBoundary] using hrest))
      | inr message =>
          rw [mem_support_bind_iff] at hresult
          obtain ⟨step?, hstep, hrest⟩ := hresult
          cases step? with
          | none => simp at hrest
          | some step =>
              exact (observations_prefix_of_mem_runObservedCleanFromTable
                ((maskedSign parameter root ftsSecret message).run cache) observations state fuel
                  table step hstep).trans
                (ih step.value.1 step.observations step.state step.remaining table
                  step.value.2 (by simpa only [observedMaterializedBoundary] using hrest))

set_option maxRecDepth 100000 in
theorem materializedDoomed_of_mem_observedMaterializedBoundary
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ObservedCleanRunResult (α × SplitHashCache))
    (hdoomed : DoomedResolvedContext table (directDeferredContext state))
    (hresult : some result ∈ support
      (observedMaterializedBoundary parameter root ftsSecret computation observations state fuel
        table cache)) :
    result.table = table ∧
      DoomedResolvedContext table (directDeferredContext result.state) := by
  induction computation using OracleComp.inductionOn generalizing
      observations state fuel table cache with
  | pure value =>
      simp [observedMaterializedBoundary] at hresult
      obtain rfl := hresult
      exact ⟨rfl, hdoomed⟩
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
                  have hnext := materializedDoomed_of_mem_runObservedCleanFromTable
                    ((splitUniformImpl n).run cache) observations state fuel table step hdoomed hstep
                  simp only at hrest
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
                  have hnext := materializedDoomed_of_mem_runObservedCleanFromTable
                    ((probingHashQueryAfterRootAwarePublicPlan parameter input publicContext.state
                      plan).run cache) observations state fuel table step hdoomed hstep
                  simp only at hrest
                  exact ih step.value.1 step.observations step.state step.remaining table
                    step.value.2 hnext.2 (by
                      simpa only [observedMaterializedBoundary] using hrest)
      | inr message =>
          rw [mem_support_bind_iff] at hresult
          obtain ⟨step?, hstep, hrest⟩ := hresult
          cases step? with
          | none => simp at hrest
          | some step =>
              have hnext := materializedDoomed_of_mem_runObservedCleanFromTable
                ((maskedSign parameter root ftsSecret message).run cache) observations state fuel
                  table step hdoomed hstep
              simp only at hrest
              exact ih step.value.1 step.observations step.state step.remaining table
                step.value.2 hnext.2 (by
                  simpa only [observedMaterializedBoundary] using hrest)

def SnapshotObservedPrefixStableRel
    (table : OtsSecretIndex → HashOutput)
    (source : PrivateWitnessSnapshotOutput)
    (observed : Option
      (ObservedCleanRunResult (α × SplitHashCache))) : Prop :=
  observed = none ∨
    (∃ result aligned, observed = some result ∧
      aligned <+: result.observations ∧
      SnapshotsObservedAt table source.2 aligned ∧
      (∀ witness, source.1 = some witness →
        result.state.values (.position witness.position) = some witness.output)) ∨
    (∃ result, observed = some result ∧
      DoomedResolvedContext table (directDeferredContext result.state))

def observedResolvedResult
    (observations : List CleanProbeObservation)
    (result : ResolvedRunResult (α × SplitHashCache)) :
    ObservedCleanRunResult (α × SplitHashCache) :=
  ⟨result.context.state, result.remaining, result.value, result.table, observations⟩

set_option maxRecDepth 100000 in
theorem relTriple_pure_snapshot_observedMaterializedBoundary
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (source : PrivateWitnessSnapshotOutput)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (haligned : SnapshotsObservedAt table source.2 observations)
    (hstable : (∀ witness, source.1 = some witness →
        state.values (.position witness.position) = some witness.output) ∨
      DoomedResolvedContext table (directDeferredContext state)) :
    RelTriple
      (pure source : ProbComp PrivateWitnessSnapshotOutput)
      (observedMaterializedBoundary parameter root ftsSecret computation observations state fuel
        table cache)
      (SnapshotObservedPrefixStableRel table) := by
  have hbase := relTriple_true
    (pure source : ProbComp PrivateWitnessSnapshotOutput)
    (observedMaterializedBoundary parameter root ftsSecret computation observations state fuel
      table cache)
  have hleft :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hbase
      (fun output => output ∈ support (pure source : ProbComp PrivateWitnessSnapshotOutput))
      (fun output houtput => houtput)
  have hboth :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleft
  apply relTriple_post_mono hboth
  intro left right hrelation
  have hleftEq : left = source := by simpa using hrelation.1.2
  subst left
  cases right with
  | none => exact Or.inl rfl
  | some result =>
      rcases hstable with hstored | hdoomed
      · right
        left
        refine ⟨result, observations, rfl,
          observations_prefix_of_mem_observedMaterializedBoundary parameter root ftsSecret
            computation observations state fuel table cache result hrelation.2,
          haligned, ?_⟩
        intro witness hwitness
        exact valuesLE_of_mem_observedMaterializedBoundary parameter root ftsSecret computation
          observations state fuel table cache result hrelation.2 _ witness.output
            (hstored witness hwitness)
      · right
        right
        exact ⟨result, rfl,
          (materializedDoomed_of_mem_observedMaterializedBoundary parameter root ftsSecret
            computation observations state fuel table cache result hdoomed hrelation.2).2⟩

set_option maxRecDepth 100000 in
theorem relTriple_any_observedMaterializedBoundary_of_doomed
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (left : ProbComp PrivateWitnessSnapshotOutput)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hdoomed : DoomedResolvedContext table (directDeferredContext state)) :
    RelTriple left
      (observedMaterializedBoundary parameter root ftsSecret computation observations state fuel
        table cache)
      (SnapshotObservedPrefixStableRel table) := by
  have hbase := relTriple_true left
    (observedMaterializedBoundary parameter root ftsSecret computation observations state fuel
      table cache)
  have hboth :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hbase
  apply relTriple_post_mono hboth
  intro source observed hrelation
  cases observed with
  | none => exact Or.inl rfl
  | some result =>
      right
      right
      exact ⟨result, rfl,
        (materializedDoomed_of_mem_observedMaterializedBoundary parameter root ftsSecret
          computation observations state fuel table cache result hdoomed hrelation.2).2⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem relTriple_finishWitnessObservedStep
    (parameter : PublicParameter) (rootOf : α → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (next : α → OracleComp (OracleWorld + SigningSpec) β)
    (leftObserve : DeferredContext → Nat → (α × SplitHashCache) →
      List PlannedProbeSnapshot → ProbComp PrivateWitnessSnapshotOutput)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (table : OtsSecretIndex → HashOutput)
    (leftResult : DirectWitnessResult (α × SplitHashCache))
    (rightResult : Option (ObservedCleanRunResult (α × SplitHashCache)))
    (hrelation : WitnessObservedStepRel table observations leftResult rightResult)
    (haligned : SnapshotsObservedAt table snapshots observations)
    (hrecursive : ∀ left right,
      leftResult = .done left →
      rightResult = some (observedResolvedResult observations right) →
      OrdinaryMaterializedRunEq table left right →
      RelTriple
        (canonicalizeDirectWitnessSnapshotObserve table leftObserve left.context left.remaining
          ((left.value.1, left.value.2)) snapshots)
        (observedMaterializedBoundary parameter (rootOf right.value.1) ftsSecret
          (next right.value.1)
          observations right.context.state right.remaining table right.value.2)
        (SnapshotObservedPrefixStableRel table)) :
    RelTriple
      (finishDirectWitnessSnapshotObserve
        (canonicalizeDirectWitnessSnapshotObserve table leftObserve) snapshots leftResult)
      (match rightResult with
        | none => pure none
        | some result =>
            observedMaterializedBoundary parameter (rootOf result.value.1) ftsSecret
              (next result.value.1)
              result.observations result.state result.remaining table result.value.2)
      (SnapshotObservedPrefixStableRel table) := by
  obtain ⟨detailed, hproject, hstable⟩ := hrelation
  cases detailed with
  | stopped reason =>
      have hright : rightResult = none := by
        simpa [projectDirectDetailedObserved] using hproject.symm
      subst rightResult
      have hbase := relTriple_true
        (finishDirectWitnessSnapshotObserve
          (canonicalizeDirectWitnessSnapshotObserve table leftObserve) snapshots leftResult)
        (pure none : ProbComp
          (Option (ObservedCleanRunResult (β × SplitHashCache))))
      have hsupported :=
        SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hbase
      apply relTriple_post_mono hsupported
      intro source observed hrel
      have : observed = none := by simpa using hrel.2
      subst observed
      exact Or.inl rfl
  | done right =>
      have hright : rightResult = some
          (observedResolvedResult observations right) := by
        simpa [projectDirectDetailedObserved, observedResolvedResult] using hproject.symm
      subst rightResult
      simp only [projectDirectDetailedObserved, finishDirectWitnessSnapshotObserve]
      cases leftResult with
      | stoppedFuel =>
          change RelTriple (pure (none, snapshots))
            (observedMaterializedBoundary parameter (rootOf right.value.1) ftsSecret
              (next right.value.1)
              observations right.context.state right.remaining table right.value.2)
            (SnapshotObservedPrefixStableRel table)
          exact relTriple_pure_snapshot_observedMaterializedBoundary parameter
            (rootOf right.value.1) ftsSecret
            (next right.value.1) (none, snapshots) observations right.context.state
            right.remaining table right.value.2
            haligned
            (Or.inr (by rw [← hstable.2]; exact hstable.1.2))
      | stoppedOrdinary =>
          change RelTriple (pure (none, snapshots))
            (observedMaterializedBoundary parameter (rootOf right.value.1) ftsSecret
              (next right.value.1)
              observations right.context.state right.remaining table right.value.2)
            (SnapshotObservedPrefixStableRel table)
          exact relTriple_pure_snapshot_observedMaterializedBoundary parameter
            (rootOf right.value.1) ftsSecret
            (next right.value.1) (none, snapshots) observations right.context.state
            right.remaining table right.value.2
            haligned
            (Or.inr (by rw [← hstable.2]; exact hstable.1.2))
      | stoppedPrivate witness =>
          change RelTriple (pure (some witness, snapshots))
            (observedMaterializedBoundary parameter (rootOf right.value.1) ftsSecret
              (next right.value.1)
              observations right.context.state right.remaining table right.value.2)
            (SnapshotObservedPrefixStableRel table)
          rcases hstable with hstored | hdoomed
          · exact relTriple_pure_snapshot_observedMaterializedBoundary parameter
              (rootOf right.value.1) ftsSecret
              (next right.value.1) (some witness, snapshots) observations right.context.state
              right.remaining table right.value.2
              haligned
              (Or.inl (by
                intro other hother
                have : other = witness := Option.some.inj hother.symm
                subst other
                exact hstored.1))
          · exact relTriple_pure_snapshot_observedMaterializedBoundary parameter
              (rootOf right.value.1) ftsSecret
              (next right.value.1) (some witness, snapshots) observations right.context.state
              right.remaining table right.value.2
              haligned
              (Or.inr (by rw [← hdoomed.2]; exact hdoomed.1.2))
      | done left =>
          change RelTriple
            (canonicalizeDirectWitnessSnapshotObserve table leftObserve left.context
              left.remaining left.value snapshots)
            (observedMaterializedBoundary parameter (rootOf right.value.1) ftsSecret
              (next right.value.1)
              observations right.context.state right.remaining table right.value.2)
            (SnapshotObservedPrefixStableRel table)
          rcases hstable with hclean | hdoomed
          · exact hrecursive left right rfl hright hclean
          · exact relTriple_any_observedMaterializedBoundary_of_doomed parameter
              (rootOf right.value.1) ftsSecret
              (next right.value.1)
              (canonicalizeDirectWitnessSnapshotObserve table leftObserve left.context
                left.remaining left.value snapshots)
              observations right.context.state right.remaining table right.value.2
              (by rw [← hdoomed.2]; exact hdoomed.1.2)

set_option maxRecDepth 100000 in
theorem relTriple_runDirectResolvedWitness_observed_of_probeFree
    (table : OtsSecretIndex → HashOutput)
    (leftComputation rightComputation :
      OracleComp (LazyRevealProbe.World Coordinate) (α × SplitHashCache))
    (observations : List CleanProbeObservation)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (hbase : RelTriple
      (runDirectResolvedWitnessFromTable left leftFuel table leftComputation)
      (runDirectResolvedDetailedFromTable right rightFuel table rightComputation)
      (DirectWitnessMaterializedStableRunEq table))
    (hprobeFree : rightComputation.IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 0)
    (hrightMaterialized : right = directDeferredContext right.state) :
    RelTriple
      (runDirectResolvedWitnessFromTable left leftFuel table leftComputation)
      (runObservedCleanFromTable observations right.state rightFuel table rightComputation)
      (WitnessObservedStepRel table observations) := by
  have hstrength : RelTriple
      (runDirectResolvedWitnessFromTable left leftFuel table leftComputation)
      (runDirectResolvedDetailedFromTable right rightFuel table rightComputation)
      (fun leftResult rightResult =>
        WitnessObservedStepRel table observations leftResult
          (projectDirectDetailedObserved observations rightResult)) := by
    apply relTriple_post_mono hbase
    intro leftResult rightResult hrelation
    exact ⟨rightResult, rfl, hrelation⟩
  have hmapped := relTriple_map
    (R := WitnessObservedStepRel table observations)
    (f := id) (g := projectDirectDetailedObserved observations) hstrength
  rw [id_map] at hmapped
  have hmap : projectDirectDetailedObserved observations <$>
        runDirectResolvedDetailedFromTable right rightFuel table rightComputation =
      runObservedCleanFromTable observations right.state rightFuel table rightComputation := by
    rw [hrightMaterialized]
    calc
      _ = attachCleanProbeObservations observations <$>
          (projectDirectDetailedClean <$>
            runDirectResolvedDetailedFromTable (directDeferredContext right.state) rightFuel table
              rightComputation) := by
        rw [Functor.map_map]
        apply map_congr
        intro result
        exact projectDirectDetailedObserved_eq_attach observations result
      _ = attachCleanProbeObservations observations <$>
          runCleanFromTable right.state rightFuel table rightComputation := by
        rw [map_projectDirectDetailedClean_run_eq_clean]
      _ = _ := map_attachCleanProbeObservations_runCleanFromTable_of_probeFree rightComputation
        observations right.state rightFuel table hprobeFree
  exact relTriple_of_evalDist_eq_right (congrArg evalDist hmap) hmapped

theorem probingHashQueryAfterPlan_isProbeBound_one
    (parameter : PublicParameter) (input : HashInput) (plan : PlannedHashQuery)
    (cache : SplitHashCache) :
    ((probingHashQueryAfterPlan parameter input plan).run cache).IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 1 := by
  unfold probingHashQueryAfterPlan executePlannedHashQuery
  rw [StateT.run_bind]
  apply OracleComp.isQueryBoundP_bind (n := 1) (m := 0)
  · exact executeCandidate?_isProbeBound_one plan.candidate? cache
  · intro result _hresult
    cases plan.action with
    | ordinary => exact splitHashQuery_probeFree (.ordinary input) result.2
    | resolve coordinate => exact resolveKnownInput_probeFree parameter coordinate input result.2

theorem probingHashQueryAfterRootAwarePublicPlan_isProbeBound_one
    (parameter : PublicParameter) (input : HashInput)
    (publicState : LazyRevealProbe.State Coordinate) (plan : PlannedHashQuery)
    (cache : SplitHashCache) :
    ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run cache).IsQueryBoundP
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 1 := by
  unfold probingHashQueryAfterRootAwarePublicPlan
  rw [StateT.run_bind]
  apply OracleComp.isQueryBoundP_bind (n := 1) (m := 0)
  · exact executeCandidate?_isProbeBound_one _ cache
  · intro result _hresult
    exact probingHashQueryPublicAction_probeFree parameter input publicState plan.action result.2

theorem probingHashQueryAfterRootAwarePublicPlan_eq_of_values_eq
    (parameter : PublicParameter) (input : HashInput)
    {left right : LazyRevealProbe.State Coordinate}
    (hvalues : left.values = right.values) (plan : PlannedHashQuery) :
    probingHashQueryAfterRootAwarePublicPlan parameter input left plan =
      probingHashQueryAfterRootAwarePublicPlan parameter input right plan := by
  unfold probingHashQueryAfterRootAwarePublicPlan probingHashQueryPublicAction
  apply bind_congr
  intro _
  cases plan.action with
  | ordinary => rfl
  | resolve coordinate =>
      exact resolvePublicKnownInput_eq_of_values_eq parameter hvalues coordinate input

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem relTriple_directSnapshotBoundary_observedMaterialized
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) RetainedRestResult)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (left right : DeferredContext) (leftFuel rightFuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (leftCache rightCache : SplitHashCache) (q bound : Nat)
    (hbound :
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
            SecretKey)) computation).IsQueryBoundP
        (fun query => query matches Sum.inr _) bound)
    (hcontext : FinalizationContextLE table left right)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hrevealed : left.state.revealed = right.state.revealed)
    (hvalues : LazyRevealProbe.ValuesLE left.state right.state)
    (hpublished : PublishedValues left.state)
    (hrightMaterialized : right = directDeferredContext right.state)
    (hcanonical : CanonicalMaterializedValues table left)
    (haligned : SnapshotsObservedAt table snapshots observations)
    (hleftLower : bound ≤ leftFuel) (hleftUpper : leftFuel ≤ q)
    (hrightLower : q + bound ≤ rightFuel) :
    RelTriple
      (directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve parameter root ftsSecret
        computation (retainedResolvedFinalizationPrivateWitnessSnapshotObserve table root)
        snapshots left leftFuel table leftCache)
      (observedMaterializedBoundary parameter root ftsSecret computation observations right.state
        rightFuel table rightCache)
      (SnapshotObservedPrefixStableRel table) := by
  induction computation using OracleComp.inductionOn generalizing
      snapshots observations left right leftFuel rightFuel leftCache rightCache bound with
  | pure value =>
      rw [directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve,
        OracleComp.construct_pure, observedMaterializedBoundary, OracleComp.construct_pure]
      have hnotPrivate : ¬PrivateStructuralHit left :=
        not_privateStructuralHit_of_deferredCompletable hcontext.leftCompletable
      simp [retainedResolvedFinalizationPrivateWitnessSnapshotObserve, hnotPrivate]
      right
      left
      exact ⟨_, observations, rfl, List.prefix_rfl, haligned, by simp⟩
  | query_bind query next ih =>
      rw [directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve,
        OracleComp.construct_query_bind, observedMaterializedBoundary,
        OracleComp.construct_query_bind]
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              rw [simulateQ_expandedAdversaryImpl_query_bind_inl,
                OracleComp.isQueryBoundP_query_bind_iff] at hbound
              simp only
              let leftObserve : DeferredContext → Nat →
                  (Fin (n + 1) × SplitHashCache) → List PlannedProbeSnapshot →
                    ProbComp PrivateWitnessSnapshotOutput :=
                fun nextContext remaining value laterSnapshots =>
                  directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve parameter root
                    ftsSecret (next value.1)
                    (retainedResolvedFinalizationPrivateWitnessSnapshotObserve table root)
                    laterSnapshots nextContext remaining table value.2
              have hbase := (witnessMaterializedStableCouples_splitUniformImpl table n)
                left right leftFuel rightFuel leftCache rightCache hcontext (by omega) hcache
                hrevealed hvalues hpublished hrightMaterialized
              have hlocal := relTriple_runDirectResolvedWitness_observed_of_probeFree table
                ((splitUniformImpl n).run leftCache) ((splitUniformImpl n).run rightCache)
                observations left right leftFuel rightFuel
                hbase (splitUniformImpl_probeFree n rightCache) hrightMaterialized
              have hleftSupported :=
                SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hlocal
                  (fun result => result ∈ support
                    (runDirectResolvedWitnessFromTable left leftFuel table
                      ((splitUniformImpl n).run leftCache)))
                  (fun result hresult => hresult)
              have hbothSupported :=
                SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support
                  hleftSupported
              unfold runDirectWitnessSnapshotObserve
              apply relTriple_bind hbothSupported
              intro leftResult rightResult hstep
              rcases hstep with ⟨⟨hstep, hleftSupport⟩, hrightSupport⟩
              change RelTriple
                (finishDirectWitnessSnapshotObserve
                  (canonicalizeDirectWitnessSnapshotObserve table leftObserve) snapshots
                  leftResult)
                (match rightResult with
                  | none => pure none
                  | some result =>
                      observedMaterializedBoundary parameter root ftsSecret
                        (next result.value.1) result.observations result.state result.remaining
                        table result.value.2)
                (SnapshotObservedPrefixStableRel table)
              have hfinish := relTriple_finishWitnessObservedStep (α := Fin (n + 1))
                (β := RetainedRestResult) parameter (fun _ => root) ftsSecret next leftObserve
                snapshots observations table leftResult rightResult hstep haligned (by
                intro nextLeft nextRight hleftEq hrightEq hclean
                rw [hleftEq] at hleftSupport
                rw [hrightEq] at hrightSupport
                have hcanonicalRun := hclean.canonicalize_left
                let canonical := canonicalizeMaterializedValues table nextLeft.context
                have hleftCompletable : DeferredCompletable table canonical :=
                  hcanonicalRun.context_le.leftCompletable
                have hnotPrivate : ¬PrivateStructuralHit canonical :=
                  not_privateStructuralHit_of_deferredCompletable hleftCompletable
                have hleftFuelPreserved : leftFuel ≤ nextLeft.remaining := by
                  have := fuel_le_remaining_add_of_done_runDirectResolvedWitnessFromTable
                    ((splitUniformImpl n).run leftCache) left leftFuel table nextLeft 0
                    (splitUniformImpl_probeFree n leftCache) hleftSupport
                  omega
                have hrightFuelPreserved : rightFuel ≤ nextRight.remaining := by
                  have := fuel_le_remaining_add_of_mem_runObservedCleanFromTable
                    ((splitUniformImpl n).run rightCache) observations right.state rightFuel table
                    (observedResolvedResult observations nextRight) 0
                    (splitUniformImpl_probeFree n rightCache) hrightSupport
                  simpa [observedResolvedResult] using this
                have hleftRemainingUpper : nextLeft.remaining ≤ leftFuel :=
                  remaining_le_fuel_of_done_runDirectResolvedDetailedFromTable
                    ((splitUniformImpl n).run leftCache) left leftFuel table nextLeft
                    (by
                      rw [← map_erase_runDirectResolvedWitnessFromTable
                        ((splitUniformImpl n).run leftCache) left leftFuel table, support_map]
                      exact ⟨.done nextLeft, hleftSupport, rfl⟩)
                unfold canonicalizeDirectWitnessSnapshotObserve
                  classifyDirectWitnessSnapshotObserve
                simp only [canonical, hnotPrivate, ↓reduceDIte, hclean.left_published,
                  ↓reduceIte, hleftCompletable]
                rw [← hclean.value_eq]
                simpa [leftObserve] using
                  (ih nextLeft.value.1 snapshots observations canonical nextRight.context
                    nextLeft.remaining nextRight.remaining nextLeft.value.2 nextRight.value.2 bound
                    (hbound.2 nextLeft.value.1) hcanonicalRun.context_le hcanonicalRun.cache_eq
                    hcanonicalRun.revealed_eq hcanonicalRun.values_le
                    hcanonicalRun.left_published hcanonicalRun.right_materialized
                    (canonicalizeMaterializedValues_canonical table nextLeft.context
                      hclean.context_le.view.leftConsistent)
                    haligned (by omega) (by omega) (by omega)))
              convert hfinish using 1
              cases rightResult <;> rfl
          | inr input =>
              rw [simulateQ_expandedAdversaryImpl_query_bind_inl,
                OracleComp.isQueryBoundP_query_bind_iff] at hbound
              simp only
              have hrightValues :
                  (materializedCanonicalContext table right.state).state.values =
                    left.state.values := by
                unfold materializedCanonicalContext
                rw [← hrightMaterialized]
                exact canonicalized_right_values_eq_of_finalizationContextLE hcontext
                  hrevealed hcanonical
              have hplanEq :
                  purePlanProbingHashQuery parameter input
                      (materializedCanonicalContext table right.state).state =
                    purePlanProbingHashQuery parameter input left.state :=
                purePlanProbingHashQuery_eq_of_values_eq hrightValues parameter input
              rw [hplanEq]
              rw [← rootAwareCandidateForPlan?_purePlan parameter input left.state]
              let plan := purePlanProbingHashQuery parameter input left.state
              have hpublicExecutor :
                  probingHashQueryAfterRootAwarePublicPlan parameter input
                      (materializedCanonicalContext table right.state).state plan =
                    probingHashQueryAfterRootAwarePublicPlan parameter input left.state plan :=
                probingHashQueryAfterRootAwarePublicPlan_eq_of_values_eq parameter input
                  hrightValues plan
              rw [hpublicExecutor]
              let candidate? := rootAwareCandidateForPlan? parameter input plan
              let nextSnapshots := appendPlannedSnapshot snapshots candidate? left
              let nextObservations := observationsAfterCandidate observations right.state candidate?
              have hcontextDirect :
                  FinalizationContextLE table left (directDeferredContext right.state) := by
                rwa [← hrightMaterialized]
              have hnextAligned : SnapshotsObservedAt table nextSnapshots nextObservations := by
                exact haligned.appendCandidate candidate? hcontextDirect hrevealed hpublished
                  hcanonical
              have houter : IsOuterHash (.inl (.inr input)) := by simp [IsOuterHash]
              have hboundPositive : 0 < bound := by
                rcases hbound.1 with hnot | hpositive
                · exact (hnot (by simp)).elim
                · exact hpositive
              have hleftPositive : 0 < leftFuel := by omega
              have hstrictFuel : leftFuel < rightFuel := by omega
              have hlocal :=
                relTriple_runDirectResolvedWitness_afterPlan_observedMaterialized table parameter
                  input left.state plan observations left right leftFuel rightFuel leftCache
                  rightCache rfl hleftPositive hstrictFuel hcontext hcache hrevealed hvalues
                  hpublished hrightMaterialized
              have hleftSupported :=
                SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hlocal
                  (fun result => result ∈ support
                    (runDirectResolvedWitnessFromTable left leftFuel table
                      ((probingHashQueryAfterPlan parameter input plan).run leftCache)))
                  (fun result hresult => hresult)
              have hbothSupported :=
                SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support
                  hleftSupported
              let leftObserve : DeferredContext → Nat →
                  (HashOutput × SplitHashCache) → List PlannedProbeSnapshot →
                    ProbComp PrivateWitnessSnapshotOutput :=
                fun nextContext remaining value laterSnapshots =>
                  directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve parameter root
                    ftsSecret (next value.1)
                    (retainedResolvedFinalizationPrivateWitnessSnapshotObserve table root)
                    laterSnapshots nextContext remaining table value.2
              unfold runDirectWitnessSnapshotObserve
              apply relTriple_bind hbothSupported
              intro leftResult rightResult hstep
              rcases hstep with ⟨⟨hstep, hleftSupport⟩, hrightSupport⟩
              have hfinish := relTriple_finishWitnessObservedStep (α := HashOutput)
                (β := RetainedRestResult) parameter (fun _ => root) ftsSecret next leftObserve
                nextSnapshots nextObservations table leftResult rightResult hstep hnextAligned (by
                intro nextLeft nextRight hleftEq hrightEq hclean
                rw [hleftEq] at hleftSupport
                rw [hrightEq] at hrightSupport
                have hcanonicalRun := hclean.canonicalize_left
                let canonical := canonicalizeMaterializedValues table nextLeft.context
                have hleftCompletable : DeferredCompletable table canonical :=
                  hcanonicalRun.context_le.leftCompletable
                have hnotPrivate : ¬PrivateStructuralHit canonical :=
                  not_privateStructuralHit_of_deferredCompletable hleftCompletable
                have hleftFuelSpent : leftFuel ≤ nextLeft.remaining + 1 :=
                  fuel_le_remaining_add_of_done_runDirectResolvedWitnessFromTable
                    ((probingHashQueryAfterPlan parameter input plan).run leftCache) left leftFuel
                    table nextLeft 1
                    (probingHashQueryAfterPlan_isProbeBound_one parameter input plan leftCache)
                    hleftSupport
                have hrightFuelSpent : rightFuel ≤ nextRight.remaining + 1 := by
                  have := fuel_le_remaining_add_of_mem_runObservedCleanFromTable
                    ((probingHashQueryAfterRootAwarePublicPlan parameter input left.state plan).run
                      rightCache) observations right.state rightFuel table
                    (observedResolvedResult nextObservations nextRight) 1
                    (probingHashQueryAfterRootAwarePublicPlan_isProbeBound_one parameter input
                      left.state plan rightCache) hrightSupport
                  simpa [observedResolvedResult] using this
                have hleftRemainingUpper : nextLeft.remaining ≤ leftFuel :=
                  remaining_le_fuel_of_done_runDirectResolvedDetailedFromTable
                    ((probingHashQueryAfterPlan parameter input plan).run leftCache) left leftFuel
                    table nextLeft (by
                      rw [← map_erase_runDirectResolvedWitnessFromTable
                        ((probingHashQueryAfterPlan parameter input plan).run leftCache) left
                        leftFuel table, support_map]
                      exact ⟨.done nextLeft, hleftSupport, rfl⟩)
                unfold canonicalizeDirectWitnessSnapshotObserve
                  classifyDirectWitnessSnapshotObserve
                simp only [canonical, hnotPrivate, ↓reduceDIte, hclean.left_published,
                  ↓reduceIte, hleftCompletable]
                rw [← hclean.value_eq]
                simpa [leftObserve, IsOuterHash] using
                  (ih nextLeft.value.1 nextSnapshots nextObservations canonical
                    nextRight.context nextLeft.remaining nextRight.remaining nextLeft.value.2
                    nextRight.value.2 (bound - 1)
                    (by simpa [IsOuterHash] using hbound.2 nextLeft.value.1)
                    hcanonicalRun.context_le hcanonicalRun.cache_eq hcanonicalRun.revealed_eq
                    hcanonicalRun.values_le hcanonicalRun.left_published
                    hcanonicalRun.right_materialized
                    (canonicalizeMaterializedValues_canonical table nextLeft.context
                      hclean.context_le.view.leftConsistent)
                    hnextAligned (by omega) (by omega) (by omega)))
              convert hfinish using 1
              · rfl
              · cases rightResult <;> rfl
      | inr message =>
          rw [simulateQ_expandedAdversaryImpl_query_bind_inr] at hbound
          simp only
          let leftObserve : DeferredContext → Nat →
              (Option Signature × SplitHashCache) → List PlannedProbeSnapshot →
                ProbComp PrivateWitnessSnapshotOutput :=
            fun nextContext remaining value laterSnapshots =>
              directDetailedBoundaryNormalizedPrivateWitnessSnapshotObserve parameter root
                ftsSecret (next value.1)
                (retainedResolvedFinalizationPrivateWitnessSnapshotObserve table root)
                laterSnapshots nextContext remaining table value.2
          have hbase := (witnessMaterializedStableCouples_maskedSign table parameter root
            ftsSecret message) left right leftFuel rightFuel leftCache rightCache hcontext
              (by omega) hcache hrevealed hvalues hpublished hrightMaterialized
          have hlocal := relTriple_runDirectResolvedWitness_observed_of_probeFree table
            ((maskedSign parameter root ftsSecret message).run leftCache)
            ((maskedSign parameter root ftsSecret message).run rightCache)
            observations left right leftFuel rightFuel hbase
            (maskedSign_probeFree parameter root ftsSecret message rightCache) hrightMaterialized
          have hleftSupported :=
            SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hlocal
              (fun result => result ∈ support
                (runDirectResolvedWitnessFromTable left leftFuel table
                  ((maskedSign parameter root ftsSecret message).run leftCache)))
              (fun result hresult => hresult)
          have hbothSupported :=
            SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support
              hleftSupported
          unfold runDirectWitnessSnapshotObserve
          apply relTriple_bind hbothSupported
          intro leftResult rightResult hstep
          rcases hstep with ⟨⟨hstep, hleftSupport⟩, hrightSupport⟩
          have hfinish := relTriple_finishWitnessObservedStep (α := Option Signature)
            (β := RetainedRestResult) parameter (fun _ => root) ftsSecret next leftObserve
            snapshots observations table leftResult rightResult hstep haligned (by
            intro nextLeft nextRight hleftEq hrightEq hclean
            rw [hleftEq] at hleftSupport
            rw [hrightEq] at hrightSupport
            have hcanonicalRun := hclean.canonicalize_left
            let canonical := canonicalizeMaterializedValues table nextLeft.context
            have hleftCompletable : DeferredCompletable table canonical :=
              hcanonicalRun.context_le.leftCompletable
            have hnotPrivate : ¬PrivateStructuralHit canonical :=
              not_privateStructuralHit_of_deferredCompletable hleftCompletable
            have hleftFuelPreserved : leftFuel ≤ nextLeft.remaining := by
              have := fuel_le_remaining_add_of_done_runDirectResolvedWitnessFromTable
                ((maskedSign parameter root ftsSecret message).run leftCache) left leftFuel table
                nextLeft 0 (maskedSign_probeFree parameter root ftsSecret message leftCache)
                hleftSupport
              omega
            have hrightFuelPreserved : rightFuel ≤ nextRight.remaining := by
              have := fuel_le_remaining_add_of_mem_runObservedCleanFromTable
                ((maskedSign parameter root ftsSecret message).run rightCache) observations
                right.state rightFuel table (observedResolvedResult observations nextRight) 0
                (maskedSign_probeFree parameter root ftsSecret message rightCache) hrightSupport
              simpa [observedResolvedResult] using this
            have hleftRemainingUpper : nextLeft.remaining ≤ leftFuel :=
              remaining_le_fuel_of_done_runDirectResolvedDetailedFromTable
                ((maskedSign parameter root ftsSecret message).run leftCache) left leftFuel table
                nextLeft (by
                  rw [← map_erase_runDirectResolvedWitnessFromTable
                    ((maskedSign parameter root ftsSecret message).run leftCache) left leftFuel
                    table, support_map]
                  exact ⟨.done nextLeft, hleftSupport, rfl⟩)
            unfold canonicalizeDirectWitnessSnapshotObserve
              classifyDirectWitnessSnapshotObserve
            simp only [canonical, hnotPrivate, ↓reduceDIte, hclean.left_published,
              ↓reduceIte, hleftCompletable]
            rw [← hclean.value_eq]
            have hdetailed : DirectDetailedResult.done nextLeft ∈ support
                (runDirectResolvedDetailedFromTable left leftFuel table
                  ((maskedSign parameter root ftsSecret message).run leftCache)) := by
              rw [← map_erase_runDirectResolvedWitnessFromTable
                ((maskedSign parameter root ftsSecret message).run leftCache)
                left leftFuel table, support_map]
              exact ⟨.done nextLeft, hleftSupport, rfl⟩
            have hdirect : some nextLeft ∈ support
                (runDirectResolvedFromTable left leftFuel table
                  ((maskedSign parameter root ftsSecret message).run leftCache)) :=
              mem_support_runDirectResolvedFromTable_of_done_detailed
                ((maskedSign parameter root ftsSecret message).run leftCache)
                left leftFuel table nextLeft hdetailed
            have hraw := raw_done_of_mem_runDirectResolvedFromTable
              ((maskedSign parameter root ftsSecret message).run leftCache)
              left leftFuel table nextLeft hdirect
            have houtput : nextLeft.value.1 ∈ support
                (scheme.sign
                  (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
                    SecretKey) message) := by
              exact maskedSign_done_output_mem_support parameter root table ftsSecret
                message left.state nextLeft.context.state leftCache nextLeft.value.2
                leftFuel nextLeft.remaining nextLeft.value.1
                  hclean.context_le.view.leftStarts (by
                    simpa only [SigningSpec, maskedExpandedAdversaryImpl,
                      maskedSigningImpl] using hraw)
            have htailBound := isQueryBoundP_of_bind hbound nextLeft.value.1 houtput
            simpa [leftObserve, IsOuterHash] using
              (ih nextLeft.value.1 snapshots observations canonical nextRight.context
                nextLeft.remaining nextRight.remaining nextLeft.value.2 nextRight.value.2 bound
                (htailBound.mono (by omega))
                hcanonicalRun.context_le hcanonicalRun.cache_eq hcanonicalRun.revealed_eq
                hcanonicalRun.values_le hcanonicalRun.left_published
                hcanonicalRun.right_materialized
                (canonicalizeMaterializedValues_canonical table nextLeft.context
                  hclean.context_le.view.leftConsistent)
                haligned (by omega) (by omega) (by omega)))
          convert hfinish using 1
          · rfl
          · cases rightResult <;> rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
