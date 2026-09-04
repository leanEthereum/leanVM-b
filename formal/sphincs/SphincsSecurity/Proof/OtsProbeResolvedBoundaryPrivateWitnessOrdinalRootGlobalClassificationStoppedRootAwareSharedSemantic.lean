import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAwareSharedExperiment

/-!
# Successful shared-prefix semantics

The lemmas in this module eliminate the conservative failure arm of the root-aware outcome under
the successful first-root gate carried by the observed marginal.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option linter.constructorNameAsVariable false
attribute [local irreducible] maskedPublishedTreeRoot

set_option maxRecDepth 100000 in
theorem revealed_subset_of_done_runDirectResolvedDetailedFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult α)
    (hresult : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table computation)) :
    context.state.revealed ⊆ result.context.state.revealed := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      simp [runDirectResolvedDetailedFromTable] at hresult
      subst result
      exact Finset.Subset.rfl
  | query_bind input next ih =>
      cases input with
      | uniform n =>
          rw [runDirectResolvedDetailedFromTable_uniform_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output context fuel hrest
      | hashOutput =>
          rw [runDirectResolvedDetailedFromTable_hashOutput_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, hrest⟩ := hresult
          exact ih output context fuel hrest
      | ensure coordinate =>
          rw [runDirectResolvedDetailedFromTable_ensure_query_bind] at hresult
          exact ih () { context with state := context.state.ensure coordinate } fuel hresult
      | probe coordinate candidate =>
          rw [runDirectResolvedDetailedFromTable_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · exact ih () context remaining (by simpa [hrevealed] using hresult)
              · exact ih ()
                  { context with state := context.state.addPending coordinate candidate }
                  remaining (by simpa [hrevealed] using hresult)
      | peek coordinate =>
          rw [runDirectResolvedDetailedFromTable_peek_query_bind] at hresult
          exact ih (context.state.values coordinate) context fuel hresult
      | publish coordinate =>
          rw [runDirectResolvedDetailedFromTable_publish_query_bind] at hresult
          have htail := ih ()
            { context with state := context.state.publish coordinate } fuel hresult
          intro other hother
          apply htail
          simp [LazyRevealProbe.State.publish, hother]
      | reveal coordinate =>
          rw [runDirectResolvedDetailedFromTable_reveal_query_bind] at hresult
          cases hstate : context.state.values coordinate with
          | some output =>
              simp only [hstate] at hresult
              exact ih output context fuel hresult
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
                      fuel hresult
              | position position =>
                  cases hprivate : context.values position with
                  | some output =>
                      by_cases hhit : context.state.hitAt (.position position) output
                      · simp [hprivate, hhit] at hresult
                      · simp only [hprivate, hhit, ↓reduceIte] at hresult
                        exact ih output
                          { state := context.state.materialize (.position position) output
                            values := context.values }
                          fuel hresult
                  | none =>
                      simp only [hprivate, mem_support_bind_iff] at hresult
                      obtain ⟨output, _houtput, hrest⟩ := hresult
                      by_cases hhit : context.state.hitAt (.position position) output
                      · simp [hhit] at hrest
                      · simp only [hhit, ↓reduceIte] at hrest
                        exact ih output
                          { state := context.state.materialize (.position position) output
                            values := context.values.install position output }
                          fuel hrest

theorem revealed_subset_of_mem_runObservedCleanFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (result : ObservedCleanRunResult α)
    (hresult : some result ∈ support
      (runObservedCleanFromTable observations state fuel table computation)) :
    state.revealed ⊆ result.state.revealed := by
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
      exact revealed_subset_of_done_runDirectResolvedDetailedFromTable computation
        (directDeferredContext state) fuel table detailed hdetailed

set_option maxRecDepth 100000 in
theorem revealedAtProbe_of_mem_runObservedCleanFromTable_of_initial_revealed :
    ∀ (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
      (observations : List CleanProbeObservation)
      (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
      (table : OtsSecretIndex → HashOutput) (target : Position) (ordinal : Nat)
      (result : ObservedCleanRunResult α),
      Coordinate.position target ∈ state.revealed →
      observations.length ≤ ordinal →
      some result ∈ support
        (runObservedCleanFromTable observations state fuel table computation) →
      (hordinal : ordinal < result.observations.length) →
      (result.observations.get ⟨ordinal, hordinal⟩).coordinate = .position target →
      (result.observations.get ⟨ordinal, hordinal⟩).revealedAtProbe = true
  | computation, observations, state, fuel, table, target, ordinal, result,
      hrevealed, hlength, hresult, hordinal, hcoordinate => by
    induction computation using OracleComp.inductionOn generalizing
        observations state fuel table with
    | pure value =>
        simp [runObservedCleanFromTable] at hresult
        subst result
        simp at hordinal
        omega
    | query_bind input next ih =>
        cases input with
        | uniform n =>
            rw [runObservedCleanFromTable, OracleComp.construct_query_bind,
              mem_support_bind_iff] at hresult
            obtain ⟨output, _houtput, hrest⟩ := hresult
            exact ih output observations state fuel table hrevealed hlength hrest
        | hashOutput =>
            rw [runObservedCleanFromTable, OracleComp.construct_query_bind,
              mem_support_bind_iff] at hresult
            obtain ⟨output, _houtput, hrest⟩ := hresult
            exact ih output observations state fuel table hrevealed hlength hrest
        | ensure coordinate =>
            rw [runObservedCleanFromTable, OracleComp.construct_query_bind] at hresult
            exact ih () observations (state.ensure coordinate) fuel table hrevealed hlength hresult
        | probe coordinate candidate =>
            rw [runObservedCleanFromTable_probe_query_bind] at hresult
            cases fuel with
            | zero => simp at hresult
            | succ remaining =>
                let observation := cleanProbeObservation state coordinate candidate
                let nextObservations := observations ++ [observation]
                have hprefix : nextObservations <+: result.observations := by
                  by_cases hcoordinateRevealed : coordinate ∈ state.revealed
                  · exact observations_prefix_of_mem_runObservedCleanFromTable
                      (next ()) nextObservations state remaining table result
                      (by simpa [hcoordinateRevealed, nextObservations, observation] using hresult)
                  · exact observations_prefix_of_mem_runObservedCleanFromTable
                      (next ()) nextObservations (state.addPending coordinate candidate) remaining
                      table result
                      (by simpa [hcoordinateRevealed, nextObservations, observation] using hresult)
                by_cases heq : observations.length = ordinal
                · have hnextLength : ordinal < nextObservations.length := by
                    simp [nextObservations, heq]
                  have hget := hprefix.getElem hnextLength
                  subst ordinal
                  have hprobeCoordinate : coordinate = .position target := by
                    have hcoordinateEq := congrArg CleanProbeObservation.coordinate hget
                    change result.observations[observations.length].coordinate =
                      .position target at hcoordinate
                    simpa [nextObservations, observation, cleanProbeObservation] using
                      hcoordinateEq.trans hcoordinate
                  subst coordinate
                  have hrevealedEq := congrArg CleanProbeObservation.revealedAtProbe hget
                  change result.observations[observations.length].revealedAtProbe = true
                  exact hrevealedEq.symm.trans (by
                    simp [nextObservations, observation, cleanProbeObservation, hrevealed])
                · have hnextLength : nextObservations.length ≤ ordinal := by
                    simp [nextObservations]
                    omega
                  by_cases hcoordinateRevealed : coordinate ∈ state.revealed
                  · exact ih () nextObservations state remaining table hrevealed hnextLength
                      (by simpa [hcoordinateRevealed, nextObservations, observation] using hresult)
                  · exact ih () nextObservations (state.addPending coordinate candidate) remaining
                      table hrevealed hnextLength
                      (by simpa [hcoordinateRevealed, nextObservations, observation] using hresult)
        | peek coordinate =>
            rw [runObservedCleanFromTable, OracleComp.construct_query_bind] at hresult
            exact ih (state.values coordinate) observations state fuel table hrevealed hlength
              hresult
        | publish coordinate =>
            rw [runObservedCleanFromTable, OracleComp.construct_query_bind] at hresult
            exact ih () observations (state.publish coordinate) fuel table
              (by simp [LazyRevealProbe.State.publish, hrevealed]) hlength hresult
        | reveal coordinate =>
            rw [runObservedCleanFromTable, OracleComp.construct_query_bind] at hresult
            cases hvalue : state.values coordinate with
            | some output =>
                simp only [hvalue] at hresult
                exact ih output observations state fuel table hrevealed hlength hresult
            | none =>
                simp only [hvalue] at hresult
                cases coordinate with
                | chainStart lay tree leafIdx chainIdx =>
                    let output := table ⟨lay, tree, leafIdx, chainIdx⟩
                    by_cases hhit : state.hitAt
                        (.chainStart lay tree leafIdx chainIdx) output
                    · simp [output, hhit] at hresult
                    · simp only [output, hhit, ↓reduceIte] at hresult
                      exact ih output observations
                        (state.materialize (.chainStart lay tree leafIdx chainIdx) output) fuel
                        table hrevealed hlength hresult
                | position position =>
                    rw [mem_support_bind_iff] at hresult
                    obtain ⟨output, _houtput, hrest⟩ := hresult
                    by_cases hhit : state.hitAt (.position position) output
                    · simp [hhit] at hrest
                    · simp only [hhit, ↓reduceIte] at hrest
                      exact ih output observations (state.materialize (.position position) output)
                        fuel table hrevealed hlength hrest

theorem revealedAtProbe_of_prefix
    {before after : List CleanProbeObservation} {ordinal : Nat} {target : Position}
    (hprefix : before <+: after)
    (hbefore : ordinal < before.length) (hafter : ordinal < after.length)
    (hcoordinate : (after.get ⟨ordinal, hafter⟩).coordinate = .position target)
    (hrevealed : (before.get ⟨ordinal, hbefore⟩).revealedAtProbe = true) :
    (after.get ⟨ordinal, hafter⟩).revealedAtProbe = true := by
  have hget := hprefix.getElem hbefore
  have hcoordinateEq := congrArg CleanProbeObservation.coordinate hget
  change after[ordinal].coordinate = .position target at hcoordinate
  have _hbeforeCoordinate : before[ordinal].coordinate = .position target :=
    hcoordinateEq.trans hcoordinate
  have hrevealedEq := congrArg CleanProbeObservation.revealedAtProbe hget
  change before[ordinal].revealedAtProbe = true at hrevealed
  change after[ordinal].revealedAtProbe = true
  exact hrevealedEq.symm.trans hrevealed

set_option maxRecDepth 100000 in
theorem revealedAtProbe_of_mem_observedMaterializedBoundary_of_initial_revealed :
    ∀ (parameter : PublicParameter) (root : Digest)
      (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
      (computation : OracleComp (OracleWorld + SigningSpec) α)
      (observations : List CleanProbeObservation)
      (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
      (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
      (target : Position) (ordinal : Nat)
      (result : ObservedCleanRunResult (α × SplitHashCache)),
      Coordinate.position target ∈ state.revealed →
      observations.length ≤ ordinal →
      some result ∈ support
        (observedMaterializedBoundary parameter root ftsSecret computation observations state fuel
          table cache) →
      (hordinal : ordinal < result.observations.length) →
      (result.observations.get ⟨ordinal, hordinal⟩).coordinate = .position target →
      (result.observations.get ⟨ordinal, hordinal⟩).revealedAtProbe = true
  | parameter, root, ftsSecret, computation, observations, state, fuel, table, cache, target,
      ordinal, result, hrevealed, hlength, hresult, hordinal, hcoordinate => by
    induction computation using OracleComp.inductionOn generalizing
        observations state fuel table cache with
    | pure value =>
        simp [observedMaterializedBoundary] at hresult
        obtain rfl := hresult
        simp at hordinal
        omega
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
                    by_cases hbefore : ordinal < step.observations.length
                    · have hstepRevealed :=
                        revealedAtProbe_of_mem_runObservedCleanFromTable_of_initial_revealed
                          ((splitUniformImpl n).run cache) observations state fuel table target
                          ordinal step hrevealed hlength hstep hbefore (by
                            have hprefix := observations_prefix_of_mem_observedMaterializedBoundary
                              parameter root ftsSecret (next step.value.1) step.observations
                              step.state step.remaining table step.value.2 result
                              (by simpa only [observedMaterializedBoundary] using hrest)
                            have hget := hprefix.getElem hbefore
                            have hcoordinateEq := congrArg CleanProbeObservation.coordinate hget
                            change result.observations[ordinal].coordinate = .position target at hcoordinate
                            exact hcoordinateEq.trans hcoordinate)
                      have hprefix := observations_prefix_of_mem_observedMaterializedBoundary
                        parameter root ftsSecret (next step.value.1) step.observations step.state
                        step.remaining table step.value.2 result
                        (by simpa only [observedMaterializedBoundary] using hrest)
                      exact revealedAtProbe_of_prefix hprefix hbefore hordinal hcoordinate
                        hstepRevealed
                    · have hstepRevealed : Coordinate.position target ∈ step.state.revealed :=
                        revealed_subset_of_mem_runObservedCleanFromTable
                          ((splitUniformImpl n).run cache) observations state fuel table step hstep
                          hrevealed
                      exact ih step.value.1 step.observations step.state step.remaining table
                        step.value.2 hstepRevealed (Nat.le_of_not_gt hbefore)
                        (by simpa only [observedMaterializedBoundary] using hrest)
            | inr input =>
                rw [mem_support_bind_iff] at hresult
                obtain ⟨step?, hstep, hrest⟩ := hresult
                cases step? with
                | none => simp at hrest
                | some step =>
                    let publicContext := materializedCanonicalContext table state
                    let plan := purePlanProbingHashQuery parameter input publicContext.state
                    let stepComputation :=
                      (probingHashQueryAfterRootAwarePublicPlan parameter input publicContext.state
                        plan).run cache
                    by_cases hbefore : ordinal < step.observations.length
                    · have hprefix := observations_prefix_of_mem_observedMaterializedBoundary
                        parameter root ftsSecret (next step.value.1) step.observations step.state
                        step.remaining table step.value.2 result
                        (by simpa only [observedMaterializedBoundary] using hrest)
                      have hget := hprefix.getElem hbefore
                      have hcoordinateEq := congrArg CleanProbeObservation.coordinate hget
                      have hstepCoordinate :
                          (step.observations.get ⟨ordinal, hbefore⟩).coordinate =
                            .position target := by
                        change result.observations[ordinal].coordinate = .position target at hcoordinate
                        exact hcoordinateEq.trans hcoordinate
                      have hstepRevealed :=
                        revealedAtProbe_of_mem_runObservedCleanFromTable_of_initial_revealed
                          stepComputation observations state fuel table target ordinal step
                          hrevealed hlength hstep hbefore hstepCoordinate
                      exact revealedAtProbe_of_prefix hprefix hbefore hordinal hcoordinate
                        hstepRevealed
                    · have hstepRevealed : Coordinate.position target ∈ step.state.revealed :=
                        revealed_subset_of_mem_runObservedCleanFromTable stepComputation observations
                          state fuel table step hstep hrevealed
                      exact ih step.value.1 step.observations step.state step.remaining table
                        step.value.2 hstepRevealed (Nat.le_of_not_gt hbefore)
                        (by simpa only [observedMaterializedBoundary] using hrest)
        | inr message =>
            rw [mem_support_bind_iff] at hresult
            obtain ⟨step?, hstep, hrest⟩ := hresult
            cases step? with
            | none => simp at hrest
            | some step =>
                let stepComputation := (maskedSign parameter root ftsSecret message).run cache
                by_cases hbefore : ordinal < step.observations.length
                · have hprefix := observations_prefix_of_mem_observedMaterializedBoundary
                    parameter root ftsSecret (next step.value.1) step.observations step.state
                    step.remaining table step.value.2 result
                    (by simpa only [observedMaterializedBoundary] using hrest)
                  have hget := hprefix.getElem hbefore
                  have hcoordinateEq := congrArg CleanProbeObservation.coordinate hget
                  have hstepCoordinate :
                      (step.observations.get ⟨ordinal, hbefore⟩).coordinate = .position target := by
                    change result.observations[ordinal].coordinate = .position target at hcoordinate
                    exact hcoordinateEq.trans hcoordinate
                  have hstepRevealed :=
                    revealedAtProbe_of_mem_runObservedCleanFromTable_of_initial_revealed
                      stepComputation observations state fuel table target ordinal step hrevealed
                      hlength hstep hbefore hstepCoordinate
                  exact revealedAtProbe_of_prefix hprefix hbefore hordinal hcoordinate hstepRevealed
                · have hstepRevealed : Coordinate.position target ∈ step.state.revealed :=
                    revealed_subset_of_mem_runObservedCleanFromTable stepComputation observations
                      state fuel table step hstep hrevealed
                  exact ih step.value.1 step.observations step.state step.remaining table
                    step.value.2 hstepRevealed (Nat.le_of_not_gt hbefore)
                    (by simpa only [observedMaterializedBoundary] using hrest)

theorem observations_eq_of_mem_runObservedCleanFromTable_rootAwarePublic
    (parameter : PublicParameter) (input : HashInput)
    (publicState : LazyRevealProbe.State Coordinate) (plan : PlannedHashQuery)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : ObservedCleanRunResult (HashOutput × SplitHashCache))
    (hresult : some result ∈ support
      (runObservedCleanFromTable observations state fuel table
        ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run cache))) :
    result.observations = observationsAfterCandidate observations state
      (rootAwareCandidateForPlan? parameter input plan) := by
  have hmapped : some result ∈ support
      (attachCleanProbeObservations
          (observationsAfterCandidate observations state
            (rootAwareCandidateForPlan? parameter input plan)) <$>
        runCleanFromTable state fuel table
          ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run cache)) := by
    rw [map_attach_runClean_rootAwarePublic_eq_observed]
    exact hresult
  rw [support_map] at hmapped
  obtain ⟨clean, _hclean, hattach⟩ := hmapped
  cases clean with
  | none => simp [attachCleanProbeObservations] at hattach
  | some clean =>
      have heq : result =
          (⟨clean.state, clean.remaining, clean.value, clean.table,
            observationsAfterCandidate observations state
              (rootAwareCandidateForPlan? parameter input plan)⟩ :
            ObservedCleanRunResult (HashOutput × SplitHashCache)) := by
        simpa [attachCleanProbeObservations] using Option.some.inj hattach.symm
      exact congrArg ObservedCleanRunResult.observations heq

set_option maxRecDepth 100000 in
theorem revealed_subset_of_mem_observedMaterializedBoundary
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
    state.revealed ⊆ result.state.revealed := by
  induction computation using OracleComp.inductionOn generalizing
      observations state fuel table cache with
  | pure value =>
      simp [observedMaterializedBoundary] at hresult
      obtain rfl := hresult
      exact Finset.Subset.rfl
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
                  exact (revealed_subset_of_mem_runObservedCleanFromTable
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
                  exact (revealed_subset_of_mem_runObservedCleanFromTable
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
              exact (revealed_subset_of_mem_runObservedCleanFromTable
                ((maskedSign parameter root ftsSecret message).run cache) observations state fuel
                  table step hstep).trans
                (ih step.value.1 step.observations step.state step.remaining table
                  step.value.2 (by simpa only [observedMaterializedBoundary] using hrest))

theorem finished_probe_matches_of_successful_root
    {table : OtsSecretIndex → HashOutput} {ordinal : Nat} {target : Position}
    {rightRoot leftRoot : Digest}
    {result : ObservedCleanRunResult α} {candidate : Probe}
    {selected : Fin result.observations.length}
    (hgood : ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
      table ordinal target rightRoot (some result))
    (hselected : selected.val = ordinal)
    (hcandidate : candidate = (result.observations.get selected).toProbe)
    (hstored : StoredLayerRoot result.state target leftRoot)
    (htracked : CleanProbeObservationsTrackedBy result.observations result.state) :
    (MaterializedSelectionOutcome.finished (some candidate)).Matches target leftRoot := by
  obtain ⟨⟨⟨⟨_finalResult, _hfinish⟩, _hdoomed,
      goodSelected, hgoodSelected, hfirst, _hroot⟩,
    hposition⟩, _hcomparison⟩ := hgood
  obtain ⟨hitSelected, hhitSelected, hhit, _hnoEarlier⟩ := hfirst
  have hselectedEq : selected = goodSelected :=
    Fin.ext (hselected.trans hgoodSelected.symm)
  have hhitSelectedEq : hitSelected = goodSelected :=
    Fin.ext (hhitSelected.trans hgoodSelected.symm)
  subst selected
  subst hitSelected
  have hlt : ordinal < result.observations.length := by
    rw [← hgoodSelected]
    exact goodSelected.isLt
  have hindex : (⟨ordinal, hlt⟩ : Fin result.observations.length) = goodSelected :=
    Fin.ext hgoodSelected.symm
  have htargetData :
      (result.observations.get goodSelected).coordinate = .position target ∧
        IsLayerRoot target := by
    simp only [observedFirstLayerRootPosition?, hlt, ↓reduceDIte] at hposition
    rw [candidateLayerRootPosition?_eq_some_iff, hindex] at hposition
    exact hposition
  obtain ⟨_hhidden, output, hvalueAtProbe, hdigest⟩ := hhit
  have htrackedObservation := htracked
    (result.observations.get goodSelected) (List.get_mem _ _)
  have hfinalValue := htrackedObservation.1 output hvalueAtProbe
  obtain ⟨stored, hstoredValue, hstoredDigest⟩ := hstored
  rw [htargetData.1] at hfinalValue
  have houtput : output = stored := Option.some.inj (hfinalValue.symm.trans hstoredValue)
  subst stored
  change candidate = ⟨.position target, leftRoot⟩
  rw [hcandidate]
  unfold CleanProbeObservation.toProbe
  rw [htargetData.1, ← hdigest, hstoredDigest]

theorem selected_finish_matches_of_successful_root
    {table : OtsSecretIndex → HashOutput} {ordinal : Nat} {target : Position}
    {rightRoot leftRoot : Digest}
    {parameter : PublicParameter} {publicRoot : Digest}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    {computation : OracleComp (OracleWorld + SigningSpec) α}
    {observations : List CleanProbeObservation} {candidates : List Probe}
    {state : LazyRevealProbe.State Coordinate} {fuel : Nat} {cache : SplitHashCache}
    (hselected : ordinal < candidates.length)
    (haligned : candidates = observations.map CleanProbeObservation.toProbe)
    (hstored : StoredLayerRoot state target leftRoot)
    (htracked : CleanProbeObservationsTrackedBy observations state)
    {result : ObservedCleanRunResult (α × SplitHashCache)}
    (hrun : some result ∈ support
      (observedMaterializedBoundary parameter publicRoot ftsSecret computation observations state
        fuel table cache))
    (hgood : ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
      table ordinal target rightRoot (some result)) :
    (MaterializedSelectionOutcome.finished
      (some (candidates.get ⟨ordinal, hselected⟩))).Matches target leftRoot := by
  have hgood' := hgood
  obtain ⟨⟨⟨⟨_finalResult, _hfinish⟩, _hdoomed,
      goodSelected, hgoodSelected, _hfirst, _hroot⟩,
    _hposition⟩, _hcomparison⟩ := hgood
  have hobservationSelected : ordinal < observations.length := by
    simpa [haligned] using hselected
  have hprefix := observations_prefix_of_mem_observedMaterializedBoundary parameter publicRoot
    ftsSecret computation observations state fuel table cache result hrun
  have hget : observations[ordinal] = result.observations[ordinal] :=
    hprefix.getElem hobservationSelected
  have hresultSelected : ordinal < result.observations.length := by
    rw [← hgoodSelected]
    exact goodSelected.isLt
  have hindex : (⟨ordinal, hresultSelected⟩ : Fin result.observations.length) = goodSelected :=
    Fin.ext hgoodSelected.symm
  have hcandidatesGet : candidates.get ⟨ordinal, hselected⟩ =
      (observations.get ⟨ordinal, hobservationSelected⟩).toProbe := by
    subst candidates
    simp
  have hcandidate : candidates.get ⟨ordinal, hselected⟩ =
      (result.observations.get goodSelected).toProbe := by
    rw [hcandidatesGet, ← hindex]
    exact congrArg CleanProbeObservation.toProbe hget
  have hstoredFinal : StoredLayerRoot result.state target leftRoot :=
    storedLayerRoot_mono hstored
      (valuesLE_of_mem_observedMaterializedBoundary parameter publicRoot ftsSecret computation
        observations state fuel table cache result hrun)
  have htrackedFinal := cleanProbeObservationsTrackedBy_of_mem_observedMaterializedBoundary
    parameter publicRoot ftsSecret computation observations state fuel table cache htracked result
    hrun
  exact finished_probe_matches_of_successful_root hgood' hgoodSelected hcandidate hstoredFinal
    htrackedFinal

theorem not_hasExistingHiddenHit_of_prefix_first_at_or_after
    {before : List CleanProbeObservation} {result : ObservedCleanRunResult α}
    {ordinal : Nat}
    (hprefix : before <+: result.observations)
    (hlength : before.length ≤ ordinal)
    (hfirst : FirstExistingHiddenHitAt result ordinal) :
    ¬(⟨result.state, result.remaining, result.value, result.table, before⟩ :
      ObservedCleanRunResult α).HasExistingHiddenHit := by
  rintro ⟨observation, hobservation, hhit⟩
  obtain ⟨beforeIndex, hget⟩ := List.mem_iff_get.mp hobservation
  have hresultIndex : beforeIndex.val < result.observations.length :=
    lt_of_lt_of_le beforeIndex.isLt hprefix.length_le
  let resultIndex : Fin result.observations.length := ⟨beforeIndex.val, hresultIndex⟩
  obtain ⟨selected, hselected, _hselectedHit, hnoEarlier⟩ := hfirst
  apply hnoEarlier resultIndex (lt_of_lt_of_le beforeIndex.isLt hlength)
  have hprefixGet : before[beforeIndex.val] = result.observations[resultIndex.val] :=
    hprefix.getElem beforeIndex.isLt
  simpa [ExistingHiddenHitAtOrdinal, resultIndex, ← hprefixGet, ← hget] using hhit

theorem successful_root_not_of_noncompletable_prefix
    {table : OtsSecretIndex → HashOutput} {ordinal : Nat} {target : Position}
    {rightRoot : Digest}
    {parameter : PublicParameter} {publicRoot : Digest}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    {computation : OracleComp (OracleWorld + SigningSpec) α}
    {observations : List CleanProbeObservation}
    {state : LazyRevealProbe.State Coordinate} {fuel : Nat} {cache : SplitHashCache}
    (hlength : observations.length ≤ ordinal)
    (htracked : CleanProbeObservationsTrackedBy observations state)
    (hcovered : CleanProbeObservationsCoverPending observations state)
    (hstarts : StartTableAgrees state table)
    (hbudget : fuel + state.pending.card < Fintype.card Digest)
    (hnotCompletable : ¬DeferredCompletable table (directDeferredContext state))
    {result : ObservedCleanRunResult (α × SplitHashCache)}
    (hrun : some result ∈ support
      (observedMaterializedBoundary parameter publicRoot ftsSecret computation observations state
        fuel table cache))
    (hgood : ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
      table ordinal target rightRoot (some result)) : False := by
  obtain ⟨⟨⟨⟨finalResult, hfinish⟩, _hdoomed,
      _selected, _hselected, hfirst, _hroot⟩,
    _hposition⟩, _hcomparison⟩ := hgood
  have hprefix := observations_prefix_of_mem_observedMaterializedBoundary parameter publicRoot
    ftsSecret computation observations state fuel table cache result hrun
  have hnoHit : ¬(⟨state, fuel, result.value, table, observations⟩ :
      ObservedCleanRunResult (α × SplitHashCache)).HasExistingHiddenHit := by
    apply not_hasExistingHiddenHit_of_prefix_first_at_or_after hprefix hlength hfirst
  have hvalid : (directDeferredContext state).Valid :=
    directDeferredContext_valid_of_no_existingHiddenHit
      ⟨state, fuel, result.value, table, observations⟩ htracked hcovered hnoHit
  have hmissing := missingChainStartHit_of_doomed_direct_valid table state
    ⟨hvalid.valuesConsistent, hstarts, hnotCompletable⟩ hvalid (by omega)
  exact not_missingChainStartHit_of_successful_observedMaterializedBoundary parameter publicRoot
    ftsSecret computation observations state fuel table cache result finalResult hrun hfinish
    hmissing

theorem successful_root_not_of_revealed_prefix
    {table : OtsSecretIndex → HashOutput} {ordinal : Nat} {target : Position}
    {rightRoot : Digest}
    {parameter : PublicParameter} {publicRoot : Digest}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    {computation : OracleComp (OracleWorld + SigningSpec) α}
    {observations : List CleanProbeObservation}
    {state : LazyRevealProbe.State Coordinate} {fuel : Nat} {cache : SplitHashCache}
    (hlength : observations.length ≤ ordinal)
    (hrevealed : Coordinate.position target ∈ state.revealed)
    {result : ObservedCleanRunResult (α × SplitHashCache)}
    (hrun : some result ∈ support
      (observedMaterializedBoundary parameter publicRoot ftsSecret computation observations state
        fuel table cache))
    (hgood : ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
      table ordinal target rightRoot (some result)) : False := by
  obtain ⟨⟨⟨⟨_finalResult, _hfinish⟩, _hdoomed,
      selected, hselected, hfirst, _hroot⟩,
    hposition⟩, _hcomparison⟩ := hgood
  obtain ⟨hitSelected, hhitSelected, hhit, _hnoEarlier⟩ := hfirst
  have hselectedEq : hitSelected = selected :=
    Fin.ext (hhitSelected.trans hselected.symm)
  subst hitSelected
  obtain ⟨hhidden, _output, _hvalue, _hdigest⟩ := hhit
  have hlt : ordinal < result.observations.length := by
    rw [← hselected]
    exact selected.isLt
  have hindex : (⟨ordinal, hlt⟩ : Fin result.observations.length) = selected :=
    Fin.ext hselected.symm
  have htargetData :
      (result.observations.get selected).coordinate = .position target := by
    simp only [observedFirstLayerRootPosition?, hlt, ↓reduceDIte] at hposition
    rw [candidateLayerRootPosition?_eq_some_iff, hindex] at hposition
    exact hposition.1
  have hrevealedAtProbe :=
    revealedAtProbe_of_mem_observedMaterializedBoundary_of_initial_revealed parameter publicRoot
      ftsSecret computation observations state fuel table cache target ordinal result hrevealed
      hlength hrun hlt (by simpa [hindex] using htargetData)
  rw [hindex] at hrevealedAtProbe
  exact Bool.false_ne_true (hhidden.symm.trans hrevealedAtProbe)

theorem selected_finish_pair_matches_of_successful_root
    {table : OtsSecretIndex → HashOutput} {ordinal : Nat} {target : Position}
    {rightRoot leftRoot : Digest}
    {parameter : PublicParameter} {publicRoot : Digest}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    {computation : OracleComp (OracleWorld + SigningSpec) α}
    {observations : List CleanProbeObservation} {candidates : List Probe}
    {state : LazyRevealProbe.State Coordinate} {fuel : Nat} {cache : SplitHashCache}
    (hselected : ordinal < candidates.length)
    (haligned : candidates = observations.map CleanProbeObservation.toProbe)
    (hstored : StoredLayerRoot state target leftRoot)
    (htracked : CleanProbeObservationsTrackedBy observations state)
    {pair : Option (ObservedCleanRunResult (α × SplitHashCache)) ×
      MaterializedSelectionOutcome}
    (hpair : pair ∈ support
      (finishObservedWithSelectionOutcome parameter publicRoot ftsSecret computation observations
        state fuel table cache (.finished (some (candidates.get ⟨ordinal, hselected⟩)))))
    (hgood : ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
      table ordinal target rightRoot pair.1) :
    pair.2.Matches target leftRoot := by
  unfold finishObservedWithSelectionOutcome at hpair
  rw [mem_support_bind_iff] at hpair
  obtain ⟨observed, hobserved, hreturn⟩ := hpair
  simp only [support_pure, Set.mem_singleton_iff] at hreturn
  subst pair
  cases observed with
  | none =>
      simp [ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt,
        ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget,
        ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt] at hgood
  | some result =>
      exact selected_finish_matches_of_successful_root hselected haligned hstored htracked
        hobserved hgood

theorem successful_root_not_of_unsafe_hash_prefix
    {table : OtsSecretIndex → HashOutput} {ordinal : Nat} {target : Position}
    {rightRoot leftRoot : Digest}
    {parameter : PublicParameter} {publicRoot : Digest}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    {input : HashInput} {next : HashOutput → OracleComp (OracleWorld + SigningSpec) α}
    {observations : List CleanProbeObservation} {candidates : List Probe}
    {state : LazyRevealProbe.State Coordinate} {fuel : Nat} {cache : SplitHashCache}
    {candidate : Probe}
    (haligned : candidates = observations.map CleanProbeObservation.toProbe)
    (hnextLength : (appendPlannedCandidate candidates (some candidate)).length ≤ ordinal)
    (hhidden : Coordinate.position target ∉ state.revealed)
    (hstored : StoredLayerRoot state target leftRoot)
    (hcandidate : rootAwareCandidateForPlan? parameter input
      (purePlanProbingHashQuery parameter input
        (materializedCanonicalContext table state).state) = some candidate)
    (hunsafe : ¬RootAwareCandidateAvoidsRoots target leftRoot rightRoot (some candidate))
    {result : ObservedCleanRunResult (α × SplitHashCache)}
    (hrun : some result ∈ support
      (observedMaterializedBoundary parameter publicRoot ftsSecret
        (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
          (Sum.inl (Sum.inr input))) >>= next)
        observations state fuel table cache))
    (hgood : ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
      table ordinal target rightRoot (some result)) : False := by
  rw [observedMaterializedBoundary_hash_query_bind, mem_support_bind_iff] at hrun
  obtain ⟨step?, hstep, hrest⟩ := hrun
  cases step? with
  | none => simp at hrest
  | some step =>
      let publicContext := materializedCanonicalContext table state
      let plan := purePlanProbingHashQuery parameter input publicContext.state
      let observation := cleanProbeObservation state candidate.coordinate candidate.candidate
      have hcandidateActual : rootAwareCandidateForPlan? parameter input plan = some candidate := by
        simpa [plan, publicContext] using hcandidate
      have hstepObservations : step.observations = observations ++ [observation] := by
        have := observations_eq_of_mem_runObservedCleanFromTable_rootAwarePublic parameter input
          publicContext.state plan observations state fuel table cache step hstep
        simpa [observationsAfterCandidate, hcandidateActual, observation] using this
      have htail : some result ∈ support
          (observedMaterializedBoundary parameter publicRoot ftsSecret (next step.value.1)
            step.observations step.state step.remaining table step.value.2) := by
        simpa only [observedMaterializedBoundary] using hrest
      have hprefix := observations_prefix_of_mem_observedMaterializedBoundary parameter publicRoot
        ftsSecret (next step.value.1) step.observations step.state step.remaining table step.value.2
        result htail
      have hbefore : observations.length < ordinal := by
        have hcandidatesLength : candidates.length = observations.length := by
          simp [haligned]
        simpa [appendPlannedCandidate, hcandidatesLength] using hnextLength
      have hstepIndex : observations.length < step.observations.length := by
        simp [hstepObservations]
      have hresultIndex : observations.length < result.observations.length :=
        lt_of_lt_of_le hstepIndex hprefix.length_le
      have hget := hprefix.getElem hstepIndex
      have hobservationEq :
          result.observations.get ⟨observations.length, hresultIndex⟩ = observation := by
        have hstepGet : step.observations[observations.length] = observation := by
          simp [hstepObservations, observation]
        have hget' := hget.symm
        change result.observations[observations.length] = step.observations[observations.length]
          at hget'
        exact hget'.trans hstepGet
      obtain ⟨⟨⟨⟨_finalResult, _hfinish⟩, _hdoomed,
          _selected, _hselected, hfirst, _hroot⟩,
        _hposition⟩, hcomparison⟩ := hgood
      obtain ⟨_firstSelected, _hfirstSelected, _hfirstHit, hnoEarlier⟩ := hfirst
      simp only [RootAwareCandidateAvoidsRoots, not_and_or] at hunsafe
      rcases hunsafe with hleft | hright
      · apply hnoEarlier ⟨observations.length, hresultIndex⟩ hbefore
        change (result.observations.get
          ⟨observations.length, hresultIndex⟩).ExistingHiddenHit
        rw [hobservationEq]
        obtain ⟨output, hvalue, hdigest⟩ := hstored
        have hcand : candidate = ⟨.position target, leftRoot⟩ := by
          exact Option.some.inj (not_ne_iff.mp hleft)
        subst candidate
        refine ⟨by simp [observation, cleanProbeObservation, hhidden], output, ?_, ?_⟩
        · simpa [observation, cleanProbeObservation] using hvalue
        · simpa [observation, cleanProbeObservation] using hdigest
      · apply hcomparison observation.toProbe
        · unfold observedPrefixProbes
          apply List.mem_map.mpr
          refine ⟨observation, ?_, rfl⟩
          apply List.mem_take_iff_getElem.mpr
          refine ⟨observations.length, by omega, ?_⟩
          change result.observations[observations.length] = observation at hobservationEq
          exact hobservationEq
        · have hcand : candidate = ⟨.position target, rightRoot⟩ :=
            Option.some.inj (not_ne_iff.mp hright)
          subst candidate
          simp [observation, CleanProbeObservation.toProbe, cleanProbeObservation]

theorem selected_hash_finish_pair_matches_of_successful_root
    {table : OtsSecretIndex → HashOutput} {ordinal : Nat} {target : Position}
    {rightRoot leftRoot : Digest}
    {parameter : PublicParameter} {publicRoot : Digest}
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    {input : HashInput} {next : HashOutput → OracleComp (OracleWorld + SigningSpec) α}
    {observations : List CleanProbeObservation} {candidates : List Probe}
    {state : LazyRevealProbe.State Coordinate} {fuel : Nat} {cache : SplitHashCache}
    (hnotSelected : ¬ordinal < candidates.length)
    (haligned : candidates = observations.map CleanProbeObservation.toProbe)
    (hstored : StoredLayerRoot state target leftRoot)
    (htracked : CleanProbeObservationsTrackedBy observations state)
    (hnextSelected : ordinal <
      (appendPlannedCandidate candidates
        (rootAwareCandidateForPlan? parameter input
          (purePlanProbingHashQuery parameter input
            (materializedCanonicalContext table state).state))).length)
    {pair : Option (ObservedCleanRunResult (α × SplitHashCache)) ×
      MaterializedSelectionOutcome}
    (hpair : pair ∈ support
      (finishObservedWithSelectionOutcome parameter publicRoot ftsSecret
        (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
          (Sum.inl (Sum.inr input))) >>= next)
        observations state fuel table cache
        (.finished (some
          ((appendPlannedCandidate candidates
            (rootAwareCandidateForPlan? parameter input
              (purePlanProbingHashQuery parameter input
                (materializedCanonicalContext table state).state))).get
              ⟨ordinal, hnextSelected⟩)))))
    (hgood : ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
      table ordinal target rightRoot pair.1) :
    pair.2.Matches target leftRoot := by
  unfold finishObservedWithSelectionOutcome at hpair
  rw [mem_support_bind_iff] at hpair
  obtain ⟨observed, hobserved, hreturn⟩ := hpair
  simp only [support_pure, Set.mem_singleton_iff] at hreturn
  subst pair
  cases observed with
  | none =>
      simp [ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt,
        ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget,
        ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt] at hgood
  | some result =>
      have hobserved' := hobserved
      have hgood' := hgood
      let plan := purePlanProbingHashQuery parameter input
        (materializedCanonicalContext table state).state
      let candidate? := rootAwareCandidateForPlan? parameter input plan
      cases hcandidate : candidate? with
      | none =>
          have hlength : (appendPlannedCandidate candidates candidate?).length =
              candidates.length := by simp [appendPlannedCandidate, hcandidate]
          exact (hnotSelected (by simpa [plan, candidate?, hlength] using hnextSelected)).elim
      | some candidate =>
          have hcandidatesLength : candidates.length = observations.length := by simp [haligned]
          have hordinal : ordinal = observations.length := by
            have hnextLength : ordinal < candidates.length + 1 := by
              simpa [plan, candidate?, hcandidate, appendPlannedCandidate] using hnextSelected
            have holdLength : candidates.length ≤ ordinal := Nat.le_of_not_gt hnotSelected
            omega
          have hselectedCandidate :
              (appendPlannedCandidate candidates candidate?).get
                  ⟨ordinal, by simpa [plan, candidate?] using hnextSelected⟩ = candidate := by
            subst ordinal
            subst candidates
            simp [appendPlannedCandidate, candidate?, hcandidate]
          rw [observedMaterializedBoundary_hash_query_bind, mem_support_bind_iff] at hobserved
          obtain ⟨step?, hstep, hrest⟩ := hobserved
          cases step? with
          | none => simp at hrest
          | some step =>
              let publicContext := materializedCanonicalContext table state
              have hplan : plan = purePlanProbingHashQuery parameter input publicContext.state := rfl
              let observation := cleanProbeObservation state candidate.coordinate candidate.candidate
              have hcandidateActual : rootAwareCandidateForPlan? parameter input plan =
                  some candidate := hcandidate
              have hstepObservations : step.observations = observations ++ [observation] := by
                have := observations_eq_of_mem_runObservedCleanFromTable_rootAwarePublic parameter
                  input publicContext.state plan observations state fuel table cache step hstep
                simpa [observationsAfterCandidate, hcandidateActual, observation] using this
              have htail : some result ∈ support
                  (observedMaterializedBoundary parameter publicRoot ftsSecret (next step.value.1)
                    step.observations step.state step.remaining table step.value.2) := by
                simpa only [observedMaterializedBoundary] using hrest
              have hprefix := observations_prefix_of_mem_observedMaterializedBoundary parameter
                publicRoot ftsSecret (next step.value.1) step.observations step.state step.remaining
                table step.value.2 result htail
              have hstepIndex : observations.length < step.observations.length := by
                simp [hstepObservations]
              have hresultIndex : observations.length < result.observations.length :=
                lt_of_lt_of_le hstepIndex hprefix.length_le
              have hget := hprefix.getElem hstepIndex
              have hobservationEq :
                  result.observations.get ⟨observations.length, hresultIndex⟩ = observation := by
                have hstepGet : step.observations[observations.length] = observation := by
                  simp [hstepObservations, observation]
                have hget' := hget.symm
                change result.observations[observations.length] =
                  step.observations[observations.length] at hget'
                exact hget'.trans hstepGet
              obtain ⟨⟨⟨⟨_finalResult, _hfinish⟩, _hdoomed,
                  selected, hselectedOrdinal, _hfirst, _hroot⟩,
                _hposition⟩, _hcomparison⟩ := hgood
              have hselectedEq : selected = ⟨observations.length, hresultIndex⟩ := by
                exact Fin.ext (hselectedOrdinal.trans hordinal)
              have hcandidateFinal : candidate =
                  (result.observations.get selected).toProbe := by
                rw [hselectedEq, hobservationEq]
                simp [observation, CleanProbeObservation.toProbe, cleanProbeObservation]
              have hstoredFinal : StoredLayerRoot result.state target leftRoot :=
                storedLayerRoot_mono hstored
                  (valuesLE_of_mem_observedMaterializedBoundary parameter publicRoot ftsSecret
                    (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
                      (Sum.inl (Sum.inr input))) >>= next)
                    observations state fuel table cache result hobserved')
              have htrackedFinal :=
                cleanProbeObservationsTrackedBy_of_mem_observedMaterializedBoundary parameter
                  publicRoot ftsSecret
                  (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
                    (Sum.inl (Sum.inr input))) >>= next)
                  observations state fuel table cache htracked result hobserved'
              have houtcomeCandidate :
                  (appendPlannedCandidate candidates
                    (rootAwareCandidateForPlan? parameter input
                      (purePlanProbingHashQuery parameter input
                        (materializedCanonicalContext table state).state))).get
                    ⟨ordinal, hnextSelected⟩ = candidate := by
                simpa [plan, candidate?] using hselectedCandidate
              rw [houtcomeCandidate]
              exact finished_probe_matches_of_successful_root hgood' hselectedOrdinal
                hcandidateFinal hstoredFinal htrackedFinal

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem successful_root_forces_match_of_mem_observedRootSelectionSharedPrefix
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot : Digest)
    (target : Position) (leftRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation) (candidates : List Probe)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (haligned : candidates = observations.map CleanProbeObservation.toProbe)
    (hstored : StoredLayerRoot state target leftRoot)
    (htargetHidden : Coordinate.position target ∉ state.revealed)
    (htracked : CleanProbeObservationsTrackedBy observations state)
    (hcovered : CleanProbeObservationsCoverPending observations state)
    (hstarts : StartTableAgrees state table)
    (hbudget : fuel + state.pending.card < Fintype.card Digest)
    (pair : Option (ObservedCleanRunResult (α × SplitHashCache)) ×
      MaterializedSelectionOutcome)
    (hpair : pair ∈ support
      (observedRootSelectionSharedPrefix ordinal parameter publicRoot target leftRoot rightRoot
        ftsSecret computation observations candidates state fuel table cache))
    (hgood : ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
      table ordinal target rightRoot pair.1) :
    pair.2.Matches target leftRoot := by
  induction computation using OracleComp.inductionOn generalizing
      observations candidates state fuel cache pair with
  | pure value =>
      rw [observedRootSelectionSharedPrefix, OracleComp.construct_pure] at hpair
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte, support_pure, Set.mem_singleton_iff] at hpair
        subst pair
        exact selected_finish_matches_of_successful_root hselected haligned hstored htracked
          (show some
              (⟨state, fuel, (value, cache), table, observations⟩ :
                ObservedCleanRunResult (α × SplitHashCache)) ∈ support
              (observedMaterializedBoundary parameter publicRoot ftsSecret (pure value)
                observations state fuel table cache) by
            rw [observedMaterializedBoundary, OracleComp.construct_pure]
            simp) hgood
      · simp only [hselected, ↓reduceDIte, support_pure, Set.mem_singleton_iff] at hpair
        subst pair
        obtain ⟨⟨⟨⟨_finalResult, _hfinish⟩, _hdoomed,
            selected, hselectedOrdinal, _hfirst, _hroot⟩,
          _hposition⟩, _hcomparison⟩ := hgood
        have hobservationLength : ordinal < observations.length := by
          rw [← hselectedOrdinal]
          exact selected.isLt
        have hcandidatesLength : candidates.length = observations.length := by
          simp [haligned]
        exact (hselected (by omega)).elim
  | query_bind query next ih =>
      rw [observedRootSelectionSharedPrefix_query_bind] at hpair
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte] at hpair
        exact selected_finish_pair_matches_of_successful_root hselected haligned hstored htracked
          hpair hgood
      · simp only [hselected, ↓reduceDIte] at hpair
        have hlength : observations.length ≤ ordinal := by
          have hcandidatesLength : candidates.length = observations.length := by simp [haligned]
          omega
        cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                rw [mem_support_bind_iff] at hpair
                obtain ⟨detailed, hdetailed, hcontinue⟩ := hpair
                cases detailed with
                | stopped reason =>
                    simp [continueObservedRootSelectionSharedPrefix] at hcontinue
                    subst pair
                    simp [ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt,
                      ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget,
                      ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt] at hgood
                | done step =>
                    unfold continueObservedRootSelectionSharedPrefix at hcontinue
                    by_cases hcompletable :
                        DeferredCompletable table (directDeferredContext step.context.state)
                    · simp only [hcompletable, ↓reduceIte] at hcontinue
                      by_cases hrevealed : Coordinate.position target ∈ step.context.state.revealed
                      · simp only [hrevealed, ↓reduceIte] at hcontinue
                        unfold finishObservedWithSelectionOutcome at hcontinue
                        rw [mem_support_bind_iff] at hcontinue
                        obtain ⟨observed, hobserved, hreturn⟩ := hcontinue
                        simp only [support_pure, Set.mem_singleton_iff] at hreturn
                        subst pair
                        cases observed with
                        | none =>
                            simp [ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt,
                              ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget,
                              ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt]
                              at hgood
                        | some result =>
                            exact (successful_root_not_of_revealed_prefix hlength hrevealed
                              hobserved hgood).elim
                      · simp only [hrevealed, ↓reduceIte] at hcontinue
                        let observedStep : ObservedCleanRunResult (Fin (n + 1) × SplitHashCache) :=
                          ⟨step.context.state, step.remaining, step.value, step.table, observations⟩
                        have hobservedStep : some observedStep ∈ support
                            (runObservedCleanFromTable observations state fuel table
                              ((splitUniformImpl n).run cache)) := by
                          have hmapped : some observedStep ∈ support
                              (observedResultOfDetailed observations <$>
                                runDirectResolvedDetailedFromTable (directDeferredContext state)
                                  fuel table ((splitUniformImpl n).run cache)) := by
                            rw [support_map]
                            exact ⟨.done step, hdetailed, rfl⟩
                          rw [map_observedResultOfDetailed_run_eq_observed_of_probeFree
                            ((splitUniformImpl n).run cache) observations state fuel table
                            (splitUniformImpl_probeFree n cache)] at hmapped
                          exact hmapped
                        have hnextTracked :=
                          cleanProbeObservationsTrackedBy_of_mem_runObservedCleanFromTable
                            ((splitUniformImpl n).run cache) observations state fuel table htracked
                            observedStep hobservedStep
                        have hnextCovered :=
                          cleanProbeObservationsCoverPending_of_mem_runObservedCleanFromTable
                            ((splitUniformImpl n).run cache) observations state fuel table hcovered
                            observedStep hobservedStep
                        have hnextStarts := startTableAgrees_of_mem_runObservedCleanFromTable
                          ((splitUniformImpl n).run cache) observations state fuel table hstarts
                          observedStep hobservedStep
                        have hnextStored : StoredLayerRoot step.context.state target leftRoot :=
                          storedLayerRoot_mono hstored
                            (valuesLE_of_done_runDirectResolvedDetailedFromTable
                              ((splitUniformImpl n).run cache) (directDeferredContext state) fuel
                              table step hdetailed)
                        have hnextBudget : step.remaining + step.context.state.pending.card <
                            Fintype.card Digest := by
                          have hstepBound := remaining_add_pending_card_le_of_done_runDirectResolvedDetailedFromTable
                            ((splitUniformImpl n).run cache) (directDeferredContext state) fuel table
                            step hdetailed
                          simp only [directDeferredContext] at hstepBound
                          omega
                        exact ih step.value.1 observations candidates step.context.state
                          step.remaining step.value.2 haligned hnextStored hrevealed hnextTracked
                          hnextCovered hnextStarts.2 hnextBudget pair hcontinue hgood
                    · simp only [hcompletable, ↓reduceIte] at hcontinue
                      unfold finishObservedWithSelectionOutcome at hcontinue
                      rw [mem_support_bind_iff] at hcontinue
                      obtain ⟨observed, hobserved, hreturn⟩ := hcontinue
                      simp only [support_pure, Set.mem_singleton_iff] at hreturn
                      subst pair
                      cases observed with
                      | none =>
                          simp [ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt,
                            ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget,
                            ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt]
                            at hgood
                      | some result =>
                          let observedStep : ObservedCleanRunResult (Fin (n + 1) × SplitHashCache) :=
                            ⟨step.context.state, step.remaining, step.value, step.table, observations⟩
                          have hobservedStep : some observedStep ∈ support
                              (runObservedCleanFromTable observations state fuel table
                                ((splitUniformImpl n).run cache)) := by
                            have hmapped : some observedStep ∈ support
                                (observedResultOfDetailed observations <$>
                                  runDirectResolvedDetailedFromTable (directDeferredContext state)
                                    fuel table ((splitUniformImpl n).run cache)) := by
                              rw [support_map]
                              exact ⟨.done step, hdetailed, rfl⟩
                            rw [map_observedResultOfDetailed_run_eq_observed_of_probeFree
                              ((splitUniformImpl n).run cache) observations state fuel table
                              (splitUniformImpl_probeFree n cache)] at hmapped
                            exact hmapped
                          have hnextTracked :=
                            cleanProbeObservationsTrackedBy_of_mem_runObservedCleanFromTable
                              ((splitUniformImpl n).run cache) observations state fuel table htracked
                              observedStep hobservedStep
                          have hnextCovered :=
                            cleanProbeObservationsCoverPending_of_mem_runObservedCleanFromTable
                              ((splitUniformImpl n).run cache) observations state fuel table hcovered
                              observedStep hobservedStep
                          have hnextStarts := startTableAgrees_of_mem_runObservedCleanFromTable
                            ((splitUniformImpl n).run cache) observations state fuel table hstarts
                            observedStep hobservedStep
                          have hnextBudget : step.remaining + step.context.state.pending.card <
                              Fintype.card Digest := by
                            have hstepBound := remaining_add_pending_card_le_of_done_runDirectResolvedDetailedFromTable
                              ((splitUniformImpl n).run cache) (directDeferredContext state) fuel
                              table step hdetailed
                            simp only [directDeferredContext] at hstepBound
                            omega
                          exact (successful_root_not_of_noncompletable_prefix hlength hnextTracked
                            hnextCovered hnextStarts.2 hnextBudget hcompletable hobserved hgood).elim
            | inr input =>
                let publicContext := materializedCanonicalContext table state
                let plan := purePlanProbingHashQuery parameter input publicContext.state
                let candidate? := rootAwareCandidateForPlan? parameter input plan
                let nextCandidates := appendPlannedCandidate candidates candidate?
                let nextObservations := observationsAfterCandidate observations state candidate?
                by_cases hnextSelected : ordinal < nextCandidates.length
                · have hactual : ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state))).length := by
                    simpa [nextCandidates, candidate?, plan, publicContext] using hnextSelected
                  simp only [hactual, ↓reduceDIte] at hpair
                  exact selected_hash_finish_pair_matches_of_successful_root hselected haligned
                    hstored htracked hactual hpair hgood
                · have hactual : ¬ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state))).length := by
                    simpa [nextCandidates, candidate?, plan, publicContext] using hnextSelected
                  simp only [hactual, ↓reduceDIte] at hpair
                  by_cases hsafe : RootAwareCandidateAvoidsRoots target leftRoot rightRoot candidate?
                  · have hactualSafe : RootAwareCandidateAvoidsRoots target leftRoot rightRoot
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state)) := by
                      simpa [candidate?, plan, publicContext] using hsafe
                    simp only [hactualSafe, ↓reduceIte, mem_support_bind_iff] at hpair
                    obtain ⟨detailed, hdetailed, hcontinue⟩ := hpair
                    cases detailed with
                    | stopped reason =>
                        simp [continueObservedRootSelectionSharedPrefix] at hcontinue
                        subst pair
                        simp [ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt,
                          ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget,
                          ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt]
                          at hgood
                    | done step =>
                        unfold continueObservedRootSelectionSharedPrefix at hcontinue
                        by_cases hcompletable :
                            DeferredCompletable table (directDeferredContext step.context.state)
                        · simp only [hcompletable, ↓reduceIte] at hcontinue
                          by_cases hrevealed :
                              Coordinate.position target ∈ step.context.state.revealed
                          · simp only [hrevealed, ↓reduceIte] at hcontinue
                            unfold finishObservedWithSelectionOutcome at hcontinue
                            rw [mem_support_bind_iff] at hcontinue
                            obtain ⟨observed, hobserved, hreturn⟩ := hcontinue
                            simp only [support_pure, Set.mem_singleton_iff] at hreturn
                            subst pair
                            cases observed with
                            | none =>
                                simp [ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt,
                                  ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget,
                                  ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt]
                                  at hgood
                            | some result =>
                                have hnextLength : nextObservations.length ≤ ordinal := by
                                  cases hcandidate : candidate? with
                                  | none =>
                                      simpa [nextObservations, nextCandidates, observationsAfterCandidate,
                                        appendPlannedCandidate, hcandidate, haligned] using
                                        Nat.le_of_not_gt hnextSelected
                                  | some candidate =>
                                      simpa [nextObservations, nextCandidates, observationsAfterCandidate,
                                        appendPlannedCandidate, hcandidate, haligned] using
                                        Nat.le_of_not_gt hnextSelected
                                exact (successful_root_not_of_revealed_prefix hnextLength hrevealed
                                  hobserved hgood).elim
                          · simp only [hrevealed, ↓reduceIte] at hcontinue
                            let observedStep : ObservedCleanRunResult (HashOutput × SplitHashCache) :=
                              ⟨step.context.state, step.remaining, step.value, step.table,
                                nextObservations⟩
                            have hobservedStep : some observedStep ∈ support
                                (runObservedCleanFromTable observations state fuel table
                                  ((probingHashQueryAfterRootAwarePublicPlan parameter input
                                    publicContext.state plan).run cache)) := by
                              have hmapped : some observedStep ∈ support
                                  (projectDirectDetailedObserved nextObservations <$>
                                    runDirectResolvedDetailedFromTable (directDeferredContext state)
                                      fuel table
                                      ((probingHashQueryAfterRootAwarePublicPlan parameter input
                                        publicContext.state plan).run cache)) := by
                                rw [support_map]
                                exact ⟨.done step, hdetailed, rfl⟩
                              rw [map_projectDirectDetailedObserved_rootAwarePublic parameter input
                                publicContext.state plan observations state fuel table cache]
                                at hmapped
                              exact hmapped
                            have hnextAligned : nextCandidates =
                                nextObservations.map CleanProbeObservation.toProbe := by
                              cases hcandidate : candidate? with
                              | none =>
                                  simp [nextCandidates, nextObservations, appendPlannedCandidate,
                                    observationsAfterCandidate, hcandidate, haligned]
                              | some candidate =>
                                  simp [nextCandidates, nextObservations, appendPlannedCandidate,
                                    observationsAfterCandidate, hcandidate, haligned,
                                    CleanProbeObservation.toProbe, cleanProbeObservation]
                            have hnextTracked :=
                              cleanProbeObservationsTrackedBy_of_mem_runObservedCleanFromTable
                                ((probingHashQueryAfterRootAwarePublicPlan parameter input
                                  publicContext.state plan).run cache)
                                observations state fuel table htracked observedStep hobservedStep
                            have hnextCovered :=
                              cleanProbeObservationsCoverPending_of_mem_runObservedCleanFromTable
                                ((probingHashQueryAfterRootAwarePublicPlan parameter input
                                  publicContext.state plan).run cache)
                                observations state fuel table hcovered observedStep hobservedStep
                            have hnextStarts := startTableAgrees_of_mem_runObservedCleanFromTable
                              ((probingHashQueryAfterRootAwarePublicPlan parameter input
                                publicContext.state plan).run cache)
                              observations state fuel table hstarts observedStep hobservedStep
                            have hnextStored : StoredLayerRoot step.context.state target leftRoot :=
                              storedLayerRoot_mono hstored
                                (valuesLE_of_done_runDirectResolvedDetailedFromTable
                                  ((probingHashQueryAfterRootAwarePublicPlan parameter input
                                    publicContext.state plan).run cache)
                                  (directDeferredContext state) fuel table step hdetailed)
                            have hnextBudget : step.remaining + step.context.state.pending.card <
                                Fintype.card Digest := by
                              have hstepBound :=
                                remaining_add_pending_card_le_of_done_runDirectResolvedDetailedFromTable
                                  ((probingHashQueryAfterRootAwarePublicPlan parameter input
                                    publicContext.state plan).run cache)
                                  (directDeferredContext state) fuel table step hdetailed
                              simp only [directDeferredContext] at hstepBound
                              omega
                            exact ih step.value.1 nextObservations nextCandidates step.context.state
                              step.remaining step.value.2 hnextAligned hnextStored hrevealed
                              hnextTracked hnextCovered hnextStarts.2 hnextBudget pair hcontinue hgood
                        · simp only [hcompletable, ↓reduceIte] at hcontinue
                          unfold finishObservedWithSelectionOutcome at hcontinue
                          rw [mem_support_bind_iff] at hcontinue
                          obtain ⟨observed, hobserved, hreturn⟩ := hcontinue
                          simp only [support_pure, Set.mem_singleton_iff] at hreturn
                          subst pair
                          cases observed with
                          | none =>
                              simp [ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt,
                                ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget,
                                ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt]
                                at hgood
                          | some result =>
                              let observedStep : ObservedCleanRunResult (HashOutput × SplitHashCache) :=
                                ⟨step.context.state, step.remaining, step.value, step.table,
                                  nextObservations⟩
                              have hobservedStep : some observedStep ∈ support
                                  (runObservedCleanFromTable observations state fuel table
                                    ((probingHashQueryAfterRootAwarePublicPlan parameter input
                                      publicContext.state plan).run cache)) := by
                                have hmapped : some observedStep ∈ support
                                    (projectDirectDetailedObserved nextObservations <$>
                                      runDirectResolvedDetailedFromTable
                                        (directDeferredContext state) fuel table
                                        ((probingHashQueryAfterRootAwarePublicPlan parameter input
                                          publicContext.state plan).run cache)) := by
                                  rw [support_map]
                                  exact ⟨.done step, hdetailed, rfl⟩
                                rw [map_projectDirectDetailedObserved_rootAwarePublic parameter input
                                  publicContext.state plan observations state fuel table cache]
                                  at hmapped
                                exact hmapped
                              have hnextTracked :=
                                cleanProbeObservationsTrackedBy_of_mem_runObservedCleanFromTable
                                  ((probingHashQueryAfterRootAwarePublicPlan parameter input
                                    publicContext.state plan).run cache)
                                  observations state fuel table htracked observedStep hobservedStep
                              have hnextCovered :=
                                cleanProbeObservationsCoverPending_of_mem_runObservedCleanFromTable
                                  ((probingHashQueryAfterRootAwarePublicPlan parameter input
                                    publicContext.state plan).run cache)
                                  observations state fuel table hcovered observedStep hobservedStep
                              have hnextStarts := startTableAgrees_of_mem_runObservedCleanFromTable
                                ((probingHashQueryAfterRootAwarePublicPlan parameter input
                                  publicContext.state plan).run cache)
                                observations state fuel table hstarts observedStep hobservedStep
                              have hnextLength : nextObservations.length ≤ ordinal := by
                                cases hcandidate : candidate? with
                                | none =>
                                    simpa [nextObservations, nextCandidates,
                                      observationsAfterCandidate, appendPlannedCandidate,
                                      hcandidate, haligned] using Nat.le_of_not_gt hnextSelected
                                | some candidate =>
                                    simpa [nextObservations, nextCandidates,
                                      observationsAfterCandidate, appendPlannedCandidate,
                                      hcandidate, haligned] using Nat.le_of_not_gt hnextSelected
                              have hnextBudget : step.remaining + step.context.state.pending.card <
                                  Fintype.card Digest := by
                                have hstepBound :=
                                  remaining_add_pending_card_le_of_done_runDirectResolvedDetailedFromTable
                                    ((probingHashQueryAfterRootAwarePublicPlan parameter input
                                      publicContext.state plan).run cache)
                                    (directDeferredContext state) fuel table step hdetailed
                                simp only [directDeferredContext] at hstepBound
                                omega
                              exact (successful_root_not_of_noncompletable_prefix hnextLength
                                hnextTracked hnextCovered hnextStarts.2 hnextBudget hcompletable
                                hobserved hgood).elim
                  · have hactualSafe : ¬RootAwareCandidateAvoidsRoots target leftRoot rightRoot
                        (rootAwareCandidateForPlan? parameter input
                          (purePlanProbingHashQuery parameter input
                            (materializedCanonicalContext table state).state)) := by
                      simpa [candidate?, plan, publicContext] using hsafe
                    simp only [hactualSafe, ↓reduceIte] at hpair
                    unfold finishObservedWithSelectionOutcome at hpair
                    rw [mem_support_bind_iff] at hpair
                    obtain ⟨observed, hobserved, hreturn⟩ := hpair
                    simp only [support_pure, Set.mem_singleton_iff] at hreturn
                    subst pair
                    cases observed with
                    | none =>
                        simp [ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt,
                          ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget,
                          ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt]
                          at hgood
                    | some result =>
                        cases hcandidate : candidate? with
                        | none =>
                            simp [RootAwareCandidateAvoidsRoots, hcandidate] at hsafe
                        | some candidate =>
                            have hcandActual : rootAwareCandidateForPlan? parameter input
                                (purePlanProbingHashQuery parameter input
                                  (materializedCanonicalContext table state).state) =
                                some candidate := by
                              simpa [candidate?, plan, publicContext] using hcandidate
                            have hnextLength :
                                (appendPlannedCandidate candidates (some candidate)).length ≤
                                  ordinal := by
                              simpa [nextCandidates, candidate?, hcandidate] using
                                Nat.le_of_not_gt hnextSelected
                            exact (successful_root_not_of_unsafe_hash_prefix haligned hnextLength
                              htargetHidden hstored hcandActual (by
                                simpa [candidate?, hcandidate] using hsafe) hobserved hgood).elim
        | inr message =>
            rw [mem_support_bind_iff] at hpair
            obtain ⟨detailed, hdetailed, hcontinue⟩ := hpair
            cases detailed with
            | stopped reason =>
                simp [continueObservedRootSelectionSharedPrefix] at hcontinue
                subst pair
                simp [ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt,
                  ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget,
                  ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt] at hgood
            | done step =>
                unfold continueObservedRootSelectionSharedPrefix at hcontinue
                by_cases hcompletable :
                    DeferredCompletable table (directDeferredContext step.context.state)
                · simp only [hcompletable, ↓reduceIte] at hcontinue
                  by_cases hrevealed : Coordinate.position target ∈ step.context.state.revealed
                  · simp only [hrevealed, ↓reduceIte] at hcontinue
                    unfold finishObservedWithSelectionOutcome at hcontinue
                    rw [mem_support_bind_iff] at hcontinue
                    obtain ⟨observed, hobserved, hreturn⟩ := hcontinue
                    simp only [support_pure, Set.mem_singleton_iff] at hreturn
                    subst pair
                    cases observed with
                    | none =>
                        simp [ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt,
                          ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget,
                          ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt]
                          at hgood
                    | some result =>
                        exact (successful_root_not_of_revealed_prefix hlength hrevealed hobserved
                          hgood).elim
                  · simp only [hrevealed, ↓reduceIte] at hcontinue
                    let observedStep :
                        ObservedCleanRunResult (Option Signature × SplitHashCache) :=
                      ⟨step.context.state, step.remaining, step.value, step.table, observations⟩
                    have hobservedStep : some observedStep ∈ support
                        (runObservedCleanFromTable observations state fuel table
                          ((maskedSign parameter publicRoot ftsSecret message).run cache)) := by
                      have hmapped : some observedStep ∈ support
                          (observedResultOfDetailed observations <$>
                            runDirectResolvedDetailedFromTable (directDeferredContext state) fuel
                              table ((maskedSign parameter publicRoot ftsSecret message).run
                                cache)) := by
                        rw [support_map]
                        exact ⟨.done step, hdetailed, rfl⟩
                      rw [map_observedResultOfDetailed_run_eq_observed_of_probeFree
                        ((maskedSign parameter publicRoot ftsSecret message).run cache)
                        observations state fuel table
                        (maskedSign_probeFree parameter publicRoot ftsSecret message cache)]
                        at hmapped
                      exact hmapped
                    have hnextTracked :=
                      cleanProbeObservationsTrackedBy_of_mem_runObservedCleanFromTable
                        ((maskedSign parameter publicRoot ftsSecret message).run cache)
                        observations state fuel table htracked observedStep hobservedStep
                    have hnextCovered :=
                      cleanProbeObservationsCoverPending_of_mem_runObservedCleanFromTable
                        ((maskedSign parameter publicRoot ftsSecret message).run cache)
                        observations state fuel table hcovered observedStep hobservedStep
                    have hnextStarts := startTableAgrees_of_mem_runObservedCleanFromTable
                      ((maskedSign parameter publicRoot ftsSecret message).run cache)
                      observations state fuel table hstarts observedStep hobservedStep
                    have hnextStored : StoredLayerRoot step.context.state target leftRoot :=
                      storedLayerRoot_mono hstored
                        (valuesLE_of_done_runDirectResolvedDetailedFromTable
                          ((maskedSign parameter publicRoot ftsSecret message).run cache)
                          (directDeferredContext state) fuel table step hdetailed)
                    have hnextBudget : step.remaining + step.context.state.pending.card <
                        Fintype.card Digest := by
                      have hstepBound :=
                        remaining_add_pending_card_le_of_done_runDirectResolvedDetailedFromTable
                          ((maskedSign parameter publicRoot ftsSecret message).run cache)
                          (directDeferredContext state) fuel table step hdetailed
                      simp only [directDeferredContext] at hstepBound
                      omega
                    exact ih step.value.1 observations candidates step.context.state
                      step.remaining step.value.2 haligned hnextStored hrevealed hnextTracked
                      hnextCovered hnextStarts.2 hnextBudget pair hcontinue hgood
                · simp only [hcompletable, ↓reduceIte] at hcontinue
                  unfold finishObservedWithSelectionOutcome at hcontinue
                  rw [mem_support_bind_iff] at hcontinue
                  obtain ⟨observed, hobserved, hreturn⟩ := hcontinue
                  simp only [support_pure, Set.mem_singleton_iff] at hreturn
                  subst pair
                  cases observed with
                  | none =>
                      simp [ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt,
                        ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget,
                        ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt]
                        at hgood
                  | some result =>
                      let observedStep :
                          ObservedCleanRunResult (Option Signature × SplitHashCache) :=
                        ⟨step.context.state, step.remaining, step.value, step.table, observations⟩
                      have hobservedStep : some observedStep ∈ support
                          (runObservedCleanFromTable observations state fuel table
                            ((maskedSign parameter publicRoot ftsSecret message).run cache)) := by
                        have hmapped : some observedStep ∈ support
                            (observedResultOfDetailed observations <$>
                              runDirectResolvedDetailedFromTable (directDeferredContext state) fuel
                                table ((maskedSign parameter publicRoot ftsSecret message).run
                                  cache)) := by
                          rw [support_map]
                          exact ⟨.done step, hdetailed, rfl⟩
                        rw [map_observedResultOfDetailed_run_eq_observed_of_probeFree
                          ((maskedSign parameter publicRoot ftsSecret message).run cache)
                          observations state fuel table
                          (maskedSign_probeFree parameter publicRoot ftsSecret message cache)]
                          at hmapped
                        exact hmapped
                      have hnextTracked :=
                        cleanProbeObservationsTrackedBy_of_mem_runObservedCleanFromTable
                          ((maskedSign parameter publicRoot ftsSecret message).run cache)
                          observations state fuel table htracked observedStep hobservedStep
                      have hnextCovered :=
                        cleanProbeObservationsCoverPending_of_mem_runObservedCleanFromTable
                          ((maskedSign parameter publicRoot ftsSecret message).run cache)
                          observations state fuel table hcovered observedStep hobservedStep
                      have hnextStarts := startTableAgrees_of_mem_runObservedCleanFromTable
                        ((maskedSign parameter publicRoot ftsSecret message).run cache)
                        observations state fuel table hstarts observedStep hobservedStep
                      have hnextBudget : step.remaining + step.context.state.pending.card <
                          Fintype.card Digest := by
                        have hstepBound :=
                          remaining_add_pending_card_le_of_done_runDirectResolvedDetailedFromTable
                            ((maskedSign parameter publicRoot ftsSecret message).run cache)
                            (directDeferredContext state) fuel table step hdetailed
                        simp only [directDeferredContext] at hstepBound
                        omega
                      exact (successful_root_not_of_noncompletable_prefix hlength hnextTracked
                        hnextCovered hnextStarts.2 hnextBudget hcompletable hobserved hgood).elim

theorem successful_root_forces_match_after_installed_root
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache))
    (high : RootOutputHigh) (leftRoot rightRoot : Digest)
    (habsent : rootResult.state.values (.position target) = none ∧
      Coordinate.position target ∉ rootResult.state.revealed)
    (hpending : rootResult.state.pending = ∅)
    (hstarts : StartTableAgrees rootResult.state rootResult.table)
    (hbudget : rootResult.remaining < Fintype.card Digest)
    (pair : Option (ObservedCleanRunResult (RetainedRestResult × SplitHashCache)) ×
      MaterializedSelectionOutcome)
    (hpair : pair ∈ support
      (observedRootSelectionSharedPrefix ordinal parameter rootResult.value.1 target leftRoot
        rightRoot ftsSecret
        (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) [] []
        (materializedDeferredState
          { directDeferredContext rootResult.state with
            values := (directDeferredContext rootResult.state).values.install target
              (rootOutputOfParts leftRoot high) })
        rootResult.remaining rootResult.table
        (rootInstalledCache target (fun root => rootOutputOfParts root high)
          rootResult.value.2 leftRoot)))
    (hgood : ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
      rootResult.table ordinal target rightRoot
      (retainObservedRoot rootResult.value.1 pair.1)) :
    pair.2.Matches target leftRoot := by
  let context : DeferredContext := directDeferredContext rootResult.state
  let rootContext :=
    { context with values := context.values.install target (rootOutputOfParts leftRoot high) }
  let initialState := materializedDeferredState rootContext
  have hstored : StoredLayerRoot initialState target leftRoot := by
    refine ⟨rootOutputOfParts leftRoot high, ?_, truncateHash_rootOutputOfParts leftRoot high⟩
    simp only [initialState, materializedDeferredState_position]
    unfold DeferredContext.positionValue
    rw [show rootContext.state.values (.position target) = none by
      simpa [rootContext, context, directDeferredContext] using habsent.1]
    simp [rootContext, context, directDeferredContext, DeferredStructuralValues.install]
  have hhidden : Coordinate.position target ∉ initialState.revealed := by
    change Coordinate.position target ∉ rootResult.state.revealed
    exact habsent.2
  have htracked : CleanProbeObservationsTrackedBy [] initialState := by
    simp [CleanProbeObservationsTrackedBy]
  have hcovered : CleanProbeObservationsCoverPending [] initialState := by
    intro entry hentry
    have : entry ∈ rootResult.state.pending := by
      simpa [initialState, rootContext, context, directDeferredContext] using hentry
    rw [hpending] at this
    simp at this
  have hstartsInitial : StartTableAgrees initialState rootResult.table := by
    intro index output hvalue
    apply hstarts index output
    simpa [initialState, rootContext, context, directDeferredContext,
      OtsSecretIndex.coordinate] using hvalue
  have hbudgetInitial : rootResult.remaining + initialState.pending.card <
      Fintype.card Digest := by
    simpa [initialState, rootContext, context, directDeferredContext, hpending] using hbudget
  have hgoodPair : ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
      rootResult.table ordinal target rightRoot pair.1 := by
    cases hpairFirst : pair.1 with
    | none =>
        rw [hpairFirst] at hgood
        simp [retainObservedRoot,
          ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt,
          ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget,
          ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt] at hgood
    | some result =>
        rw [hpairFirst] at hgood
        simp only [retainObservedRoot] at hgood
        rcases hgood with ⟨⟨⟨hfinish, hdoomed, hfirst⟩, hposition⟩, havoid⟩
        refine ⟨⟨⟨?_, hdoomed, ?_⟩, ?_⟩, ?_⟩
        · obtain ⟨finalResult, hfinalResult⟩ := hfinish
          unfold finishObservedCleanRunFromTable at hfinalResult
          rw [mem_support_bind_iff] at hfinalResult
          obtain ⟨finalized, hfinalized, hreturn⟩ := hfinalResult
          cases finalized with
          | none => simp at hreturn
          | some finalized =>
              obtain ⟨finalState, finalTable⟩ := finalized
              refine ⟨⟨finalState, result.remaining, result.value, finalTable,
                result.observations⟩, ?_⟩
              unfold finishObservedCleanRunFromTable
              rw [mem_support_bind_iff]
              exact ⟨some (finalState, finalTable), hfinalized, by simp⟩
        · simpa [ObservedCleanRunOption.FirstExistingHiddenRootHitAt, FirstExistingHiddenHitAt,
            ExistingHiddenHitAtOrdinal] using hfirst
        · simpa [observedFirstLayerRootPosition?] using hposition
        · simpa [observedPrefixProbes] using havoid
  exact successful_root_forces_match_of_mem_observedRootSelectionSharedPrefix ordinal parameter
    rootResult.value.1 target leftRoot rightRoot ftsSecret
    (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) [] [] initialState
    rootResult.remaining rootResult.table
    (rootInstalledCache target (fun root => rootOutputOfParts root high) rootResult.value.2 leftRoot)
    rfl hstored hhidden htracked hcovered hstartsInitial hbudgetInitial pair (by
      simpa [initialState, rootContext, context] using hpair) hgoodPair

theorem map_observed_sampledHighObservedRootAwareSharedAfterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache)) :
    (fun result => (result.1, result.2.1, result.2.2.1)) <$>
        sampledHighObservedRootAwareSharedAfterRootResult ordinal adversary parameter
          ftsSecret target rootResult =
      sampledHighEagerObservedRootAwareAfterRootResult ordinal adversary parameter
        ftsSecret target rootResult := by
  unfold sampledHighObservedRootAwareSharedAfterRootResult
    sampledHighEagerObservedRootAwareAfterRootResult
  simp only [map_eq_bind_pure_comp, bind_assoc]
  apply bind_congr
  intro high
  apply bind_congr
  intro leftRoot
  apply bind_congr
  intro rightRoot
  let state := materializedDeferredState
    { directDeferredContext rootResult.state with
      values := (directDeferredContext rootResult.state).values.install target
        (rootOutputOfParts leftRoot high) }
  let cache := rootInstalledCache target (fun root => rootOutputOfParts root high)
    rootResult.value.2 leftRoot
  simp only [pure_bind, Function.comp_apply]
  calc
    _ = (fun observed => (leftRoot, rightRoot,
          retainObservedRoot rootResult.value.1 observed)) <$>
        (Prod.fst <$> observedRootSelectionSharedPrefix ordinal parameter rootResult.value.1
          target leftRoot rightRoot ftsSecret
          (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) [] []
          state rootResult.remaining rootResult.table cache) := by
      rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp, bind_assoc]
      rfl
    _ = _ := by
      rw [map_fst_observedRootSelectionSharedPrefix]
      rfl

theorem evalDist_map_outcome_sampledHighObservedRootAwareSharedAfterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache)) :
    evalDist ((fun result => (result.1, result.2.1, result.2.2.2)) <$>
        sampledHighObservedRootAwareSharedAfterRootResult ordinal adversary parameter
          ftsSecret target rootResult) =
      evalDist
        (sampledHighMaterializedRootAwareOutcomeAfterRootResult ordinal adversary parameter
          ftsSecret target rootResult) := by
  unfold sampledHighObservedRootAwareSharedAfterRootResult
    sampledHighMaterializedRootAwareOutcomeAfterRootResult
  simp only [map_eq_bind_pure_comp, bind_assoc]
  apply evalDist_bind_congr
  intro high _hhigh
  apply evalDist_bind_congr
  intro leftRoot _hleftRoot
  apply evalDist_bind_congr
  intro rightRoot _hrightRoot
  let state := materializedDeferredState
    { directDeferredContext rootResult.state with
      values := (directDeferredContext rootResult.state).values.install target
        (rootOutputOfParts leftRoot high) }
  let cache := rootInstalledCache target (fun root => rootOutputOfParts root high)
    rootResult.value.2 leftRoot
  calc
    _ = evalDist ((fun outcome => (leftRoot, rightRoot, outcome)) <$>
          (Prod.snd <$> observedRootSelectionSharedPrefix ordinal parameter rootResult.value.1
            target leftRoot rightRoot ftsSecret
            (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) [] []
            state rootResult.remaining rootResult.table cache)) := by
      rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp, bind_assoc]
      rfl
    _ = evalDist ((fun outcome => (leftRoot, rightRoot, outcome)) <$>
          materializedActualRootAwareOrdinalSelectionOutcome ordinal parameter rootResult.value.1
            target leftRoot rightRoot ftsSecret
            (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) [] state
            rootResult.remaining rootResult.table cache) := by
      have hmarginal := evalDist_map_snd_observedRootSelectionSharedPrefix ordinal parameter
        rootResult.value.1 target leftRoot rightRoot ftsSecret
        (retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩) [] [] state
        rootResult.remaining rootResult.table cache
      simpa only [evalDist_map, Functor.map_map] using
        congrArg (Functor.map fun outcome => (leftRoot, rightRoot, outcome)) hmarginal
    _ = _ := rfl

theorem relTriple_sampledHighEagerObservedRootComparison_materializedRootAwareOutcome
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache))
    (habsent : rootResult.state.values (.position target) = none ∧
      Coordinate.position target ∉ rootResult.state.revealed)
    (hpending : rootResult.state.pending = ∅)
    (hstarts : StartTableAgrees rootResult.state rootResult.table)
    (hbudget : rootResult.remaining < Fintype.card Digest) :
    RelTriple
      ((fun result => (result.2.2, result.2.1)) <$>
        sampledHighEagerObservedRootAwareAfterRootResult ordinal adversary parameter
          ftsSecret target rootResult)
      (sampledHighMaterializedRootAwareOutcomeAfterRootResult ordinal adversary parameter
        ftsSecret target rootResult)
      (SuccessfulObservedRootMaterializedMatchRel rootResult.table ordinal target) := by
  let shared := sampledHighObservedRootAwareSharedAfterRootResult ordinal adversary parameter
    ftsSecret target rootResult
  have hbase :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support
      (relTriple_refl shared) (fun result => result ∈ support shared)
      (fun result hresult => hresult)
  have hsemantic : RelTriple shared shared
      (fun left right =>
        SuccessfulObservedRootMaterializedMatchRel rootResult.table ordinal target
          (left.2.2.1, left.2.1) (right.1, right.2.1, right.2.2.2)) := by
    apply relTriple_post_mono hbase
    intro left right hrelation
    obtain ⟨heq, hleft⟩ := hrelation
    subst right
    intro hgood
    unfold shared sampledHighObservedRootAwareSharedAfterRootResult at hleft
    rw [mem_support_bind_iff] at hleft
    obtain ⟨high, _hhigh, hleft⟩ := hleft
    rw [mem_support_bind_iff] at hleft
    obtain ⟨leftRoot, _hleftRoot, hleft⟩ := hleft
    rw [mem_support_bind_iff] at hleft
    obtain ⟨rightRoot, _hrightRoot, hleft⟩ := hleft
    rw [mem_support_bind_iff] at hleft
    obtain ⟨pair, hpair, hreturn⟩ := hleft
    simp only [support_pure, Set.mem_singleton_iff] at hreturn
    subst left
    exact successful_root_forces_match_after_installed_root ordinal adversary parameter ftsSecret
      target rootResult high leftRoot rightRoot habsent hpending hstarts hbudget pair hpair hgood
  have hmapped := relTriple_map
    (f := fun result : Digest × Digest ×
        Option (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) ×
          MaterializedSelectionOutcome => (result.2.2.1, result.2.1))
    (g := fun result : Digest × Digest ×
        Option (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) ×
          MaterializedSelectionOutcome => (result.1, result.2.1, result.2.2.2)) hsemantic
  have hleft : evalDist
      ((fun result => (result.2.2.1, result.2.1)) <$> shared) =
      evalDist ((fun result => (result.2.2, result.2.1)) <$>
        sampledHighEagerObservedRootAwareAfterRootResult ordinal adversary parameter
          ftsSecret target rootResult) := by
    rw [← map_observed_sampledHighObservedRootAwareSharedAfterRootResult ordinal adversary
      parameter ftsSecret target rootResult]
    simp only [Functor.map_map]
    rfl
  apply relTriple_of_evalDist_eq_left hleft.symm
  apply relTriple_of_evalDist_eq_right
    (evalDist_map_outcome_sampledHighObservedRootAwareSharedAfterRootResult ordinal adversary
      parameter ftsSecret target rootResult)
  exact hmapped

noncomputable def eagerObservedRootComparisonExperimentAfterTable
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    ProbComp
      (Option (ObservedCleanRunResult (RetainedGameResult × SplitHashCache)) × Digest) := do
  let rootResult ← runCleanFromTable
    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel table
    (maskedPublishedTreeRoot.run emptySplitHashCache)
  match rootResult with
  | none => pure (none, 0)
  | some result =>
      (fun sampled => (sampled.2.2, sampled.2.1)) <$>
        sampledHighEagerObservedRootAwareAfterRootResult ordinal adversary parameter
          ftsSecret target result

def RootResultReadyForSharedSemantic
    (target : Position) (table : OtsSecretIndex → HashOutput) :
    Option (CleanRunResult (Digest × SplitHashCache)) → Prop
  | none => True
  | some result =>
      result.state.values (.position target) = none ∧
        Coordinate.position target ∉ result.state.revealed ∧
        result.state.pending = ∅ ∧ result.table = table ∧
        StartTableAgrees result.state table ∧
        result.remaining < Fintype.card Digest

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem rootResultReadyForSharedSemantic_of_mem
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hfuel : fuel < Fintype.card Digest)
    (output : Option (CleanRunResult (Digest × SplitHashCache)))
    (houtput : output ∈ support
      (runCleanFromTable (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
        fuel table (maskedPublishedTreeRoot.run emptySplitHashCache))) :
    RootResultReadyForSharedSemantic target table output := by
  cases output with
  | none => trivial
  | some result =>
      have habsent : result.state.values (.position target) = none ∧
          Coordinate.position target ∉ result.state.revealed :=
        target_absent_of_mem_runCleanFromTable_maskedPublishedTreeRoot target hroot hparent fuel
          table result houtput
      have hpending : result.state.pending = ∅ :=
        pending_eq_empty_of_mem_runCleanFromTable_maskedPublishedTreeRoot fuel table result houtput
      have htable : result.table = table ∧ StartTableAgrees result.state table :=
        startTableAgrees_of_mem_runCleanFromTable
        (maskedPublishedTreeRoot.run emptySplitHashCache)
        (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel table
        (startTableAgrees_empty table) result houtput
      have hobserved : some
          (⟨result.state, result.remaining, result.value, result.table, []⟩ :
            ObservedCleanRunResult (Digest × SplitHashCache)) ∈ support
          (runObservedCleanFromTable [] LazyRevealProbe.State.empty fuel table
            (maskedPublishedTreeRoot.run emptySplitHashCache)) := by
        rw [← map_attachCleanProbeObservations_runCleanFromTable_of_probeFree
          (maskedPublishedTreeRoot.run emptySplitHashCache) [] LazyRevealProbe.State.empty fuel
          table (maskedPublishedTreeRoot_probeFree emptySplitHashCache), support_map]
        exact ⟨some result, houtput, rfl⟩
      have hremaining : result.remaining ≤ fuel :=
        remaining_le_of_mem_runObservedCleanFromTable
          (maskedPublishedTreeRoot.run emptySplitHashCache) [] LazyRevealProbe.State.empty fuel
          table ⟨result.state, result.remaining, result.value, result.table, []⟩ hobserved
      exact ⟨habsent.1, habsent.2, hpending, htable.1, htable.2,
        hremaining.trans_lt hfuel⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem relTriple_eagerObservedRootComparison_materializedRootAwareOutcomeAfterTable
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hfuel : fuel < Fintype.card Digest) :
    RelTriple
      (eagerObservedRootComparisonExperimentAfterTable ordinal adversary parameter ftsSecret
        target fuel table)
      (materializedRootAwareOrdinalOutcomeExperimentAfterTable ordinal adversary parameter
        ftsSecret target fuel table)
      (SuccessfulObservedRootMaterializedMatchRel table ordinal target) := by
  let rootRun := runCleanFromTable
    (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel table
    (maskedPublishedTreeRoot.run emptySplitHashCache)
  have hbase :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support
      (relTriple_refl rootRun) (RootResultReadyForSharedSemantic target table)
      (rootResultReadyForSharedSemantic_of_mem target hroot hparent fuel table hfuel)
  unfold eagerObservedRootComparisonExperimentAfterTable
    materializedRootAwareOrdinalOutcomeExperimentAfterTable
  apply relTriple_bind hbase
  intro leftResult rightResult hrelation
  obtain ⟨heq, hready⟩ := hrelation
  subst rightResult
  cases leftResult with
  | none =>
      apply relTriple_pure_pure
      intro hgood
      simp [ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt,
        ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget,
        ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt] at hgood
  | some result =>
      obtain ⟨hvalue, hrevealed, hpending, htable, hstarts, hbudget⟩ := hready
      have hstartsResult : StartTableAgrees result.state result.table := by
        rw [htable]
        exact hstarts
      rw [← htable]
      exact relTriple_sampledHighEagerObservedRootComparison_materializedRootAwareOutcome ordinal
        adversary parameter ftsSecret target result ⟨hvalue, hrevealed⟩ hpending hstartsResult
        hbudget

theorem probEvent_eagerObservedRootComparison_le_production_mul
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (hfuel : fuel < Fintype.card Digest) :
    Pr[fun result =>
        ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
          table ordinal target result.2 result.1 |
      eagerObservedRootComparisonExperimentAfterTable ordinal adversary parameter ftsSecret
        target fuel table] ≤
      Pr[fun result => materializedOrdinalSelectionAt target result.2 |
          materializedRootAwareOrdinalProductionExperimentAfterTable ordinal adversary parameter
            ftsSecret target fuel table] *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  calc
    _ ≤ Pr[fun result => result.2.2.Matches target result.1 |
          materializedRootAwareOrdinalOutcomeExperimentAfterTable ordinal adversary parameter
            ftsSecret target fuel table] := by
      apply probEvent_le_of_relTriple
        (relTriple_eagerObservedRootComparison_materializedRootAwareOutcomeAfterTable ordinal
          adversary parameter ftsSecret target hroot hparent fuel table hfuel)
      intro observed outcome hrelation hgood
      exact hrelation hgood
    _ ≤ _ := probEvent_materializedRootAwareOrdinalOutcome_match_le ordinal adversary parameter
      ftsSecret target hroot hparent fuel table

end SphincsSecurity.Concrete.OtsProbeSimulation
