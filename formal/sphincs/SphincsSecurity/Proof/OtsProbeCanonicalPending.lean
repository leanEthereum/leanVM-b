import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeCanonicalFuel
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivatePreparationLift
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootProbe

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local irreducible] maskedPublishedTreeRoot
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
theorem pendingCoveredBy_of_mem_runResolvedFromTable
    (candidates : List Probe)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult α)
    (hcovered : PendingCoveredBy candidates context)
    (hbound : computation.IsQueryBoundP (IsUncoveredProbe candidates) 0)
    (hresult : some result ∈ support
      (runResolvedFromTable context fuel table computation)) :
    PendingCoveredBy candidates result.context := by
  induction computation using OracleComp.inductionOn generalizing context fuel with
  | pure value =>
      simp [runResolvedFromTable] at hresult
      subst result
      exact hcovered
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      cases input with
      | uniform n =>
          rw [runResolvedFromTable_uniform_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, htail⟩ := hresult
          exact ih output context fuel hcovered (hbound.2 output) htail
      | hashOutput =>
          rw [runResolvedFromTable_hashOutput_query_bind,
            mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, htail⟩ := hresult
          exact ih output context fuel hcovered (hbound.2 output) htail
      | ensure coordinate =>
          rw [runResolvedFromTable_ensure_query_bind] at hresult
          exact ih () { context with state := context.state.ensure coordinate } fuel hcovered
            (hbound.2 ()) hresult
      | probe coordinate digest =>
          have hmem : (⟨coordinate, digest⟩ : Probe) ∈ candidates := by
            simpa [IsUncoveredProbe] using hbound.1
          have htail : (next ()).IsQueryBoundP (IsUncoveredProbe candidates) 0 := by
            simpa [IsUncoveredProbe] using hbound.2 ()
          cases fuel with
          | zero => simp [runResolvedFromTable_probe_query_bind] at hresult
          | succ remaining =>
              rw [runResolvedFromTable_probe_query_bind] at hresult
              by_cases hrevealed : coordinate ∈ context.state.revealed
              · simp only [hrevealed, ↓reduceIte] at hresult
                exact ih () context remaining hcovered htail hresult
              · simp only [hrevealed, ↓reduceIte] at hresult
                exact ih () { context with state := context.state.addPending coordinate digest }
                  remaining (hcovered.addPending_of_mem ⟨coordinate, digest⟩ hmem) htail hresult
      | peek coordinate =>
          rw [runResolvedFromTable_peek_query_bind] at hresult
          exact ih (context.state.values coordinate) context fuel hcovered (hbound.2 _) hresult
      | publish coordinate =>
          rw [runResolvedFromTable_publish_query_bind] at hresult
          exact ih () { context with state := context.state.publish coordinate } fuel hcovered
            (hbound.2 ()) hresult
      | reveal coordinate =>
          rw [runResolvedFromTable_reveal_query_bind] at hresult
          cases coordinate <;> rw [mem_support_bind_iff] at hresult
          all_goals
            obtain ⟨option, _hresolve, htail⟩ := hresult
            cases option with
            | none => simp at htail
            | some resolved =>
                apply ih resolved.output _ fuel _ (hbound.2 resolved.output) htail
                exact hcovered.of_subset (Finset.filter_subset _ _)

theorem runResolvedFromTable_peekCoordinate
    (coordinate : Coordinate) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    runResolvedFromTable context fuel table ((peekCoordinate coordinate).run cache) =
      pure (some ⟨context, fuel, ((context.state.values coordinate).map truncateHash, cache), table⟩) := by
  change runResolvedFromTable context fuel table
    (LazyRevealProbe.peekQuery coordinate >>= fun result => pure (result.map truncateHash, cache)) = _
  rw [LazyRevealProbe.peekQuery, runResolvedFromTable_peek_query_bind]
  rfl

theorem runResolved_planFirstMissingInputCoordinate
    (state : LazyRevealProbe.State Coordinate) (input : HashInput) :
    ∀ slot coordinates context fuel table cache,
      context.state = state →
      runResolvedFromTable context fuel table
          ((planFirstMissingInputCoordinate input slot coordinates).run cache) =
        pure (some ⟨context, fuel,
          (firstMissingInputCoordinatePlan state input slot coordinates, cache), table⟩) := by
  intro slot coordinates
  induction coordinates generalizing slot with
  | nil =>
      intro context fuel table cache hstate
      simp [planFirstMissingInputCoordinate, firstMissingInputCoordinatePlan,
        runResolvedFromTable]
  | cons coordinate remaining ih =>
      intro context fuel table cache hstate
      rw [planFirstMissingInputCoordinate, StateT.run_bind,
        runResolvedFromTable_bind,
        runResolvedFromTable_peekCoordinate]
      simp only [pure_bind]
      rw [hstate]
      cases hvalue : state.values coordinate with
      | none =>
          simp [hvalue, firstMissingInputCoordinatePlan,
            runResolvedFromTable]
      | some output =>
          change runResolvedFromTable context fuel table
            ((planFirstMissingInputCoordinate input (slot + 1) remaining).run cache) = _
          rw [ih (slot + 1) context fuel table cache hstate]
          simp [firstMissingInputCoordinatePlan, hvalue]

theorem runResolved_planLeafInputProbe
    (state : LazyRevealProbe.State Coordinate)
    (input : HashInput) (candidate : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hstate : context.state = state) :
    runResolvedFromTable context fuel table
        ((planLeafInputProbe input candidate lay tree leafIdx).run cache) =
      pure (some ⟨context, fuel,
        (leafInputProbePlan state input candidate lay tree leafIdx, cache), table⟩) := by
  rw [planLeafInputProbe, StateT.run_bind,
    runResolvedFromTable_bind,
    runResolvedFromTable_peekCoordinate]
  simp only [pure_bind]
  rw [hstate]
  cases hvalue : state.values candidate.coordinate with
  | none =>
      simp [hvalue, leafInputProbePlan, runResolvedFromTable]
  | some output =>
      change runResolvedFromTable context fuel table
        ((planFirstMissingInputCoordinate input 0
          ((Position.leaf lay tree leafIdx).children.map Coordinate.position)).run cache) = _
      rw [runResolved_planFirstMissingInputCoordinate state input 0
        ((Position.leaf lay tree leafIdx).children.map Coordinate.position)
        context fuel table cache hstate]
      simp [leafInputProbePlan, hvalue]

theorem runResolved_planProbingHashQuery
    (parameter : PublicParameter) (input : HashInput)
    (state : LazyRevealProbe.State Coordinate) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hstate : context.state = state) :
    runResolvedFromTable context fuel table
        ((planProbingHashQuery parameter input).run cache) =
      pure (some ⟨context, fuel,
        (purePlanProbingHashQuery parameter input state, cache), table⟩) := by
  unfold planProbingHashQuery purePlanProbingHashQuery
  cases hprobe : decodeProbe? parameter input with
  | some candidate =>
      cases hposition : decodePosition? parameter input with
      | none => simp [runResolvedFromTable]
      | some position =>
          cases position with
          | leaf lay tree leafIdx =>
              rw [StateT.run_bind,
                runResolvedFromTable_bind,
                runResolved_planLeafInputProbe state input candidate lay tree
                  leafIdx context fuel table cache hstate]
              simp [runResolvedFromTable]
          | chain | node | ftsLeaf | ftsNode | ftsRoots =>
              simp [runResolvedFromTable]
  | none =>
      cases hposition : decodePosition? parameter input with
      | none => simp [runResolvedFromTable]
      | some position =>
          cases position with
          | node lay tree level nodeIdx =>
              rw [StateT.run_bind,
                runResolvedFromTable_bind,
                runResolved_planFirstMissingInputCoordinate state input 0
                  ((Position.node lay tree level nodeIdx).children.map Coordinate.position)
                  context fuel table cache hstate]
              simp [runResolvedFromTable]
          | chain | leaf | ftsLeaf | ftsNode | ftsRoots =>
              simp [runResolvedFromTable]

theorem runResolved_probingHashQuery_eq_afterPlan
    (parameter : PublicParameter) (input : HashInput) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    runResolvedFromTable context fuel table ((probingHashQuery parameter input).run cache) =
      runResolvedFromTable context fuel table ((probingHashQueryAfterPlan parameter input
        (purePlanProbingHashQuery parameter input context.state)).run cache) := by
  rw [probingHashQuery_eq_plan_then_afterPlan, StateT.run_bind, runResolvedFromTable_bind,
    runResolved_planProbingHashQuery parameter input context.state context fuel table cache rfl]
  simp only [pure_bind]

noncomputable def canonicalQueryCandidates (parameter : PublicParameter)
    (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) : List Probe :=
  match input with
  | .inl (.inr input) => (purePlanProbingHashQuery parameter input context.state).candidate?.toList
  | _ => []

noncomputable def canonicalTraceCandidates (parameter : PublicParameter) (history : List CanonicalQuerySelection) : List Probe :=
  history.flatMap fun entry => canonicalQueryCandidates parameter entry.input entry.context

theorem canonicalQueryCandidates_length_le_hashCount
    (parameter : PublicParameter) (input : (OracleWorld + SigningSpec).Domain) (context : DeferredContext) :
    (canonicalQueryCandidates parameter input context).length ≤ outerHashQueryCount input := by
  cases input with
  | inl query =>
      cases query with
      | inl n => exact le_rfl
      | inr input =>
          unfold canonicalQueryCandidates outerHashQueryCount
          cases (purePlanProbingHashQuery parameter input context.state).candidate? <;> simp
  | inr message => exact le_rfl

theorem canonicalTraceCandidates_length_le_hashCount
    (parameter : PublicParameter) (history : List CanonicalQuerySelection) :
    (canonicalTraceCandidates parameter history).length ≤ canonicalTraceHashCount history := by
  induction history with
  | nil => exact le_rfl
  | cons head tail ih =>
      simpa only [canonicalTraceCandidates, List.flatMap_cons, List.length_append,
        canonicalTraceHashCount, List.map_cons, List.sum_cons] using
        Nat.add_le_add (canonicalQueryCandidates_length_le_hashCount parameter head.input head.context) ih

theorem PendingCoveredBy.card_le
    {candidates : List Probe} {context : DeferredContext}
    (hcovered : PendingCoveredBy candidates context) :
    context.state.pending.card ≤ candidates.length := by
  classical
  have hsubset : context.state.pending ⊆
      (candidates.map fun candidate => (candidate.coordinate, candidate.candidate)).toFinset := by
    intro entry hentry
    obtain ⟨candidate, hcandidate, hcoordinate, hdigest⟩ := hcovered entry hentry
    simp only [List.mem_toFinset, List.mem_map]
    exact ⟨candidate, hcandidate, Prod.ext hcoordinate hdigest⟩
  exact (Finset.card_le_card hsubset).trans
    (by simpa only [List.length_map] using (List.toFinset_card_le
      (candidates.map fun candidate => (candidate.coordinate, candidate.candidate))))

theorem canonicalTraceHashCount_take_le
    (history : List CanonicalQuerySelection) (ordinal : Nat) :
    canonicalTraceHashCount (history.take ordinal) ≤ canonicalTraceHashCount history := by
  exact ((List.take_sublist _ _).map _).sum_le_sum (fun _ _ => Nat.zero_le _)

end SphincsSecurity.Concrete.OtsProbeSimulation
