import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootSelectionProbability

/-!
# Deferred selection to materialized selection

The ordinary refinement relation is generalized to two computations. This is the semantic bridge
between the real deferred planned suffix and the materialized suffix that executes the same public
plan. A private first fire on the deferred side remains an admissible stopped outcome; a
materialization-only discrepancy makes the right side doomed.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def OrdinaryMaterializedStableCouplesBetween
    (table : OtsSecretIndex → HashOutput)
    (left right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ leftContext rightContext leftFuel rightFuel leftCache rightCache,
    FinalizationContextLE table leftContext rightContext →
    leftFuel ≤ rightFuel →
    ordinaryQueryCache leftCache = ordinaryQueryCache rightCache →
    leftContext.state.revealed = rightContext.state.revealed →
    LazyRevealProbe.ValuesLE leftContext.state rightContext.state →
    PublishedValues leftContext.state →
    rightContext = directDeferredContext rightContext.state →
    RelTriple
      (runDirectResolvedDetailedFromTable leftContext leftFuel table
        (left.run leftCache))
      (runDirectResolvedDetailedFromTable rightContext rightFuel table
        (right.run rightCache))
      (DirectDetailedOrdinaryStableRunEq table)

theorem OrdinaryMaterializedStableCouples.toBetween
    {table : OtsSecretIndex → HashOutput}
    {computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    (hcomputation : OrdinaryMaterializedStableCouples table computation) :
    OrdinaryMaterializedStableCouplesBetween table computation computation :=
  hcomputation

theorem ordinaryMaterializedStableCouplesBetween_pure
    (table : OtsSecretIndex → HashOutput) (leftValue rightValue : α)
    (hvalue : leftValue = rightValue) :
    OrdinaryMaterializedStableCouplesBetween table
      (pure leftValue) (pure rightValue) := by
  subst rightValue
  exact (ordinaryMaterializedStableCouples_pure table leftValue).toBetween

theorem OrdinaryMaterializedStableCouplesBetween.bind
    {table : OtsSecretIndex → HashOutput}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {leftNext : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    {rightNext : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hfirst : OrdinaryMaterializedStableCouplesBetween table left right)
    (hnext : ∀ value,
      OrdinaryMaterializedStableCouplesBetween table
        (leftNext value) (rightNext value)) :
    OrdinaryMaterializedStableCouplesBetween table
      (left >>= leftNext) (right >>= rightNext) := by
  intro leftContext rightContext leftFuel rightFuel leftCache rightCache hcontext hfuel hcache
    hrevealed hvalues hpublished hrightMaterialized
  rw [StateT.run_bind, StateT.run_bind]
  apply relTriple_runDirectResolvedDetailed_bind_stable table
    (left.run leftCache) (right.run rightCache)
    (fun value cache => (leftNext value).run cache)
    (fun value cache => (rightNext value).run cache)
    leftContext rightContext leftFuel rightFuel
  · exact hfirst leftContext rightContext leftFuel rightFuel leftCache rightCache hcontext hfuel
      hcache hrevealed hvalues hpublished hrightMaterialized
  · intro leftResult rightResult hrelation
    have hvalue : leftResult.value.1 = rightResult.value.1 := hrelation.value_eq
    rw [← hvalue]
    rw [hrelation.left_table, hrelation.right_table]
    exact hnext leftResult.value.1
      leftResult.context rightResult.context leftResult.remaining rightResult.remaining
      leftResult.value.2 rightResult.value.2 hrelation.context_le hrelation.remaining_le
      hrelation.cache_eq hrelation.revealed_eq hrelation.values_le hrelation.left_published
      hrelation.right_materialized

def OrdinaryMaterializedStableCouplesBetweenPositive
    (table : OtsSecretIndex → HashOutput)
    (left right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ leftContext rightContext leftFuel rightFuel leftCache rightCache,
    0 < leftFuel →
    FinalizationContextLE table leftContext rightContext →
    leftFuel ≤ rightFuel →
    ordinaryQueryCache leftCache = ordinaryQueryCache rightCache →
    leftContext.state.revealed = rightContext.state.revealed →
    LazyRevealProbe.ValuesLE leftContext.state rightContext.state →
    PublishedValues leftContext.state →
    rightContext = directDeferredContext rightContext.state →
    RelTriple
      (runDirectResolvedDetailedFromTable leftContext leftFuel table
        (left.run leftCache))
      (runDirectResolvedDetailedFromTable rightContext rightFuel table
        (right.run rightCache))
      (DirectDetailedOrdinaryStableRunEq table)

theorem OrdinaryMaterializedStableCouplesBetweenPositive.bind
    {table : OtsSecretIndex → HashOutput}
    {left right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {leftNext rightNext : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hfirst : OrdinaryMaterializedStableCouplesBetweenPositive table left right)
    (hnext : ∀ value, OrdinaryMaterializedStableCouplesBetween table
      (leftNext value) (rightNext value)) :
    OrdinaryMaterializedStableCouplesBetweenPositive table
      (left >>= leftNext) (right >>= rightNext) := by
  intro leftContext rightContext leftFuel rightFuel leftCache rightCache hpositive hcontext hfuel
    hcache hrevealed hvalues hpublished hrightMaterialized
  rw [StateT.run_bind, StateT.run_bind]
  apply relTriple_runDirectResolvedDetailed_bind_stable table
    (left.run leftCache) (right.run rightCache)
    (fun value cache => (leftNext value).run cache)
    (fun value cache => (rightNext value).run cache)
    leftContext rightContext leftFuel rightFuel
  · exact hfirst leftContext rightContext leftFuel rightFuel leftCache rightCache hpositive
      hcontext hfuel hcache hrevealed hvalues hpublished hrightMaterialized
  · intro leftResult rightResult hrelation
    have hvalue : leftResult.value.1 = rightResult.value.1 := hrelation.value_eq
    rw [← hvalue, hrelation.left_table, hrelation.right_table]
    exact hnext leftResult.value.1
      leftResult.context rightResult.context leftResult.remaining rightResult.remaining
      leftResult.value.2 rightResult.value.2 hrelation.context_le hrelation.remaining_le
      hrelation.cache_eq hrelation.revealed_eq hrelation.values_le hrelation.left_published
      hrelation.right_materialized

set_option maxRecDepth 100000 in
theorem ordinaryMaterializedStableCouplesBetween_probe
    (table : OtsSecretIndex → HashOutput) (candidate : Probe) :
    OrdinaryMaterializedStableCouplesBetweenPositive table
      (probe candidate) (probe candidate) := by
  intro left right leftFuel rightFuel leftCache rightCache hpositive hcontext hfuel hcache hrevealed
    hvalues hpublished hrightMaterialized
  cases leftFuel with
  | zero => omega
  | succ leftRemaining =>
      obtain ⟨rightRemaining, hrightFuel⟩ : ∃ rightRemaining,
          rightFuel = rightRemaining + 1 := by
        refine ⟨rightFuel - 1, ?_⟩
        omega
      subst rightFuel
      unfold probe
      simp only [StateT.run_liftM]
      unfold LazyRevealProbe.probeQuery
      rw [runDirectResolvedDetailedFromTable_probe_query_bind,
        runDirectResolvedDetailedFromTable_probe_query_bind]
      by_cases hleftRevealed : candidate.coordinate ∈ left.state.revealed
      · have hrightRevealed : candidate.coordinate ∈ right.state.revealed := by
          rw [← hrevealed]
          exact hleftRevealed
        simp only [hleftRevealed, hrightRevealed, ↓reduceIte]
        exact (ordinaryMaterializedStableCouples_pure table ()).toBetween
          left right leftRemaining rightRemaining leftCache rightCache hcontext (by omega)
          hcache hrevealed hvalues hpublished hrightMaterialized
      · have hrightRevealed : candidate.coordinate ∉ right.state.revealed := by
          rwa [← hrevealed]
        simp only [hleftRevealed, hrightRevealed, ↓reduceIte]
        let nextLeft : DeferredContext :=
          { left with state := left.state.addPending candidate.coordinate candidate.candidate }
        let nextRight : DeferredContext :=
          { right with state := right.state.addPending candidate.coordinate candidate.candidate }
        by_cases hcompletable : DeferredCompletable table nextRight
        · have hnext := hcontext.addPending_both_of_right_completable
            candidate.coordinate candidate.candidate hcompletable
          have hnextPublished : PublishedValues nextLeft.state := by
            simpa [nextLeft, PublishedValues, LazyRevealProbe.State.addPending] using hpublished
          exact (ordinaryMaterializedStableCouples_pure table ()).toBetween
            nextLeft nextRight leftRemaining rightRemaining leftCache rightCache hnext (by omega)
            hcache hrevealed hvalues hnextPublished (by
              show nextRight = directDeferredContext nextRight.state
              dsimp [nextRight]
              rw [hrightMaterialized]
              simp [directDeferredContext, directDeferredValues_addPending])
        · rw [runDirectResolvedDetailedFromTable_pure,
            runDirectResolvedDetailedFromTable_pure]
          apply relTriple_pure_pure
          right
          exact ⟨⟨rfl, hcontext.view.rightConsistent.addPending
                candidate.coordinate candidate.candidate,
                hcontext.view.rightStarts.addPending
                  candidate.coordinate candidate.candidate, hcompletable⟩, by
                show nextRight = directDeferredContext nextRight.state
                dsimp [nextRight]
                rw [hrightMaterialized]
                simp [directDeferredContext, directDeferredValues_addPending]⟩

theorem ordinaryMaterializedStableCouplesBetween_executeCandidate
    (table : OtsSecretIndex → HashOutput) (candidate? : Option Probe) :
    OrdinaryMaterializedStableCouplesBetweenPositive table
      (executeCandidate? candidate?) (executeCandidate? candidate?) := by
  cases candidate? with
  | none =>
      intro left right leftFuel rightFuel leftCache rightCache _hpositive
      exact ordinaryMaterializedStableCouplesBetween_pure table () () rfl
        left right leftFuel rightFuel leftCache rightCache
  | some candidate => exact ordinaryMaterializedStableCouplesBetween_probe table candidate

theorem runDirectResolvedDetailedFromTable_peekPositionValues_eq_pure
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    ∀ positions,
    runDirectResolvedDetailedFromTable context fuel table
        ((peekPositionValues positions).run cache) =
      pure (.done ⟨context, fuel,
        (purePeekPositionValues context.state positions, cache), table⟩)
  | [] => by
      simp [peekPositionValues, purePeekPositionValues,
        runDirectResolvedDetailedFromTable]
  | position :: remaining => by
      rw [peekPositionValues, StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
        runDirectResolvedDetailedFromTable_peekCoordinate]
      cases hvalue : truncateHash <$> context.state.values (.position position) with
      | none =>
          simp [purePeekPositionValues, hvalue, runDirectResolvedDetailedFromTable]
      | some value =>
          simp only [pure_bind]
          rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
            runDirectResolvedDetailedFromTable_peekPositionValues_eq_pure context fuel table cache
              remaining]
          cases htail : purePeekPositionValues context.state remaining <;>
            simp [purePeekPositionValues, hvalue, htail, runDirectResolvedDetailedFromTable]

set_option maxRecDepth 100000 in
theorem runDirectResolvedDetailedFromTable_peekTableInput_eq_pure
    (parameter : PublicParameter) (coordinate : Coordinate)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    runDirectResolvedDetailedFromTable context fuel table
        ((peekTableInput parameter coordinate).run cache) =
      pure (.done ⟨context, fuel,
        (purePeekTableInput parameter context.state coordinate, cache), table⟩) := by
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      simp [peekTableInput, purePeekTableInput, runDirectResolvedDetailedFromTable]
  | position position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          rw [peekTableInput.eq_2]
          by_cases hzero : step.val = 0
          · rw [if_pos hzero]
            rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
              runDirectResolvedDetailedFromTable_peekCoordinate]
            cases hvalue : truncateHash <$>
                context.state.values (.chainStart lay tree leafIdx chainIdx) <;>
              simp [purePeekTableInput, hzero, hvalue,
                runDirectResolvedDetailedFromTable]
          · rw [if_neg hzero]
            rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
              runDirectResolvedDetailedFromTable_peekPositionValues_eq_pure]
            cases hvalues : purePeekPositionValues context.state
                (Position.chain lay tree leafIdx chainIdx step).children <;>
              simp [purePeekTableInput, hzero, hvalues,
                runDirectResolvedDetailedFromTable]
      | leaf lay tree leafIdx =>
          simp only [peekTableInput]
          rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
            runDirectResolvedDetailedFromTable_peekPositionValues_eq_pure]
          cases hvalues : purePeekPositionValues context.state _ <;>
            simp [purePeekTableInput, hvalues, runDirectResolvedDetailedFromTable]
      | node lay tree level nodeIdx =>
          simp only [peekTableInput]
          rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
            runDirectResolvedDetailedFromTable_peekPositionValues_eq_pure]
          cases hvalues : purePeekPositionValues context.state _ <;>
            simp [purePeekTableInput, hvalues, runDirectResolvedDetailedFromTable]
      | ftsLeaf index tree leafIdx =>
          simp only [peekTableInput]
          rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
            runDirectResolvedDetailedFromTable_peekPositionValues_eq_pure]
          cases hvalues : purePeekPositionValues context.state _ <;>
            simp [purePeekTableInput, hvalues, runDirectResolvedDetailedFromTable]
      | ftsNode index tree level nodeIdx =>
          simp only [peekTableInput]
          rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
            runDirectResolvedDetailedFromTable_peekPositionValues_eq_pure]
          cases hvalues : purePeekPositionValues context.state _ <;>
            simp [purePeekTableInput, hvalues, runDirectResolvedDetailedFromTable]
      | ftsRoots index =>
          simp only [peekTableInput]
          rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
            runDirectResolvedDetailedFromTable_peekPositionValues_eq_pure]
          cases hvalues : purePeekPositionValues context.state _ <;>
            simp [purePeekTableInput, hvalues, runDirectResolvedDetailedFromTable]

set_option maxRecDepth 100000 in
theorem runDirectResolvedDetailedFromTable_resolveKnownInput_eq_public
    (parameter : PublicParameter) (coordinate : Coordinate) (input : HashInput)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    runDirectResolvedDetailedFromTable context fuel table
        ((resolveKnownInput parameter coordinate input).run cache) =
      runDirectResolvedDetailedFromTable context fuel table
        ((resolvePublicKnownInput parameter context.state coordinate input).run cache) := by
  unfold resolveKnownInput resolvePublicKnownInput
  rw [StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
    runDirectResolvedDetailedFromTable_peekTableInput_eq_pure]
  simp only [pure_bind]
  cases hknown : purePeekTableInput parameter context.state coordinate with
  | none => rfl
  | some knownInput =>
      by_cases heq : knownInput = input <;> simp [heq]

theorem purePeekPositionValues_eq_of_values_eq
    {left right : LazyRevealProbe.State Coordinate}
    (hvalues : left.values = right.values) : ∀ positions,
    purePeekPositionValues left positions = purePeekPositionValues right positions
  | [] => rfl
  | position :: remaining => by
      simp only [purePeekPositionValues]
      rw [hvalues]
      cases truncateHash <$> right.values (.position position) with
      | none => rfl
      | some value => rw [purePeekPositionValues_eq_of_values_eq hvalues remaining]

theorem purePeekTableInput_eq_of_values_eq
    (parameter : PublicParameter)
    {left right : LazyRevealProbe.State Coordinate}
    (hvalues : left.values = right.values) (coordinate : Coordinate) :
    purePeekTableInput parameter left coordinate =
      purePeekTableInput parameter right coordinate := by
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx => rfl
  | position position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          simp only [purePeekTableInput]
          by_cases hzero : step.val = 0
          · simp only [hzero, ↓reduceIte]
            rw [hvalues]
          · simp only [hzero, ↓reduceIte]
            rw [purePeekPositionValues_eq_of_values_eq hvalues]
      | leaf | node | ftsLeaf | ftsNode | ftsRoots =>
          simp only [purePeekTableInput]
          rw [purePeekPositionValues_eq_of_values_eq hvalues]

theorem resolvePublicKnownInput_eq_of_values_eq
    (parameter : PublicParameter)
    {left right : LazyRevealProbe.State Coordinate}
    (hvalues : left.values = right.values)
    (coordinate : Coordinate) (input : HashInput) :
    resolvePublicKnownInput parameter left coordinate input =
      resolvePublicKnownInput parameter right coordinate input := by
  unfold resolvePublicKnownInput
  rw [purePeekTableInput_eq_of_values_eq parameter hvalues coordinate]

set_option maxRecDepth 100000 in
theorem runDirectResolvedDetailedFromTable_afterPlan_eq_publicPlan
    (parameter : PublicParameter) (input : HashInput) (plan : PlannedHashQuery)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    runDirectResolvedDetailedFromTable context fuel table
        ((probingHashQueryAfterPlan parameter input plan).run cache) =
      runDirectResolvedDetailedFromTable context fuel table
        ((probingHashQueryAfterPublicPlan parameter input context.state plan).run cache) := by
  unfold probingHashQueryAfterPlan probingHashQueryAfterPublicPlan executePlannedHashQuery
  cases hcandidate : plan.candidate? with
  | none =>
      simp only [executeCandidate?, pure_bind]
      cases haction : plan.action with
      | ordinary => rfl
      | resolve coordinate =>
          exact runDirectResolvedDetailedFromTable_resolveKnownInput_eq_public parameter
            coordinate input context fuel table cache
  | some candidate =>
      simp only [executeCandidate?]
      rw [StateT.run_bind, StateT.run_bind, runDirectResolvedDetailedFromTable_bind,
        runDirectResolvedDetailedFromTable_bind]
      simp only [probe, StateT.run_liftM, LazyRevealProbe.probeQuery,
        runDirectResolvedDetailedFromTable_probe_query_bind]
      cases fuel with
      | zero => rfl
      | succ remaining =>
          by_cases hrevealed : candidate.coordinate ∈ context.state.revealed
          · simp only [hrevealed, ↓reduceIte]
            rw [runDirectResolvedDetailedFromTable_pure, pure_bind]
            cases haction : plan.action with
            | ordinary => rfl
            | resolve coordinate =>
                exact runDirectResolvedDetailedFromTable_resolveKnownInput_eq_public parameter
                  coordinate input context remaining table cache
          · simp only [hrevealed, ↓reduceIte]
            let nextContext : DeferredContext :=
              { context with state :=
                  context.state.addPending candidate.coordinate candidate.candidate }
            rw [show
              runDirectResolvedDetailedFromTable nextContext remaining table (pure ((), cache)) =
                pure (.done ⟨nextContext, remaining, ((), cache), table⟩) by
              exact runDirectResolvedDetailedFromTable_pure _ _ _ _]
            simp only [pure_bind]
            cases haction : plan.action with
            | ordinary => rfl
            | resolve coordinate =>
                have hbase := runDirectResolvedDetailedFromTable_resolveKnownInput_eq_public
                  parameter coordinate input nextContext remaining table cache
                have hpublic := resolvePublicKnownInput_eq_of_values_eq parameter
                  (left := nextContext.state) (right := context.state) (by
                    rfl) coordinate input
                rw [hpublic] at hbase
                exact hbase

end SphincsSecurity.Concrete.OtsProbeSimulation
