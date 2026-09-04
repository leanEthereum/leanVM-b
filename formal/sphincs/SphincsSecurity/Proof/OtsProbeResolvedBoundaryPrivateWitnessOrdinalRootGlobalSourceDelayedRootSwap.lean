import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalSourceDelayedRootBridge

/-!
# Delayed selector root swap

The delayed selector must retain executions that encounter an unrelated pending hit. Its root
exchange therefore runs in the permissive interpreter itself, rather than passing through the
failure-discarding materialized selector.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def RootHiddenPermissiveRelatesWith
    (target : Position) (leftOutput rightOutput : HashOutput)
    (valueRel : α → β → Prop)
    (left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β) : Prop :=
  ∀ leftState rightState,
    RootHiddenStateRel target leftOutput rightOutput leftState rightState →
    ∀ fuel table leftCache rightCache,
      RootHiddenCacheRel target leftOutput rightOutput leftCache rightCache →
      RelTriple
        (runPermissiveFromTable leftState fuel table (left.run leftCache))
        (runPermissiveFromTable rightState fuel table (right.run rightCache))
        (RootHiddenCleanRelWith target leftOutput rightOutput valueRel)

theorem rootHiddenPermissiveRelatesWith_pure
    (target : Position) (leftOutput rightOutput : HashOutput)
    (leftValue : α) (rightValue : β) (hvalue : R leftValue rightValue) :
    RootHiddenPermissiveRelatesWith target leftOutput rightOutput R
      (pure leftValue) (pure rightValue) := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  simp only [StateT.run_pure, runPermissiveFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure ⟨hstate, rfl, rfl, hvalue, hcache⟩

theorem RootHiddenPermissiveRelatesWith.bind
    {target : Position} {leftOutput rightOutput : HashOutput}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    {leftNext : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) γ}
    {rightNext : β → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) δ}
    (hfirst : RootHiddenPermissiveRelatesWith target leftOutput rightOutput R left right)
    (hnext : ∀ leftValue rightValue, R leftValue rightValue →
      RootHiddenPermissiveRelatesWith target leftOutput rightOutput S
        (leftNext leftValue) (rightNext rightValue)) :
    RootHiddenPermissiveRelatesWith target leftOutput rightOutput S
      (left >>= leftNext) (right >>= rightNext) := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  rw [StateT.run_bind, StateT.run_bind, runPermissiveFromTable_bind,
    runPermissiveFromTable_bind]
  apply relTriple_bind
    (hfirst leftState rightState hstate fuel table leftCache rightCache hcache)
  intro leftResult rightResult hresult
  cases leftResult with
  | none =>
      cases rightResult with
      | none => exact relTriple_pure_pure trivial
      | some rightResult => simp [RootHiddenCleanRelWith] at hresult
  | some leftResult =>
      cases rightResult with
      | none => simp [RootHiddenCleanRelWith] at hresult
      | some rightResult =>
          rcases hresult with ⟨hnextState, hremaining, htable, hvalue, hnextCache⟩
          simp only
          rw [← hremaining, ← htable]
          exact hnext leftResult.value.1 rightResult.value.1 hvalue
            leftResult.state rightResult.state hnextState leftResult.remaining leftResult.table
              leftResult.value.2 rightResult.value.2 hnextCache

def RootHiddenPermissiveRelates
    (target : Position) (leftOutput rightOutput : HashOutput)
    (left right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  RootHiddenPermissiveRelatesWith target leftOutput rightOutput (fun x y => x = y) left right

theorem rootHiddenPermissiveRelates_pure
    (target : Position) (leftOutput rightOutput : HashOutput) (value : α) :
    RootHiddenPermissiveRelates target leftOutput rightOutput (pure value) (pure value) :=
  rootHiddenPermissiveRelatesWith_pure target leftOutput rightOutput value value rfl

theorem rootHiddenPermissiveRelates_splitUniformImpl
    (target : Position) (leftOutput rightOutput : HashOutput) (n : Nat) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (splitUniformImpl n) (splitUniformImpl n) := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  unfold splitUniformImpl LazyRevealProbe.uniformQuery
  rw [StateT.run_liftM, StateT.run_liftM,
    runPermissiveFromTable_uniform_query_bind, runPermissiveFromTable_uniform_query_bind]
  apply relTriple_bind
    (relTriple_refl (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
  intro leftValue rightValue hvalue
  subst rightValue
  simp only [runPermissiveFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure ⟨hstate, rfl, rfl, rfl, hcache⟩

theorem rootHiddenPermissiveRelates_ensureCoordinate
    (target : Position) (leftOutput rightOutput : HashOutput)
    (coordinate : Coordinate) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (ensureCoordinate coordinate) (ensureCoordinate coordinate) := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  unfold ensureCoordinate LazyRevealProbe.ensureQuery
  rw [StateT.run_liftM, StateT.run_liftM,
    runPermissiveFromTable_ensure_query_bind, runPermissiveFromTable_ensure_query_bind]
  simp only [runPermissiveFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure ⟨hstate.ensure coordinate, rfl, rfl, trivial, hcache⟩

theorem rootHiddenPermissiveRelates_probe
    (target : Position) (leftOutput rightOutput : HashOutput)
    (candidate : Probe) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (probe candidate) (probe candidate) := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  unfold probe LazyRevealProbe.probeQuery
  rw [StateT.run_liftM, StateT.run_liftM,
    runPermissiveFromTable_probe_query_bind, runPermissiveFromTable_probe_query_bind]
  cases fuel with
  | zero => exact relTriple_pure_pure trivial
  | succ remaining =>
      have hrevealed : candidate.coordinate ∈ leftState.revealed ↔
          candidate.coordinate ∈ rightState.revealed := by rw [hstate.revealed]
      by_cases hleftRevealed : candidate.coordinate ∈ leftState.revealed
      · have hrightRevealed := hrevealed.mp hleftRevealed
        simp only [hleftRevealed, hrightRevealed, ↓reduceIte,
          runPermissiveFromTable, OracleComp.construct_pure]
        exact relTriple_pure_pure ⟨hstate, rfl, rfl, trivial, hcache⟩
      · have hrightRevealed : candidate.coordinate ∉ rightState.revealed :=
          fun hmem => hleftRevealed (hrevealed.mpr hmem)
        simp only [hleftRevealed, hrightRevealed, ↓reduceIte,
          runPermissiveFromTable, OracleComp.construct_pure]
        exact relTriple_pure_pure
          ⟨hstate.addPending candidate.coordinate candidate.candidate,
            rfl, rfl, trivial, hcache⟩

theorem rootHiddenPermissiveRelates_splitHashQuery_ordinary
    (target : Position) (leftOutput rightOutput : HashOutput)
    (input : HashInput) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (splitHashQuery (.ordinary input)) (splitHashQuery (.ordinary input)) := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  have hlookup := hcache.ordinary input
  rw [splitHashQuery_run_eq, splitHashQuery_run_eq]
  cases hleft : leftCache (.ordinary input) with
  | some output =>
      have hright : rightCache (.ordinary input) = some output := by
        rw [← hlookup]
        exact hleft
      simp only [hright, runPermissiveFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨hstate, rfl, rfl, rfl, hcache⟩
  | none =>
      have hright : rightCache (.ordinary input) = none := by
        rw [← hlookup]
        exact hleft
      simp only [hright]
      unfold LazyRevealProbe.hashOutputQuery
      rw [runPermissiveFromTable_hashOutput_query_bind,
        runPermissiveFromTable_hashOutput_query_bind]
      apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
      intro leftSample rightSample hsample
      subst rightSample
      simp only [runPermissiveFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨hstate, rfl, rfl, rfl,
        hcache.update_same_ordinary input leftSample⟩

theorem rootHiddenPermissiveRelates_revealCoordinate_of_ne
    (target : Position) (leftOutput rightOutput : HashOutput)
    (coordinate : Coordinate) (hne : coordinate ≠ .position target) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (revealCoordinate coordinate) (revealCoordinate coordinate) := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  rw [revealCoordinate_run, revealCoordinate_run, LazyRevealProbe.revealQuery,
    runPermissiveFromTable_reveal_query_bind, runPermissiveFromTable_reveal_query_bind]
  have hvalue := hstate.other_values coordinate hne
  cases hleft : leftState.values coordinate with
  | some output =>
      have hright : rightState.values coordinate = some output := by
        rw [← hvalue]
        exact hleft
      simp only [hright, runPermissiveFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨hstate, rfl, rfl, rfl,
        hcache.update_same_hidden_of_ne coordinate output hne⟩
  | none =>
      have hright : rightState.values coordinate = none := by
        rw [← hvalue]
        exact hleft
      simp only [hright]
      cases coordinate with
      | chainStart lay tree leafIdx chainIdx =>
          simp only
          let output := table ⟨lay, tree, leafIdx, chainIdx⟩
          simp only [runPermissiveFromTable, OracleComp.construct_pure]
          exact relTriple_pure_pure
            ⟨hstate.materialize_other (.chainStart lay tree leafIdx chainIdx) output hne,
              rfl, rfl, rfl,
              hcache.update_same_hidden_of_ne
                (.chainStart lay tree leafIdx chainIdx) output hne⟩
      | position position =>
          apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
          intro leftSample rightSample hsample
          subst rightSample
          simp only [runPermissiveFromTable, OracleComp.construct_pure]
          exact relTriple_pure_pure
            ⟨hstate.materialize_other (.position position) leftSample hne,
              rfl, rfl, rfl,
              hcache.update_same_hidden_of_ne (.position position) leftSample hne⟩

theorem rootHiddenPermissiveRelates_publishCoordinate_of_ne
    (target : Position) (leftOutput rightOutput : HashOutput)
    (coordinate : Coordinate) (hne : coordinate ≠ .position target) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (publishCoordinate coordinate) (publishCoordinate coordinate) := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  unfold publishCoordinate LazyRevealProbe.publishQuery
  rw [StateT.run_liftM, StateT.run_liftM,
    runPermissiveFromTable_publish_query_bind, runPermissiveFromTable_publish_query_bind]
  simp only [runPermissiveFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure
    ⟨hstate.publish_of_ne coordinate hne, rfl, rfl, trivial, hcache⟩

theorem rootHiddenPermissiveRelates_revealPublishedCoordinate_of_ne
    (target : Position) (leftOutput rightOutput : HashOutput)
    (coordinate : Coordinate) (hne : coordinate ≠ .position target) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (revealPublishedCoordinate coordinate) (revealPublishedCoordinate coordinate) := by
  unfold revealPublishedCoordinate
  exact (rootHiddenPermissiveRelates_revealCoordinate_of_ne target leftOutput rightOutput
    coordinate hne).bind fun leftValue rightValue hvalue =>
      (rootHiddenPermissiveRelates_publishCoordinate_of_ne target leftOutput rightOutput
        coordinate hne).bind fun _ _ _ => by
          subst rightValue
          exact rootHiddenPermissiveRelates_pure target leftOutput rightOutput leftValue

end SphincsSecurity.Concrete.OtsProbeSimulation
