import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootSwapCache

/-!
# Hidden layer-root state quotient

Two delayed-root runs may store different full outputs at one unpublished structural position while
all public lazy-state bookkeeping remains equal. This quotient isolates that one cell and is the
state-side companion of `RootEncodingCacheRel`.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

structure RootHiddenStateRel
    (target : Position) (leftOutput rightOutput : HashOutput)
    (left right : LazyRevealProbe.State Coordinate) : Prop where
  pending : left.pending = right.pending
  revealed : left.revealed = right.revealed
  ensured : left.ensured = right.ensured
  target_private : Coordinate.position target ∉ left.revealed
  left_target : left.values (.position target) = some leftOutput
  right_target : right.values (.position target) = some rightOutput
  other_values : ∀ coordinate, coordinate ≠ .position target →
    left.values coordinate = right.values coordinate

theorem RootHiddenStateRel.refl
    (target : Position) (output : HashOutput)
    (state : LazyRevealProbe.State Coordinate)
    (hprivate : Coordinate.position target ∉ state.revealed)
    (hvalue : state.values (.position target) = some output) :
    RootHiddenStateRel target output output state state :=
  ⟨rfl, rfl, rfl, hprivate, hvalue, hvalue, fun _ _ => rfl⟩

theorem RootHiddenStateRel.symm
    {target : Position} {leftOutput rightOutput : HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hrel : RootHiddenStateRel target leftOutput rightOutput left right) :
    RootHiddenStateRel target rightOutput leftOutput right left := by
  refine ⟨hrel.pending.symm, hrel.revealed.symm, hrel.ensured.symm, ?_,
    hrel.right_target, hrel.left_target, ?_⟩
  · intro hmem
    apply hrel.target_private
    rw [hrel.revealed]
    exact hmem
  · intro coordinate hne
    exact (hrel.other_values coordinate hne).symm

theorem rootHiddenStateRel_materialize
    (target : Position) (leftOutput rightOutput : HashOutput)
    (state : LazyRevealProbe.State Coordinate)
    (hprivate : Coordinate.position target ∉ state.revealed) :
    RootHiddenStateRel target leftOutput rightOutput
      (state.materialize (.position target) leftOutput)
      (state.materialize (.position target) rightOutput) := by
  refine ⟨rfl, rfl, rfl, hprivate, ?_, ?_, ?_⟩
  · simp [LazyRevealProbe.State.materialize]
  · simp [LazyRevealProbe.State.materialize]
  · intro coordinate hne
    simp [LazyRevealProbe.State.materialize, Function.update_of_ne hne]

theorem RootHiddenStateRel.values_isSome_eq
    {target : Position} {leftOutput rightOutput : HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hrel : RootHiddenStateRel target leftOutput rightOutput left right)
    (coordinate : Coordinate) :
    (left.values coordinate).isSome = (right.values coordinate).isSome := by
  by_cases heq : coordinate = .position target
  · subst coordinate
    rw [hrel.left_target, hrel.right_target]
    rfl
  · rw [hrel.other_values coordinate heq]

theorem RootHiddenStateRel.ensure
    {target : Position} {leftOutput rightOutput : HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hrel : RootHiddenStateRel target leftOutput rightOutput left right)
    (coordinate : Coordinate) :
    RootHiddenStateRel target leftOutput rightOutput
      (left.ensure coordinate) (right.ensure coordinate) := by
  refine ⟨hrel.pending, hrel.revealed, ?_, hrel.target_private,
    hrel.left_target, hrel.right_target, hrel.other_values⟩
  simp [LazyRevealProbe.State.ensure, hrel.ensured]

theorem RootHiddenStateRel.addPending
    {target : Position} {leftOutput rightOutput : HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hrel : RootHiddenStateRel target leftOutput rightOutput left right)
    (coordinate : Coordinate) (candidate : Digest) :
    RootHiddenStateRel target leftOutput rightOutput
      (left.addPending coordinate candidate) (right.addPending coordinate candidate) := by
  refine ⟨?_, hrel.revealed, hrel.ensured, hrel.target_private,
    hrel.left_target, hrel.right_target, hrel.other_values⟩
  simp [LazyRevealProbe.State.addPending, hrel.pending]

theorem RootHiddenStateRel.clearPending
    {target : Position} {leftOutput rightOutput : HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hrel : RootHiddenStateRel target leftOutput rightOutput left right)
    (coordinate : Coordinate) :
    RootHiddenStateRel target leftOutput rightOutput
      (left.clearPending coordinate) (right.clearPending coordinate) := by
  refine ⟨?_, hrel.revealed, hrel.ensured, hrel.target_private,
    hrel.left_target, hrel.right_target, hrel.other_values⟩
  simp [LazyRevealProbe.State.clearPending, LazyRevealProbe.State.pendingAway, hrel.pending]

theorem RootHiddenStateRel.publish_of_ne
    {target : Position} {leftOutput rightOutput : HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hrel : RootHiddenStateRel target leftOutput rightOutput left right)
    (coordinate : Coordinate) (hne : coordinate ≠ .position target) :
    RootHiddenStateRel target leftOutput rightOutput
      (left.publish coordinate) (right.publish coordinate) := by
  refine ⟨hrel.pending, ?_, hrel.ensured, ?_,
    hrel.left_target, hrel.right_target, hrel.other_values⟩
  · simp [LazyRevealProbe.State.publish, hrel.revealed]
  · simp [LazyRevealProbe.State.publish, hrel.target_private, Ne.symm hne]

theorem RootHiddenStateRel.materialize_other
    {target : Position} {leftOutput rightOutput : HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hrel : RootHiddenStateRel target leftOutput rightOutput left right)
    (coordinate : Coordinate) (output : HashOutput)
    (hne : coordinate ≠ .position target) :
    RootHiddenStateRel target leftOutput rightOutput
      (left.materialize coordinate output) (right.materialize coordinate output) := by
  refine ⟨?_, hrel.revealed, ?_, hrel.target_private, ?_, ?_, ?_⟩
  · simp [LazyRevealProbe.State.materialize, LazyRevealProbe.State.pendingAway, hrel.pending]
  · simp [LazyRevealProbe.State.materialize, hrel.ensured]
  · simpa [LazyRevealProbe.State.materialize, Function.update_of_ne hne.symm]
      using hrel.left_target
  · simpa [LazyRevealProbe.State.materialize, Function.update_of_ne hne.symm]
      using hrel.right_target
  · intro other hother
    by_cases heq : other = coordinate
    · subst other
      simp [LazyRevealProbe.State.materialize]
    · simp [LazyRevealProbe.State.materialize, Function.update_of_ne heq,
        hrel.other_values other hother]

theorem firstMissingInputCoordinatePlan_eq_of_rootHiddenStateRel
    {target : Position} {leftOutput rightOutput : HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hrel : RootHiddenStateRel target leftOutput rightOutput left right)
    (input : HashInput) : ∀ slot coordinates,
    firstMissingInputCoordinatePlan left input slot coordinates =
      firstMissingInputCoordinatePlan right input slot coordinates := by
  intro slot coordinates
  induction coordinates generalizing slot with
  | nil => rfl
  | cons coordinate remaining ih =>
      rw [firstMissingInputCoordinatePlan, firstMissingInputCoordinatePlan]
      have hpresent := hrel.values_isSome_eq coordinate
      cases hleft : left.values coordinate with
      | none =>
          cases hright : right.values coordinate with
          | none => rfl
          | some rightValue => simp [hleft, hright] at hpresent
      | some leftValue =>
          cases hright : right.values coordinate with
          | none => simp [hleft, hright] at hpresent
          | some rightValue =>
              exact ih (slot + 1)

theorem leafInputProbePlan_eq_of_rootHiddenStateRel
    {target : Position} {leftOutput rightOutput : HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hrel : RootHiddenStateRel target leftOutput rightOutput left right)
    (input : HashInput) (candidate : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    leafInputProbePlan left input candidate lay tree leafIdx =
      leafInputProbePlan right input candidate lay tree leafIdx := by
  unfold leafInputProbePlan
  have hpresent := hrel.values_isSome_eq candidate.coordinate
  cases hleft : left.values candidate.coordinate with
  | none =>
      cases hright : right.values candidate.coordinate with
      | none => rfl
      | some rightValue => simp [hleft, hright] at hpresent
  | some leftValue =>
      cases hright : right.values candidate.coordinate with
      | none => simp [hleft, hright] at hpresent
      | some rightValue =>
          exact firstMissingInputCoordinatePlan_eq_of_rootHiddenStateRel hrel input 0
            ((Position.leaf lay tree leafIdx).children.map Coordinate.position)

theorem purePlanProbingHashQuery_eq_of_rootHiddenStateRel
    {target : Position} {leftOutput rightOutput : HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hrel : RootHiddenStateRel target leftOutput rightOutput left right)
    (parameter : PublicParameter) (input : HashInput) :
    purePlanProbingHashQuery parameter input left =
      purePlanProbingHashQuery parameter input right := by
  unfold purePlanProbingHashQuery
  cases hprobe : decodeProbe? parameter input with
  | some candidate =>
      cases hposition : decodePosition? parameter input with
      | none => rfl
      | some position =>
          cases position with
          | leaf lay tree leafIdx =>
              simp only
              rw [leafInputProbePlan_eq_of_rootHiddenStateRel hrel]
          | chain | node | ftsLeaf | ftsNode | ftsRoots => rfl
  | none =>
      cases hposition : decodePosition? parameter input with
      | none => rfl
      | some position =>
          cases position with
          | node lay tree level nodeIdx =>
              simp only
              rw [firstMissingInputCoordinatePlan_eq_of_rootHiddenStateRel hrel]
          | chain | leaf | ftsLeaf | ftsNode | ftsRoots => rfl

theorem rootAwarePlannedCandidate?_eq_of_rootHiddenStateRel
    {target : Position} {leftOutput rightOutput : HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hrel : RootHiddenStateRel target leftOutput rightOutput left right)
    (parameter : PublicParameter) (input : HashInput) :
    rootAwarePlannedCandidate? parameter input left =
      rootAwarePlannedCandidate? parameter input right := by
  unfold rootAwarePlannedCandidate?
  rw [purePlanProbingHashQuery_eq_of_rootHiddenStateRel hrel parameter input]

theorem runCleanFromTable_pure_oracle
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (value : α) :
    runCleanFromTable state fuel table
        (pure value : OracleComp (LazyRevealProbe.World Coordinate) α) =
      pure (some ⟨state, fuel, value, table⟩) := by
  simp [runCleanFromTable]

theorem runCleanFromTable_planFirstMissingInputCoordinate
    (state : LazyRevealProbe.State Coordinate) (input : HashInput) :
    ∀ slot coordinates fuel table cache,
    runCleanFromTable state fuel table
        ((planFirstMissingInputCoordinate input slot coordinates).run cache) =
      pure (some ⟨state, fuel,
        (firstMissingInputCoordinatePlan state input slot coordinates, cache), table⟩) := by
  intro slot coordinates
  induction coordinates generalizing slot with
  | nil =>
      intro fuel table cache
      simp [planFirstMissingInputCoordinate, firstMissingInputCoordinatePlan, runCleanFromTable]
  | cons coordinate remaining ih =>
      intro fuel table cache
      rw [planFirstMissingInputCoordinate, StateT.run_bind, runCleanFromTable_bind,
        peekCoordinate_run_eq, LazyRevealProbe.peekQuery, runCleanFromTable_peek_query_bind]
      rw [runCleanFromTable_pure_oracle]
      simp only [pure_bind]
      cases hvalue : state.values coordinate with
      | none => simp [hvalue, firstMissingInputCoordinatePlan, runCleanFromTable]
      | some output =>
          rw [show truncateHash <$> some output = some (truncateHash output) by rfl]
          rw [ih (slot + 1) fuel table cache]
          simp [hvalue, firstMissingInputCoordinatePlan]

theorem runCleanFromTable_planLeafInputProbe
    (state : LazyRevealProbe.State Coordinate)
    (input : HashInput) (candidate : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    runCleanFromTable state fuel table
        ((planLeafInputProbe input candidate lay tree leafIdx).run cache) =
      pure (some ⟨state, fuel,
        (leafInputProbePlan state input candidate lay tree leafIdx, cache), table⟩) := by
  rw [planLeafInputProbe, StateT.run_bind, runCleanFromTable_bind,
    peekCoordinate_run_eq, LazyRevealProbe.peekQuery, runCleanFromTable_peek_query_bind]
  rw [runCleanFromTable_pure_oracle]
  simp only [pure_bind]
  cases hvalue : state.values candidate.coordinate with
  | none => simp [hvalue, leafInputProbePlan, runCleanFromTable]
  | some output =>
      rw [show truncateHash <$> some output = some (truncateHash output) by rfl]
      rw [runCleanFromTable_planFirstMissingInputCoordinate state input 0
        ((Position.leaf lay tree leafIdx).children.map Coordinate.position) fuel table cache]
      simp [hvalue, leafInputProbePlan]

theorem runCleanFromTable_planProbingHashQuery
    (parameter : PublicParameter) (input : HashInput)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    runCleanFromTable state fuel table
        ((planProbingHashQuery parameter input).run cache) =
      pure (some ⟨state, fuel,
        (purePlanProbingHashQuery parameter input state, cache), table⟩) := by
  unfold planProbingHashQuery purePlanProbingHashQuery
  cases hprobe : decodeProbe? parameter input with
  | some candidate =>
      cases hposition : decodePosition? parameter input with
      | none => simp [runCleanFromTable]
      | some position =>
          cases position with
          | leaf lay tree leafIdx =>
              simp only [StateT.run_bind, runCleanFromTable_bind]
              rw [runCleanFromTable_planLeafInputProbe]
              simp [runCleanFromTable]
          | chain | node | ftsLeaf | ftsNode | ftsRoots =>
              simp [runCleanFromTable]
  | none =>
      cases hposition : decodePosition? parameter input with
      | none => simp [runCleanFromTable]
      | some position =>
          cases position with
          | node lay tree level nodeIdx =>
              simp only [StateT.run_bind, runCleanFromTable_bind]
              rw [runCleanFromTable_planFirstMissingInputCoordinate]
              simp [runCleanFromTable]
          | chain | leaf | ftsLeaf | ftsNode | ftsRoots =>
              simp [runCleanFromTable]

structure RootHiddenCacheRel
    (target : Position) (leftOutput rightOutput : HashOutput)
    (left right : SplitHashCache) : Prop where
  ordinary : ∀ input, left (.ordinary input) = right (.ordinary input)
  left_target : left (.hidden (.position target)) = some leftOutput
  right_target : right (.hidden (.position target)) = some rightOutput
  other_hidden : ∀ coordinate, coordinate ≠ .position target →
    left (.hidden coordinate) = right (.hidden coordinate)

theorem RootHiddenCacheRel.symm
    {target : Position} {leftOutput rightOutput : HashOutput}
    {left right : SplitHashCache}
    (hrel : RootHiddenCacheRel target leftOutput rightOutput left right) :
    RootHiddenCacheRel target rightOutput leftOutput right left :=
  ⟨fun input => (hrel.ordinary input).symm, hrel.right_target, hrel.left_target,
    fun coordinate hne => (hrel.other_hidden coordinate hne).symm⟩

def replaceHiddenRootCache
    (target : Position) (output : HashOutput) (cache : SplitHashCache) : SplitHashCache :=
  Function.update cache (.hidden (.position target)) (some output)

theorem rootHiddenCacheRel_replace
    (target : Position) (leftOutput rightOutput : HashOutput)
    (cache : SplitHashCache)
    (hleft : cache (.hidden (.position target)) = some leftOutput) :
    RootHiddenCacheRel target leftOutput rightOutput cache
      (replaceHiddenRootCache target rightOutput cache) := by
  refine ⟨?_, hleft, ?_, ?_⟩
  · intro input
    simp [replaceHiddenRootCache]
  · simp [replaceHiddenRootCache]
  · intro coordinate hne
    have hkey : SplitHashKey.hidden coordinate ≠ .hidden (.position target) := by
      intro heq
      exact hne (SplitHashKey.hidden.inj heq)
    simp [replaceHiddenRootCache, Function.update_of_ne hkey]

theorem replaceHiddenRootCache_involutive
    (target : Position) (leftOutput rightOutput : HashOutput)
    (cache : SplitHashCache)
    (hleft : cache (.hidden (.position target)) = some leftOutput) :
    replaceHiddenRootCache target leftOutput
        (replaceHiddenRootCache target rightOutput cache) = cache := by
  funext key
  by_cases heq : key = .hidden (.position target)
  · subst key
    simp [replaceHiddenRootCache, hleft]
  · simp [replaceHiddenRootCache, Function.update_of_ne heq]

def RootHiddenCleanSameRel
    (target : Position) (leftOutput rightOutput : HashOutput) :
    Option (CleanRunResult (α × SplitHashCache)) →
      Option (CleanRunResult (α × SplitHashCache)) → Prop
  | some left, some right =>
      RootHiddenStateRel target leftOutput rightOutput left.state right.state ∧
        left.remaining = right.remaining ∧ left.table = right.table ∧
        left.value.1 = right.value.1 ∧
        RootHiddenCacheRel target leftOutput rightOutput left.value.2 right.value.2
  | none, none => True
  | _, _ => False

def RootHiddenRelates
    (target : Position) (leftOutput rightOutput : HashOutput)
    (left right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ leftState rightState,
    RootHiddenStateRel target leftOutput rightOutput leftState rightState →
    ∀ fuel table leftCache rightCache,
      RootHiddenCacheRel target leftOutput rightOutput leftCache rightCache →
      RelTriple
        (runCleanFromTable leftState fuel table (left.run leftCache))
        (runCleanFromTable rightState fuel table (right.run rightCache))
        (RootHiddenCleanSameRel target leftOutput rightOutput)

theorem rootHiddenRelates_pure
    (target : Position) (leftOutput rightOutput : HashOutput) (value : α) :
    RootHiddenRelates target leftOutput rightOutput
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) α)
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) α) := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  simp only [StateT.run_pure, runCleanFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure ⟨hstate, rfl, rfl, rfl, hcache⟩

theorem RootHiddenRelates.bind
    {target : Position} {leftOutput rightOutput : HashOutput}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {leftNext rightNext : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hfirst : RootHiddenRelates target leftOutput rightOutput left right)
    (hnext : ∀ leftValue rightValue, leftValue = rightValue →
      RootHiddenRelates target leftOutput rightOutput
        (leftNext leftValue) (rightNext rightValue)) :
    RootHiddenRelates target leftOutput rightOutput
      (left >>= leftNext) (right >>= rightNext) := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  rw [StateT.run_bind, StateT.run_bind, runCleanFromTable_bind,
    runCleanFromTable_bind]
  apply relTriple_bind
    (hfirst leftState rightState hstate fuel table leftCache rightCache hcache)
  intro leftResult rightResult hresult
  cases leftResult with
  | none =>
      cases rightResult with
      | none => exact relTriple_pure_pure trivial
      | some rightResult => simp [RootHiddenCleanSameRel] at hresult
  | some leftResult =>
      cases rightResult with
      | none => simp [RootHiddenCleanSameRel] at hresult
      | some rightResult =>
          rcases hresult with ⟨hnextState, hremaining, htable, hvalue, hnextCache⟩
          simp only
          rw [← hremaining, ← htable, ← hvalue]
          exact hnext leftResult.value.1 leftResult.value.1 rfl
            leftResult.state rightResult.state hnextState leftResult.remaining
              leftResult.table leftResult.value.2 rightResult.value.2 hnextCache

theorem rootHiddenRelates_planProbingHashQuery
    (target : Position) (leftOutput rightOutput : HashOutput)
    (parameter : PublicParameter) (input : HashInput) :
    RootHiddenRelates target leftOutput rightOutput
      (planProbingHashQuery parameter input)
      (planProbingHashQuery parameter input) := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  rw [runCleanFromTable_planProbingHashQuery,
    runCleanFromTable_planProbingHashQuery]
  apply relTriple_pure_pure
  refine ⟨hstate, rfl, rfl, ?_, hcache⟩
  exact congrArg id
    (purePlanProbingHashQuery_eq_of_rootHiddenStateRel hstate parameter input)

theorem rootHiddenRelates_splitUniformImpl
    (target : Position) (leftOutput rightOutput : HashOutput) (n : Nat) :
    RootHiddenRelates target leftOutput rightOutput
      (splitUniformImpl n) (splitUniformImpl n) := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  unfold splitUniformImpl LazyRevealProbe.uniformQuery
  rw [StateT.run_liftM, StateT.run_liftM,
    runCleanFromTable_uniform_query_bind, runCleanFromTable_uniform_query_bind]
  apply relTriple_bind
    (relTriple_refl (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
  intro leftValue rightValue hvalue
  subst rightValue
  simp only [runCleanFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure ⟨hstate, rfl, rfl, rfl, hcache⟩

theorem rootHiddenRelates_ensureCoordinate
    (target : Position) (leftOutput rightOutput : HashOutput)
    (coordinate : Coordinate) :
    RootHiddenRelates target leftOutput rightOutput
      (ensureCoordinate coordinate) (ensureCoordinate coordinate) := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  rw [runCleanFromTable_ensureCoordinate, runCleanFromTable_ensureCoordinate]
  exact relTriple_pure_pure ⟨hstate.ensure coordinate, rfl, rfl, rfl, hcache⟩

theorem rootHiddenRelates_probe
    (target : Position) (leftOutput rightOutput : HashOutput)
    (candidate : Probe) :
    RootHiddenRelates target leftOutput rightOutput
      (probe candidate) (probe candidate) := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  unfold probe LazyRevealProbe.probeQuery
  rw [StateT.run_liftM, StateT.run_liftM,
    runCleanFromTable_probe_query_bind, runCleanFromTable_probe_query_bind]
  cases fuel with
  | zero => exact relTriple_pure_pure trivial
  | succ remaining =>
      have hrevealed : candidate.coordinate ∈ leftState.revealed ↔
          candidate.coordinate ∈ rightState.revealed := by rw [hstate.revealed]
      by_cases hleftRevealed : candidate.coordinate ∈ leftState.revealed
      · have hrightRevealed := hrevealed.mp hleftRevealed
        simp only [hleftRevealed, hrightRevealed, ↓reduceIte,
          runCleanFromTable, OracleComp.construct_pure]
        exact relTriple_pure_pure ⟨hstate, rfl, rfl, rfl, hcache⟩
      · have hrightRevealed : candidate.coordinate ∉ rightState.revealed :=
          fun hmem => hleftRevealed (hrevealed.mpr hmem)
        simp only [hleftRevealed, hrightRevealed, ↓reduceIte,
          runCleanFromTable, OracleComp.construct_pure]
        exact relTriple_pure_pure ⟨hstate.addPending candidate.coordinate candidate.candidate,
          rfl, rfl, rfl, hcache⟩

end SphincsSecurity.Concrete.OtsProbeSimulation
