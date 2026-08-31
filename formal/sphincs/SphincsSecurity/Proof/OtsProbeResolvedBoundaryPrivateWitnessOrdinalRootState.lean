import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootSwapCache

/-!
# Hidden layer-root state quotient

Two delayed-root runs may store different full outputs at one unpublished structural position while
all public lazy-state bookkeeping remains equal. This quotient isolates that one cell and is the
state-side companion of `RootEncodingCacheRel`.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

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

end SphincsSecurity.Concrete.OtsProbeSimulation
