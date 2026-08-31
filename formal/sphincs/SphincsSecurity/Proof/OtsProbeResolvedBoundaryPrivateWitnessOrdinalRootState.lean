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

end SphincsSecurity.Concrete.OtsProbeSimulation
