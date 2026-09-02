import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootProbeCoupling
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootSelectionDeferred
import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootSelectionMaterialize

/-!
# Safe pending differences after root synchronization

After the delayed execution materializes the selected root, the eager execution can differ only by retaining earlier candidates at that root. Those candidates avoid the installed digest. This relation records exactly that difference.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

structure SafeTargetPendingLE
    (target : Position) (output : HashOutput)
    (left right : LazyRevealProbe.State Coordinate) : Prop where
  pending : left.pending ⊆ right.pending
  values : left.values = right.values
  revealed : left.revealed = right.revealed
  ensured : left.ensured = right.ensured
  target_value : left.values (.position target) = some output
  extra : ∀ coordinate candidate,
    (coordinate, candidate) ∈ right.pending →
      (coordinate, candidate) ∈ left.pending ∨
        (coordinate = .position target ∧ candidate ≠ truncateHash output)

theorem SafeTargetPendingLE.refl
    (target : Position) (output : HashOutput)
    (state : LazyRevealProbe.State Coordinate)
    (htarget : state.values (.position target) = some output) :
    SafeTargetPendingLE target output state state :=
  ⟨fun _ hentry => hentry, rfl, rfl, rfl, htarget,
    fun _ _ hentry => Or.inl hentry⟩

theorem SafeTargetPendingLE.toProbeStateLE
    {target : Position} {output : HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hrel : SafeTargetPendingLE target output left right)
    (hroot : IsLayerRoot target) :
    ProbeStateLE left right := by
  refine ⟨hrel.pending, hrel.values, hrel.revealed, hrel.ensured, ?_⟩
  intro coordinate candidate hentry
  rcases hrel.extra coordinate candidate hentry with hleft | ⟨hcoordinate, _hsafe⟩
  · exact Or.inl hleft
  · exact Or.inr ⟨target, hcoordinate, hroot⟩

theorem SafeTargetPendingLE.right_target_value
    {target : Position} {output : HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hrel : SafeTargetPendingLE target output left right) :
    right.values (.position target) = some output := by
  rw [← hrel.values]
  exact hrel.target_value

theorem SafeTargetPendingLE.hitAt_iff_of_ne
    {target : Position} {output : HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hrel : SafeTargetPendingLE target output left right)
    (coordinate : Coordinate) (value : HashOutput)
    (hne : coordinate ≠ .position target) :
    left.hitAt coordinate value ↔ right.hitAt coordinate value := by
  unfold LazyRevealProbe.State.hitAt
  rw [LazyRevealProbe.State.mem_pendingAt_iff,
    LazyRevealProbe.State.mem_pendingAt_iff]
  constructor
  · intro hentry
    exact hrel.pending hentry
  · intro hentry
    rcases hrel.extra coordinate (truncateHash value) hentry with hleft | hextra
    · exact hleft
    · exact (hne hextra.1).elim

theorem SafeTargetPendingLE.addPending
    {target : Position} {output : HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hrel : SafeTargetPendingLE target output left right)
    (coordinate : Coordinate) (candidate : Digest) :
    SafeTargetPendingLE target output
      (left.addPending coordinate candidate)
      (right.addPending coordinate candidate) := by
  refine ⟨?_, hrel.values, hrel.revealed, hrel.ensured, hrel.target_value, ?_⟩
  · intro entry hentry
    simp only [LazyRevealProbe.State.addPending, Finset.mem_insert] at hentry ⊢
    exact hentry.elim Or.inl (fun hold => Or.inr (hrel.pending hold))
  · intro other otherCandidate hentry
    simp only [LazyRevealProbe.State.addPending, Finset.mem_insert] at hentry ⊢
    rcases hentry with hnew | hold
    · exact Or.inl (Or.inl hnew)
    · rcases hrel.extra other otherCandidate hold with hleft | hextra
      · exact Or.inl (Or.inr hleft)
      · exact Or.inr hextra

theorem SafeTargetPendingLE.ensure
    {target : Position} {output : HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hrel : SafeTargetPendingLE target output left right)
    (coordinate : Coordinate) :
    SafeTargetPendingLE target output
      (left.ensure coordinate) (right.ensure coordinate) := by
  refine ⟨hrel.pending, hrel.values, hrel.revealed, ?_, hrel.target_value, hrel.extra⟩
  simp [LazyRevealProbe.State.ensure, hrel.ensured]

theorem SafeTargetPendingLE.publish
    {target : Position} {output : HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hrel : SafeTargetPendingLE target output left right)
    (coordinate : Coordinate) :
    SafeTargetPendingLE target output
      (left.publish coordinate) (right.publish coordinate) := by
  refine ⟨hrel.pending, hrel.values, ?_, hrel.ensured, hrel.target_value, hrel.extra⟩
  simp [LazyRevealProbe.State.publish, hrel.revealed]

theorem SafeTargetPendingLE.clearPending
    {target : Position} {output : HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hrel : SafeTargetPendingLE target output left right)
    (coordinate : Coordinate) :
    SafeTargetPendingLE target output
      (left.clearPending coordinate) (right.clearPending coordinate) := by
  refine ⟨?_, hrel.values, hrel.revealed, hrel.ensured, hrel.target_value, ?_⟩
  · intro entry hentry
    simp only [LazyRevealProbe.State.clearPending, LazyRevealProbe.State.pendingAway,
      Finset.mem_filter] at hentry ⊢
    exact ⟨hrel.pending hentry.1, hentry.2⟩
  · intro other candidate hentry
    simp only [LazyRevealProbe.State.clearPending, LazyRevealProbe.State.pendingAway,
      Finset.mem_filter] at hentry ⊢
    rcases hrel.extra other candidate hentry.1 with hleft | hextra
    · exact Or.inl ⟨hleft, hentry.2⟩
    · exact Or.inr hextra

theorem SafeTargetPendingLE.materialize_of_ne
    {target : Position} {output : HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hrel : SafeTargetPendingLE target output left right)
    (coordinate : Coordinate) (value : HashOutput)
    (hne : coordinate ≠ .position target) :
    SafeTargetPendingLE target output
      (left.materialize coordinate value)
      (right.materialize coordinate value) := by
  refine ⟨?_, ?_, hrel.revealed, ?_, ?_, ?_⟩
  · intro entry hentry
    simp only [LazyRevealProbe.State.materialize, LazyRevealProbe.State.pendingAway,
      Finset.mem_filter] at hentry ⊢
    exact ⟨hrel.pending hentry.1, hentry.2⟩
  · simp [LazyRevealProbe.State.materialize, hrel.values]
  · simp [LazyRevealProbe.State.materialize, hrel.ensured]
  · simp [LazyRevealProbe.State.materialize, Function.update_of_ne (Ne.symm hne),
      hrel.target_value]
  · intro other candidate hentry
    simp only [LazyRevealProbe.State.materialize, LazyRevealProbe.State.pendingAway,
      Finset.mem_filter] at hentry ⊢
    rcases hrel.extra other candidate hentry.1 with hleft | hextra
    · exact Or.inl ⟨hleft, hentry.2⟩
    · exact Or.inr hextra

theorem SafeTargetPendingLE.clean_extra
    {target : Position} {output : HashOutput}
    {left right : LazyRevealProbe.State Coordinate}
    (hrel : SafeTargetPendingLE target output left right)
    (coordinate : Coordinate) (candidate : Digest)
    (hentry : (coordinate, candidate) ∈ right.pending)
    (hnotLeft : (coordinate, candidate) ∉ left.pending) :
    coordinate = .position target ∧ candidate ≠ truncateHash output := by
  rcases hrel.extra coordinate candidate hentry with hleft | hextra
  · exact (hnotLeft hleft).elim
  · exact hextra

theorem safeTargetPendingLE_materialized_completePrivatePosition
    (target : Position) (output : HashOutput) (context : DeferredContext)
    (hhidden : context.state.values (.position target) = none)
    (hsafe : ∀ candidate,
      (Coordinate.position target, candidate) ∈ context.state.pending →
        candidate ≠ truncateHash output) :
    SafeTargetPendingLE target output
      (materializedDeferredState
        (completePrivatePosition target context output).toDeferredContext)
      (materializedDeferredState
        { context with values := context.values.install target output }) := by
  refine ⟨?_, ?_, rfl, rfl, ?_, ?_⟩
  · intro entry hentry
    simp only [materializedDeferredState_pending, completePrivatePosition,
      LazyRevealProbe.State.clearPending,
      LazyRevealProbe.State.pendingAway, Finset.mem_filter] at hentry ⊢
    exact hentry.1
  · funext coordinate
    cases coordinate with
    | chainStart lay tree leafIdx chainIdx => rfl
    | position position =>
        by_cases heq : position = target
        · subst position
          simp [materializedDeferredState, DeferredContext.positionValue,
            completePrivatePosition, DeferredStructuralValues.install]
        · simp [materializedDeferredState, DeferredContext.positionValue,
            completePrivatePosition, DeferredStructuralValues.install,
            Function.update_of_ne heq]
  · simp [materializedDeferredState, DeferredContext.positionValue,
      completePrivatePosition, DeferredStructuralValues.install, hhidden]
  · intro coordinate candidate hentry
    simp only [materializedDeferredState_pending] at hentry ⊢
    by_cases heq : coordinate = .position target
    · exact Or.inr ⟨heq, hsafe candidate (heq ▸ hentry)⟩
    · exact Or.inl (by
        simp only [completePrivatePosition, LazyRevealProbe.State.clearPending,
          LazyRevealProbe.State.pendingAway,
          Finset.mem_filter]
        exact ⟨hentry, heq⟩)

theorem safeTargetPendingLE_of_goodForRoots_pendingCovered
    {target : Position} {output : HashOutput} {rightRoot : Digest}
    {ordinal : Nat} {selection : PrivateOrdinalSelection}
    (hgood : selection.GoodForRoots target output rightRoot ordinal)
    (hcovered : PendingCoveredBy (selection.candidates.take ordinal) selection.context) :
    SafeTargetPendingLE target output
      (materializedDeferredState
        (completePrivatePosition target selection.context output).toDeferredContext)
      (materializedDeferredState
        { selection.context with
          values := selection.context.values.install target output }) := by
  apply safeTargetPendingLE_materialized_completePrivatePosition target output selection.context
    hgood.2.1
  intro candidate hentry heq
  obtain ⟨probe, hprobe, hcoordinate, hdigest⟩ := hcovered _ hentry
  have havoid := (hgood.2.2.2.2 probe hprobe).1
  apply havoid
  cases probe
  simp only [Probe.mk.injEq] at hcoordinate hdigest ⊢
  exact ⟨hcoordinate, hdigest.trans heq⟩

end SphincsSecurity.Concrete.OtsProbeSimulation
