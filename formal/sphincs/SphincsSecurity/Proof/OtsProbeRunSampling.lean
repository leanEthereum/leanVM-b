import SphincsSecurity.Proof.Prelude
import SphincsSecurity.Proof.OtsProbeSampling

/-!
# Finite-table deferral through one-time probing runs

The clean eager interpreter reads missing chain starts from one finite table. All uniform draws and
all ordinary or structural random-oracle outputs remain lazy. Its result retains the hidden state,
probe fuel and table needed by finalization.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

noncomputable local instance runSampleableOtsHashTable :
    SampleableType (OtsSecretIndex → HashOutput) :=
  SampleableType.ofFintype (OtsSecretIndex → HashOutput)

noncomputable def sampleOtsHashTable :
    ProbComp (OtsSecretIndex → HashOutput) :=
  $ᵗ (OtsSecretIndex → HashOutput)

theorem evalDist_sampleOtsHashTable_bind_const (result : ProbComp alpha) :
    𝒟[sampleOtsHashTable >>= fun _ => result] = 𝒟[result] := by
  exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
    sampleOtsHashTable (by rw [sampleOtsHashTable]; simp) result

def StartTableAgrees (state : LazyRevealProbe.State Coordinate)
    (table : OtsSecretIndex → HashOutput) : Prop :=
  ∀ index output, state.values index.coordinate = some output → output = table index

theorem startTableAgrees_empty (table : OtsSecretIndex → HashOutput) :
    StartTableAgrees (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) table := by
  intro index output hvalue
  simp [LazyRevealProbe.State.empty] at hvalue

theorem StartTableAgrees.ensure
    {state : LazyRevealProbe.State Coordinate}
    {table : OtsSecretIndex → HashOutput} (hagrees : StartTableAgrees state table)
    (coordinate : Coordinate) : StartTableAgrees (state.ensure coordinate) table := by
  exact hagrees

theorem StartTableAgrees.addPending
    {state : LazyRevealProbe.State Coordinate}
    {table : OtsSecretIndex → HashOutput} (hagrees : StartTableAgrees state table)
    (coordinate : Coordinate) (candidate : Digest) :
    StartTableAgrees (state.addPending coordinate candidate) table := by
  exact hagrees

theorem StartTableAgrees.publish
    {state : LazyRevealProbe.State Coordinate}
    {table : OtsSecretIndex → HashOutput} (hagrees : StartTableAgrees state table)
    (coordinate : Coordinate) : StartTableAgrees (state.publish coordinate) table := by
  exact hagrees

theorem StartTableAgrees.materialize_start
    {state : LazyRevealProbe.State Coordinate}
    {table : OtsSecretIndex → HashOutput} (hagrees : StartTableAgrees state table)
    (index : OtsSecretIndex) :
    StartTableAgrees (state.materialize index.coordinate (table index)) table := by
  intro other output hvalue
  by_cases heq : other = index
  · subst other
    simpa [LazyRevealProbe.State.materialize] using hvalue.symm
  · have hcoordinate : other.coordinate ≠ index.coordinate :=
      fun h => heq (OtsSecretIndex.coordinate_injective h)
    apply hagrees other output
    simpa [LazyRevealProbe.State.materialize, hcoordinate] using hvalue

theorem StartTableAgrees.materialize_position
    {state : LazyRevealProbe.State Coordinate}
    {table : OtsSecretIndex → HashOutput} (hagrees : StartTableAgrees state table)
    (position : Position) (output : HashOutput) :
    StartTableAgrees (state.materialize (.position position) output) table := by
  intro index cached hvalue
  apply hagrees index cached
  simpa [LazyRevealProbe.State.materialize, OtsSecretIndex.coordinate] using hvalue

theorem StartTableAgrees.complete_start
    {state : LazyRevealProbe.State Coordinate}
    {table : OtsSecretIndex → HashOutput} (hagrees : StartTableAgrees state table)
    (index : OtsSecretIndex) :
    StartTableAgrees (state.complete index.coordinate (table index)) table := by
  intro other output hvalue
  by_cases heq : other = index
  · subst other
    simpa [LazyRevealProbe.State.complete] using hvalue.symm
  · have hcoordinate : other.coordinate ≠ index.coordinate :=
      fun h => heq (OtsSecretIndex.coordinate_injective h)
    apply hagrees other output
    simpa [LazyRevealProbe.State.complete, hcoordinate] using hvalue

theorem StartTableAgrees.complete_position
    {state : LazyRevealProbe.State Coordinate}
    {table : OtsSecretIndex → HashOutput} (hagrees : StartTableAgrees state table)
    (position : Position) (output : HashOutput) :
    StartTableAgrees (state.complete (.position position) output) table := by
  intro index cached hvalue
  apply hagrees index cached
  simpa [LazyRevealProbe.State.complete, OtsSecretIndex.coordinate] using hvalue

theorem pendingAt_clearPending_of_ne
    (state : LazyRevealProbe.State Coordinate) (left right : Coordinate)
    (hne : right ≠ left) :
    (state.clearPending left).pendingAt right = state.pendingAt right := by
  ext candidate
  simp [LazyRevealProbe.State.pendingAt, LazyRevealProbe.State.clearPending,
    LazyRevealProbe.State.pendingAway, hne]

theorem pendingAt_complete_of_ne
    (state : LazyRevealProbe.State Coordinate) (left right : Coordinate)
    (output : HashOutput) (hne : right ≠ left) :
    (state.complete left output).pendingAt right = state.pendingAt right := by
  exact pendingAt_clearPending_of_ne state left right hne

theorem hitAt_clearPending_of_ne
    (state : LazyRevealProbe.State Coordinate) (left right : Coordinate)
    (output : HashOutput) (hne : right ≠ left) :
    (state.clearPending left).hitAt right output ↔ state.hitAt right output := by
  unfold LazyRevealProbe.State.hitAt
  rw [pendingAt_clearPending_of_ne state left right hne]

theorem hitAt_complete_of_ne
    (state : LazyRevealProbe.State Coordinate) (left right : Coordinate)
    (leftOutput rightOutput : HashOutput) (hne : right ≠ left) :
    (state.complete left leftOutput).hitAt right rightOutput ↔
      state.hitAt right rightOutput := by
  unfold LazyRevealProbe.State.hitAt
  rw [pendingAt_complete_of_ne state left right leftOutput hne]

@[simp] theorem values_clearPending
    (state : LazyRevealProbe.State Coordinate) (left right : Coordinate) :
    (state.clearPending left).values right = state.values right := rfl

theorem values_complete_of_ne
    (state : LazyRevealProbe.State Coordinate) (left right : Coordinate)
    (output : HashOutput) (hne : right ≠ left) :
    (state.complete left output).values right = state.values right := by
  simp [LazyRevealProbe.State.complete, Function.update, hne]

theorem clearPending_comm
    (state : LazyRevealProbe.State Coordinate) (left right : Coordinate) :
    (state.clearPending left).clearPending right =
      (state.clearPending right).clearPending left := by
  rcases state with ⟨pending, values, revealed, ensured⟩
  simp [LazyRevealProbe.State.clearPending, LazyRevealProbe.State.pendingAway, and_comm]
  exact Finset.filter_comm (fun x : Coordinate × Digest => ¬ x.1 = left)
    (fun x => ¬ x.1 = right) pending

theorem clearPending_complete_comm
    (state : LazyRevealProbe.State Coordinate) (left right : Coordinate)
    (output : HashOutput) :
    (state.clearPending left).complete right output =
      (state.complete right output).clearPending left := by
  rcases state with ⟨pending, values, revealed, ensured⟩
  simp [LazyRevealProbe.State.clearPending, LazyRevealProbe.State.complete,
    LazyRevealProbe.State.pendingAway, and_comm]
  exact Finset.filter_comm (fun x : Coordinate × Digest => ¬ x.1 = left)
    (fun x => ¬ x.1 = right) pending

theorem complete_comm
    (state : LazyRevealProbe.State Coordinate) (left right : Coordinate)
    (leftOutput rightOutput : HashOutput) (hne : left ≠ right) :
    (state.complete left leftOutput).complete right rightOutput =
      (state.complete right rightOutput).complete left leftOutput := by
  rcases state with ⟨pending, values, revealed, ensured⟩
  simp [LazyRevealProbe.State.complete, LazyRevealProbe.State.pendingAway,
    Function.update_comm hne, and_comm]
  exact Finset.filter_comm (fun x : Coordinate × Digest => ¬ x.1 = left)
    (fun x => ¬ x.1 = right) pending

def StructuralScheduleWP (computation : OracleComp HashSpec alpha)
    (post : alpha → List Coordinate → LazyRevealProbe.State Coordinate →
      QueryCache HashSpec → Prop)
    (coordinates : List Coordinate) (state : LazyRevealProbe.State Coordinate)
    (cache : QueryCache HashSpec) : Prop :=
  OracleComp.construct
    (C := fun _ : OracleComp HashSpec alpha =>
      List Coordinate → LazyRevealProbe.State Coordinate → QueryCache HashSpec → Prop)
    post
    (fun input _next recursivelyScheduled coordinates state cache =>
      ∃ position : Position,
        (Coordinate.position position ∈ coordinates ∧
          state.values (.position position) = none ∧
          cache input = none ∧
          ∀ output, ¬state.hitAt (.position position) output →
            recursivelyScheduled output
              (coordinates.erase (.position position))
              (state.complete (.position position) output)
              (cache.cacheQuery input output)) ∨
        (∃ output : HashOutput,
          Coordinate.position position ∈ coordinates ∧
          state.values (.position position) = some output ∧
          cache input = some output ∧
          recursivelyScheduled output
            (coordinates.erase (.position position))
            (state.clearPending (.position position)) cache))
    computation coordinates state cache

@[simp] theorem structuralScheduleWP_pure
    (value : alpha)
    (post : alpha → List Coordinate → LazyRevealProbe.State Coordinate →
      QueryCache HashSpec → Prop)
    (coordinates : List Coordinate) (state : LazyRevealProbe.State Coordinate)
    (cache : QueryCache HashSpec) :
    StructuralScheduleWP (pure value) post coordinates state cache =
      post value coordinates state cache := by
  rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
