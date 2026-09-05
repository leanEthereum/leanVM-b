import SphincsSecurity.Proof.LazyRevealProbe

namespace SphincsSecurity.LazyRevealProbe

open OracleComp OracleSpec ENNReal

variable {Coordinate : Type} [DecidableEq Coordinate]

def State.unmaterializedPending (state : State Coordinate) : Finset (Coordinate × Digest) :=
  state.pending.filter fun entry => state.values entry.1 = none

omit [DecidableEq Coordinate] in
theorem State.unmaterializedPending_card_le (state : State Coordinate) :
    state.unmaterializedPending.card ≤ state.pending.card := Finset.card_filter_le _ _

theorem State.unmaterializedPending_clearPending (state : State Coordinate) (coordinate : Coordinate) :
    (state.clearPending coordinate).unmaterializedPending =
      state.unmaterializedPending.filter (fun entry => entry.1 ≠ coordinate) := by
  ext entry
  simp only [unmaterializedPending, clearPending, pendingAway, Finset.mem_filter]
  tauto

theorem State.unmaterializedPending_materialize (state : State Coordinate)
    (coordinate : Coordinate) (output : HashOutput) :
    (state.materialize coordinate output).unmaterializedPending =
      (state.clearPending coordinate).unmaterializedPending := by
  ext entry
  by_cases heq : entry.1 = coordinate
  · simp [unmaterializedPending, materialize, clearPending, pendingAway, heq]
  · simp [unmaterializedPending, materialize, clearPending, pendingAway, heq]

theorem State.unmaterializedPending_complete (state : State Coordinate)
    (coordinate : Coordinate) (output : HashOutput) :
    (state.complete coordinate output).unmaterializedPending =
      (state.clearPending coordinate).unmaterializedPending :=
  state.unmaterializedPending_materialize coordinate output

theorem State.unmaterializedPending_clearPending_card_le (state : State Coordinate) (coordinate : Coordinate) :
    (state.clearPending coordinate).unmaterializedPending.card ≤ state.unmaterializedPending.card := by
  rw [state.unmaterializedPending_clearPending]
  exact Finset.card_filter_le _ _

theorem State.unmaterializedPending_card_split_le (state : State Coordinate) (coordinate : Coordinate)
    (hvalue : state.values coordinate = none) :
    (state.clearPending coordinate).unmaterializedPending.card + (state.pendingAt coordinate).card ≤
      state.unmaterializedPending.card := by
  have hat : state.pending.filter (fun entry => entry.1 = coordinate) =
      state.unmaterializedPending.filter (fun entry => entry.1 = coordinate) := by
    ext entry
    simp only [unmaterializedPending, Finset.mem_filter]
    constructor
    · rintro ⟨hmem, heq⟩
      exact ⟨⟨hmem, heq ▸ hvalue⟩, heq⟩
    · exact fun h => ⟨h.1.1, h.2⟩
  apply (Nat.add_le_add_left (state.pendingAt_card_le coordinate) _).trans_eq
  rw [hat, state.unmaterializedPending_clearPending, Nat.add_comm]
  exact Finset.card_filter_add_card_filter_not _

theorem finalizeFrom_probability_le_unmaterializedPending (coordinates : List Coordinate)
    (state : State Coordinate) :
    Pr[fun hit : Bool => hit = true | finalizeFrom coordinates state] ≤
      (state.unmaterializedPending.card : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  induction coordinates generalizing state with
  | nil => simp [finalizeFrom]
  | cons coordinate remaining ih =>
      rw [finalizeFrom]
      cases hvalue : state.values coordinate with
      | some output =>
          exact (ih (state.clearPending coordinate)).trans
            (mul_le_mul' (Nat.cast_le.mpr (state.unmaterializedPending_clearPending_card_le coordinate)) le_rfl)
      | none =>
          refine (probEvent_bind_le_probEvent_add
            (mx := sampleHashOutput)
            (my := fun output => if state.hitAt coordinate output then pure true
              else finalizeFrom remaining (state.complete coordinate output))
            (q := fun hit : Bool => hit = true) (p := state.hitAt coordinate)
            (ε := ((state.clearPending coordinate).unmaterializedPending.card : ℝ≥0∞) *
              ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ?_).trans ?_
          · intro output _ hmiss
            simp only [hmiss, ↓reduceIte]
            simpa only [state.unmaterializedPending_complete] using ih (state.complete coordinate output)
          · apply (add_le_add (probEvent_sampleHashOutput_hitAt_le state coordinate) le_rfl).trans
            rw [← add_mul, ← Nat.cast_add]
            apply mul_le_mul' _ le_rfl
            exact Nat.cast_le.mpr (by simpa only [Nat.add_comm] using state.unmaterializedPending_card_split_le coordinate hvalue)

theorem finalize_probability_le_unmaterializedPending (state : State Coordinate) :
    Pr[fun hit : Bool => hit = true | finalize state] ≤
      (state.unmaterializedPending.card : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ :=
  finalizeFrom_probability_le_unmaterializedPending state.coordinates.toList state

end SphincsSecurity.LazyRevealProbe
