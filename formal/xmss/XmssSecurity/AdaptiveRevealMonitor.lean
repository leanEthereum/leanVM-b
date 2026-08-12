import XmssSecurity.AdaptiveEpochCollision

open OracleComp ENNReal
open scoped BigOperators

namespace XmssSecurity.AdaptiveRevealMonitor

variable {Index : Type} [Fintype Index] [DecidableEq Index]

structure State (Index : Type) where
  pending : Index → Finset Digest
  revealed : Index → Option Digest

def State.pendingCount (state : State Index) : Nat :=
  ∑ index, (state.pending index).card

def State.addPending (state : State Index) (index : Index) (digest : Digest) : State Index :=
  { state with pending := Function.update state.pending index (insert digest (state.pending index)) }

def State.install (state : State Index) (index : Index) (digest : Digest) : State Index :=
  { pending := Function.update state.pending index ∅
    revealed := Function.update state.revealed index (some digest) }

theorem State.pendingCount_addPending_le
    (state : State Index) (index : Index) (digest : Digest) :
    (state.addPending index digest).pendingCount ≤ state.pendingCount + 1 := by
  classical
  unfold pendingCount addPending
  change (∑ candidate,
      (Function.update state.pending index
        (insert digest (state.pending index)) candidate).card) ≤ _
  have hupdate :
      (fun candidate =>
        (Function.update state.pending index
          (insert digest (state.pending index)) candidate).card) =
        Function.update (fun candidate => (state.pending candidate).card) index
          (insert digest (state.pending index)).card := by
    funext candidate
    by_cases heq : candidate = index <;> simp [heq]
  rw [hupdate, Finset.sum_update_of_mem (Finset.mem_univ index)]
  have hsum := Finset.sum_erase_add Finset.univ
    (fun candidate => (state.pending candidate).card) (Finset.mem_univ index)
  calc
    (insert digest (state.pending index)).card +
        ∑ candidate ∈ Finset.univ \ {index}, (state.pending candidate).card ≤
      ((state.pending index).card + 1) +
        ∑ candidate ∈ Finset.univ \ {index}, (state.pending candidate).card := by
          gcongr
          exact Finset.card_insert_le digest (state.pending index)
    _ = (∑ candidate ∈ Finset.univ \ {index},
          (state.pending candidate).card) + (state.pending index).card + 1 := by
      omega
    _ = (∑ candidate, (state.pending candidate).card) + 1 := by
      rw [Finset.sdiff_singleton_eq_erase, hsum]

theorem State.pendingCount_install_add
    (state : State Index) (index : Index) (digest : Digest) :
    (state.install index digest).pendingCount + (state.pending index).card =
      state.pendingCount := by
  classical
  unfold pendingCount install
  change (∑ candidate,
      (Function.update state.pending index ∅ candidate).card) +
        (state.pending index).card = _
  have hupdate :
      (fun candidate =>
        (Function.update state.pending index ∅ candidate).card) =
        Function.update (fun candidate => (state.pending candidate).card) index 0 := by
    funext candidate
    by_cases heq : candidate = index <;> simp [heq]
  rw [hupdate, Finset.sum_update_of_mem (Finset.mem_univ index), zero_add,
    Finset.sdiff_singleton_eq_erase]
  exact Finset.sum_erase_add Finset.univ
    (fun candidate => (state.pending candidate).card) (Finset.mem_univ index)

def State.empty : State Index :=
  { pending := fun _ => ∅
    revealed := fun _ => none }

omit [DecidableEq Index] in
@[simp]
theorem State.pendingCount_empty : (State.empty : State Index).pendingCount = 0 := by
  simp [State.empty, State.pendingCount]

noncomputable def State.pendingEntries (state : State Index) : List (Finset Digest) :=
  (Finset.univ.toList : List Index).map state.pending

omit [DecidableEq Index] in
theorem pendingEntries_card_sum (state : State Index) :
    (state.pendingEntries.map Finset.card).sum = state.pendingCount := by
  simp [State.pendingEntries, State.pendingCount, List.map_map]

noncomputable def finalizePending : List (Finset Digest) → ProbComp Bool :=
  fun entries => match entries with
  | [] => pure false
  | targets :: rest => (do
      let output ← $ᵗ HashOutput
      if truncateHash output ∈ targets then
        pure true
      else
        finalizePending rest)

@[simp]
theorem finalizePending_nil : finalizePending [] = pure false := rfl

theorem finalizePending_cons (targets : Finset Digest) (rest : List (Finset Digest)) :
    finalizePending (targets :: rest) = (do
      let output ← $ᵗ HashOutput
      if truncateHash output ∈ targets then
        pure true
      else
        finalizePending rest) := rfl

theorem finalizePending_true_probability_le :
    ∀ entries : List (Finset Digest),
      Pr[(fun hit : Bool => hit = true) | finalizePending entries] ≤
        (entries.map Finset.card).sum *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  intro entries
  induction entries with
  | nil => simp [finalizePending]
  | cons targets rest ih =>
      rw [finalizePending_cons]
      refine (probEvent_bind_le_probEvent_add
        (mx := ($ᵗ HashOutput))
        (my := fun output =>
          if truncateHash output ∈ targets then pure true
          else finalizePending rest)
        (q := fun hit : Bool => hit = true)
        (p := fun output : HashOutput => truncateHash output ∈ targets)
        (ε := (rest.map Finset.card).sum *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ?_).trans ?_
      · intro output _ hmiss
        simp only [hmiss, ↓reduceIte]
        exact ih
      · refine add_le_add
          (EncodingMonitor.uniform_truncate_mem_finset_le targets) le_rfl |>.trans ?_
        simp only [List.map_cons, List.sum_cons, Nat.cast_add]
        rw [add_mul]

omit [DecidableEq Index] in
theorem finalizeState_true_probability_le (state : State Index) :
    Pr[(fun hit : Bool => hit = true) | finalizePending state.pendingEntries] ≤
      (state.pendingCount : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  simpa [pendingEntries_card_sum] using
    (finalizePending_true_probability_le state.pendingEntries)

inductive ControllerAction (σ Index : Type) where
  | stop
  | skip (next : σ)
  | probe (index : Index) (target : Digest) (next : Bool → σ)
  | reveal (index : Index) (next : Digest → σ)

noncomputable def run {σ : Type}
    (controller : σ → ProbComp (ControllerAction σ Index))
    (state : State Index) (steps fuel : Nat) (control : σ) : ProbComp Bool :=
  match steps with
  | 0 => finalizePending state.pendingEntries
  | steps + 1 => do
      let action ← controller control
      match action with
      | .stop => finalizePending state.pendingEntries
      | .skip next => run controller state steps fuel next
      | .probe index target next =>
          match fuel with
          | 0 => finalizePending state.pendingEntries
          | remaining + 1 =>
              match state.revealed index with
              | some _ => run controller state steps remaining (next false)
              | none =>
                  run controller (state.addPending index target) steps remaining
                    (next false)
      | .reveal index next =>
          match state.revealed index with
          | some value => run controller state steps fuel (next value)
          | none => do
              let output ← $ᵗ HashOutput
              let value := truncateHash output
              if value ∈ state.pending index then
                pure true
              else
                run controller (state.install index value) steps fuel (next value)

/-- Arbitrary probabilistic control, public side information, and adaptive disclosures cannot make more than `q` unrevealed equality guesses cost more than `q / 2^128`. -/
theorem run_true_probability_le {σ : Type}
    (controller : σ → ProbComp (ControllerAction σ Index))
    (state : State Index) (steps fuel : Nat) (control : σ) :
    Pr[(fun hit : Bool => hit = true) |
      run controller state steps fuel control] ≤
      ((fuel + state.pendingCount : Nat) : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  induction steps generalizing state fuel control with
  | zero =>
      refine (finalizeState_true_probability_le state).trans ?_
      gcongr
      omega
  | succ steps ih =>
      rw [run]
      refine probEvent_bind_le_of_forall_le fun action _haction => ?_
      cases action with
      | stop =>
          refine (finalizeState_true_probability_le state).trans ?_
          gcongr
          omega
      | skip next => exact ih state fuel next
      | probe index target next =>
          cases fuel with
          | zero =>
              simp only
              simpa using finalizeState_true_probability_le state
          | succ remaining =>
              cases hrevealed : state.revealed index with
              | some value =>
                  simp only
                  rw [hrevealed]
                  change Pr[(fun hit : Bool => hit = true) |
                    run controller state steps remaining (next false)] ≤ _
                  refine (ih state remaining (next false)).trans ?_
                  gcongr
                  omega
              | none =>
                  simp only
                  rw [hrevealed]
                  change Pr[(fun hit : Bool => hit = true) |
                    run controller (state.addPending index target) steps remaining
                      (next false)] ≤ _
                  refine (ih (state.addPending index target) remaining (next false)).trans ?_
                  have hadd := state.pendingCount_addPending_le index target
                  have hnat : remaining + (state.addPending index target).pendingCount ≤
                      remaining + 1 + state.pendingCount := by omega
                  exact mul_le_mul_left (by exact_mod_cast hnat)
                    (((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹)
      | reveal index next =>
          cases hrevealed : state.revealed index with
          | some value =>
              simp only
              rw [hrevealed]
              change Pr[(fun hit : Bool => hit = true) |
                run controller state steps fuel (next value)] ≤ _
              exact ih state fuel (next value)
          | none =>
              simp only
              rw [hrevealed]
              change Pr[(fun hit : Bool => hit = true) |
                ($ᵗ HashOutput) >>= fun output =>
                  let value := truncateHash output
                  if value ∈ state.pending index then pure true
                  else run controller (state.install index value) steps fuel
                    (next value)] ≤ _
              refine (probEvent_bind_le_probEvent_add
                (mx := ($ᵗ HashOutput))
                (my := fun output =>
                  let value := truncateHash output
                  if value ∈ state.pending index then pure true
                  else run controller (state.install index value) steps fuel
                    (next value))
                (q := fun hit : Bool => hit = true)
                (p := fun output : HashOutput =>
                  truncateHash output ∈ state.pending index)
                (ε := ((fuel + (state.install index 0).pendingCount : Nat) : ℝ≥0∞) *
                  ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ?_).trans ?_
              · intro output _ hmiss
                simp only [hmiss, ↓reduceIte]
                have hcount :
                    (state.install index (truncateHash output)).pendingCount =
                      (state.install index 0).pendingCount := rfl
                simpa [hcount] using
                  ih (state.install index (truncateHash output)) fuel
                    (next (truncateHash output))
              · refine add_le_add
                  (EncodingMonitor.uniform_truncate_mem_finset_le
                    (state.pending index)) le_rfl |>.trans ?_
                have hconserve := state.pendingCount_install_add index 0
                rw [← add_mul]
                gcongr
                rw [← Nat.cast_add]
                exact Nat.cast_le.mpr (by omega)

theorem run_empty_true_probability_le {σ : Type}
    (controller : σ → ProbComp (ControllerAction σ Index))
    (steps fuel : Nat) (control : σ) :
    Pr[(fun hit : Bool => hit = true) |
      run controller State.empty steps fuel control] ≤
      (fuel : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  simpa [div_eq_mul_inv] using
    run_true_probability_le controller (State.empty : State Index) steps fuel control

end XmssSecurity.AdaptiveRevealMonitor
