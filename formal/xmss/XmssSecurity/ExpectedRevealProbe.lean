import XmssSecurity.AdaptiveRevealMonitor

open OracleComp ENNReal

namespace XmssSecurity.AdaptiveRevealMonitor

variable {Index : Type} [Fintype Index] [DecidableEq Index]

noncomputable def expectedProbeCount {σ : Type}
    (controller : σ → ProbComp (ControllerAction σ Index)) :
    State Index → Nat → σ → ENNReal
  | _state, 0, _control => 0
  | state, steps + 1, control =>
      ∑' action, Pr[= action | controller control] *
        match action with
        | .stop => 0
        | .skip next => expectedProbeCount controller state steps next
        | .probe index target next =>
            1 + expectedProbeCount controller
              (match state.revealed index with
               | some _ => state
               | none => state.addPending index target)
              steps (next false)
        | .reveal index next =>
            match state.revealed index with
            | some value => expectedProbeCount controller state steps (next value)
            | none =>
                ∑' output, Pr[= output | $ᵗ HashOutput] *
                  expectedProbeCount controller
                    (state.install index (truncateHash output)) steps
                    (next (truncateHash output))

noncomputable def runExpected {σ : Type}
    (controller : σ → ProbComp (ControllerAction σ Index)) :
    State Index → Nat → σ → ProbComp Bool
  | state, 0, _control => finalizePending state.pendingEntries
  | state, steps + 1, control => do
      let action ← controller control
      match action with
      | .stop => finalizePending state.pendingEntries
      | .skip next => runExpected controller state steps next
      | .probe index target next =>
          match state.revealed index with
          | some _ => runExpected controller state steps (next false)
          | none =>
              (runExpected controller (state.addPending index target)
                steps (next false))
      | .reveal index next =>
          match state.revealed index with
          | some value => runExpected controller state steps (next value)
          | none => do
              let output ← $ᵗ HashOutput
              let value := truncateHash output
              if value ∈ state.pending index then pure true
              else
                (runExpected controller (state.install index value) steps
                  (next value))

set_option maxHeartbeats 1000000 in
theorem runExpected_true_probability_le_expectedProbeCount {σ : Type}
    (controller : σ → ProbComp (ControllerAction σ Index))
    (state : State Index) (steps : Nat) (control : σ) :
    Pr[(· = true) | runExpected controller state steps control] ≤
      (expectedProbeCount controller state steps control + state.pendingCount) *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  induction steps generalizing state control with
  | zero =>
      exact (finalizeState_true_probability_le state).trans
        (by simp [expectedProbeCount])
  | succ steps ih =>
      rw [runExpected, probEvent_bind_eq_tsum]
      let actionCost : ControllerAction σ Index → ENNReal
        | .stop => 0
        | .skip next => expectedProbeCount controller state steps next
        | .probe index target next =>
            1 + expectedProbeCount controller
              (match state.revealed index with
               | some _ => state
               | none => state.addPending index target)
              steps (next false)
        | .reveal index next =>
            match state.revealed index with
            | some value => expectedProbeCount controller state steps (next value)
            | none =>
                ∑' output, Pr[= output | $ᵗ HashOutput] *
                  expectedProbeCount controller
                    (state.install index (truncateHash output)) steps
                    (next (truncateHash output))
      have haction (action : ControllerAction σ Index) :
          Pr[(· = true) |
            match action with
            | .stop => finalizePending state.pendingEntries
            | .skip next => runExpected controller state steps next
            | .probe index target next =>
                match state.revealed index with
                | some _ => runExpected controller state steps (next false)
                | none =>
                    (runExpected controller (state.addPending index target)
                      steps (next false))
            | .reveal index next =>
                match state.revealed index with
                | some value => runExpected controller state steps (next value)
                | none => do
                    let output ← $ᵗ HashOutput
                    let value := truncateHash output
                    if value ∈ state.pending index then pure true
                    else
                      (runExpected controller (state.install index value) steps
                        (next value))] ≤
            (actionCost action + state.pendingCount) *
              ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
        cases action with
        | stop =>
            exact (finalizeState_true_probability_le state).trans (by simp [actionCost])
        | skip next =>
            simpa [actionCost, add_mul] using ih state next
        | probe index target next =>
            cases hrevealed : state.revealed index with
            | some value =>
                simp only [hrevealed]
                refine (ih state (next false)).trans ?_
                simp only [actionCost, hrevealed]
                gcongr
                exact le_add_left le_rfl
            | none =>
                simp only [hrevealed]
                refine (ih (state.addPending index target) (next false)).trans ?_
                simp only [actionCost, hrevealed]
                apply mul_le_mul_left
                calc
                  expectedProbeCount controller (state.addPending index target)
                        steps (next false) +
                      (state.addPending index target).pendingCount ≤
                    expectedProbeCount controller (state.addPending index target)
                        steps (next false) + (state.pendingCount + 1) := by
                          gcongr
                          exact_mod_cast state.pendingCount_addPending_le index target
                  _ = ((1 : Nat) : ENNReal) + expectedProbeCount controller
                        (state.addPending index target) steps (next false) +
                      state.pendingCount := by
                    norm_num
                    ac_rfl
        | reveal index next =>
            cases hrevealed : state.revealed index with
            | some value =>
                simpa [actionCost, hrevealed] using ih state (next value)
            | none =>
                simp only [actionCost, hrevealed]
                rw [probEvent_bind_eq_tsum]
                let continuationCost : HashOutput → ENNReal := fun output =>
                  expectedProbeCount controller
                    (state.install index (truncateHash output)) steps
                    (next (truncateHash output))
                calc
                  ∑' output, Pr[= output | $ᵗ HashOutput] *
                      Pr[(· = true) |
                        if truncateHash output ∈ state.pending index then pure true
                        else runExpected controller
                          (state.install index (truncateHash output)) steps
                          (next (truncateHash output))] ≤
                    ∑' output, ((if truncateHash output ∈ state.pending index then
                        Pr[= output | $ᵗ HashOutput] else 0) +
                      Pr[= output | $ᵗ HashOutput] *
                        ((continuationCost output +
                          (state.install index (truncateHash output)).pendingCount) *
                            ((2 ^ digestBits : Nat) : ENNReal)⁻¹)) := by
                      apply ENNReal.tsum_le_tsum
                      intro output
                      by_cases hhit : truncateHash output ∈ state.pending index
                      · simp [hhit]
                      · simp only [hhit, if_false, zero_add]
                        exact mul_le_mul' le_rfl
                          (by simpa [continuationCost] using
                            (ih (state.install index (truncateHash output))
                              (next (truncateHash output))))
                  _ ≤ ((state.pending index).card : ENNReal) *
                        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
                      ((∑' output, Pr[= output | $ᵗ HashOutput] *
                          continuationCost output) +
                        (state.install index 0).pendingCount) *
                          ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
                    rw [ENNReal.tsum_add]
                    apply add_le_add
                    · rw [← probEvent_eq_tsum_ite]
                      exact EncodingMonitor.uniform_truncate_mem_finset_le
                        (state.pending index)
                    · simp_rw [← mul_assoc]
                      rw [ENNReal.tsum_mul_right]
                      gcongr
                      calc
                        ∑' output, Pr[= output | $ᵗ HashOutput] *
                            (continuationCost output +
                              (state.install index (truncateHash output)).pendingCount) =
                          (∑' output, Pr[= output | $ᵗ HashOutput] *
                            continuationCost output) +
                          ∑' output, Pr[= output | $ᵗ HashOutput] *
                            (state.install index 0).pendingCount := by
                              simp_rw [show ∀ output : HashOutput,
                                (state.install index (truncateHash output)).pendingCount =
                                  (state.install index 0).pendingCount from fun _ => rfl,
                                mul_add]
                              rw [ENNReal.tsum_add]
                        _ ≤ (∑' output, Pr[= output | $ᵗ HashOutput] *
                              continuationCost output) +
                            (state.install index 0).pendingCount := by
                              gcongr
                              rw [ENNReal.tsum_mul_right]
                              exact mul_le_of_le_one_left (by finiteness)
                                tsum_probOutput_le_one
                  _ = ((∑' output, Pr[= output | $ᵗ HashOutput] *
                          continuationCost output) + state.pendingCount) *
                        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
                    rw [← add_mul]
                    congr 1
                    calc
                      ((state.pending index).card : ENNReal) +
                          ((∑' output, Pr[= output | $ᵗ HashOutput] *
                              continuationCost output) +
                            (state.install index 0).pendingCount) =
                        (∑' output, Pr[= output | $ᵗ HashOutput] *
                            continuationCost output) +
                          ((state.install index 0).pendingCount +
                            (state.pending index).card) := by ac_rfl
                      _ = (∑' output, Pr[= output | $ᵗ HashOutput] *
                              continuationCost output) + state.pendingCount := by
                        congr 1
                        exact_mod_cast state.pendingCount_install_add index 0
      calc
        ∑' action, Pr[= action | controller control] *
            Pr[(· = true) |
              match action with
              | .stop => finalizePending state.pendingEntries
              | .skip next => runExpected controller state steps next
              | .probe index target next =>
                  match state.revealed index with
                  | some _ => runExpected controller state steps (next false)
                  | none => runExpected controller (state.addPending index target)
                      steps (next false)
              | .reveal index next =>
                  match state.revealed index with
                  | some value => runExpected controller state steps (next value)
                  | none => do
                      let output ← $ᵗ HashOutput
                      let value := truncateHash output
                      if value ∈ state.pending index then pure true
                      else
                        (runExpected controller (state.install index value) steps
                          (next value))] ≤
          ∑' action, Pr[= action | controller control] *
            ((actionCost action + state.pendingCount) *
              ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
                apply ENNReal.tsum_le_tsum
                intro action
                exact mul_le_mul' le_rfl (haction action)
        _ ≤ ((∑' action, Pr[= action | controller control] * actionCost action) +
              state.pendingCount) *
            ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
          simp_rw [← mul_assoc]
          rw [ENNReal.tsum_mul_right]
          gcongr
          simp_rw [mul_add]
          rw [ENNReal.tsum_add]
          apply add_le_add_right
          rw [ENNReal.tsum_mul_right]
          exact mul_le_of_le_one_left (by finiteness) tsum_probOutput_le_one
        _ = _ := by
          rfl

theorem runExpected_empty_true_probability_le_expectedProbeCount {σ : Type}
    (controller : σ → ProbComp (ControllerAction σ Index))
    (steps : Nat) (control : σ) :
    Pr[(· = true) | runExpected controller State.empty steps control] ≤
      expectedProbeCount controller State.empty steps control /
        ((2 ^ digestBits : Nat) : ENNReal) := by
  simpa [div_eq_mul_inv] using
    runExpected_true_probability_le_expectedProbeCount controller
      (State.empty : State Index) steps control

end XmssSecurity.AdaptiveRevealMonitor
