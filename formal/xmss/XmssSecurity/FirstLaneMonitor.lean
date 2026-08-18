import XmssSecurity.AdaptiveRevealMonitor
import XmssSecurity.CappedEncodingMonitor

open OracleComp ENNReal

namespace XmssSecurity.FirstLaneMonitor

variable {Index : Type} [Fintype Index] [DecidableEq Index]

inductive ControllerAction (Control Index : Type) where
  | stop
  | skip (next : Control)
  | encodingQuery (epoch : Epoch) (next : HashOutput → Control)
  | encodingSignAttempt (epoch : Epoch) (next : HashOutput → Control)
  | probe (index : Index) (target : Digest) (next : Bool → Control)
  | reveal (index : Index) (next : Digest → Control)

noncomputable def run {Control : Type}
    (controller : Control → ProbComp (ControllerAction Control Index)) :
    EncodingMonitor.State → AdaptiveRevealMonitor.State Index →
      Nat → Nat → Control → ProbComp Bool
  | _encodingState, chainState, 0, _fuel, _control =>
      AdaptiveRevealMonitor.finalizePending chainState.pendingEntries
  | encodingState, chainState, steps + 1, fuel, control => do
      let action ← controller control
      match action with
      | .stop =>
          AdaptiveRevealMonitor.finalizePending chainState.pendingEntries
      | .skip next =>
          run controller encodingState chainState steps fuel next
      | .encodingQuery epoch next =>
          match fuel with
          | 0 => AdaptiveRevealMonitor.finalizePending chainState.pendingEntries
          | remaining + 1 =>
              CappedEncodingMonitor.applyProgrammedQueryMonitor epoch
                (fun output nextEncodingState =>
                  run controller nextEncodingState chainState steps remaining
                    (next output)) encodingState
      | .encodingSignAttempt epoch next =>
          CappedEncodingMonitor.applyProgrammedSignAttemptMonitor epoch
            (fun output nextEncodingState =>
              run controller nextEncodingState chainState steps fuel
                (next output)) encodingState
      | .probe index target next =>
          match fuel with
          | 0 => AdaptiveRevealMonitor.finalizePending chainState.pendingEntries
          | remaining + 1 =>
              match chainState.revealed index with
              | some _ =>
                  run controller encodingState chainState steps remaining
                    (next false)
              | none =>
                  run controller encodingState
                    (chainState.addPending index target) steps remaining
                    (next false)
      | .reveal index next =>
          match chainState.revealed index with
          | some value =>
              run controller encodingState chainState steps fuel (next value)
          | none => do
              let output ← $ᵗ HashOutput
              let value := truncateHash output
              if value ∈ chainState.pending index then pure true
              else
                run controller encodingState (chainState.install index value)
                  steps fuel (next value)

theorem run_true_probability_le {Control : Type}
    (controller : Control → ProbComp (ControllerAction Control Index))
    (encodingState : EncodingMonitor.State)
    (chainState : AdaptiveRevealMonitor.State Index)
    (steps fuel : Nat) (control : Control) :
    Pr[(· = true) |
      run controller encodingState chainState steps fuel control] ≤
      ((fuel + chainState.pendingCount : Nat) : ENNReal) *
          (Fintype.card Digest : ENNReal)⁻¹ +
        CappedEncodingMonitor.State.pendingRisk encodingState := by
  induction steps generalizing encodingState chainState fuel control with
  | zero =>
      refine (AdaptiveRevealMonitor.finalizeState_true_probability_le
        chainState).trans ?_
      rw [show (Fintype.card Digest : ENNReal) =
        ((2 ^ digestBits : Nat) : ENNReal) by norm_num [digestBits]]
      apply le_add_right
      gcongr
      omega
  | succ steps ih =>
      rw [run]
      refine probEvent_bind_le_of_forall_le fun action _ => ?_
      cases action with
      | stop =>
          refine (AdaptiveRevealMonitor.finalizeState_true_probability_le
            chainState).trans ?_
          rw [show (Fintype.card Digest : ENNReal) =
            ((2 ^ digestBits : Nat) : ENNReal) by norm_num [digestBits]]
          apply le_add_right
          gcongr
          omega
      | skip next =>
          exact ih encodingState chainState fuel next
      | encodingQuery epoch next =>
          cases fuel with
          | zero =>
              simp only
              refine (AdaptiveRevealMonitor.finalizeState_true_probability_le
                chainState).trans ?_
              rw [show (Fintype.card Digest : ENNReal) =
                ((2 ^ digestBits : Nat) : ENNReal) by norm_num [digestBits]]
              apply le_add_right
              gcongr
              omega
          | succ remaining =>
              simp only
              simpa [Nat.succ_add] using
                CappedEncodingMonitor.applyProgrammedQueryMonitor_true_probability_le
                  epoch
                  (fun output nextEncodingState =>
                    run controller nextEncodingState chainState steps remaining
                      (next output)) encodingState
                  (remaining + chainState.pendingCount)
                  (fun output nextEncodingState =>
                    ih nextEncodingState chainState remaining (next output))
      | encodingSignAttempt epoch next =>
          simp only
          exact
            CappedEncodingMonitor.applyProgrammedSignAttemptMonitor_true_probability_le
              epoch
              (fun output nextEncodingState =>
                run controller nextEncodingState chainState steps fuel
                  (next output)) encodingState
              (fuel + chainState.pendingCount)
              (fun output nextEncodingState =>
                ih nextEncodingState chainState fuel (next output))
      | probe index target next =>
          cases fuel with
          | zero =>
              simp only
              refine (AdaptiveRevealMonitor.finalizeState_true_probability_le
                chainState).trans ?_
              rw [show (Fintype.card Digest : ENNReal) =
                ((2 ^ digestBits : Nat) : ENNReal) by norm_num [digestBits]]
              apply le_add_right
              gcongr
              omega
          | succ remaining =>
              cases hrevealed : chainState.revealed index with
              | some value =>
                  simp only
                  rw [hrevealed]
                  change Pr[(· = true) |
                    run controller encodingState chainState steps remaining
                      (next false)] ≤ _
                  refine (ih encodingState chainState remaining
                    (next false)).trans ?_
                  gcongr
                  omega
              | none =>
                  simp only
                  rw [hrevealed]
                  change Pr[(· = true) |
                    run controller encodingState
                      (chainState.addPending index target) steps remaining
                      (next false)] ≤ _
                  refine (ih encodingState
                    (chainState.addPending index target) remaining
                    (next false)).trans ?_
                  have hadd := chainState.pendingCount_addPending_le index target
                  have hnat : remaining +
                      (chainState.addPending index target).pendingCount ≤
                    remaining.succ + chainState.pendingCount := by omega
                  exact add_le_add
                    (mul_le_mul_left
                      (by exact_mod_cast hnat :
                        ((remaining +
                          (chainState.addPending index target).pendingCount : Nat) :
                            ENNReal) ≤
                          ((remaining.succ + chainState.pendingCount : Nat) :
                            ENNReal)) _)
                    le_rfl
      | reveal index next =>
          cases hrevealed : chainState.revealed index with
          | some value =>
              simp only
              rw [hrevealed]
              change Pr[(· = true) |
                run controller encodingState chainState steps fuel
                  (next value)] ≤ _
              exact ih encodingState chainState fuel (next value)
          | none =>
              simp only
              rw [hrevealed]
              change Pr[(· = true) | ($ᵗ HashOutput) >>= fun output =>
                let value := truncateHash output
                if value ∈ chainState.pending index then pure true
                else run controller encodingState
                  (chainState.install index value) steps fuel (next value)] ≤ _
              refine (probEvent_bind_le_probEvent_add
                (mx := ($ᵗ HashOutput))
                (my := fun output =>
                  let value := truncateHash output
                  if value ∈ chainState.pending index then pure true
                  else run controller encodingState
                    (chainState.install index value) steps fuel (next value))
                (q := fun hit : Bool => hit = true)
                (p := fun output : HashOutput =>
                  truncateHash output ∈ chainState.pending index)
                (ε := ((fuel +
                    (chainState.install index 0).pendingCount : Nat) : ENNReal) *
                      (Fintype.card Digest : ENNReal)⁻¹ +
                    CappedEncodingMonitor.State.pendingRisk encodingState) ?_).trans ?_
              · intro output _ hmiss
                simp only [hmiss, ↓reduceIte]
                have hcount :
                    (chainState.install index
                      (truncateHash output)).pendingCount =
                    (chainState.install index 0).pendingCount := rfl
                simpa [hcount] using ih encodingState
                  (chainState.install index (truncateHash output)) fuel
                  (next (truncateHash output))
              · refine add_le_add
                  (EncodingMonitor.uniform_truncate_mem_finset_le
                    (chainState.pending index)) le_rfl |>.trans ?_
                have hconserve := chainState.pendingCount_install_add index 0
                rw [show (Fintype.card Digest : ENNReal) =
                  ((2 ^ digestBits : Nat) : ENNReal) by norm_num [digestBits]]
                have hnat :
                  (chainState.pending index).card +
                      (fuel + (chainState.install index 0).pendingCount) ≤
                    fuel + chainState.pendingCount := by omega
                calc
                  ((chainState.pending index).card : ENNReal) *
                        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
                      (((fuel +
                          (chainState.install index 0).pendingCount : Nat) :
                            ENNReal) *
                          ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
                        CappedEncodingMonitor.State.pendingRisk encodingState) =
                    (((chainState.pending index).card +
                        (fuel +
                          (chainState.install index 0).pendingCount) : Nat) :
                          ENNReal) *
                        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
                      CappedEncodingMonitor.State.pendingRisk encodingState := by
                        push_cast
                        ring
                  _ ≤ ((fuel + chainState.pendingCount : Nat) : ENNReal) *
                        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
                      CappedEncodingMonitor.State.pendingRisk encodingState := by
                    gcongr

theorem run_empty_true_probability_le {Control : Type}
    (controller : Control → ProbComp (ControllerAction Control Index))
    (steps fuel : Nat) (control : Control) :
    Pr[(· = true) |
      run controller EncodingMonitor.State.empty
        AdaptiveRevealMonitor.State.empty steps fuel control] ≤
      (fuel : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
  simpa [AdaptiveRevealMonitor.State.pendingCount_empty,
    CappedEncodingMonitor.State.pendingRisk_empty, div_eq_mul_inv,
    digestBits] using
      run_true_probability_le controller EncodingMonitor.State.empty
        (AdaptiveRevealMonitor.State.empty :
          AdaptiveRevealMonitor.State Index) steps fuel control

end XmssSecurity.FirstLaneMonitor
