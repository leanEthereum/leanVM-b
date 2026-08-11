import XmssSecurity.AdaptiveFreshTarget
import VCVio.OracleComp.Constructions.SampleableType

open OracleComp ENNReal
open scoped BigOperators

namespace XmssSecurity.EncodingMonitor

set_option maxRecDepth 100000

structure State where
  pending : Epoch → Finset Digest
  signed : Epoch → Option Digest

def State.pendingCount (state : State) : Nat :=
  ∑ epoch, (state.pending epoch).card

def State.addPending (state : State) (epoch : Epoch) (digest : Digest) : State :=
  { state with pending := Function.update state.pending epoch (insert digest (state.pending epoch)) }

def State.install (state : State) (epoch : Epoch) (digest : Digest) : State :=
  { pending := Function.update state.pending epoch ∅
    signed := Function.update state.signed epoch (some digest) }

theorem State.pendingCount_addPending_le (state : State) (epoch : Epoch)
    (digest : Digest) :
    (state.addPending epoch digest).pendingCount ≤ state.pendingCount + 1 := by
  classical
  unfold pendingCount addPending
  change (∑ candidate,
      (Function.update state.pending epoch
        (insert digest (state.pending epoch)) candidate).card) ≤ _
  have hupdate :
      (fun candidate =>
        (Function.update state.pending epoch
          (insert digest (state.pending epoch)) candidate).card) =
        Function.update (fun candidate => (state.pending candidate).card) epoch
          (insert digest (state.pending epoch)).card := by
    funext candidate
    by_cases heq : candidate = epoch <;> simp [heq]
  rw [hupdate]
  rw [Finset.sum_update_of_mem (Finset.mem_univ epoch)]
  have hsum := Finset.sum_erase_add Finset.univ
    (fun candidate => (state.pending candidate).card) (Finset.mem_univ epoch)
  calc
    (insert digest (state.pending epoch)).card +
        ∑ candidate ∈ Finset.univ \ {epoch}, (state.pending candidate).card ≤
      ((state.pending epoch).card + 1) +
        ∑ candidate ∈ Finset.univ \ {epoch}, (state.pending candidate).card := by
          gcongr
          exact Finset.card_insert_le digest (state.pending epoch)
    _ = (∑ candidate ∈ Finset.univ \ {epoch},
          (state.pending candidate).card) + (state.pending epoch).card + 1 := by
      omega
    _ = (∑ candidate, (state.pending candidate).card) + 1 := by
      rw [Finset.sdiff_singleton_eq_erase, hsum]

theorem State.pendingCount_install_add (state : State) (epoch : Epoch)
    (digest : Digest) :
    (state.install epoch digest).pendingCount + (state.pending epoch).card =
      state.pendingCount := by
  classical
  unfold pendingCount install
  change (∑ candidate,
      (Function.update state.pending epoch ∅ candidate).card) +
        (state.pending epoch).card = _
  have hupdate :
      (fun candidate =>
        (Function.update state.pending epoch ∅ candidate).card) =
        Function.update (fun candidate => (state.pending candidate).card) epoch 0 := by
    funext candidate
    by_cases heq : candidate = epoch <;> simp [heq]
  rw [hupdate]
  rw [Finset.sum_update_of_mem (Finset.mem_univ epoch)]
  rw [zero_add, Finset.sdiff_singleton_eq_erase]
  exact Finset.sum_erase_add Finset.univ
    (fun candidate => (state.pending candidate).card) (Finset.mem_univ epoch)

theorem State.pendingCount_install_eq (state : State) (epoch : Epoch)
    (left right : Digest) :
    (state.install epoch left).pendingCount =
      (state.install epoch right).pendingCount := by
  rfl

def State.empty : State :=
  { pending := fun _ => ∅
    signed := fun _ => none }

@[simp]
theorem State.pendingCount_empty : State.empty.pendingCount = 0 := by
  unfold empty pendingCount
  simp

attribute [irreducible] State.pendingCount

inductive Action where
  | query (epoch : Epoch)
  | sign (epoch : Epoch)
  | stop

noncomputable def run : State → Nat → (List HashOutput → Action) → ProbComp Bool
  | _state, 0, _strategy => pure false
  | state, fuel + 1, strategy =>
      match strategy [] with
      | .stop => pure false
      | .query epoch => do
          let output ← $ᵗ HashOutput
          let digest := truncateHash output
          match state.signed epoch with
          | some target =>
              if digest = target then
                pure true
              else
                run state fuel (fun history => strategy (output :: history))
          | none =>
              run (state.addPending epoch digest) fuel
                (fun history => strategy (output :: history))
      | .sign epoch =>
          match state.signed epoch with
          | some _ => pure false
          | none => do
              let output ← $ᵗ HashOutput
              let digest := truncateHash output
              if digest ∈ state.pending epoch then
                pure true
              else
                run (state.install epoch digest) fuel
                  (fun history => strategy (output :: history))

theorem uniform_truncate_mem_finset_le (targets : Finset Digest) :
    Pr[fun output : HashOutput => truncateHash output ∈ targets | $ᵗ HashOutput] ≤
      (targets.card : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  have hevent :
      (fun output : HashOutput => truncateHash output ∈ targets) =
      (fun output : HashOutput => ∃ target ∈ targets,
        truncateHash output = target) := by
    funext output
    apply propext
    constructor
    · intro hmem
      exact ⟨truncateHash output, hmem, rfl⟩
    · rintro ⟨target, hmem, heq⟩
      exact heq ▸ hmem
  rw [hevent]
  calc
    Pr[fun output : HashOutput => ∃ target ∈ targets,
          truncateHash output = target |
        $ᵗ HashOutput] ≤
      ∑ target ∈ targets,
        Pr[fun output : HashOutput => truncateHash output = target |
          $ᵗ HashOutput] :=
      probEvent_exists_finset_le_sum targets ($ᵗ HashOutput)
        (fun target output => truncateHash output = target)
    _ = ∑ _target ∈ targets,
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      apply Finset.sum_congr rfl
      intro target _
      exact Rom.uniform_truncate_probability target
    _ = (targets.card : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      rw [Finset.sum_const, nsmul_eq_mul]

/-- Each fresh encoding entry is charged at most once: when its epoch target is installed if it came before signing, or when the entry is sampled if it came after signing. -/
theorem run_true_probability_le (state : State) (fuel : Nat)
    (strategy : List HashOutput → Action) :
    Pr[(fun hit : Bool => hit = true) | run state fuel strategy] ≤
      ((fuel + state.pendingCount : Nat) : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  induction fuel generalizing state strategy with
  | zero =>
      rw [run, probEvent_pure]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact zero_le
  | succ fuel ih =>
      cases haction : strategy [] with
      | stop =>
          rw [run, haction]
          change Pr[(fun hit : Bool => hit = true) | (pure false : ProbComp Bool)] ≤ _
          rw [probEvent_pure]
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact zero_le
      | query epoch =>
          cases hsigned : state.signed epoch with
          | none =>
              rw [run, haction]
              change Pr[(fun hit : Bool => hit = true) |
                ($ᵗ HashOutput) >>= fun output =>
                  match state.signed epoch with
                  | some target =>
                      if truncateHash output = target then pure true
                      else run state fuel
                        (fun history => strategy (output :: history))
                  | none =>
                      run (state.addPending epoch (truncateHash output)) fuel
                        (fun history => strategy (output :: history))] ≤ _
              rw [hsigned]
              refine probEvent_bind_le_of_forall_le
                (mx := ($ᵗ HashOutput))
                (my := fun output =>
                  run (state.addPending epoch (truncateHash output)) fuel
                    (fun history => strategy (output :: history)))
                (q := fun hit : Bool => hit = true) fun output _ => ?_
              refine (ih (state.addPending epoch (truncateHash output))
                (fun history => strategy (output :: history))).trans ?_
              have hcount := state.pendingCount_addPending_le epoch
                (truncateHash output)
              have hnat : fuel + (state.addPending epoch
                    (truncateHash output)).pendingCount ≤
                  fuel.succ + state.pendingCount := by
                calc
                  fuel + (state.addPending epoch
                      (truncateHash output)).pendingCount ≤
                    fuel + (state.pendingCount + 1) :=
                      Nat.add_le_add_left hcount fuel
                  _ = fuel.succ + state.pendingCount := by omega
              exact mul_le_mul' (Nat.cast_le.mpr hnat) le_rfl
          | some target =>
              rw [run, haction]
              change Pr[(fun hit : Bool => hit = true) |
                ($ᵗ HashOutput) >>= fun output =>
                  match state.signed epoch with
                  | some target =>
                      if truncateHash output = target then pure true
                      else run state fuel
                        (fun history => strategy (output :: history))
                  | none =>
                      run (state.addPending epoch (truncateHash output)) fuel
                        (fun history => strategy (output :: history))] ≤ _
              rw [hsigned]
              refine (probEvent_bind_le_probEvent_add
                (mx := ($ᵗ HashOutput))
                (my := fun output =>
                  if truncateHash output = target then pure true
                  else run state fuel
                    (fun history => strategy (output :: history)))
                (q := fun hit : Bool => hit = true)
                (p := fun output : HashOutput => truncateHash output = target)
                (ε := ((fuel + state.pendingCount : Nat) : ℝ≥0∞) *
                  ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ?_).trans ?_
              · intro output _ hmiss
                simp only [hmiss, ↓reduceIte]
                exact ih state (fun history => strategy (output :: history))
              · rw [Rom.uniform_truncate_probability]
                push_cast
                ring_nf
                exact le_rfl
      | sign epoch =>
          cases hsigned : state.signed epoch with
          | some target =>
              rw [run, haction]
              change Pr[(fun hit : Bool => hit = true) |
                match state.signed epoch with
                | some _ => pure false
                | none => ($ᵗ HashOutput) >>= fun output =>
                    if truncateHash output ∈ state.pending epoch then pure true
                    else run (state.install epoch (truncateHash output)) fuel
                      (fun history => strategy (output :: history))] ≤ _
              rw [hsigned, probEvent_pure]
              simp only [Bool.false_eq_true, ↓reduceIte]
              exact zero_le
          | none =>
              rw [run, haction]
              change Pr[(fun hit : Bool => hit = true) |
                match state.signed epoch with
                | some _ => pure false
                | none => ($ᵗ HashOutput) >>= fun output =>
                    if truncateHash output ∈ state.pending epoch then pure true
                    else run (state.install epoch (truncateHash output)) fuel
                      (fun history => strategy (output :: history))] ≤ _
              rw [hsigned]
              refine (probEvent_bind_le_probEvent_add
                (mx := ($ᵗ HashOutput))
                (my := fun output =>
                  if truncateHash output ∈ state.pending epoch then pure true
                  else run (state.install epoch (truncateHash output)) fuel
                    (fun history => strategy (output :: history)))
                (q := fun hit : Bool => hit = true)
                (p := fun output : HashOutput =>
                  truncateHash output ∈ state.pending epoch)
                (ε := ((fuel + (state.install epoch 0).pendingCount : Nat) : ℝ≥0∞) *
                  ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ?_).trans ?_
              · intro output _ hmiss
                simp only [hmiss, ↓reduceIte]
                have hcount :
                    (state.install epoch (truncateHash output)).pendingCount =
                      (state.install epoch 0).pendingCount := by
                  exact state.pendingCount_install_eq epoch _ _
                have htail := ih (state.install epoch (truncateHash output))
                  (fun history => strategy (output :: history))
                rw [hcount] at htail
                exact htail
              · refine add_le_add
                  (uniform_truncate_mem_finset_le (state.pending epoch)) le_rfl |>.trans ?_
                have hconserve := state.pendingCount_install_add epoch 0
                have hnat :
                  (state.pending epoch).card +
                      (fuel + (state.install epoch 0).pendingCount) ≤
                    fuel.succ + state.pendingCount := by omega
                rw [← add_mul]
                gcongr
                rw [← Nat.cast_add]
                exact Nat.cast_le.mpr hnat

theorem run_empty_true_probability_le (fuel : Nat)
    (strategy : List HashOutput → Action) :
    Pr[(fun hit : Bool => hit = true) | run State.empty fuel strategy] ≤
      (fuel : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  simpa [State.pendingCount_empty, div_eq_mul_inv] using
    run_true_probability_le State.empty fuel strategy

end XmssSecurity.EncodingMonitor
