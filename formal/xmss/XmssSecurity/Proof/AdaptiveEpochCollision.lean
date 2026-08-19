import XmssSecurity.Proof.AdaptiveFreshTarget
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

/-- A monitored action after its fresh random-oracle output has been revealed. -/
inductive ObservedAction where
  | query (epoch : Epoch) (output : HashOutput)
  | sign (epoch : Epoch) (output : HashOutput)

def ObservedAction.IsSignAt (target : Epoch) : ObservedAction → Prop
  | .query _ _ => False
  | .sign epoch _ => epoch = target

def ObservedAction.signEpoch? : ObservedAction → Option Epoch
  | .query _ _ => none
  | .sign epoch _ => some epoch

def observedSignEpochs : List ObservedAction → List Epoch
  | [] => []
  | .query _ _ :: actions => observedSignEpochs actions
  | .sign epoch _ :: actions => epoch :: observedSignEpochs actions

@[simp]
theorem observedSignEpochs_append (left right : List ObservedAction) :
    observedSignEpochs (left ++ right) =
      observedSignEpochs left ++ observedSignEpochs right := by
  induction left with
  | nil => rfl
  | cons action left ih =>
      cases action <;> simp [observedSignEpochs, ih]

def State.applyObserved (state : State) : ObservedAction → Option (State × Bool)
  | .query epoch output =>
      let digest := truncateHash output
      match state.signed epoch with
      | some target => some (state, digest = target)
      | none => some (state.addPending epoch digest, false)
  | .sign epoch output =>
      match state.signed epoch with
      | some _ => none
      | none =>
          let digest := truncateHash output
          some (state.install epoch digest, digest ∈ state.pending epoch)

def runObserved : State → List ObservedAction → Bool
  | _state, [] => false
  | state, action :: actions =>
      match state.applyObserved action with
      | none => false
      | some (nextState, hit) => hit || runObserved nextState actions

@[simp]
theorem runObserved_nil (state : State) : runObserved state [] = false := rfl

@[simp]
theorem runObserved_cons (state : State) (action : ObservedAction)
    (actions : List ObservedAction) :
    runObserved state (action :: actions) =
      match state.applyObserved action with
      | none => false
      | some (nextState, hit) => hit || runObserved nextState actions := rfl

structure ReplayResult where
  state : State
  hit : Bool
  valid : Bool

def State.applyObservedTotal (state : State) : ObservedAction → ReplayResult
  | .query epoch output =>
      let digest := truncateHash output
      match state.signed epoch with
      | some target => ⟨state, digest = target, true⟩
      | none => ⟨state.addPending epoch digest, false, true⟩
  | .sign epoch output =>
      match state.signed epoch with
      | some _ => ⟨state, false, false⟩
      | none =>
          let digest := truncateHash output
          ⟨state.install epoch digest, digest ∈ state.pending epoch, true⟩

def replayObserved : State → List ObservedAction → ReplayResult
  | state, [] => ⟨state, false, true⟩
  | state, action :: actions =>
      let head := state.applyObservedTotal action
      let tail := replayObserved head.state actions
      ⟨tail.state, head.hit || tail.hit, head.valid && tail.valid⟩

@[simp]
theorem replayObserved_nil (state : State) :
    replayObserved state [] = ⟨state, false, true⟩ := rfl

@[simp]
theorem replayObserved_cons (state : State) (action : ObservedAction)
    (actions : List ObservedAction) :
    replayObserved state (action :: actions) =
      let head := state.applyObservedTotal action
      let tail := replayObserved head.state actions
      ⟨tail.state, head.hit || tail.hit, head.valid && tail.valid⟩ := rfl

theorem replayObserved_valid_iff (state : State) (actions : List ObservedAction) :
    (replayObserved state actions).valid = true ↔
      (∀ epoch ∈ observedSignEpochs actions, state.signed epoch = none) ∧
        (observedSignEpochs actions).Nodup := by
  induction actions generalizing state with
  | nil => simp [replayObserved, observedSignEpochs]
  | cons action actions ih =>
      cases action with
      | query epoch output =>
          cases hsigned : state.signed epoch <;>
            simp [replayObserved, State.applyObservedTotal, observedSignEpochs,
              hsigned, ih, State.addPending]
      | sign epoch output =>
          cases hsigned : state.signed epoch with
          | none =>
              rw [replayObserved_cons]
              simp only [State.applyObservedTotal, hsigned, Bool.true_and, ih,
                observedSignEpochs, List.mem_cons, forall_eq_or_imp, List.nodup_cons]
              have htail :
                  (∀ candidate ∈ observedSignEpochs actions,
                      (state.install epoch (truncateHash output)).signed candidate = none) ↔
                    epoch ∉ observedSignEpochs actions ∧
                      ∀ candidate ∈ observedSignEpochs actions,
                        state.signed candidate = none := by
                constructor
                · intro hall
                  constructor
                  · intro hepoch
                    have := hall epoch hepoch
                    simp [State.install] at this
                  · intro candidate hcandidate
                    have hnone := hall candidate hcandidate
                    have hne : candidate ≠ epoch := by
                      intro heq
                      subst candidate
                      have := hall epoch hcandidate
                      simp [State.install] at this
                    simpa [State.install, hne] using hnone
                · rintro ⟨hepoch, hall⟩ candidate hcandidate
                  have hne : candidate ≠ epoch := by
                    intro heq
                    subst candidate
                    exact hepoch hcandidate
                  simpa [State.install, hne] using
                    hall candidate hcandidate
              rw [htail]
              simp [and_assoc, and_comm]
          | some target =>
              rw [replayObserved_cons]
              simp only [State.applyObservedTotal, hsigned, Bool.false_and,
                Bool.false_eq_true, false_iff, observedSignEpochs, List.mem_cons,
                forall_eq_or_imp]
              simp

@[simp]
theorem replayObserved_empty_valid_iff (actions : List ObservedAction) :
    (replayObserved State.empty actions).valid = true ↔
      (observedSignEpochs actions).Nodup := by
  rw [replayObserved_valid_iff]
  simp [State.empty]

theorem runObserved_eq_replayObserved_hit_of_valid
    (state : State) (actions : List ObservedAction)
    (hvalid : (replayObserved state actions).valid = true) :
    runObserved state actions = (replayObserved state actions).hit := by
  induction actions generalizing state with
  | nil => rfl
  | cons action actions ih =>
      cases action with
      | query epoch output =>
          cases hsigned : state.signed epoch <;>
            simp only [runObserved, State.applyObserved, hsigned, replayObserved,
              State.applyObservedTotal, Bool.true_and] at hvalid ⊢
          · rw [ih _ hvalid]
          · rw [ih _ hvalid]
      | sign epoch output =>
          cases hsigned : state.signed epoch with
          | none =>
              simp only [runObserved, State.applyObserved, hsigned, replayObserved,
                State.applyObservedTotal, Bool.true_and] at hvalid ⊢
              rw [ih _ hvalid]
          | some target =>
              simp [replayObserved, State.applyObservedTotal, hsigned] at hvalid

theorem replayObserved_append (state : State)
    (left right : List ObservedAction) :
    replayObserved state (left ++ right) =
      let firstResult := replayObserved state left
      let secondResult := replayObserved firstResult.state right
      ⟨secondResult.state, firstResult.hit || secondResult.hit,
        firstResult.valid && secondResult.valid⟩ := by
  induction left generalizing state with
  | nil => rfl
  | cons action left ih =>
      simp only [List.cons_append, replayObserved_cons]
      rw [ih]
      simp [Bool.or_assoc, Bool.and_assoc]

theorem replayObserved_state_signed_eq_of_not_mem
    (state : State) (actions : List ObservedAction) (epoch : Epoch)
    (hnot : epoch ∉ observedSignEpochs actions) :
    (replayObserved state actions).state.signed epoch = state.signed epoch := by
  induction actions generalizing state with
  | nil => rfl
  | cons action actions ih =>
      cases action with
      | query queriedEpoch output =>
          have htail : epoch ∉ observedSignEpochs actions := by
            simpa [observedSignEpochs] using hnot
          cases hsigned : state.signed queriedEpoch with
          | some target =>
              rw [replayObserved_cons]
              simp only [State.applyObservedTotal, hsigned]
              exact ih state htail
          | none =>
              rw [replayObserved_cons]
              simp only [State.applyObservedTotal, hsigned]
              exact (ih (state.addPending queriedEpoch (truncateHash output)) htail).trans
                (by rfl)
      | sign signedEpoch output =>
          have hsignedNe : signedEpoch ≠ epoch := by
            intro heq
            subst signedEpoch
            exact hnot (by simp [observedSignEpochs])
          have htail : epoch ∉ observedSignEpochs actions := by
            intro hmem
            exact hnot (by simp [observedSignEpochs, hmem])
          cases hsigned : state.signed signedEpoch with
          | none =>
              rw [replayObserved_cons]
              simp only [State.applyObservedTotal, hsigned]
              rw [ih (state.install signedEpoch (truncateHash output)) htail]
              simp [State.install, Ne.symm hsignedNe]
          | some target =>
              rw [replayObserved_cons]
              simp only [State.applyObservedTotal, hsigned]
              exact ih state htail

theorem replayObserved_pending_mono_of_not_mem
    (state : State) (actions : List ObservedAction) (epoch : Epoch)
    (hnot : epoch ∉ observedSignEpochs actions) :
    state.pending epoch ⊆ (replayObserved state actions).state.pending epoch := by
  induction actions generalizing state with
  | nil => exact fun _ hmem => hmem
  | cons action actions ih =>
      cases action with
      | query queriedEpoch output =>
          have htail : epoch ∉ observedSignEpochs actions := by
            simpa [observedSignEpochs] using hnot
          cases hsigned : state.signed queriedEpoch with
          | some target =>
              rw [replayObserved_cons]
              simp only [State.applyObservedTotal, hsigned]
              exact ih state htail
          | none =>
              rw [replayObserved_cons]
              simp only [State.applyObservedTotal, hsigned]
              refine fun digest hdigest => ih (state.addPending queriedEpoch
                (truncateHash output)) htail ?_
              by_cases heq : queriedEpoch = epoch
              · subst queriedEpoch
                simpa [State.addPending] using Finset.mem_insert_of_mem hdigest
              · simpa [State.addPending, Ne.symm heq] using hdigest
      | sign signedEpoch output =>
          have hsignedNe : signedEpoch ≠ epoch := by
            intro heq
            subst signedEpoch
            exact hnot (by simp [observedSignEpochs])
          have htail : epoch ∉ observedSignEpochs actions := by
            intro hmem
            exact hnot (by simp [observedSignEpochs, hmem])
          cases hsigned : state.signed signedEpoch with
          | some target =>
              rw [replayObserved_cons]
              simp only [State.applyObservedTotal, hsigned]
              exact ih state htail
          | none =>
              rw [replayObserved_cons]
              simp only [State.applyObservedTotal, hsigned]
              refine fun digest hdigest => ih (state.install signedEpoch
                (truncateHash output)) htail ?_
              simpa [State.install, Ne.symm hsignedNe] using hdigest

theorem replayObserved_hit_of_query_before_sign
    (state : State) (epoch : Epoch) (queriedOutput signedOutput : HashOutput)
    (middle after : List ObservedAction)
    (hsigned : state.signed epoch = none)
    (hnoMiddleSign : epoch ∉ observedSignEpochs middle)
    (hcollision : truncateHash queriedOutput = truncateHash signedOutput) :
    (replayObserved state
      (.query epoch queriedOutput :: middle ++ .sign epoch signedOutput :: after)).hit =
        true := by
  simp only [List.cons_append]
  rw [congrArg ReplayResult.hit (replayObserved_cons state
    (.query epoch queriedOutput) (middle ++ .sign epoch signedOutput :: after))]
  simp only [State.applyObservedTotal, hsigned, Bool.false_or]
  rw [replayObserved_append]
  let middleResult := replayObserved
    (state.addPending epoch (truncateHash queriedOutput)) middle
  have hmiddleSigned : middleResult.state.signed epoch = none := by
    calc
      middleResult.state.signed epoch =
          (state.addPending epoch (truncateHash queriedOutput)).signed epoch :=
        replayObserved_state_signed_eq_of_not_mem _ middle epoch hnoMiddleSign
      _ = none := hsigned
  have hinitialPending : truncateHash queriedOutput ∈
      (state.addPending epoch (truncateHash queriedOutput)).pending epoch := by
    simp [State.addPending]
  have hmiddlePending : truncateHash signedOutput ∈ middleResult.state.pending epoch := by
    rw [← hcollision]
    exact replayObserved_pending_mono_of_not_mem _ middle epoch hnoMiddleSign
      hinitialPending
  change (middleResult.hit ||
    (replayObserved middleResult.state (.sign epoch signedOutput :: after)).hit) = true
  rw [congrArg ReplayResult.hit (replayObserved_cons middleResult.state
    (.sign epoch signedOutput) after)]
  simp [State.applyObservedTotal, hmiddleSigned, hmiddlePending]

theorem replayObserved_hit_of_sign_before_query
    (state : State) (epoch : Epoch) (signedOutput queriedOutput : HashOutput)
    (middle after : List ObservedAction)
    (hsigned : state.signed epoch = none)
    (hnoMiddleSign : epoch ∉ observedSignEpochs middle)
    (hcollision : truncateHash signedOutput = truncateHash queriedOutput) :
    (replayObserved state
      (.sign epoch signedOutput :: middle ++ .query epoch queriedOutput :: after)).hit =
        true := by
  simp only [List.cons_append]
  rw [congrArg ReplayResult.hit (replayObserved_cons state
    (.sign epoch signedOutput) (middle ++ .query epoch queriedOutput :: after))]
  simp only [State.applyObservedTotal, hsigned]
  rw [replayObserved_append]
  let middleResult := replayObserved
    (state.install epoch (truncateHash signedOutput)) middle
  have hmiddleSigned : middleResult.state.signed epoch =
      some (truncateHash signedOutput) := by
    calc
      middleResult.state.signed epoch =
          (state.install epoch (truncateHash signedOutput)).signed epoch :=
        replayObserved_state_signed_eq_of_not_mem _ middle epoch hnoMiddleSign
      _ = some (truncateHash signedOutput) := by simp [State.install]
  change (decide (truncateHash signedOutput ∈ state.pending epoch) ||
    (middleResult.hit ||
      (replayObserved middleResult.state (.query epoch queriedOutput :: after)).hit)) = true
  rw [congrArg ReplayResult.hit (replayObserved_cons middleResult.state
    (.query epoch queriedOutput) after)]
  simp [State.applyObservedTotal, hmiddleSigned, hcollision]

theorem runObserved_empty_eq_true_of_query_before_sign
    (epoch : Epoch) (queriedOutput signedOutput : HashOutput)
    (before middle after : List ObservedAction)
    (hnoBeforeSign : epoch ∉ observedSignEpochs before)
    (hnoMiddleSign : epoch ∉ observedSignEpochs middle)
    (hcollision : truncateHash queriedOutput = truncateHash signedOutput)
    (hvalid : (observedSignEpochs
      (before ++ [.query epoch queriedOutput] ++ middle ++
        [.sign epoch signedOutput] ++ after)).Nodup) :
    runObserved State.empty
      (before ++ [.query epoch queriedOutput] ++ middle ++
        [.sign epoch signedOutput] ++ after) = true := by
  let tail := .query epoch queriedOutput :: middle ++ .sign epoch signedOutput :: after
  have hlist : before ++ [.query epoch queriedOutput] ++ middle ++
      [.sign epoch signedOutput] ++ after = before ++ tail := by
    simp [tail, List.append_assoc]
  rw [hlist]
  have hreplayValid : (replayObserved State.empty (before ++ tail)).valid = true :=
    replayObserved_empty_valid_iff (before ++ tail) |>.2 (by simpa [← hlist] using hvalid)
  rw [runObserved_eq_replayObserved_hit_of_valid _ _ hreplayValid]
  rw [replayObserved_append]
  let beforeResult := replayObserved State.empty before
  have hbeforeSigned : beforeResult.state.signed epoch = none := by
    calc
      beforeResult.state.signed epoch = State.empty.signed epoch :=
        replayObserved_state_signed_eq_of_not_mem State.empty before epoch hnoBeforeSign
      _ = none := rfl
  have htailHit : (replayObserved beforeResult.state tail).hit = true := by
    exact replayObserved_hit_of_query_before_sign beforeResult.state epoch queriedOutput
      signedOutput middle after hbeforeSigned hnoMiddleSign hcollision
  change (beforeResult.hit || (replayObserved beforeResult.state tail).hit) = true
  simp [htailHit]

theorem runObserved_empty_eq_true_of_sign_before_query
    (epoch : Epoch) (signedOutput queriedOutput : HashOutput)
    (before middle after : List ObservedAction)
    (hnoBeforeSign : epoch ∉ observedSignEpochs before)
    (hnoMiddleSign : epoch ∉ observedSignEpochs middle)
    (hcollision : truncateHash signedOutput = truncateHash queriedOutput)
    (hvalid : (observedSignEpochs
      (before ++ [.sign epoch signedOutput] ++ middle ++
        [.query epoch queriedOutput] ++ after)).Nodup) :
    runObserved State.empty
      (before ++ [.sign epoch signedOutput] ++ middle ++
        [.query epoch queriedOutput] ++ after) = true := by
  let tail := .sign epoch signedOutput :: middle ++ .query epoch queriedOutput :: after
  have hlist : before ++ [.sign epoch signedOutput] ++ middle ++
      [.query epoch queriedOutput] ++ after = before ++ tail := by
    simp [tail, List.append_assoc]
  rw [hlist]
  have hreplayValid : (replayObserved State.empty (before ++ tail)).valid = true :=
    replayObserved_empty_valid_iff (before ++ tail) |>.2 (by simpa [← hlist] using hvalid)
  rw [runObserved_eq_replayObserved_hit_of_valid _ _ hreplayValid]
  rw [replayObserved_append]
  let beforeResult := replayObserved State.empty before
  have hbeforeSigned : beforeResult.state.signed epoch = none := by
    calc
      beforeResult.state.signed epoch = State.empty.signed epoch :=
        replayObserved_state_signed_eq_of_not_mem State.empty before epoch hnoBeforeSign
      _ = none := rfl
  have htailHit : (replayObserved beforeResult.state tail).hit = true := by
    exact replayObserved_hit_of_sign_before_query beforeResult.state epoch signedOutput
      queriedOutput middle after hbeforeSigned hnoMiddleSign hcollision
  change (beforeResult.hit || (replayObserved beforeResult.state tail).hit) = true
  simp [htailHit]

theorem observedSignEpochs_not_mem_around_sign
    (epoch : Epoch) (output : HashOutput)
    (before after : List ObservedAction)
    (hvalid : (observedSignEpochs
      (before ++ [.sign epoch output] ++ after)).Nodup) :
    epoch ∉ observedSignEpochs before ∧ epoch ∉ observedSignEpochs after := by
  have hnormalized :
      (observedSignEpochs before ++ epoch :: observedSignEpochs after).Nodup := by
    simpa [observedSignEpochs, List.append_assoc] using hvalid
  have hparts := List.nodup_append.mp hnormalized
  constructor
  · intro hmem
    exact hparts.2.2 epoch hmem epoch (by simp) rfl
  · exact (List.nodup_cons.mp hparts.2.1).1

theorem runObserved_empty_eq_true_of_query_before_sign_of_nodup
    (epoch : Epoch) (queriedOutput signedOutput : HashOutput)
    (before middle after : List ObservedAction)
    (hcollision : truncateHash queriedOutput = truncateHash signedOutput)
    (hvalid : (observedSignEpochs
      (before ++ [.query epoch queriedOutput] ++ middle ++
        [.sign epoch signedOutput] ++ after)).Nodup) :
    runObserved State.empty
      (before ++ [.query epoch queriedOutput] ++ middle ++
        [.sign epoch signedOutput] ++ after) = true := by
  have haround := observedSignEpochs_not_mem_around_sign epoch signedOutput
    (before ++ [.query epoch queriedOutput] ++ middle) after (by
      simpa [List.append_assoc] using hvalid)
  have hnoPrefix : epoch ∉ observedSignEpochs before := by
    intro hmem
    apply haround.1
    simp [hmem]
  have hnoMiddle : epoch ∉ observedSignEpochs middle := by
    intro hmem
    apply haround.1
    have : epoch ∈ observedSignEpochs before ++ observedSignEpochs middle :=
      List.mem_append_right _ hmem
    simpa [observedSignEpochs, List.append_assoc] using this
  exact runObserved_empty_eq_true_of_query_before_sign epoch queriedOutput
    signedOutput before middle after hnoPrefix hnoMiddle hcollision hvalid

theorem runObserved_empty_eq_true_of_sign_before_query_of_nodup
    (epoch : Epoch) (signedOutput queriedOutput : HashOutput)
    (before middle after : List ObservedAction)
    (hcollision : truncateHash signedOutput = truncateHash queriedOutput)
    (hvalid : (observedSignEpochs
      (before ++ [.sign epoch signedOutput] ++ middle ++
        [.query epoch queriedOutput] ++ after)).Nodup) :
    runObserved State.empty
      (before ++ [.sign epoch signedOutput] ++ middle ++
        [.query epoch queriedOutput] ++ after) = true := by
  have haround := observedSignEpochs_not_mem_around_sign epoch signedOutput before
    (middle ++ [.query epoch queriedOutput] ++ after) (by
      simpa [List.append_assoc] using hvalid)
  have hnoMiddle : epoch ∉ observedSignEpochs middle := by
    intro hmem
    apply haround.2
    have : epoch ∈ observedSignEpochs middle ++ observedSignEpochs after :=
      List.mem_append_left _ hmem
    simpa [observedSignEpochs, List.append_assoc] using this
  exact runObserved_empty_eq_true_of_sign_before_query epoch signedOutput
    queriedOutput before middle after haround.1 hnoMiddle hcollision hvalid

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

inductive ControllerAction (σ : Type) where
  | stop
  | skip (next : σ)
  | query (epoch : Epoch) (next : HashOutput → σ)
  | sign (epoch : Epoch) (next : HashOutput → σ)

/-- The adaptive collision monitor with an arbitrary probabilistic controller. The controller may retain all side information, while every observed encoding output is sampled independently. -/
noncomputable def runProbabilistic {σ : Type}
    (controller : σ → ProbComp (ControllerAction σ)) : State → Nat → σ → ProbComp Bool
  | _state, 0, _control => pure false
  | state, fuel + 1, control => do
      let action ← controller control
      match action with
      | .stop => pure false
      | .skip next => runProbabilistic controller state fuel next
      | .query epoch next => do
          let output ← $ᵗ HashOutput
          let digest := truncateHash output
          match state.signed epoch with
          | some target =>
              if digest = target then
                pure true
              else
                runProbabilistic controller state fuel (next output)
          | none =>
              runProbabilistic controller (state.addPending epoch digest) fuel
                (next output)
      | .sign epoch next =>
          match state.signed epoch with
          | some _ => pure false
          | none => do
              let output ← $ᵗ HashOutput
              let digest := truncateHash output
              if digest ∈ state.pending epoch then
                pure true
              else
                runProbabilistic controller (state.install epoch digest) fuel
                  (next output)

/-- Probabilistic control and retained side information do not increase the adaptive epoch-collision bound. -/
theorem runProbabilistic_true_probability_le {σ : Type}
    (controller : σ → ProbComp (ControllerAction σ))
    (state : State) (fuel : Nat) (control : σ) :
    Pr[(fun hit : Bool => hit = true) |
      runProbabilistic controller state fuel control] ≤
      ((fuel + state.pendingCount : Nat) : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  induction fuel generalizing state control with
  | zero =>
      rw [runProbabilistic, probEvent_pure]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact zero_le
  | succ fuel ih =>
      rw [runProbabilistic]
      refine probEvent_bind_le_of_forall_le fun action _ => ?_
      cases action with
      | stop =>
          rw [probEvent_pure]
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact zero_le
      | skip next =>
          change Pr[(fun hit : Bool => hit = true) |
            runProbabilistic controller state fuel next] ≤ _
          refine (ih state next).trans ?_
          gcongr
          omega
      | query epoch next =>
          cases hsigned : state.signed epoch with
          | none =>
              change Pr[(fun hit : Bool => hit = true) |
                ($ᵗ HashOutput) >>= fun output =>
                  match state.signed epoch with
                  | some target =>
                      if truncateHash output = target then pure true
                      else runProbabilistic controller state fuel (next output)
                  | none =>
                      runProbabilistic controller
                        (state.addPending epoch (truncateHash output)) fuel
                        (next output)] ≤ _
              rw [hsigned]
              refine probEvent_bind_le_of_forall_le
                (mx := ($ᵗ HashOutput))
                (my := fun output =>
                  runProbabilistic controller
                    (state.addPending epoch (truncateHash output)) fuel
                    (next output))
                (q := fun hit : Bool => hit = true) fun output _ => ?_
              refine (ih (state.addPending epoch (truncateHash output))
                (next output)).trans ?_
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
              change Pr[(fun hit : Bool => hit = true) |
                ($ᵗ HashOutput) >>= fun output =>
                  match state.signed epoch with
                  | some target =>
                      if truncateHash output = target then pure true
                      else runProbabilistic controller state fuel (next output)
                  | none =>
                      runProbabilistic controller
                        (state.addPending epoch (truncateHash output)) fuel
                        (next output)] ≤ _
              rw [hsigned]
              refine (probEvent_bind_le_probEvent_add
                (mx := ($ᵗ HashOutput))
                (my := fun output =>
                  if truncateHash output = target then pure true
                  else runProbabilistic controller state fuel (next output))
                (q := fun hit : Bool => hit = true)
                (p := fun output : HashOutput => truncateHash output = target)
                (ε := ((fuel + state.pendingCount : Nat) : ℝ≥0∞) *
                  ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ?_).trans ?_
              · intro output _ hmiss
                simp only [hmiss, ↓reduceIte]
                exact ih state (next output)
              · rw [Rom.uniform_truncate_probability]
                push_cast
                ring_nf
                exact le_rfl
      | sign epoch next =>
          cases hsigned : state.signed epoch with
          | some target =>
              change Pr[(fun hit : Bool => hit = true) |
                match state.signed epoch with
                | some _ => pure false
                | none => ($ᵗ HashOutput) >>= fun output =>
                    if truncateHash output ∈ state.pending epoch then pure true
                    else runProbabilistic controller
                      (state.install epoch (truncateHash output)) fuel
                      (next output)] ≤ _
              rw [hsigned, probEvent_pure]
              simp only [Bool.false_eq_true, ↓reduceIte]
              exact zero_le
          | none =>
              change Pr[(fun hit : Bool => hit = true) |
                match state.signed epoch with
                | some _ => pure false
                | none => ($ᵗ HashOutput) >>= fun output =>
                    if truncateHash output ∈ state.pending epoch then pure true
                    else runProbabilistic controller
                      (state.install epoch (truncateHash output)) fuel
                      (next output)] ≤ _
              rw [hsigned]
              refine (probEvent_bind_le_probEvent_add
                (mx := ($ᵗ HashOutput))
                (my := fun output =>
                  if truncateHash output ∈ state.pending epoch then pure true
                  else runProbabilistic controller
                    (state.install epoch (truncateHash output)) fuel (next output))
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
                  (next output)
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

theorem runProbabilistic_empty_true_probability_le {σ : Type}
    (controller : σ → ProbComp (ControllerAction σ))
    (fuel : Nat) (control : σ) :
    Pr[(fun hit : Bool => hit = true) |
      runProbabilistic controller State.empty fuel control] ≤
      (fuel : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  simpa [State.pendingCount_empty, div_eq_mul_inv] using
    runProbabilistic_true_probability_le controller State.empty fuel control

theorem pair_sublist_iff (first second : α) (actions : List α) :
    List.Sublist [first, second] actions ↔
      ∃ before middle after,
        actions = before ++ (first :: (middle ++ (second :: after))) := by
  constructor
  · intro hsub
    induction actions with
    | nil => simp at hsub
    | cons action actions ih =>
        cases hsub with
        | cons _ htail =>
            obtain ⟨before, middle, after, hactions⟩ := ih htail
            exact ⟨action :: before, middle, after, by simp [hactions]⟩
        | cons_cons _ htail =>
            have hsecond : second ∈ actions := by
              exact List.singleton_sublist.mp htail
            obtain ⟨middle, after, hactions⟩ := List.append_of_mem hsecond
            exact ⟨[], middle, after, by simp [hactions]⟩
  · rintro ⟨before, middle, after, rfl⟩
    have hsecond : List.Sublist [second] (middle ++ second :: after) :=
      List.singleton_sublist.mpr (List.mem_append_right middle (by simp))
    have hprefix : List.Sublist (first :: (middle ++ (second :: after)))
        (before ++ (first :: (middle ++ (second :: after)))) :=
      List.sublist_append_right before _
    exact (hsecond.cons_cons first).trans hprefix

theorem observedSignEpochs_sublist {left right : List ObservedAction}
    (hsub : List.Sublist left right) :
    List.Sublist (observedSignEpochs left) (observedSignEpochs right) := by
  induction hsub with
  | slnil => exact .slnil
  | cons action hsub ih =>
      cases action with
      | query epoch output => exact ih
      | sign epoch output => exact ih.cons epoch
  | cons_cons action hsub ih =>
      cases action with
      | query epoch output => exact ih
      | sign epoch output => exact ih.cons_cons epoch

def HasCollisionPair (actions : List ObservedAction) : Prop :=
  ∃ epoch queriedOutput signedOutput,
    truncateHash queriedOutput = truncateHash signedOutput ∧
      (List.Sublist [.query epoch queriedOutput, .sign epoch signedOutput] actions ∨
        List.Sublist [.sign epoch signedOutput, .query epoch queriedOutput] actions)

theorem HasCollisionPair.mono {left right : List ObservedAction}
    (hcollision : HasCollisionPair left) (hsub : List.Sublist left right) :
    HasCollisionPair right := by
  obtain ⟨epoch, queriedOutput, signedOutput, hdigest, hpair⟩ := hcollision
  exact ⟨epoch, queriedOutput, signedOutput, hdigest,
    hpair.imp (·.trans hsub) (·.trans hsub)⟩

def StateRepresentedBy (state : State) (actions : List ObservedAction) : Prop :=
  (∀ epoch digest, state.signed epoch = some digest →
      ∃ output, .sign epoch output ∈ actions ∧ truncateHash output = digest) ∧
    (∀ epoch digest, digest ∈ state.pending epoch →
      ∃ output, .query epoch output ∈ actions ∧ truncateHash output = digest)

theorem StateRepresentedBy.empty : StateRepresentedBy State.empty [] := by
  constructor
  · intro epoch digest hsigned
    simp [State.empty] at hsigned
  · intro epoch digest hpending
    simp [State.empty] at hpending

theorem StateRepresentedBy.applyObservedTotal
    {state : State} {actions : List ObservedAction}
    (hrepresented : StateRepresentedBy state actions)
    (action : ObservedAction) :
    StateRepresentedBy (state.applyObservedTotal action).state
      (actions ++ [action]) := by
  rcases hrepresented with ⟨hsignedRep, hpendingRep⟩
  cases action with
  | query epoch output =>
      cases hsigned : state.signed epoch with
      | some target =>
          simp only [State.applyObservedTotal, hsigned]
          constructor
          · intro candidate digest hcandid
            obtain ⟨oldOutput, hold, hdigest⟩ :=
              hsignedRep candidate digest hcandid
            exact ⟨oldOutput, List.mem_append_left _ hold, hdigest⟩
          · intro candidate digest hcandid
            obtain ⟨oldOutput, hold, hdigest⟩ :=
              hpendingRep candidate digest hcandid
            exact ⟨oldOutput, List.mem_append_left _ hold, hdigest⟩
      | none =>
          simp only [State.applyObservedTotal, hsigned]
          constructor
          · intro candidate digest hcandid
            obtain ⟨oldOutput, hold, hdigest⟩ :=
              hsignedRep candidate digest hcandid
            exact ⟨oldOutput, List.mem_append_left _ hold, hdigest⟩
          · intro candidate digest hcandid
            by_cases heq : candidate = epoch
            · subst candidate
              simp only [State.addPending, Function.update_self,
                Finset.mem_insert] at hcandid
              rcases hcandid with hcandid | hcandid
              · subst digest
                exact ⟨output, by simp, rfl⟩
              · obtain ⟨oldOutput, hold, hdigest⟩ :=
                  hpendingRep epoch digest hcandid
                exact ⟨oldOutput, List.mem_append_left _ hold, hdigest⟩
            · have hold : digest ∈ state.pending candidate := by
                simpa [State.addPending, heq] using hcandid
              obtain ⟨oldOutput, hmem, hdigest⟩ :=
                hpendingRep candidate digest hold
              exact ⟨oldOutput, List.mem_append_left _ hmem, hdigest⟩
  | sign epoch output =>
      cases hsigned : state.signed epoch with
      | some target =>
          simp only [State.applyObservedTotal, hsigned]
          constructor
          · intro candidate digest hcandid
            obtain ⟨oldOutput, hold, hdigest⟩ :=
              hsignedRep candidate digest hcandid
            exact ⟨oldOutput, List.mem_append_left _ hold, hdigest⟩
          · intro candidate digest hcandid
            obtain ⟨oldOutput, hold, hdigest⟩ :=
              hpendingRep candidate digest hcandid
            exact ⟨oldOutput, List.mem_append_left _ hold, hdigest⟩
      | none =>
          simp only [State.applyObservedTotal, hsigned]
          constructor
          · intro candidate digest hcandid
            by_cases heq : candidate = epoch
            · subst candidate
              simp only [State.install, Function.update_self,
                Option.some.injEq] at hcandid
              subst digest
              exact ⟨output, by simp, rfl⟩
            · have hold : state.signed candidate = some digest := by
                simpa [State.install, heq] using hcandid
              obtain ⟨oldOutput, hmem, hdigest⟩ :=
                hsignedRep candidate digest hold
              exact ⟨oldOutput, List.mem_append_left _ hmem, hdigest⟩
          · intro candidate digest hcandid
            by_cases heq : candidate = epoch
            · subst candidate
              simp [State.install] at hcandid
            · have hold : digest ∈ state.pending candidate := by
                simpa [State.install, heq] using hcandid
              obtain ⟨oldOutput, hmem, hdigest⟩ :=
                hpendingRep candidate digest hold
              exact ⟨oldOutput, List.mem_append_left _ hmem, hdigest⟩

theorem replayObserved_hit_eq_true_hasCollisionPair
    (state : State) (actionsBefore tail : List ObservedAction)
    (hrepresented : StateRepresentedBy state actionsBefore)
    (hhit : (replayObserved state tail).hit = true) :
    HasCollisionPair (actionsBefore ++ tail) := by
  induction tail generalizing state actionsBefore with
  | nil => simp at hhit
  | cons action tail ih =>
      rw [replayObserved_cons] at hhit
      let head := state.applyObservedTotal action
      let rest := replayObserved head.state tail
      change (head.hit || rest.hit) = true at hhit
      rw [Bool.or_eq_true] at hhit
      rcases hhit with hhead | htail
      · cases action with
        | query epoch output =>
            cases hsigned : state.signed epoch with
            | none => simp [head, State.applyObservedTotal, hsigned] at hhead
            | some target =>
                have hquery : truncateHash output = target := by
                  simpa [head, State.applyObservedTotal, hsigned] using hhead
                obtain ⟨signedOutput, hsignedMem, hsignedDigest⟩ :=
                  hrepresented.1 epoch target hsigned
                have hpair : List.Sublist
                    [.sign epoch signedOutput, .query epoch output]
                    (actionsBefore ++ .query epoch output :: tail) := by
                  have hbase := (List.singleton_sublist.mpr hsignedMem).append
                    (List.Sublist.refl [.query epoch output])
                  exact hbase.trans (by simp)
                exact ⟨epoch, output, signedOutput,
                  hquery.trans hsignedDigest.symm, Or.inr hpair⟩
        | sign epoch output =>
            cases hsigned : state.signed epoch with
            | some target => simp [head, State.applyObservedTotal, hsigned] at hhead
            | none =>
                have hpending : truncateHash output ∈ state.pending epoch := by
                  simpa [head, State.applyObservedTotal, hsigned] using hhead
                obtain ⟨queriedOutput, hqueryMem, hqueryDigest⟩ :=
                  hrepresented.2 epoch (truncateHash output) hpending
                have hpair : List.Sublist
                    [.query epoch queriedOutput, .sign epoch output]
                    (actionsBefore ++ .sign epoch output :: tail) := by
                  have hbase := (List.singleton_sublist.mpr hqueryMem).append
                    (List.Sublist.refl [.sign epoch output])
                  exact hbase.trans (by simp)
                exact ⟨epoch, queriedOutput, output, hqueryDigest,
                  Or.inl hpair⟩
      · have htailPair := ih head.state (actionsBefore ++ [action])
          (hrepresented.applyObservedTotal action) htail
        simpa [head, List.append_assoc] using htailPair

theorem runObserved_empty_eq_true_of_collisionPair
    (actions : List ObservedAction)
    (hnodup : (observedSignEpochs actions).Nodup)
    (hcollision : HasCollisionPair actions) :
    runObserved State.empty actions = true := by
  obtain ⟨epoch, queriedOutput, signedOutput, hdigest, hpair | hpair⟩ := hcollision
  · obtain ⟨before, middle, after, hactions⟩ :=
      (pair_sublist_iff _ _ _).mp hpair
    subst actions
    simpa [List.append_assoc] using
      runObserved_empty_eq_true_of_query_before_sign_of_nodup
        epoch queriedOutput signedOutput before middle after hdigest
          (by simpa [List.append_assoc] using hnodup)
  · obtain ⟨before, middle, after, hactions⟩ :=
      (pair_sublist_iff _ _ _).mp hpair
    subst actions
    simpa [List.append_assoc] using
      runObserved_empty_eq_true_of_sign_before_query_of_nodup
        epoch signedOutput queriedOutput before middle after hdigest.symm
          (by simpa [List.append_assoc] using hnodup)

theorem collisionPair_of_runObserved_empty_eq_true
    (actions : List ObservedAction)
    (hnodup : (observedSignEpochs actions).Nodup)
    (hhit : runObserved State.empty actions = true) :
    HasCollisionPair actions := by
  have hvalid : (replayObserved State.empty actions).valid = true :=
    (replayObserved_empty_valid_iff actions).mpr hnodup
  have hreplay := runObserved_eq_replayObserved_hit_of_valid
    State.empty actions hvalid
  rw [hreplay] at hhit
  simpa using replayObserved_hit_eq_true_hasCollisionPair
    State.empty [] actions StateRepresentedBy.empty hhit

theorem runObserved_empty_eq_true_mono_sublist
    {left right : List ObservedAction}
    (hsub : List.Sublist left right)
    (hnodup : (observedSignEpochs right).Nodup)
    (hhit : runObserved State.empty left = true) :
    runObserved State.empty right = true := by
  have hsignSub := observedSignEpochs_sublist hsub
  have hleftNodup := hsignSub.nodup hnodup
  exact runObserved_empty_eq_true_of_collisionPair right hnodup
    ((collisionPair_of_runObserved_empty_eq_true left hleftNodup hhit).mono hsub)

end XmssSecurity.EncodingMonitor
