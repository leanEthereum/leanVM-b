import XmssSecurity.Proof.CappedEncodingMonitor

namespace XmssSecurity.CappedEncodingMonitor

structure OnlineState where
  current : Option EncodingMonitor.State
  hit : Bool

def OnlineState.initial : OnlineState :=
  ⟨some EncodingMonitor.State.empty, false⟩

noncomputable def OnlineState.observe
    (state : OnlineState)
    (action : EncodingMonitor.ObservedAction) : OnlineState :=
  if state.hit then state
  else
    match state.current with
    | none => state
    | some current =>
        match State.applyObserved current action with
        | none => ⟨none, false⟩
        | some (next, hit) => ⟨some next, hit⟩

noncomputable def OnlineState.observeAll :
    OnlineState → List EncodingMonitor.ObservedAction → OnlineState
  | state, [] => state
  | state, action :: rest => observeAll (state.observe action) rest

theorem OnlineState.observeAll_append
    (state : OnlineState)
    (left right : List EncodingMonitor.ObservedAction) :
    state.observeAll (left ++ right) =
      (state.observeAll left).observeAll right := by
  induction left generalizing state with
  | nil => rfl
  | cons action left ih =>
      simpa [observeAll] using ih (state.observe action)

@[simp] theorem OnlineState.observeAll_none
    (actions : List EncodingMonitor.ObservedAction) :
    (⟨none, false⟩ : OnlineState).observeAll actions = ⟨none, false⟩ := by
  induction actions with
  | nil => rfl
  | cons action actions ih => simp [observeAll, OnlineState.observe, ih]

@[simp] theorem OnlineState.observeAll_hit_true
    (current : Option EncodingMonitor.State)
    (actions : List EncodingMonitor.ObservedAction) :
    (⟨current, true⟩ : OnlineState).observeAll actions = ⟨current, true⟩ := by
  induction actions with
  | nil => rfl
  | cons action actions ih => simp [observeAll, OnlineState.observe, ih]

theorem OnlineState.observeAll_hit
    (initial : EncodingMonitor.State)
    (actions : List EncodingMonitor.ObservedAction) :
    ((⟨some initial, false⟩ : OnlineState).observeAll actions).hit =
      runObserved initial actions := by
  induction actions generalizing initial with
  | nil => rfl
  | cons action actions ih =>
      cases happly : State.applyObserved initial action with
      | none => simp [observeAll, OnlineState.observe, runObserved, happly]
      | some result =>
          rcases result with ⟨next, hit⟩
          cases hit with
          | false =>
              simpa [observeAll, OnlineState.observe, runObserved, happly]
                using ih next
          | true =>
              simp [observeAll, OnlineState.observe, runObserved, happly]

theorem OnlineState.observeAll_initial_hit
    (actions : List EncodingMonitor.ObservedAction) :
    (OnlineState.initial.observeAll actions).hit =
      runObserved EncodingMonitor.State.empty actions :=
  OnlineState.observeAll_hit EncodingMonitor.State.empty actions

end XmssSecurity.CappedEncodingMonitor
