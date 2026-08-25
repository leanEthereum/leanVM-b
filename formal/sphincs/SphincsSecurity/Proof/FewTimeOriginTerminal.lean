import SphincsSecurity.Proof.FewTimeOriginInvariant
import SphincsSecurity.Proof.FewTimeOriginPadding

/-!
# Terminal realization of the few-time origin monitor

The retained viewed trace determines the monitor fields by a pure chronological replay. This
module connects a concretely realized padded cover to the terminal event used by the adaptive
fixed-configuration bound.
-/

namespace SphincsSecurity

open OracleComp OracleSpec

namespace Concrete

theorem Fin.encodeSubtype_val_lt_of_val_lt {n : Nat} (P : Fin n → Prop)
    [DecidablePred P] (left right : {position : Fin n // P position})
    (hlt : left.1.val < right.1.val) :
    (Fin.encodeSubtype P left).val < (Fin.encodeSubtype P right).val := by
  induction n with
  | zero => exact Fin.elim0 left.1
  | succ n ih =>
      rcases left with ⟨left, hleft⟩
      rcases right with ⟨right, hright⟩
      cases left using Fin.cases with
      | zero =>
          cases right using Fin.cases with
          | zero => omega
          | succ right =>
              rw [Fin.encodeSubtype_zero_pos hleft,
                Fin.encodeSubtype_succ_pos hleft hright]
              simp
      | succ left =>
          cases right using Fin.cases with
          | zero => simp at hlt
          | succ right =>
              by_cases hzero : P 0
              · rw [Fin.encodeSubtype_succ_pos hzero hleft,
                  Fin.encodeSubtype_succ_pos hzero hright]
                simpa using ih (fun position => P position.succ)
                  ⟨left, hleft⟩ ⟨right, hright⟩ (by simpa using hlt)
              · rw [Fin.encodeSubtype_succ_neg hzero hleft,
                  Fin.encodeSubtype_succ_neg hzero hright]
                simpa using ih (fun position => P position.succ)
                  ⟨left, hleft⟩ ⟨right, hright⟩ (by simpa using hlt)

theorem Fin.encodeSubtype_val_congr {n : Nat} (P Q : Fin n → Prop)
    [DecidablePred P] [DecidablePred Q]
    (hiff : ∀ position, P position ↔ Q position)
    (left : {position : Fin n // P position})
    (right : {position : Fin n // Q position})
    (heq : left.1 = right.1) :
    (Fin.encodeSubtype P left).val = (Fin.encodeSubtype Q right).val := by
  induction n with
  | zero => exact Fin.elim0 left.1
  | succ n ih =>
      rcases left with ⟨left, hleft⟩
      rcases right with ⟨right, hright⟩
      change left = right at heq
      subst right
      cases left using Fin.cases with
      | zero =>
          rw [Fin.encodeSubtype_zero_pos hleft,
            Fin.encodeSubtype_zero_pos hright]
      | succ left =>
          by_cases hzero : P 0
          · have hzero' : Q 0 := (hiff 0).1 hzero
            rw [Fin.encodeSubtype_succ_pos hzero hleft,
              Fin.encodeSubtype_succ_pos hzero' hright]
            simpa using ih (fun position => P position.succ)
              (fun position => Q position.succ) (fun position => hiff position.succ)
              ⟨left, hleft⟩ ⟨left, hright⟩ rfl
          · have hzero' : ¬Q 0 := fun hq => hzero ((hiff 0).2 hq)
            rw [Fin.encodeSubtype_succ_neg hzero hleft,
              Fin.encodeSubtype_succ_neg hzero' hright]
            simpa using ih (fun position => P position.succ)
              (fun position => Q position.succ) (fun position => hiff position.succ)
              ⟨left, hleft⟩ ⟨left, hright⟩ rfl

inductive OriginReplayEvent where
  | uniform
  | direct (input : HashInput) (output : HashOutput)
      (initialCache finalCache : QueryCache HashSpec)
  | signer (request : SignRequest) (signature : Option Signature)
      (view : Option FewTimeView) (initialCache finalCache : QueryCache HashSpec)

def OriginReplayEvent.directIncrement : OriginReplayEvent → Nat
  | .direct _ _ _ _ => 1
  | _ => 0

def OriginReplayEvent.signerIncrement : OriginReplayEvent → Nat
  | .signer _ _ _ _ _ => 1
  | _ => 0

def OriginReplayEvents.directCount : List OriginReplayEvent → Nat
  | [] => 0
  | event :: events => event.directIncrement + OriginReplayEvents.directCount events

def OriginReplayEvents.signerCount : List OriginReplayEvent → Nat
  | [] => 0
  | event :: events => event.signerIncrement + OriginReplayEvents.signerCount events

structure OriginReplayState {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) where
  observation : OriginObservation configuration
  directOrdinal : Nat
  signerOrdinal : Nat
  valid : Bool

noncomputable def OriginReplayState.initial {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) : OriginReplayState configuration :=
  ⟨OriginObservation.empty configuration, 0, 0, true⟩

def OriginReplayState.asMonitor {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginReplayState configuration) (cache : QueryCache HashSpec) :
    OriginMonitorState configuration :=
  ⟨⟨cache, ⟨[], [], []⟩, [], none⟩, state.observation, state.directOrdinal,
    state.signerOrdinal, state.valid⟩

noncomputable def OriginReplayState.step {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (secretKey : SecretKey) (state : OriginReplayState configuration) :
    OriginReplayEvent → OriginReplayState configuration
  | .uniform => state
  | .direct input output initialCache _ =>
      let monitored := monitorDirectSource (state.asMonitor initialCache) input output
      ⟨monitored.1, state.directOrdinal + 1, state.signerOrdinal, monitored.2⟩
  | .signer request signature view initialCache finalCache =>
      let monitored := monitorSigner secretKey request (state.asMonitor initialCache)
        ((signature, view), finalCache)
      ⟨monitored.1, state.directOrdinal, state.signerOrdinal + 1, monitored.2⟩

@[simp] theorem OriginReplayState.step_directOrdinal {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (secretKey : SecretKey) (state : OriginReplayState configuration)
    (event : OriginReplayEvent) :
    (state.step secretKey event).directOrdinal =
      state.directOrdinal + event.directIncrement := by
  cases event <;> simp [OriginReplayState.step, OriginReplayEvent.directIncrement]

@[simp] theorem OriginReplayState.step_signerOrdinal {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (secretKey : SecretKey) (state : OriginReplayState configuration)
    (event : OriginReplayEvent) :
    (state.step secretKey event).signerOrdinal =
      state.signerOrdinal + event.signerIncrement := by
  cases event <;> simp [OriginReplayState.step, OriginReplayEvent.signerIncrement]

noncomputable def replayOriginEvents {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (events : List OriginReplayEvent) : OriginReplayState configuration :=
  events.foldl (OriginReplayState.step secretKey) (OriginReplayState.initial configuration)

def originReplayEvents : List AdversaryCacheEntry → List (Option FewTimeView) →
    List OriginReplayEvent
  | [], _ => []
  | ⟨.inl (.inl _), _, _, _⟩ :: rest, views =>
      .uniform :: originReplayEvents rest views
  | ⟨.inl (.inr input), output, initialCache, finalCache⟩ :: rest, views =>
      .direct input output initialCache finalCache :: originReplayEvents rest views
  | ⟨.inr request, signature, initialCache, finalCache⟩ :: rest, [] =>
      .signer request signature none initialCache finalCache :: originReplayEvents rest []
  | ⟨.inr request, signature, initialCache, finalCache⟩ :: rest, view :: views =>
      .signer request signature view initialCache finalCache :: originReplayEvents rest views

def directIntervalCount (intervals : List AdversaryCacheEntry) : Nat :=
  (intervals.filter fun entry => isDirectHashQuery entry.input).length

def signerIntervalCount (intervals : List AdversaryCacheEntry) : Nat :=
  (intervals.filterMap AdversaryCacheEntry.signingEntry?).length

theorem originReplayEvents_length (intervals : List AdversaryCacheEntry)
    (views : List (Option FewTimeView)) :
    (originReplayEvents intervals views).length = intervals.length := by
  induction intervals generalizing views with
  | nil => rfl
  | cons entry intervals ih =>
      rcases entry with ⟨input, output, initialCache, finalCache⟩
      cases input with
      | inl worldInput =>
          cases worldInput <;> simp [originReplayEvents, ih]
      | inr request =>
          cases views <;> simp [originReplayEvents, ih]

theorem originReplayEvents_take_counts (intervals : List AdversaryCacheEntry)
    (views : List (Option FewTimeView)) (count : Nat) :
    OriginReplayEvents.directCount (originReplayEvents intervals views |>.take count) =
        directIntervalCount (intervals.take count)
      ∧ OriginReplayEvents.signerCount (originReplayEvents intervals views |>.take count) =
        signerIntervalCount (intervals.take count) := by
  induction intervals generalizing views count with
  | nil => simp [originReplayEvents, OriginReplayEvents.directCount,
      OriginReplayEvents.signerCount, directIntervalCount, signerIntervalCount]
  | cons entry intervals ih =>
      cases count with
      | zero => simp [OriginReplayEvents.directCount, OriginReplayEvents.signerCount,
          directIntervalCount, signerIntervalCount]
      | succ count =>
          rcases entry with ⟨input, output, initialCache, finalCache⟩
          cases input with
          | inl worldInput =>
              cases worldInput with
              | inl uniformInput =>
                  simpa [originReplayEvents, OriginReplayEvents.directCount,
                    OriginReplayEvents.signerCount, OriginReplayEvent.directIncrement,
                    OriginReplayEvent.signerIncrement, directIntervalCount,
                    signerIntervalCount, isDirectHashQuery,
                    AdversaryCacheEntry.signingEntry?, Nat.add_comm] using ih views count
              | inr hashInput =>
                  simpa [originReplayEvents, OriginReplayEvents.directCount,
                    OriginReplayEvents.signerCount, OriginReplayEvent.directIncrement,
                    OriginReplayEvent.signerIncrement, directIntervalCount,
                    signerIntervalCount, isDirectHashQuery,
                    AdversaryCacheEntry.signingEntry?, Nat.add_comm] using ih views count
          | inr request =>
              cases views with
              | nil =>
                  simpa [originReplayEvents, OriginReplayEvents.directCount,
                    OriginReplayEvents.signerCount, OriginReplayEvent.directIncrement,
                    OriginReplayEvent.signerIncrement, directIntervalCount,
                    signerIntervalCount, isDirectHashQuery,
                    AdversaryCacheEntry.signingEntry?, Nat.add_comm] using ih [] count
              | cons view views =>
                  simpa [originReplayEvents, OriginReplayEvents.directCount,
                    OriginReplayEvents.signerCount, OriginReplayEvent.directIncrement,
                    OriginReplayEvent.signerIncrement, directIntervalCount,
                    signerIntervalCount, isDirectHashQuery,
                    AdversaryCacheEntry.signingEntry?, Nat.add_comm] using ih views count

theorem originReplayEvents_counts (intervals : List AdversaryCacheEntry)
    (views : List (Option FewTimeView)) :
    OriginReplayEvents.directCount (originReplayEvents intervals views) =
        directIntervalCount intervals
      ∧ OriginReplayEvents.signerCount (originReplayEvents intervals views) =
        signerIntervalCount intervals := by
  have hcounts := originReplayEvents_take_counts intervals views intervals.length
  have htake : (originReplayEvents intervals views).take intervals.length =
      originReplayEvents intervals views := by
    rw [← originReplayEvents_length intervals views]
    exact List.take_length
  rw [htake, List.take_length] at hcounts
  exact hcounts

theorem encodeSubtype_directInterval_eq (intervals : List AdversaryCacheEntry)
    (position : Fin intervals.length)
    (hdirect : isDirectHashQuery (intervals.get position).input) :
    (Fin.encodeSubtype (fun candidate =>
      isDirectHashQuery (intervals.get candidate).input) ⟨position, hdirect⟩).val =
      directIntervalCount (intervals.take position.val) := by
  induction intervals with
  | nil => exact Fin.elim0 position
  | cons entry intervals ih =>
      cases position using Fin.cases with
      | zero =>
          have hzero : isDirectHashQuery
              ((entry :: intervals).get (0 : Fin (entry :: intervals).length)).input :=
            hdirect
          rw [Fin.encodeSubtype_zero_pos hzero]
          simp [directIntervalCount]
      | succ position =>
          have htail : isDirectHashQuery (intervals.get position).input := by
            simpa using hdirect
          by_cases hhead : isDirectHashQuery entry.input
          · have hzero : isDirectHashQuery
                ((entry :: intervals).get (0 : Fin (entry :: intervals).length)).input := by
              simpa using hhead
            have hencode := Fin.encodeSubtype_val_congr
              (fun candidate : Fin intervals.length =>
                isDirectHashQuery ((entry :: intervals).get candidate.succ).input)
              (fun candidate : Fin intervals.length =>
                isDirectHashQuery (intervals.get candidate).input)
              (by intro candidate; simp)
              ⟨position, hdirect⟩ ⟨position, htail⟩ rfl
            rw [Fin.encodeSubtype_succ_pos hzero hdirect]
            simp only [Fin.val_cast, Fin.val_succ]
            rw [hencode, ih position htail]
            simp [directIntervalCount, hhead, Nat.add_comm]
          · have hzero : ¬isDirectHashQuery
                ((entry :: intervals).get (0 : Fin (entry :: intervals).length)).input := by
              simpa using hhead
            have hencode := Fin.encodeSubtype_val_congr
              (fun candidate : Fin intervals.length =>
                isDirectHashQuery ((entry :: intervals).get candidate.succ).input)
              (fun candidate : Fin intervals.length =>
                isDirectHashQuery (intervals.get candidate).input)
              (by intro candidate; simp)
              ⟨position, hdirect⟩ ⟨position, htail⟩ rfl
            rw [Fin.encodeSubtype_succ_neg hzero hdirect]
            simp only [Fin.val_cast]
            rw [hencode, ih position htail]
            simp [directIntervalCount, hhead]

theorem encodeSubtype_directInterval_lt_count_take
    (intervals : List AdversaryCacheEntry)
    (position : Fin intervals.length)
    (hdirect : isDirectHashQuery (intervals.get position).input)
    (later : Nat) (hbefore : position.val < later) :
    (Fin.encodeSubtype (fun candidate =>
      isDirectHashQuery (intervals.get candidate).input) ⟨position, hdirect⟩).val <
      directIntervalCount (intervals.take later) := by
  have hsucc : directIntervalCount (intervals.take (position.val + 1)) =
      directIntervalCount (intervals.take position.val) + 1 := by
    have hgetDirect : isDirectHashQuery intervals[position.val].input := by
      simpa only [List.get_eq_getElem] using hdirect
    rw [List.take_succ_eq_append_getElem position.isLt]
    simp only [directIntervalCount, List.filter_append, List.filter_singleton,
      hgetDirect, List.length_append]
    simp
  have hprefix : position.val + 1 ≤ later := by omega
  have hsublist := List.take_sublist_take_left (l := intervals) hprefix
  have hcount :
      (intervals.take (position.val + 1)).countP
          (fun entry => decide (isDirectHashQuery entry.input)) ≤
        (intervals.take later).countP
          (fun entry => decide (isDirectHashQuery entry.input)) :=
    hsublist.countP_le
  rw [List.countP_eq_length_filter, List.countP_eq_length_filter] at hcount
  change directIntervalCount (intervals.take (position.val + 1)) ≤
    directIntervalCount (intervals.take later) at hcount
  rw [hsucc, ← encodeSubtype_directInterval_eq intervals position hdirect] at hcount
  omega

def originReplayEventOfEntry (entry : AdversaryCacheEntry)
    (view : Option FewTimeView) : OriginReplayEvent :=
  match entry with
  | ⟨.inl (.inl _), _, _, _⟩ => .uniform
  | ⟨.inl (.inr input), output, initialCache, finalCache⟩ =>
      .direct input output initialCache finalCache
  | ⟨.inr request, signature, initialCache, finalCache⟩ =>
      .signer request signature view initialCache finalCache

theorem originReplayEvents_get (intervals : List AdversaryCacheEntry)
    (views : List (Option FewTimeView)) (position : Fin intervals.length) :
    (originReplayEvents intervals views).get
        ⟨position.val, by rw [originReplayEvents_length]; exact position.isLt⟩ =
      originReplayEventOfEntry (intervals.get position)
        (views[signerIntervalCount (intervals.take position.val)]?.getD none) := by
  induction intervals generalizing views with
  | nil => exact Fin.elim0 position
  | cons entry intervals ih =>
      cases position using Fin.cases with
      | zero =>
          rcases entry with ⟨input, output, initialCache, finalCache⟩
          cases input with
          | inl worldInput =>
              cases worldInput <;>
                simp [originReplayEvents, originReplayEventOfEntry]
          | inr request =>
              cases views <;>
                simp [originReplayEvents, originReplayEventOfEntry, signerIntervalCount]
      | succ position =>
          rcases entry with ⟨input, output, initialCache, finalCache⟩
          cases input with
          | inl worldInput =>
              cases worldInput <;>
                simpa [originReplayEvents, originReplayEventOfEntry,
                  signerIntervalCount, AdversaryCacheEntry.signingEntry?] using
                    ih views position
          | inr request =>
              cases views with
              | nil =>
                  simpa [originReplayEvents, originReplayEventOfEntry,
                    signerIntervalCount, AdversaryCacheEntry.signingEntry?] using
                      ih [] position
              | cons view views =>
                  simpa [originReplayEvents, originReplayEventOfEntry,
                    signerIntervalCount, AdversaryCacheEntry.signingEntry?] using
                      ih views position

theorem filterMap_getElem?_at_rank {α β : Type} (filter : α → Option β)
    (list : List α) (position : Fin list.length) (value : β)
    (hvalue : filter (list.get position) = some value) :
    (list.filterMap filter)[((list.take position.val).filterMap filter).length]? =
      some value := by
  induction list with
  | nil => exact Fin.elim0 position
  | cons head list ih =>
      cases position using Fin.cases with
      | zero =>
          have hhead : filter head = some value := by simpa using hvalue
          simp [hhead]
      | succ position =>
          have htail : filter (list.get position) = some value := by
            simpa using hvalue
          cases hhead : filter head with
          | none => simpa [hhead] using ih position htail
          | some headValue => simpa [hhead] using ih position htail

theorem filterMap_take_length_lt_of_lt {α β : Type} (filter : α → Option β)
    (list : List α) (left right : Fin list.length)
    (value : β) (hvalue : filter (list.get left) = some value)
    (hlt : left.val < right.val) :
    ((list.take left.val).filterMap filter).length <
      ((list.take right.val).filterMap filter).length := by
  have hsucc : ((list.take (left.val + 1)).filterMap filter).length =
      ((list.take left.val).filterMap filter).length + 1 := by
    rw [List.take_succ_eq_append_getElem left.isLt]
    have hvalue' : filter list[left.val] = some value := by
      simpa only [List.get_eq_getElem] using hvalue
    simp only [List.filterMap_append, List.length_append]
    simp [hvalue']
  have hprefix : left.val + 1 ≤ right.val := by omega
  have hsublist := List.take_sublist_take_left (l := list) hprefix
  have hcount :
      (list.take (left.val + 1)).countP (fun entry => (filter entry).isSome) ≤
        (list.take right.val).countP (fun entry => (filter entry).isSome) :=
    hsublist.countP_le
  rw [← List.length_filterMap_eq_countP,
    ← List.length_filterMap_eq_countP] at hcount
  rw [hsucc] at hcount
  omega

theorem filterMap_take_length_injective_at_some {α β : Type}
    (filter : α → Option β) (list : List α)
    (left right : Fin list.length) (leftValue rightValue : β)
    (hleft : filter (list.get left) = some leftValue)
    (hright : filter (list.get right) = some rightValue)
    (hrank : ((list.take left.val).filterMap filter).length =
      ((list.take right.val).filterMap filter).length) :
    left = right := by
  apply Fin.ext
  rcases lt_trichotomy left.val right.val with hlt | heq | hgt
  · have := filterMap_take_length_lt_of_lt filter list left right leftValue hleft hlt
    omega
  · exact heq
  · have := filterMap_take_length_lt_of_lt filter list right left rightValue hright hgt
    omega

theorem FullAdversaryTrace.Chronological.get_finalCache_le_initialCache
    {intervals : List AdversaryCacheEntry}
    (hchronological : FullAdversaryTrace.Chronological intervals)
    (earlier later : Fin intervals.length) (hlt : earlier.val < later.val) :
    (intervals.get earlier).finalCache ≤ (intervals.get later).initialCache := by
  induction intervals with
  | nil => exact Fin.elim0 earlier
  | cons head rest ih =>
      cases earlier using Fin.cases with
      | zero =>
          cases later using Fin.cases with
          | zero => simp at hlt
          | succ later =>
              exact hchronological.1 (rest.get later) (List.get_mem rest later)
      | succ earlier =>
          cases later using Fin.cases with
          | zero => simp at hlt
          | succ later =>
              exact ih hchronological.2 earlier later (by simpa using hlt)

noncomputable def FewTimeCover.paddedEntry {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    {limit : Nat} (hle : signingLog.length ≤ limit)
    (selected : (cover.pattern.pad hle).selected) : cover.entries :=
  cover.entriesEquivPatternSelected.symm
    ((cover.pattern.padSelectedEquiv hle).symm selected)

noncomputable def FewTimeCover.paddedExpectedViews {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    {limit : Nat} (hle : signingLog.length ≤ limit) :
    (cover.pattern.pad hle).selected → FewTimeView :=
  fun selected => cover.entryView (cover.paddedEntry hle selected)

noncomputable def FewTimeCover.paddedExpectedInputs {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    {q limit : Nat} (hle : signingLog.length ≤ limit)
    (configuration : OriginConfiguration (cover.pattern.pad hle) q) :
    ↑configuration.prehit → HashInput :=
  fun selected => cover.entryDigestInput (cover.paddedEntry hle selected.1)

theorem FewTimeCover.paddedExpectedViews_fixedPatternHit {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    {limit : Nat} (hle : signingLog.length ≤ limit) :
    FixedFewTimePatternHit (cover.pattern.pad hle).assignment
      (cover.paddedExpectedViews hle, fewTimeTargetView index targetLeaves) := by
  constructor
  · intro selected
    change (cover.entryView (cover.paddedEntry hle selected)).1 = index
    exact cover.entryDigest_index (cover.paddedEntry hle selected)
  · intro tree
    have hentry : cover.paddedEntry hle ((cover.pattern.pad hle).assignment tree) =
        cover.entryAssignment tree := by
      apply cover.entriesEquivPatternSelected.injective
      rw [FewTimeCover.paddedEntry,
        cover.entriesEquivPatternSelected.apply_symm_apply]
      apply (cover.pattern.padSelectedEquiv hle).injective
      rw [(cover.pattern.padSelectedEquiv hle).apply_symm_apply]
      rfl
    change targetLeaves (ftsIndexOf tree) =
      (cover.entryView
        (cover.paddedEntry hle ((cover.pattern.pad hle).assignment tree))).2 tree
    rw [hentry]
    exact (cover.entryDigest_assigned_leaf tree).symm

theorem FewTimeCover.entriesEquivPatternSelected_val {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (entry : cover.entries) :
    (cover.entriesEquivPatternSelected entry).1 = cover.logIndex entry := rfl

theorem FewTimePattern.padSelectedEquiv_symm_val {small large distinct : Nat}
    (pattern : FewTimePattern small distinct) (hle : small ≤ large)
    (selected : (pattern.pad hle).selected) :
    ((pattern.padSelectedEquiv hle).symm selected).1.val = selected.1.val := by
  have happly := (pattern.padSelectedEquiv hle).apply_symm_apply selected
  have hval := congrArg (fun value => value.1.val) happly
  rw [FewTimePattern.padSelectedEquiv_apply] at hval
  exact hval

theorem FewTimeCover.paddedEntry_logIndex_val {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    {limit : Nat} (hle : signingLog.length ≤ limit)
    (selected : (cover.pattern.pad hle).selected) :
    (cover.logIndex (cover.paddedEntry hle selected)).val = selected.1.val := by
  let oldSelected := (cover.pattern.padSelectedEquiv hle).symm selected
  have happly := cover.entriesEquivPatternSelected.apply_symm_apply oldSelected
  have hval := congrArg (fun value => value.1.val) happly
  rw [cover.entriesEquivPatternSelected_val] at hval
  exact hval.trans (cover.pattern.padSelectedEquiv_symm_val hle selected)

theorem FewTimeCover.originReplayEvents_get_signer {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    (state : ViewedFullTraceState)
    (hlog : state.trace.signing.toSigningLog = signingLog)
    (hvalid : state.ValidViews secretKey)
    (hconsistent : state.trace.Consistent)
    (hcaches : state.trace.signing.CachesLe cache) (hf : cache.AgreesWithFn f)
    {limit : Nat} (hle : signingLog.length ≤ limit)
    (selected : (cover.pattern.pad hle).selected)
    (position : Fin state.trace.intervals.length)
    (request : SignRequest) (signature : Option Signature)
    (initialCache finalCache : QueryCache HashSpec)
    (hinterval : state.trace.intervals.get position =
      ⟨.inr request, signature, initialCache, finalCache⟩)
    (hrank : signerIntervalCount (state.trace.intervals.take position.val) =
      selected.1.val) :
    (originReplayEvents state.trace.intervals state.views).get
        ⟨position.val, by rw [originReplayEvents_length]; exact position.isLt⟩ =
      .signer request signature (some (cover.paddedExpectedViews hle selected))
        initialCache finalCache
      ∧ (⟨request, signature, initialCache, finalCache⟩ : SigningCacheEntry) =
        cover.cacheEntry state.trace.signing hlog (cover.paddedEntry hle selected) := by
  let entry := cover.paddedEntry hle selected
  let signingEntry : SigningCacheEntry :=
    ⟨request, signature, initialCache, finalCache⟩
  have hsigning : AdversaryCacheEntry.signingEntry?
      (state.trace.intervals.get position) = some signingEntry := by
    rw [hinterval]
    rfl
  have hfiltered := filterMap_getElem?_at_rank
    AdversaryCacheEntry.signingEntry? state.trace.intervals position signingEntry hsigning
  rw [hconsistent.2] at hfiltered
  have hentryRank : (cover.logIndex entry).val = selected.1.val :=
    cover.paddedEntry_logIndex_val hle selected
  have hcacheEntry : signingEntry =
      cover.cacheEntry state.trace.signing hlog entry := by
    change state.trace.signing[signerIntervalCount
      (state.trace.intervals.take position.val)]? = some signingEntry at hfiltered
    rw [hrank, ← hentryRank] at hfiltered
    rw [List.getElem?_eq_getElem] at hfiltered
    · simpa [entry, signingEntry, FewTimeCover.cacheEntry] using
        (Option.some.inj hfiltered).symm
  have hview := cover.signingOptionViews_traceIndex_eq_entryView state hlog hvalid
    hcaches hf entry
  have hviewGet : state.views[(cover.logIndex entry).val]? =
      some (some (cover.entryView entry)) := by
    rw [List.getElem?_eq_getElem]
    · exact congrArg some hview
    · rw [← hvalid.length_eq]
      have hlength := congrArg List.length hlog
      simpa only [SigningCacheTrace.toSigningLog, List.length_map] using
        (show (cover.logIndex entry).val < state.trace.signing.toSigningLog.length by
          rw [hlength]
          exact (cover.logIndex entry).isLt)
  constructor
  · rw [originReplayEvents_get state.trace.intervals state.views position, hinterval]
    simp only [originReplayEventOfEntry]
    rw [hrank, ← hentryRank, hviewGet]
    rfl
  · exact hcacheEntry

theorem OriginConfiguration.paddedRealized_direct_good {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    {cover : FewTimeCover f cache secretKey signingLog index targetLeaves}
    {q limit : Nat} {hle : signingLog.length ≤ limit}
    {configuration : OriginConfiguration (cover.pattern.pad hle) q}
    {trace : FullAdversaryTrace} {hlog : trace.signing.toSigningLog = signingLog}
    (hrealized : configuration.PaddedRealizedBy cover hle trace hlog)
    (hvalid : trace.ValidIntervals secretKey)
    (position : Fin trace.intervals.length)
    (input : HashInput) (output : HashOutput)
    (initialCache finalCache : QueryCache HashSpec)
    (hinterval : trace.intervals.get position =
      ⟨.inl (.inr input), output, initialCache, finalCache⟩)
    (directOrdinal : Nat)
    (hrank : directIntervalCount (trace.intervals.take position.val) = directOrdinal)
    (selected : ↑configuration.prehit)
    (hsourceAt : configuration.sourceAt? directOrdinal = some selected) :
    input = cover.paddedExpectedInputs hle configuration selected
      ∧ initialCache input = none
      ∧ signAttemptResultOfOutput output ≠ none
      ∧ hashOutputFewTimeView output =
        cover.paddedExpectedViews hle selected.1 := by
  classical
  let oldSelected := (cover.pattern.padSelectedEquiv hle).symm selected.1
  let entry := cover.entriesEquivPatternSelected.symm oldSelected
  have hpadded : cover.pattern.padSelectedEquiv hle oldSelected = selected.1 :=
    (cover.pattern.padSelectedEquiv hle).apply_symm_apply selected.1
  have hselected : cover.pattern.padSelectedEquiv hle
      (cover.entriesEquivPatternSelected entry) ∈ configuration.prehit := by
    have hentrySelected : cover.entriesEquivPatternSelected entry = oldSelected :=
      cover.entriesEquivPatternSelected.apply_symm_apply oldSelected
    rw [hentrySelected, hpadded]
    exact selected.2
  have hprecached : cover.EntryDigestPrecached trace.signing hlog entry := by
    apply (hrealized.1 oldSelected).1
    simpa [entry] using hselected
  let precached : cover.PrecachedEntries trace.signing hlog := ⟨entry, hprecached⟩
  obtain ⟨sourceOutput, sourcePosition, intervalPosition, selectedIntervalPosition,
    hdirect, hsource, hordinal, hbefore, hselectedInterval, hselectedRank,
    hinput, hmiss, hrun, hsuccess, hview⟩ := hrealized.2 precached hselected
  let realizedSelected : ↑configuration.prehit :=
    ⟨cover.pattern.padSelectedEquiv hle
      (cover.entriesEquivPatternSelected entry), hselected⟩
  have hselectedEq : realizedSelected = selected := by
    apply Subtype.ext
    change cover.pattern.padSelectedEquiv hle
      (cover.entriesEquivPatternSelected entry) = selected.1
    rw [cover.entriesEquivPatternSelected.apply_symm_apply oldSelected, hpadded]
  have hsourceValue : sourcePosition.val =
      (configuration.source.1 selected).val := by
    change sourcePosition.val = (configuration.source.1 realizedSelected).val at hsource
    rwa [hselectedEq] at hsource
  have hlookup := (configuration.sourceAt?_eq_some_iff directOrdinal selected).1 hsourceAt
  have hcurrentEncode := encodeSubtype_directInterval_eq trace.intervals position (by
    rw [hinterval]
    trivial)
  have hsourceEncode :
      (Fin.encodeSubtype (fun candidate =>
        isDirectHashQuery (trace.intervals.get candidate).input)
        ⟨intervalPosition, hdirect⟩).val =
      (Fin.encodeSubtype (fun candidate =>
        isDirectHashQuery (trace.intervals.get candidate).input)
        ⟨position, by rw [hinterval]; trivial⟩).val := by
    calc
      _ = sourcePosition.val := hordinal.symm
      _ = (configuration.source.1 selected).val := hsourceValue
      _ = directOrdinal := hlookup
      _ = directIntervalCount (trace.intervals.take position.val) := hrank.symm
      _ = _ := hcurrentEncode.symm
  have hencoded : Fin.encodeSubtype (fun candidate =>
        isDirectHashQuery (trace.intervals.get candidate).input)
        ⟨intervalPosition, hdirect⟩ =
      Fin.encodeSubtype (fun candidate =>
        isDirectHashQuery (trace.intervals.get candidate).input)
        ⟨position, by rw [hinterval]; trivial⟩ :=
    Fin.ext hsourceEncode
  have hpositions := congrArg (Fin.decodeSubtype (fun candidate =>
    isDirectHashQuery (trace.intervals.get candidate).input)) hencoded
  simp only [Fin.decodeSubtype_encodeSubtype] at hpositions
  have hposition : intervalPosition = position := congrArg Subtype.val hpositions
  subst intervalPosition
  have hinput' : input = cover.entryDigestInput entry := by
    rw [hinterval] at hinput
    simpa using hinput
  subst input
  have hmiss' : initialCache (cover.entryDigestInput entry) = none := by
    rw [hinterval] at hmiss
    exact hmiss
  have hrun' : (sourceOutput, finalCache) ∈ support
      ((randomOracle (cover.entryDigestInput entry)).run initialCache) := by
    change (sourceOutput, (trace.intervals.get position).finalCache) ∈ support
      ((randomOracle (cover.entryDigestInput entry)).run
        (trace.intervals.get position).initialCache) at hrun
    rwa [hinterval] at hrun
  have hsourceCached := randomOracle_run_output_cached
    (cover.entryDigestInput entry) initialCache finalCache sourceOutput hrun'
  have hentryMem : (⟨.inl (.inr (cover.entryDigestInput entry)), output,
      initialCache, finalCache⟩ : AdversaryCacheEntry) ∈ trace.intervals := by
    rw [← hinterval]
    exact List.get_mem trace.intervals position
  have hactualCached := trace.directHashInterval_cached hvalid
    (cover.entryDigestInput entry) output initialCache finalCache hentryMem
  have houtput : output = sourceOutput :=
    Option.some.inj (hactualCached.symm.trans hsourceCached)
  subst sourceOutput
  have hentryEq : cover.paddedEntry hle selected.1 = entry := rfl
  refine ⟨?_, hmiss', hsuccess, ?_⟩
  · change cover.entryDigestInput entry =
      cover.entryDigestInput (cover.paddedEntry hle selected.1)
    rw [hentryEq]
  · change hashOutputFewTimeView output =
      cover.entryView (cover.paddedEntry hle selected.1)
    rwa [hentryEq]

theorem OriginConfiguration.paddedRealized_source_lt_directIntervalCount
    {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    {cover : FewTimeCover f cache secretKey signingLog index targetLeaves}
    {q limit : Nat} {hle : signingLog.length ≤ limit}
    {configuration : OriginConfiguration (cover.pattern.pad hle) q}
    {trace : FullAdversaryTrace} {hlog : trace.signing.toSigningLog = signingLog}
    (hrealized : configuration.PaddedRealizedBy cover hle trace hlog)
    (selected : ↑configuration.prehit) :
    (configuration.source.1 selected).val < directIntervalCount trace.intervals := by
  classical
  let oldSelected := (cover.pattern.padSelectedEquiv hle).symm selected.1
  let entry := cover.entriesEquivPatternSelected.symm oldSelected
  have hpadded : cover.pattern.padSelectedEquiv hle oldSelected = selected.1 :=
    (cover.pattern.padSelectedEquiv hle).apply_symm_apply selected.1
  have hselected : cover.pattern.padSelectedEquiv hle
      (cover.entriesEquivPatternSelected entry) ∈ configuration.prehit := by
    rw [cover.entriesEquivPatternSelected.apply_symm_apply oldSelected, hpadded]
    exact selected.2
  have hprecached : cover.EntryDigestPrecached trace.signing hlog entry := by
    apply (hrealized.1 oldSelected).1
    simpa [entry] using hselected
  let precached : cover.PrecachedEntries trace.signing hlog := ⟨entry, hprecached⟩
  obtain ⟨_, sourcePosition, intervalPosition, _, hdirect, hsource, hordinal, _⟩ :=
    hrealized.2 precached hselected
  let realizedSelected : ↑configuration.prehit :=
    ⟨cover.pattern.padSelectedEquiv hle
      (cover.entriesEquivPatternSelected entry), hselected⟩
  have hselectedEq : realizedSelected = selected := by
    apply Subtype.ext
    change cover.pattern.padSelectedEquiv hle
      (cover.entriesEquivPatternSelected entry) = selected.1
    rw [cover.entriesEquivPatternSelected.apply_symm_apply oldSelected, hpadded]
  have hsourceValue : sourcePosition.val =
      (configuration.source.1 selected).val := by
    change sourcePosition.val = (configuration.source.1 realizedSelected).val at hsource
    rwa [hselectedEq] at hsource
  have hlt := encodeSubtype_directInterval_lt_count_take trace.intervals
    intervalPosition hdirect trace.intervals.length intervalPosition.isLt
  rw [List.take_length] at hlt
  rw [← hsourceValue, hordinal]
  exact hlt

theorem FewTimeCover.paddedSelected_lt_signingLog_length {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    (cover : FewTimeCover f cache secretKey signingLog index targetLeaves)
    {limit : Nat} (hle : signingLog.length ≤ limit)
    (selected : (cover.pattern.pad hle).selected) :
    selected.1.val < signingLog.length := by
  let oldSelected := (cover.pattern.padSelectedEquiv hle).symm selected
  rw [← cover.pattern.padSelectedEquiv_symm_val hle selected]
  exact oldSelected.1.isLt

def OriginReplayEvent.Good {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (event : OriginReplayEvent) (secretKey : SecretKey)
    (directOrdinal signerOrdinal : Nat)
    (expectedViews : pattern.selected → FewTimeView)
    (expectedInputs : ↑configuration.prehit → HashInput) : Prop :=
  match event with
  | .uniform => True
  | .direct input output initialCache _ =>
      ∀ selected, configuration.sourceAt? directOrdinal = some selected →
        input = expectedInputs selected
          ∧ initialCache input = none
          ∧ signAttemptResultOfOutput output ≠ none
          ∧ hashOutputFewTimeView output = expectedViews selected.1
  | .signer request signature view initialCache finalCache =>
      ∀ selected, pattern.selectedAt? signerOrdinal = some selected →
        if hprehit : selected ∈ configuration.prehit then
          (configuration.source.1 ⟨selected, hprehit⟩).val < directOrdinal
            ∧ PrehitSuccessfulSignerView
              (onlyInputCache initialCache (expectedInputs ⟨selected, hprehit⟩))
              secretKey request (fun value => value = expectedViews selected)
              ((signature, view), finalCache)
        else
          FreshSuccessfulSignerView initialCache secretKey request
            (fun value => value = expectedViews selected) ((signature, view), finalCache)

noncomputable def OriginReplayEvents.Good {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (secretKey : SecretKey)
    (expectedViews : pattern.selected → FewTimeView)
    (expectedInputs : ↑configuration.prehit → HashInput) :
    OriginReplayState configuration → List OriginReplayEvent → Prop
  | _, [] => True
  | state, event :: events =>
      event.Good secretKey state.directOrdinal state.signerOrdinal
          expectedViews expectedInputs
        ∧ OriginReplayEvents.Good secretKey expectedViews expectedInputs
          (state.step secretKey event) events

theorem OriginReplayEvents.good_of_get {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (secretKey : SecretKey)
    (expectedViews : pattern.selected → FewTimeView)
    (expectedInputs : ↑configuration.prehit → HashInput)
    (state : OriginReplayState configuration) (events : List OriginReplayEvent)
    (hgood : ∀ position : Fin events.length,
      (events.get position).Good secretKey
        (state.directOrdinal + OriginReplayEvents.directCount (events.take position.val))
        (state.signerOrdinal + OriginReplayEvents.signerCount (events.take position.val))
        expectedViews expectedInputs) :
    OriginReplayEvents.Good secretKey expectedViews expectedInputs state events := by
  induction events generalizing state with
  | nil => trivial
  | cons event events ih =>
      constructor
      · simpa [OriginReplayEvents.directCount, OriginReplayEvents.signerCount] using
          hgood ⟨0, by simp⟩
      · apply ih (state.step secretKey event)
        intro position
        have hnext := hgood ⟨position.val + 1, Nat.succ_lt_succ position.isLt⟩
        cases event <;>
          simpa [OriginReplayEvents.directCount, OriginReplayEvents.signerCount,
            OriginReplayEvent.directIncrement, OriginReplayEvent.signerIncrement,
            Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hnext

set_option maxHeartbeats 1000000 in
theorem OriginConfiguration.paddedRealized_replay_good {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    {cover : FewTimeCover f cache secretKey signingLog index targetLeaves}
    {q limit : Nat} {hle : signingLog.length ≤ limit}
    {configuration : OriginConfiguration (cover.pattern.pad hle) q}
    {state : ViewedFullTraceState}
    (hlog : state.trace.signing.toSigningLog = signingLog)
    (hrealized : configuration.PaddedRealizedBy cover hle state.trace hlog)
    (hvalidViews : state.ValidViews secretKey)
    (hconsistent : state.trace.Consistent)
    (hvalidIntervals : state.trace.ValidIntervals secretKey)
    (hchronological : FullAdversaryTrace.Chronological state.trace.intervals)
    (hcaches : state.trace.signing.CachesLe cache) (hf : cache.AgreesWithFn f) :
    OriginReplayEvents.Good secretKey (cover.paddedExpectedViews hle)
      (cover.paddedExpectedInputs hle configuration)
      (OriginReplayState.initial configuration)
      (originReplayEvents state.trace.intervals state.views) := by
  classical
  apply OriginReplayEvents.good_of_get
  intro eventPosition
  let intervalPosition : Fin state.trace.intervals.length :=
    ⟨eventPosition.val, by
      rw [← originReplayEvents_length state.trace.intervals state.views]
      exact eventPosition.isLt⟩
  have heventPosition : eventPosition =
      ⟨intervalPosition.val, by
        rw [originReplayEvents_length state.trace.intervals state.views]
        exact intervalPosition.isLt⟩ := Fin.ext rfl
  have hcounts := originReplayEvents_take_counts state.trace.intervals state.views
    intervalPosition.val
  have hevent := originReplayEvents_get state.trace.intervals state.views intervalPosition
  have heventAt : (originReplayEvents state.trace.intervals state.views).get
      eventPosition = originReplayEventOfEntry
        (state.trace.intervals.get intervalPosition)
        (state.views[signerIntervalCount
          (state.trace.intervals.take intervalPosition.val)]?.getD none) := by
    rw [heventPosition]
    exact hevent
  generalize hinterval : state.trace.intervals.get intervalPosition = interval at hevent heventAt
  rcases interval with ⟨input, output, initialCache, finalCache⟩
  cases input with
  | inl worldInput =>
      cases worldInput with
      | inl uniformInput =>
          simp [originReplayEventOfEntry] at heventAt
          have heventGet : (originReplayEvents state.trace.intervals state.views).get
              eventPosition = .uniform := by
            simpa only [List.get_eq_getElem] using heventAt
          rw [heventGet]
          simp only [OriginReplayEvent.Good]
      | inr hashInput =>
          simp only [originReplayEventOfEntry] at heventAt
          have heventGet : (originReplayEvents state.trace.intervals state.views).get
              eventPosition = .direct hashInput output initialCache finalCache := by
            simpa only [List.get_eq_getElem] using heventAt
          rw [heventGet]
          intro selected hsourceAt
          exact configuration.paddedRealized_direct_good hrealized hvalidIntervals
            intervalPosition hashInput output initialCache finalCache hinterval
            (OriginReplayEvents.directCount
              ((originReplayEvents state.trace.intervals state.views).take eventPosition.val))
            hcounts.1.symm selected (by
              simpa only [OriginReplayState.initial, zero_add] using hsourceAt)
  | inr request =>
      simp only [originReplayEventOfEntry] at hevent heventAt
      have heventGet : (originReplayEvents state.trace.intervals state.views).get
          eventPosition = .signer request output
            (state.views[signerIntervalCount
              (state.trace.intervals.take intervalPosition.val)]?.getD none)
            initialCache finalCache := by
        simpa only [List.get_eq_getElem] using heventAt
      rw [heventGet]
      intro selected hselectedAt
      have hselectedValue : selected.1.val =
          OriginReplayEvents.signerCount
            ((originReplayEvents state.trace.intervals state.views).take eventPosition.val) :=
        (cover.pattern.pad hle).selectedAt?_eq_some_iff _ selected |>.1 (by
          simpa [OriginReplayState.initial] using hselectedAt)
      have hrank : signerIntervalCount
          (state.trace.intervals.take intervalPosition.val) = selected.1.val := by
        rw [← hcounts.2, hselectedValue]
      have hsigner := cover.originReplayEvents_get_signer state hlog hvalidViews
        hconsistent hcaches hf hle selected intervalPosition request output initialCache
        finalCache hinterval hrank
      have heventEq : OriginReplayEvent.signer request output
          (state.views[signerIntervalCount
            (state.trace.intervals.take intervalPosition.val)]?.getD none)
          initialCache finalCache =
        OriginReplayEvent.signer request output
          (some (cover.paddedExpectedViews hle selected)) initialCache finalCache :=
        hevent.symm.trans hsigner.1
      have hviewEq : state.views[signerIntervalCount
          (state.trace.intervals.take intervalPosition.val)]?.getD none =
          some (cover.paddedExpectedViews hle selected) := by
        injection heventEq
      rw [hviewEq]
      let entry := cover.paddedEntry hle selected
      let signingEntry : SigningCacheEntry :=
        ⟨request, output, initialCache, finalCache⟩
      have hcacheEntry : signingEntry =
          cover.cacheEntry state.trace.signing hlog entry := by
        simpa [entry, signingEntry] using hsigner.2
      let chosen := cover.select (cover.representativeTree entry)
      have hfields := cover.cacheEntry_request_signature state.trace.signing hlog entry
      have hrequest : request = chosen.entry.1 := by
        have hfield := congrArg SigningCacheEntry.request hcacheEntry
        exact hfield.trans hfields.1
      have hsignature : output = some chosen.signature := by
        have hfield := congrArg SigningCacheEntry.signature hcacheEntry
        exact hfield.trans hfields.2
      have hinitial : initialCache =
          (cover.cacheEntry state.trace.signing hlog entry).initialCache :=
        congrArg SigningCacheEntry.initialCache hcacheEntry
      have hinput : tweakableHashInput secretKey.parameter .message
          (messageDigestPayload secretKey.root request chosen.signature.randomness) =
          cover.entryDigestInput entry := by
        rw [hrequest]
        rfl
      by_cases hprehit : selected ∈ configuration.prehit
      · simp only [hprehit, dite_true]
        let prehit : ↑configuration.prehit := ⟨selected, hprehit⟩
        let oldSelected := (cover.pattern.padSelectedEquiv hle).symm selected
        have hentrySelected : cover.entriesEquivPatternSelected entry = oldSelected := by
          exact cover.entriesEquivPatternSelected.apply_symm_apply oldSelected
        have hpadded : cover.pattern.padSelectedEquiv hle oldSelected = selected :=
          (cover.pattern.padSelectedEquiv hle).apply_symm_apply selected
        have hselected : cover.pattern.padSelectedEquiv hle
            (cover.entriesEquivPatternSelected entry) ∈ configuration.prehit := by
          rw [hentrySelected, hpadded]
          exact hprehit
        have hprecached : cover.EntryDigestPrecached state.trace.signing hlog entry :=
          (hrealized.1 oldSelected).1 (by
            rw [← hentrySelected]
            exact hselected)
        let precached : cover.PrecachedEntries state.trace.signing hlog :=
          ⟨entry, hprecached⟩
        obtain ⟨sourceOutput, sourcePosition, sourceInterval, selectedInterval,
          hdirect, hsource, hordinal, hbefore, hselectedInterval, hselectedRank,
          hsourceInput, hsourceMiss, hsourceRun, hsourceSuccess, hsourceView⟩ :=
          hrealized.2 precached hselected
        have hcurrentSigning : AdversaryCacheEntry.signingEntry?
            (state.trace.intervals.get intervalPosition) =
              some (cover.cacheEntry state.trace.signing hlog entry) := by
          rw [hinterval]
          change some signingEntry =
            some (cover.cacheEntry state.trace.signing hlog entry)
          exact congrArg some hcacheEntry
        have hselectedPosition : selectedInterval = intervalPosition := by
          apply filterMap_take_length_injective_at_some
            AdversaryCacheEntry.signingEntry? state.trace.intervals
            selectedInterval intervalPosition
            (cover.cacheEntry state.trace.signing hlog entry)
            (cover.cacheEntry state.trace.signing hlog entry)
          · simpa [precached] using hselectedInterval
          · exact hcurrentSigning
          · exact hselectedRank.trans
              ((cover.paddedEntry_logIndex_val hle selected).trans hrank.symm)
        have hbeforeCurrent : sourceInterval.val < intervalPosition.val := by
          rw [← hselectedPosition]
          exact hbefore
        have hsourceLt := encodeSubtype_directInterval_lt_count_take
          state.trace.intervals sourceInterval hdirect intervalPosition.val hbeforeCurrent
        let realizedPrehit : ↑configuration.prehit :=
          ⟨cover.pattern.padSelectedEquiv hle
            (cover.entriesEquivPatternSelected entry), hselected⟩
        have hprehitEq : realizedPrehit = prehit := by
          apply Subtype.ext
          change cover.pattern.padSelectedEquiv hle
            (cover.entriesEquivPatternSelected entry) = selected
          rw [hentrySelected, hpadded]
        have hsourceValue : sourcePosition.val =
            (configuration.source.1 prehit).val := by
          change sourcePosition.val =
            (configuration.source.1 realizedPrehit).val at hsource
          rwa [hprehitEq] at hsource
        have hsourceBefore : (configuration.source.1 prehit).val <
            OriginReplayEvents.directCount
              ((originReplayEvents state.trace.intervals state.views).take
                eventPosition.val) := by
          rw [hcounts.1]
          rw [← hsourceValue, hordinal]
          exact hsourceLt
        have hsourceCached := randomOracle_run_output_cached
          (cover.entryDigestInput entry)
          (state.trace.intervals.get sourceInterval).initialCache
          (state.trace.intervals.get sourceInterval).finalCache sourceOutput (by
            simpa [precached] using hsourceRun)
        have hsourceLe :=
          Concrete.FullAdversaryTrace.Chronological.get_finalCache_le_initialCache
            hchronological sourceInterval intervalPosition hbeforeCurrent
        have hcached : initialCache (cover.entryDigestInput entry) =
            some sourceOutput := by
          have := hsourceLe hsourceCached
          rwa [hinterval] at this
        refine ⟨?_, ?_⟩
        · simpa [OriginReplayState.initial, prehit] using hsourceBefore
        · refine ⟨chosen.signature, cover.paddedExpectedViews hle selected, ?_,
              sourceOutput, ?_, ?_⟩
          · exact Prod.ext hsignature rfl
          · change onlyInputCache initialCache
              (cover.paddedExpectedInputs hle configuration prehit)
              (tweakableHashInput secretKey.parameter .message
                (messageDigestPayload secretKey.root request
                  chosen.signature.randomness)) = some sourceOutput
            rw [hinput]
            change onlyInputCache initialCache (cover.entryDigestInput entry)
              (cover.entryDigestInput entry) = some sourceOutput
            simp [onlyInputCache, hcached]
          · change hashOutputFewTimeView sourceOutput = cover.entryView entry
            simpa [precached] using hsourceView
      · simp only [hprehit, dite_false]
        have hnotPrecached : ¬cover.EntryDigestPrecached state.trace.signing hlog entry := by
          intro hprecached
          apply hprehit
          have hprecached' : cover.EntryDigestPrecached state.trace.signing hlog
              (cover.entriesEquivPatternSelected.symm
                ((cover.pattern.padSelectedEquiv hle).symm selected)) := by
            simpa [entry, FewTimeCover.paddedEntry] using hprecached
          have hmember :=
            (hrealized.1 ((cover.pattern.padSelectedEquiv hle).symm selected)).2 hprecached'
          rw [(cover.pattern.padSelectedEquiv hle).apply_symm_apply selected] at hmember
          exact hmember
        refine ⟨chosen.signature, cover.paddedExpectedViews hle selected, ?_, ?_, rfl⟩
        · exact Prod.ext hsignature rfl
        · rw [hinput, hinitial]
          exact not_ne_iff.mp hnotPrecached

def viewedOriginReplayEvents (state : ViewedFullTraceState) :
    List OriginReplayEvent :=
  Concrete.originReplayEvents state.trace.intervals state.views

def appendOriginReplayView (entry : AdversaryCacheEntry)
    (views : List (Option FewTimeView)) (view : Option FewTimeView) :
    List (Option FewTimeView) :=
  match entry.input with
  | .inr _ => views ++ [view]
  | .inl _ => views

theorem originReplayEvents_append_entry
    (intervals : List AdversaryCacheEntry) (views : List (Option FewTimeView))
    (entry : AdversaryCacheEntry) (view : Option FewTimeView)
    (haligned : (intervals.filterMap AdversaryCacheEntry.signingEntry?).length =
      views.length) :
    originReplayEvents (intervals ++ [entry]) (appendOriginReplayView entry views view) =
      originReplayEvents intervals views ++ [originReplayEventOfEntry entry view] := by
  induction intervals generalizing views with
  | nil =>
      rcases entry with ⟨input, output, initialCache, finalCache⟩
      cases input with
      | inl worldInput => cases worldInput <;> rfl
      | inr request =>
          have hlength : views.length = 0 := by simpa using haligned.symm
          have hviews : views = [] := List.eq_nil_of_length_eq_zero hlength
          subst views
          rfl
  | cons head rest ih =>
      rcases head with ⟨input, output, initialCache, finalCache⟩
      cases input with
      | inl worldInput =>
          cases worldInput with
          | inl uniformInput =>
              have htail : (rest.filterMap AdversaryCacheEntry.signingEntry?).length =
                  views.length := by
                simpa [AdversaryCacheEntry.signingEntry?] using haligned
              simp only [List.cons_append, originReplayEvents]
              rw [ih views htail]
          | inr hashInput =>
              have htail : (rest.filterMap AdversaryCacheEntry.signingEntry?).length =
                  views.length := by
                simpa [AdversaryCacheEntry.signingEntry?] using haligned
              simp only [List.cons_append, originReplayEvents]
              rw [ih views htail]
      | inr request =>
          cases views with
          | nil => simp [AdversaryCacheEntry.signingEntry?] at haligned
          | cons headView restViews =>
              have htail : (rest.filterMap AdversaryCacheEntry.signingEntry?).length =
                  restViews.length := by
                simpa [AdversaryCacheEntry.signingEntry?] using haligned
              rcases entry with ⟨entryInput, entryOutput, entryInitial, entryFinal⟩
              cases entryInput with
              | inl entryWorldInput =>
                  cases entryWorldInput with
                  | inl entryUniform =>
                      simpa [appendOriginReplayView, originReplayEvents,
                        originReplayEventOfEntry] using
                          congrArg (List.cons (OriginReplayEvent.signer request output headView
                            initialCache finalCache)) (ih restViews htail)
                  | inr entryHash =>
                      simpa [appendOriginReplayView, originReplayEvents,
                        originReplayEventOfEntry] using
                          congrArg (List.cons (OriginReplayEvent.signer request output headView
                            initialCache finalCache)) (ih restViews htail)
              | inr entryRequest =>
                  simpa [appendOriginReplayView, originReplayEvents,
                    originReplayEventOfEntry] using
                      congrArg (List.cons (OriginReplayEvent.signer request output headView
                        initialCache finalCache)) (ih restViews htail)

theorem replayOriginEvents_append {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (events : List OriginReplayEvent) (event : OriginReplayEvent) :
    replayOriginEvents configuration secretKey (events ++ [event]) =
      (replayOriginEvents configuration secretKey events).step secretKey event := by
  simp [replayOriginEvents, List.foldl_append]

theorem replayOriginEvents_ordinals {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (events : List OriginReplayEvent) :
    (replayOriginEvents configuration secretKey events).directOrdinal =
        OriginReplayEvents.directCount events
      ∧ (replayOriginEvents configuration secretKey events).signerOrdinal =
        OriginReplayEvents.signerCount events := by
  have hfold : ∀ state : OriginReplayState configuration,
      (events.foldl (OriginReplayState.step secretKey) state).directOrdinal =
          state.directOrdinal + OriginReplayEvents.directCount events
        ∧ (events.foldl (OriginReplayState.step secretKey) state).signerOrdinal =
          state.signerOrdinal + OriginReplayEvents.signerCount events := by
    induction events with
    | nil => intro state; simp [OriginReplayEvents.directCount,
        OriginReplayEvents.signerCount]
    | cons event events ih =>
        intro state
        simpa [OriginReplayEvents.directCount, OriginReplayEvents.signerCount,
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            ih (state.step secretKey event)
  simpa [replayOriginEvents, OriginReplayState.initial] using
    hfold (OriginReplayState.initial configuration)

def OriginMonitorState.replayState {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginMonitorState configuration) : OriginReplayState configuration :=
  ⟨state.observation, state.directOrdinal, state.signerOrdinal, state.valid⟩

def OriginMonitorState.ReplayConsistent {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (secretKey : SecretKey) (state : OriginMonitorState configuration) : Prop :=
  state.viewed.ValidViews secretKey
    ∧ state.viewed.trace.Consistent
    ∧ state.replayState =
      replayOriginEvents configuration secretKey (viewedOriginReplayEvents state.viewed)

theorem OriginMonitorState.replayConsistent_initial {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (cache : QueryCache HashSpec) :
    (OriginMonitorState.initial configuration cache).ReplayConsistent secretKey := by
  simp [OriginMonitorState.ReplayConsistent, OriginMonitorState.initial,
    ViewedFullTraceState.ValidViews, FullAdversaryTrace.Consistent,
    OriginMonitorState.replayState, viewedOriginReplayEvents,
    originReplayEvents, replayOriginEvents, OriginReplayState.initial]

theorem OriginMonitorState.ReplayConsistent.aligned {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    {secretKey : SecretKey} {state : OriginMonitorState configuration}
    (hconsistent : state.ReplayConsistent secretKey) :
    (state.viewed.trace.intervals.filterMap
      AdversaryCacheEntry.signingEntry?).length = state.viewed.views.length := by
  rw [hconsistent.2.1.2]
  exact hconsistent.1.length_eq

theorem originMonitoredAdversaryImpl_query_replayConsistent
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : OriginMonitorState configuration)
    (result : (OracleWorld + SigningSpec).Range input × OriginMonitorState configuration)
    (hconsistent : state.ReplayConsistent secretKey)
    (hmem : result ∈ support
      ((originMonitoredAdversaryImpl configuration secretKey input).run state)) :
    result.2.ReplayConsistent secretKey := by
  classical
  have hviewedMem : (result.1, result.2.viewed) ∈ support
      ((viewedFullTracedMappedAdversaryImpl secretKey input).run state.viewed) := by
    rw [← originMonitoredAdversaryImpl_query_projection configuration secretKey input state,
      support_map]
    exact ⟨result, hmem, rfl⟩
  have hvalidViews := viewedFullTracedMappedAdversaryImpl_query_validViews secretKey input
    state.viewed (result.1, result.2.viewed) hconsistent.1 hviewedMem
  have haligned := hconsistent.aligned
  have hreplay := hconsistent.2.2
  have hreplay' : state.replayState = replayOriginEvents configuration secretKey
      (originReplayEvents state.viewed.trace.intervals state.viewed.views) := by
    simpa only [viewedOriginReplayEvents] using hreplay
  cases input with
  | inl worldInput =>
      cases worldInput with
      | inl uniformInput =>
          rw [originMonitoredAdversaryImpl] at hmem
          simp only [StateT.run, mem_support_bind_iff] at hmem
          obtain ⟨⟨output, finalCache⟩, hquery, hpure⟩ := hmem
          simp only [support_pure, Set.mem_singleton_iff] at hpure
          subst result
          refine ⟨hvalidViews,
            fullAdversaryTraceUpdate_consistent (.inl (.inl uniformInput)) state.viewed.cache
              output finalCache state.viewed.trace hconsistent.2.1, ?_⟩
          let entry : AdversaryCacheEntry :=
            ⟨.inl (.inl uniformInput), output, state.viewed.cache, finalCache⟩
          have happend := originReplayEvents_append_entry state.viewed.trace.intervals
            state.viewed.views entry none haligned
          simp only [appendOriginReplayView] at happend
          change state.replayState = replayOriginEvents configuration secretKey
            (originReplayEvents (state.viewed.trace.intervals ++ [entry]) state.viewed.views)
          rw [happend, replayOriginEvents_append, ← hreplay']
          simp [entry, originReplayEventOfEntry, OriginReplayState.step]
      | inr hashInput =>
          rw [originMonitoredAdversaryImpl] at hmem
          simp only [StateT.run, mem_support_bind_iff] at hmem
          obtain ⟨⟨output, finalCache⟩, hquery, hpure⟩ := hmem
          change HashOutput at output
          simp only [support_pure, Set.mem_singleton_iff] at hpure
          subst result
          refine ⟨hvalidViews,
            fullAdversaryTraceUpdate_consistent (.inl (.inr hashInput)) state.viewed.cache
              output finalCache state.viewed.trace hconsistent.2.1, ?_⟩
          let entry : AdversaryCacheEntry :=
            ⟨.inl (.inr hashInput), output, state.viewed.cache, finalCache⟩
          have happend := originReplayEvents_append_entry state.viewed.trace.intervals
            state.viewed.views entry none haligned
          simp only [appendOriginReplayView] at happend
          change (state.replayState.step secretKey
              (.direct hashInput output state.viewed.cache finalCache)) =
            replayOriginEvents configuration secretKey
              (originReplayEvents (state.viewed.trace.intervals ++ [entry]) state.viewed.views)
          rw [happend, replayOriginEvents_append, ← hreplay']
          simp [entry, originReplayEventOfEntry]
  | inr request =>
      rw [originMonitoredAdversaryImpl] at hmem
      simp only [StateT.run, mem_support_bind_iff] at hmem
      obtain ⟨⟨⟨signature, view⟩, finalCache⟩, hquery, hpure⟩ := hmem
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      refine ⟨hvalidViews,
        fullAdversaryTraceUpdate_consistent (.inr request) state.viewed.cache signature
          finalCache state.viewed.trace hconsistent.2.1, ?_⟩
      let entry : AdversaryCacheEntry :=
        ⟨.inr request, signature, state.viewed.cache, finalCache⟩
      have happend := originReplayEvents_append_entry state.viewed.trace.intervals
        state.viewed.views entry view haligned
      simp only [appendOriginReplayView] at happend
      change (state.replayState.step secretKey
          (.signer request signature view state.viewed.cache finalCache)) =
        replayOriginEvents configuration secretKey
          (originReplayEvents (state.viewed.trace.intervals ++ [entry])
            (state.viewed.views ++ [view]))
      rw [happend, replayOriginEvents_append, ← hreplay']
      simp [entry, originReplayEventOfEntry]

theorem originMonitoredAdversaryImpl_replayConsistent
    {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : OriginMonitorState configuration)
    (result : α × OriginMonitorState configuration)
    (hconsistent : initialState.ReplayConsistent secretKey)
    (hmem : result ∈ support
      ((simulateQ (originMonitoredAdversaryImpl configuration secretKey)
        computation).run initialState)) :
    result.2.ReplayConsistent secretKey := by
  exact OracleComp.simulateQ_run_preservesInv
    (originMonitoredAdversaryImpl configuration secretKey)
    (OriginMonitorState.ReplayConsistent secretKey)
    (by
      intro input state hstate queryResult hquery
      exact originMonitoredAdversaryImpl_query_replayConsistent configuration secretKey input
        state queryResult hstate hquery)
    computation initialState hconsistent result hmem

def OriginReplayState.Expected {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginReplayState configuration)
    (expectedViews : pattern.selected → FewTimeView)
    (expectedInputs : ↑configuration.prehit → HashInput) : Prop :=
  (state.asMonitor ∅).ScheduleCoherent
    ∧ state.valid = true
    ∧ (∀ selected ∈ state.observation.seenSources,
      state.observation.sourceInputs selected = expectedInputs selected
        ∧ state.observation.views selected.1 = expectedViews selected.1)
    ∧ ∀ selected ∈ state.observation.seenViews,
      state.observation.views selected = expectedViews selected

theorem OriginReplayState.expected_initial {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources)
    (expectedViews : pattern.selected → FewTimeView)
    (expectedInputs : ↑configuration.prehit → HashInput) :
    (OriginReplayState.initial configuration).Expected expectedViews expectedInputs := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · change (OriginMonitorState.initial configuration
      (∅ : QueryCache HashSpec)).ScheduleCoherent
    exact OriginMonitorState.scheduleCoherent_initial configuration ∅
  · intro selected hseen
    simp [OriginReplayState.initial, OriginObservation.empty] at hseen
  · intro selected hseen
    simp [OriginReplayState.initial, OriginObservation.empty] at hseen

theorem OriginReplayState.expected_step {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginReplayState configuration) (secretKey : SecretKey)
    (event : OriginReplayEvent)
    (expectedViews : pattern.selected → FewTimeView)
    (expectedInputs : ↑configuration.prehit → HashInput)
    (hexpected : state.Expected expectedViews expectedInputs)
    (hgood : event.Good secretKey state.directOrdinal state.signerOrdinal
      expectedViews expectedInputs) :
    (state.step secretKey event).Expected expectedViews expectedInputs := by
  classical
  obtain ⟨hcoherent, hvalid, hsources, hviews⟩ := hexpected
  cases event with
  | uniform => exact ⟨hcoherent, hvalid, hsources, hviews⟩
  | direct input output initialCache finalCache =>
      have hcoherentAt : (state.asMonitor initialCache).ScheduleCoherent := by
        simpa [OriginMonitorState.ScheduleCoherent, OriginReplayState.asMonitor] using hcoherent
      have hcoherentAfter := (state.asMonitor initialCache).scheduleCoherent_afterDirect
        input output hcoherentAt
      cases hsource : configuration.sourceAt? state.directOrdinal with
      | none =>
          have hstep : state.step secretKey
              (.direct input output initialCache finalCache) =
              ⟨state.observation, state.directOrdinal + 1, state.signerOrdinal,
                state.valid⟩ := by
            simp [OriginReplayState.step, OriginReplayState.asMonitor,
              monitorDirectSource, hsource]
          rw [hstep]
          refine ⟨?_, hvalid, hsources, hviews⟩
          simpa [OriginReplayState.asMonitor, OriginMonitorState.afterDirect,
            OriginMonitorState.ScheduleCoherent, monitorDirectSource, hsource]
            using hcoherentAfter
      | some selected =>
          obtain ⟨rfl, hmiss, hsuccess, houtputView⟩ := hgood selected hsource
          have hcondition : initialCache (expectedInputs selected) = none ∧
              signAttemptResultOfOutput output ≠ none := ⟨hmiss, hsuccess⟩
          have hstep : state.step secretKey
              (.direct (expectedInputs selected) output initialCache finalCache) =
              ⟨state.observation.recordSource selected (expectedInputs selected)
                  (hashOutputFewTimeView output),
                state.directOrdinal + 1, state.signerOrdinal, state.valid⟩ := by
            simp [OriginReplayState.step, OriginReplayState.asMonitor,
              monitorDirectSource, hsource, hcondition]
          rw [hstep]
          refine ⟨?_, hvalid, ?_, ?_⟩
          · simpa [OriginReplayState.asMonitor, OriginMonitorState.afterDirect,
              OriginMonitorState.ScheduleCoherent, monitorDirectSource, hsource,
              hcondition] using hcoherentAfter
          · intro other hseen
            simp only [OriginObservation.recordSource] at hseen ⊢
            rw [Finset.mem_insert] at hseen
            rcases hseen with rfl | hseen
            · simp [houtputView]
            · by_cases heq : other = selected
              · subst other
                simp [houtputView]
              · have hval : other.1 ≠ selected.1 :=
                  fun h => heq (Subtype.ext h)
                simpa [heq, hval] using hsources other hseen
          · intro other hseen
            simp only [OriginObservation.recordSource] at hseen ⊢
            rw [Finset.mem_insert] at hseen
            rcases hseen with rfl | hseen
            · simp [houtputView]
            · by_cases heq : other = selected.1
              · subst other
                simp [houtputView]
              · simpa [heq] using hviews other hseen
  | signer request signature view initialCache finalCache =>
      have hcoherentAt : (state.asMonitor initialCache).ScheduleCoherent := by
        simpa [OriginMonitorState.ScheduleCoherent, OriginReplayState.asMonitor] using hcoherent
      have hcoherentAfter := (state.asMonitor initialCache).scheduleCoherent_afterSigner
        secretKey request ((signature, view), finalCache) hcoherentAt
      cases hselected : pattern.selectedAt? state.signerOrdinal with
      | none =>
          have hstep : state.step secretKey
              (.signer request signature view initialCache finalCache) =
              ⟨state.observation, state.directOrdinal, state.signerOrdinal + 1,
                state.valid⟩ := by
            simp [OriginReplayState.step, OriginReplayState.asMonitor,
              monitorSigner, hselected]
          rw [hstep]
          refine ⟨?_, hvalid, hsources, hviews⟩
          simpa [OriginReplayState.asMonitor, OriginMonitorState.afterSigner,
            OriginMonitorState.ScheduleCoherent, monitorSigner, hselected]
            using hcoherentAfter
      | some selected =>
          by_cases hprehit : selected ∈ configuration.prehit
          · let prehit : ↑configuration.prehit := ⟨selected, hprehit⟩
            obtain ⟨hsourceBefore, hsuccess⟩ := by
              simpa [hprehit] using hgood selected hselected
            have hseenSource : prehit ∈ state.observation.seenSources :=
              (hcoherentAt hvalid).1 prehit |>.2 hsourceBefore
            obtain ⟨hinput, hsourceView⟩ := hsources prehit hseenSource
            have hsuccess' : PrehitSuccessfulSignerView
                (onlyInputCache initialCache (state.observation.sourceInputs prehit))
                secretKey request (fun value => value = state.observation.views selected)
                ((signature, view), finalCache) := by
              simpa [prehit, hinput, hsourceView] using hsuccess
            have hcondition : prehit ∈ state.observation.seenSources ∧
                PrehitSuccessfulSignerView
                  (onlyInputCache initialCache (state.observation.sourceInputs prehit))
                  secretKey request (fun value => value = state.observation.views selected)
                  ((signature, view), finalCache) := ⟨hseenSource, hsuccess'⟩
            have hstep : state.step secretKey
                (.signer request signature view initialCache finalCache) =
                ⟨state.observation, state.directOrdinal, state.signerOrdinal + 1,
                  state.valid⟩ := by
              simp [OriginReplayState.step, OriginReplayState.asMonitor, monitorSigner,
                hselected, hprehit, prehit, hcondition]
            rw [hstep]
            refine ⟨?_, hvalid, hsources, hviews⟩
            simpa [OriginReplayState.asMonitor, OriginMonitorState.afterSigner,
              OriginMonitorState.ScheduleCoherent, monitorSigner, hselected,
              hprehit, prehit, hcondition] using hcoherentAfter
          · have hsuccess : FreshSuccessfulSignerView initialCache secretKey request
                (fun value => value = expectedViews selected)
                ((signature, view), finalCache) := by
              simpa [hprehit] using hgood selected hselected
            have hfresh : freshSuccessfulView? initialCache secretKey request
                ((signature, view), finalCache) = some (expectedViews selected) :=
              (freshSuccessfulView?_eq_some_iff initialCache secretKey request
                ((signature, view), finalCache) (expectedViews selected)).2 hsuccess
            have hstep : state.step secretKey
                (.signer request signature view initialCache finalCache) =
                ⟨state.observation.recordFresh selected (expectedViews selected),
                  state.directOrdinal, state.signerOrdinal + 1, state.valid⟩ := by
              simp [OriginReplayState.step, OriginReplayState.asMonitor, monitorSigner,
                hselected, hprehit, hfresh]
            rw [hstep]
            refine ⟨?_, hvalid, ?_, ?_⟩
            · simpa [OriginReplayState.asMonitor, OriginMonitorState.afterSigner,
                OriginMonitorState.ScheduleCoherent, monitorSigner, hselected,
                hprehit, hfresh] using hcoherentAfter
            · intro other hseen
              have hne : other.1 ≠ selected := by
                intro heq
                subst selected
                exact hprehit other.2
              simpa [OriginObservation.recordFresh, hne] using hsources other hseen
            · intro other hseen
              simp only [OriginObservation.recordFresh] at hseen ⊢
              rw [Finset.mem_insert] at hseen
              rcases hseen with rfl | hseen
              · simp
              · by_cases heq : other = selected
                · subst other
                  simp
                · simpa [heq] using hviews other hseen

theorem OriginReplayState.expected_foldl {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginReplayState configuration) (secretKey : SecretKey)
    (events : List OriginReplayEvent)
    (expectedViews : pattern.selected → FewTimeView)
    (expectedInputs : ↑configuration.prehit → HashInput)
    (hexpected : state.Expected expectedViews expectedInputs)
    (hgood : OriginReplayEvents.Good secretKey expectedViews expectedInputs state events) :
    (events.foldl (OriginReplayState.step secretKey) state).Expected
      expectedViews expectedInputs := by
  induction events generalizing state with
  | nil => exact hexpected
  | cons event events ih =>
      exact ih (state.step secretKey event)
        (state.expected_step secretKey event expectedViews expectedInputs
          hexpected hgood.1) hgood.2

theorem replayOriginEvents_expected {signatures distinct sources : Nat}
    {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (events : List OriginReplayEvent)
    (expectedViews : pattern.selected → FewTimeView)
    (expectedInputs : ↑configuration.prehit → HashInput)
    (hgood : OriginReplayEvents.Good secretKey expectedViews expectedInputs
      (OriginReplayState.initial configuration) events) :
    (replayOriginEvents configuration secretKey events).Expected
      expectedViews expectedInputs := by
  exact OriginReplayState.expected_foldl (OriginReplayState.initial configuration)
    secretKey events expectedViews expectedInputs
    (OriginReplayState.expected_initial configuration expectedViews expectedInputs) hgood

theorem OriginConfiguration.paddedRealized_replay_expected {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    {cover : FewTimeCover f cache secretKey signingLog index targetLeaves}
    {q limit : Nat} {hle : signingLog.length ≤ limit}
    {configuration : OriginConfiguration (cover.pattern.pad hle) q}
    {state : ViewedFullTraceState}
    (hlog : state.trace.signing.toSigningLog = signingLog)
    (hrealized : configuration.PaddedRealizedBy cover hle state.trace hlog)
    (hvalidViews : state.ValidViews secretKey)
    (hconsistent : state.trace.Consistent)
    (hvalidIntervals : state.trace.ValidIntervals secretKey)
    (hchronological : FullAdversaryTrace.Chronological state.trace.intervals)
    (hcaches : state.trace.signing.CachesLe cache) (hf : cache.AgreesWithFn f) :
    (replayOriginEvents configuration secretKey
      (originReplayEvents state.trace.intervals state.views)).Expected
        (cover.paddedExpectedViews hle)
        (cover.paddedExpectedInputs hle configuration) := by
  apply replayOriginEvents_expected
  exact configuration.paddedRealized_replay_good hlog hrealized hvalidViews
    hconsistent hvalidIntervals hchronological hcaches hf

theorem OriginConfiguration.paddedRealized_complete_and_hit {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {secretKey : SecretKey}
    {signingLog : QueryLog SigningSpec} {index : Index}
    {targetLeaves : DigestTree → FtsLeaf}
    {cover : FewTimeCover f cache secretKey signingLog index targetLeaves}
    {q limit : Nat} {hle : signingLog.length ≤ limit}
    {configuration : OriginConfiguration (cover.pattern.pad hle) q}
    {state : OriginMonitorState configuration}
    (hlog : state.viewed.trace.signing.toSigningLog = signingLog)
    (hrealized : configuration.PaddedRealizedBy cover hle state.viewed.trace hlog)
    (hreplay : state.ReplayConsistent secretKey)
    (hvalidIntervals : state.viewed.trace.ValidIntervals secretKey)
    (hchronological : FullAdversaryTrace.Chronological state.viewed.trace.intervals)
    (hcaches : state.viewed.trace.signing.CachesLe cache)
    (hf : cache.AgreesWithFn f) :
    state.Complete ∧
      FixedFewTimePatternHit (cover.pattern.pad hle).assignment
        (state.observation.views, fewTimeTargetView index targetLeaves) := by
  have hexpectedReplay := configuration.paddedRealized_replay_expected hlog hrealized
    hreplay.1 hreplay.2.1 hvalidIntervals hchronological hcaches hf
  have hexpected : state.replayState.Expected
      (cover.paddedExpectedViews hle)
      (cover.paddedExpectedInputs hle configuration) := by
    rw [hreplay.2.2]
    exact hexpectedReplay
  have hcoherent : state.ScheduleCoherent := by
    simpa [OriginReplayState.Expected, OriginMonitorState.replayState,
      OriginReplayState.asMonitor, OriginMonitorState.ScheduleCoherent] using hexpected.1
  have hvalid : state.valid = true := hexpected.2.1
  have hordinals := replayOriginEvents_ordinals configuration secretKey
    (originReplayEvents state.viewed.trace.intervals state.viewed.views)
  have hcounts := originReplayEvents_counts state.viewed.trace.intervals state.viewed.views
  have hdirectOrdinal : state.directOrdinal =
      directIntervalCount state.viewed.trace.intervals := by
    calc
      state.directOrdinal = state.replayState.directOrdinal := rfl
      _ = (replayOriginEvents configuration secretKey
          (originReplayEvents state.viewed.trace.intervals
            state.viewed.views)).directOrdinal := congrArg OriginReplayState.directOrdinal
              hreplay.2.2
      _ = OriginReplayEvents.directCount
          (originReplayEvents state.viewed.trace.intervals state.viewed.views) := hordinals.1
      _ = directIntervalCount state.viewed.trace.intervals := hcounts.1
  have hsignerOrdinal : state.signerOrdinal =
      signerIntervalCount state.viewed.trace.intervals := by
    calc
      state.signerOrdinal = state.replayState.signerOrdinal := rfl
      _ = (replayOriginEvents configuration secretKey
          (originReplayEvents state.viewed.trace.intervals
            state.viewed.views)).signerOrdinal := congrArg OriginReplayState.signerOrdinal
              hreplay.2.2
      _ = OriginReplayEvents.signerCount
          (originReplayEvents state.viewed.trace.intervals state.viewed.views) := hordinals.2
      _ = signerIntervalCount state.viewed.trace.intervals := hcounts.2
  have hsignerCount : signerIntervalCount state.viewed.trace.intervals =
      signingLog.length := by
    rw [signerIntervalCount, hreplay.2.1.2]
    simpa only [SigningCacheTrace.toSigningLog, List.length_map] using
      congrArg List.length hlog
  have hcomplete : state.Complete := state.complete_of_valid_and_ordinals
    hcoherent hvalid
    (fun selected => by
      rw [hdirectOrdinal]
      exact configuration.paddedRealized_source_lt_directIntervalCount hrealized selected)
    (fun selected => by
      rw [hsignerOrdinal, hsignerCount]
      exact cover.paddedSelected_lt_signingLog_length hle selected)
  have hviews : state.observation.views = cover.paddedExpectedViews hle := by
    funext selected
    exact hexpected.2.2.2 selected (by
      change selected ∈ state.observation.seenViews
      rw [hcomplete.2.2.2]
      simp)
  refine ⟨hcomplete, ?_⟩
  rw [hviews]
  exact cover.paddedExpectedViews_fixedPatternHit hle
end Concrete

end SphincsSecurity
