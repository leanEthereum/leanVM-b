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

inductive OriginReplayEvent where
  | uniform
  | direct (input : HashInput) (output : HashOutput)
      (initialCache finalCache : QueryCache HashSpec)
  | signer (request : SignRequest) (signature : Option Signature)
      (view : Option FewTimeView) (initialCache finalCache : QueryCache HashSpec)

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

def viewedOriginReplayEvents (state : ViewedFullTraceState) :
    List OriginReplayEvent :=
  Concrete.originReplayEvents state.trace.intervals state.views

def appendOriginReplayView (entry : AdversaryCacheEntry)
    (views : List (Option FewTimeView)) (view : Option FewTimeView) :
    List (Option FewTimeView) :=
  match entry.input with
  | .inr _ => views ++ [view]
  | .inl _ => views

def originReplayEventOfEntry (entry : AdversaryCacheEntry)
    (view : Option FewTimeView) : OriginReplayEvent :=
  match entry with
  | ⟨.inl (.inl _), _, _, _⟩ => .uniform
  | ⟨.inl (.inr input), output, initialCache, finalCache⟩ =>
      .direct input output initialCache finalCache
  | ⟨.inr request, signature, initialCache, finalCache⟩ =>
      .signer request signature view initialCache finalCache

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
end Concrete

end SphincsSecurity
