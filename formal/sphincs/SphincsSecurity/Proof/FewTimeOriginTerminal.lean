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

end Concrete

end SphincsSecurity
