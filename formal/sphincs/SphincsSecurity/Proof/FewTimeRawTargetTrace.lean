import SphincsSecurity.Proof.FewTimeRawTargetUnion

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

def rawTargetCandidateView? (entry : AdversaryCacheEntry) : Option FewTimeView :=
  match entry with
  | ⟨.inl (.inr input), output, initialCache, _⟩ =>
      if initialCache input = none then some (hashOutputFewTimeView output) else none
  | _ => none

def rawTargetCandidateViews (intervals : List AdversaryCacheEntry) : List FewTimeView :=
  intervals.filterMap rawTargetCandidateView?

theorem rawTargetCandidateViews_append (left right : List AdversaryCacheEntry) :
    rawTargetCandidateViews (left ++ right) =
      rawTargetCandidateViews left ++ rawTargetCandidateViews right := by
  exact List.filterMap_append

def OriginTargetMonitorState.RawCandidateTraceCoherent
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginTargetMonitorState configuration) : Prop :=
  state.candidateViews = rawTargetCandidateViews state.origin.viewed.trace.intervals

theorem OriginTargetMonitorState.rawCandidateTraceCoherent_initial
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (cache : QueryCache HashSpec) :
    (OriginTargetMonitorState.initial configuration cache).RawCandidateTraceCoherent := rfl

theorem rawTargetMonitoredAdversaryImpl_query_rawCandidateTraceCoherent
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (input : (OracleWorld + SigningSpec).Domain)
    (state : OriginTargetMonitorState configuration)
    (result : (OracleWorld + SigningSpec).Range input × OriginTargetMonitorState configuration)
    (hcoherent : state.RawCandidateTraceCoherent)
    (hmem : result ∈ support
      ((rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run state)) :
    result.2.RawCandidateTraceCoherent := by
  classical
  cases input with
  | inl worldInput =>
      cases worldInput with
      | inl uniformInput =>
          simp only [rawTargetMonitoredAdversaryImpl, originMonitoredAdversaryImpl,
            StateT.run, bind_assoc, pure_bind, mem_support_bind_iff] at hmem
          obtain ⟨run, _, hpure⟩ := hmem
          simp only [support_pure, Set.mem_singleton_iff] at hpure
          subst result
          simpa [OriginTargetMonitorState.RawCandidateTraceCoherent,
            OriginTargetMonitorState.advanceOrigin, fullAdversaryTraceUpdate,
            rawTargetCandidateViews_append, rawTargetCandidateViews, rawTargetCandidateView?]
            using hcoherent
      | inr hashInput =>
          simp only [rawTargetMonitoredAdversaryImpl, originMonitoredAdversaryImpl,
            StateT.run, bind_assoc, pure_bind, mem_support_bind_iff] at hmem
          obtain ⟨run, _, hpure⟩ := hmem
          by_cases hfresh : state.origin.viewed.cache hashInput = none
          · simp only [hfresh, if_true, support_pure, Set.mem_singleton_iff] at hpure
            subst result
            simpa [OriginTargetMonitorState.RawCandidateTraceCoherent,
              OriginTargetMonitorState.advanceOrigin, OriginTargetMonitorState.recordCandidate,
              fullAdversaryTraceUpdate, rawTargetCandidateViews_append,
              rawTargetCandidateViews, rawTargetCandidateView?, hfresh] using hcoherent
          · simp only [hfresh, if_false, support_pure, Set.mem_singleton_iff] at hpure
            subst result
            simpa [OriginTargetMonitorState.RawCandidateTraceCoherent,
              OriginTargetMonitorState.advanceOrigin, fullAdversaryTraceUpdate,
              rawTargetCandidateViews_append, rawTargetCandidateViews, rawTargetCandidateView?,
              hfresh] using hcoherent
  | inr request =>
      simp only [rawTargetMonitoredAdversaryImpl, originMonitoredAdversaryImpl,
        StateT.run, bind_assoc, pure_bind, mem_support_bind_iff] at hmem
      obtain ⟨run, _, hpure⟩ := hmem
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      simpa [OriginTargetMonitorState.RawCandidateTraceCoherent,
        OriginTargetMonitorState.advanceOrigin, fullAdversaryTraceUpdate,
        rawTargetCandidateViews_append, rawTargetCandidateViews, rawTargetCandidateView?]
        using hcoherent

theorem rawTargetMonitoredAdversaryImpl_rawCandidateTraceCoherent
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : OriginTargetMonitorState configuration)
    (result : α × OriginTargetMonitorState configuration)
    (hcoherent : initialState.RawCandidateTraceCoherent)
    (hmem : result ∈ support
      ((simulateQ (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
        computation).run initialState)) : result.2.RawCandidateTraceCoherent := by
  exact OracleComp.simulateQ_run_preservesInv
    (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
    OriginTargetMonitorState.RawCandidateTraceCoherent
    (by
      intro input state hstate queryResult hquery
      exact rawTargetMonitoredAdversaryImpl_query_rawCandidateTraceCoherent
        configuration secretKey targetOrdinal input state queryResult hstate hquery)
    computation initialState hcoherent result hmem

theorem rawTargetMonitoredAdversaryImpl_query_preserves_of_advance_record
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (P : OriginTargetMonitorState configuration → Prop)
    (hadvance : ∀ state origin, P state → P (state.advanceOrigin origin))
    (hrecord : ∀ state allowed view, P state →
      P (state.recordCandidate targetOrdinal allowed view))
    (input : (OracleWorld + SigningSpec).Domain)
    (state : OriginTargetMonitorState configuration)
    (result : (OracleWorld + SigningSpec).Range input × OriginTargetMonitorState configuration)
    (hstate : P state)
    (hmem : result ∈ support
      ((rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run state)) :
    P result.2 := by
  cases input with
  | inl worldInput =>
      simp only [rawTargetMonitoredAdversaryImpl, StateT.run, mem_support_bind_iff] at hmem
      obtain ⟨⟨output, origin⟩, _, hpure⟩ := hmem
      cases worldInput with
      | inl uniformInput =>
          simp only [support_pure, Set.mem_singleton_iff] at hpure
          subst result
          exact hadvance state origin hstate
      | inr hashInput =>
          by_cases hfresh : state.origin.viewed.cache hashInput = none
          · simp only [hfresh, if_true, support_pure, Set.mem_singleton_iff] at hpure
            subst result
            exact hrecord _ _ _ (hadvance state origin hstate)
          · simp only [hfresh, if_false, support_pure, Set.mem_singleton_iff] at hpure
            subst result
            exact hadvance state origin hstate
  | inr request =>
      simp only [rawTargetMonitoredAdversaryImpl, StateT.run, mem_support_bind_iff] at hmem
      obtain ⟨⟨output, origin⟩, _, hpure⟩ := hmem
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      exact hadvance state origin hstate

theorem rawTargetMonitoredAdversaryImpl_candidateViewsCoherent
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : OriginTargetMonitorState configuration)
    (result : α × OriginTargetMonitorState configuration)
    (hcoherent : initialState.CandidateViewsCoherent targetOrdinal)
    (hmem : result ∈ support
      ((simulateQ (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
        computation).run initialState)) : result.2.CandidateViewsCoherent targetOrdinal := by
  apply OracleComp.simulateQ_run_preservesInv
    (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
    (OriginTargetMonitorState.CandidateViewsCoherent targetOrdinal)
    _ computation initialState hcoherent result hmem
  intro input state hstate queryResult hquery
  exact rawTargetMonitoredAdversaryImpl_query_preserves_of_advance_record
    configuration secretKey targetOrdinal _
    (fun state origin h => state.candidateViewsCoherent_advanceOrigin targetOrdinal origin h)
    (fun state allowed view h => state.candidateViewsCoherent_recordCandidate
      targetOrdinal allowed view h) input state queryResult hstate hquery

theorem rawTargetMonitoredAdversaryImpl_candidateAllowedCoherent
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : OriginTargetMonitorState configuration)
    (result : α × OriginTargetMonitorState configuration)
    (hcoherent : initialState.CandidateAllowedCoherent targetOrdinal)
    (hmem : result ∈ support
      ((simulateQ (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
        computation).run initialState)) : result.2.CandidateAllowedCoherent targetOrdinal := by
  apply OracleComp.simulateQ_run_preservesInv
    (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
    (OriginTargetMonitorState.CandidateAllowedCoherent targetOrdinal)
    _ computation initialState hcoherent result hmem
  intro input state hstate queryResult hquery
  exact rawTargetMonitoredAdversaryImpl_query_preserves_of_advance_record
    configuration secretKey targetOrdinal _
    (fun state origin h => state.candidateAllowedCoherent_advanceOrigin targetOrdinal origin h)
    (fun state allowed view h => state.candidateAllowedCoherent_recordCandidate
      targetOrdinal allowed view h) input state queryResult hstate hquery

theorem rawTargetMonitoredAdversaryImpl_targetView_eq_trace
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec)
    (result : α × OriginTargetMonitorState configuration)
    (hmem : result ∈ support
      ((simulateQ (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
        computation).run (OriginTargetMonitorState.initial configuration initialCache))) :
    result.2.targetView =
      (rawTargetCandidateViews result.2.origin.viewed.trace.intervals)[targetOrdinal]? := by
  have hviews := rawTargetMonitoredAdversaryImpl_candidateViewsCoherent configuration secretKey
    targetOrdinal computation _ result
    (OriginTargetMonitorState.candidateViewsCoherent_initial configuration initialCache
      targetOrdinal) hmem
  have htrace := rawTargetMonitoredAdversaryImpl_rawCandidateTraceCoherent configuration secretKey
    targetOrdinal computation _ result
    (OriginTargetMonitorState.rawCandidateTraceCoherent_initial configuration initialCache) hmem
  exact hviews.2.trans (congrArg (fun views => views[targetOrdinal]?) htrace)

end SphincsSecurity.Concrete
