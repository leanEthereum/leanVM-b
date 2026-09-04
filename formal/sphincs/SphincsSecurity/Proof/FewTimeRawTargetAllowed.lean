import SphincsSecurity.Proof.FewTimeRawTargetTrace

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

noncomputable def rawTargetCandidateAllowedAt
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (ordinal : Nat)
    (entry : AdversaryCacheEntry) : List Bool :=
  match entry with
  | ⟨.inl (.inr input), output, initialCache, _⟩ =>
      if initialCache input = none then
        [decide (configuration.sourceAt? ordinal = none ∧
          signAttemptResultOfOutput output ≠ none)]
      else []
  | _ => []

noncomputable def rawTargetCandidateAllowedFrom
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) : Nat → List AdversaryCacheEntry → List Bool
  | _, [] => []
  | ordinal, entry :: rest =>
      rawTargetCandidateAllowedAt configuration ordinal entry ++
        rawTargetCandidateAllowedFrom configuration
          (ordinal + if isDirectHashQuery entry.input then 1 else 0) rest

theorem directIntervalCount_cons (entry : AdversaryCacheEntry) (rest : List AdversaryCacheEntry) :
    directIntervalCount (entry :: rest) =
      (if isDirectHashQuery entry.input then 1 else 0) + directIntervalCount rest := by
  by_cases h : isDirectHashQuery entry.input <;>
    simp [directIntervalCount, h, Nat.add_comm]

theorem directIntervalCount_append (left right : List AdversaryCacheEntry) :
    directIntervalCount (left ++ right) = directIntervalCount left + directIntervalCount right := by
  simp [directIntervalCount]

theorem rawTargetCandidateAllowedFrom_append
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (ordinal : Nat)
    (left right : List AdversaryCacheEntry) :
    rawTargetCandidateAllowedFrom configuration ordinal (left ++ right) =
      rawTargetCandidateAllowedFrom configuration ordinal left ++
        rawTargetCandidateAllowedFrom configuration
          (ordinal + directIntervalCount left) right := by
  induction left generalizing ordinal with
  | nil => simp [rawTargetCandidateAllowedFrom, directIntervalCount]
  | cons entry rest ih =>
      simp only [List.cons_append, rawTargetCandidateAllowedFrom, ih,
        directIntervalCount_cons, List.append_assoc, Nat.add_assoc]

def OriginTargetMonitorState.RawAllowedTraceCoherent
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    {configuration : OriginConfiguration pattern sources}
    (state : OriginTargetMonitorState configuration) : Prop :=
  state.origin.directOrdinal = directIntervalCount state.origin.viewed.trace.intervals ∧
    state.candidateAllowed = rawTargetCandidateAllowedFrom configuration 0
      state.origin.viewed.trace.intervals

theorem OriginTargetMonitorState.rawAllowedTraceCoherent_initial
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (cache : QueryCache HashSpec) :
    (OriginTargetMonitorState.initial configuration cache).RawAllowedTraceCoherent := by
  exact ⟨rfl, rfl⟩

theorem rawTargetMonitoredAdversaryImpl_query_rawAllowedTraceCoherent
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (input : (OracleWorld + SigningSpec).Domain)
    (state : OriginTargetMonitorState configuration)
    (result : (OracleWorld + SigningSpec).Range input × OriginTargetMonitorState configuration)
    (hcoherent : state.RawAllowedTraceCoherent)
    (hmem : result ∈ support
      ((rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal input).run state)) :
    result.2.RawAllowedTraceCoherent := by
  classical
  obtain ⟨hcount, hallowed⟩ := hcoherent
  cases input with
  | inl worldInput =>
      cases worldInput with
      | inl uniformInput =>
          simp only [rawTargetMonitoredAdversaryImpl, originMonitoredAdversaryImpl,
            StateT.run, bind_assoc, pure_bind, mem_support_bind_iff] at hmem
          obtain ⟨run, _, hpure⟩ := hmem
          simp only [support_pure, Set.mem_singleton_iff] at hpure
          subst result
          simpa [OriginTargetMonitorState.RawAllowedTraceCoherent,
            OriginTargetMonitorState.advanceOrigin, fullAdversaryTraceUpdate,
            rawTargetCandidateAllowedFrom_append, rawTargetCandidateAllowedFrom,
            rawTargetCandidateAllowedAt, directIntervalCount_append, directIntervalCount,
            isDirectHashQuery] using And.intro hcount hallowed
      | inr hashInput =>
          simp only [rawTargetMonitoredAdversaryImpl, originMonitoredAdversaryImpl,
            StateT.run, bind_assoc, pure_bind, mem_support_bind_iff] at hmem
          obtain ⟨run, _, hpure⟩ := hmem
          by_cases hfresh : state.origin.viewed.cache hashInput = none
          · simp only [hfresh, if_true, support_pure, Set.mem_singleton_iff] at hpure
            subst result
            simp [OriginTargetMonitorState.RawAllowedTraceCoherent,
              OriginTargetMonitorState.advanceOrigin, OriginTargetMonitorState.recordCandidate,
              fullAdversaryTraceUpdate, rawTargetCandidateAllowedFrom_append,
              rawTargetCandidateAllowedFrom, rawTargetCandidateAllowedAt, hfresh,
              directIntervalCount, isDirectHashQuery,
              hcount, hallowed]
          · simp only [hfresh, if_false, support_pure, Set.mem_singleton_iff] at hpure
            subst result
            simp [OriginTargetMonitorState.RawAllowedTraceCoherent,
              OriginTargetMonitorState.advanceOrigin, fullAdversaryTraceUpdate,
              rawTargetCandidateAllowedFrom_append, rawTargetCandidateAllowedFrom,
              rawTargetCandidateAllowedAt, hfresh, directIntervalCount, isDirectHashQuery, hcount, hallowed]
  | inr request =>
      simp only [rawTargetMonitoredAdversaryImpl, originMonitoredAdversaryImpl,
        StateT.run, bind_assoc, pure_bind, mem_support_bind_iff] at hmem
      obtain ⟨run, _, hpure⟩ := hmem
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      simpa [OriginTargetMonitorState.RawAllowedTraceCoherent,
        OriginTargetMonitorState.advanceOrigin, fullAdversaryTraceUpdate,
        rawTargetCandidateAllowedFrom_append, rawTargetCandidateAllowedFrom,
        rawTargetCandidateAllowedAt, directIntervalCount_append, directIntervalCount,
        isDirectHashQuery] using And.intro hcount hallowed

theorem rawTargetMonitoredAdversaryImpl_rawAllowedTraceCoherent
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : OriginTargetMonitorState configuration)
    (result : α × OriginTargetMonitorState configuration)
    (hcoherent : initialState.RawAllowedTraceCoherent)
    (hmem : result ∈ support
      ((simulateQ (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
        computation).run initialState)) : result.2.RawAllowedTraceCoherent := by
  exact OracleComp.simulateQ_run_preservesInv
    (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
    OriginTargetMonitorState.RawAllowedTraceCoherent
    (by
      intro input state hstate queryResult hquery
      exact rawTargetMonitoredAdversaryImpl_query_rawAllowedTraceCoherent
        configuration secretKey targetOrdinal input state queryResult hstate hquery)
    computation initialState hcoherent result hmem

theorem rawTargetCandidateAllowedFrom_length
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (ordinal : Nat)
    (intervals : List AdversaryCacheEntry) :
    (rawTargetCandidateAllowedFrom configuration ordinal intervals).length =
      (rawTargetCandidateViews intervals).length := by
  induction intervals generalizing ordinal with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨input, output, initialCache, finalCache⟩
      cases input with
      | inl worldInput =>
          cases worldInput with
          | inl uniformInput =>
              simpa [rawTargetCandidateAllowedFrom, rawTargetCandidateAllowedAt,
                rawTargetCandidateViews, rawTargetCandidateView?, isDirectHashQuery] using ih ordinal
          | inr hashInput =>
              by_cases hfresh : initialCache hashInput = none <;>
                simp [rawTargetCandidateAllowedFrom, rawTargetCandidateAllowedAt,
                  rawTargetCandidateViews, rawTargetCandidateView?, hfresh, ih]
      | inr request =>
          simpa [rawTargetCandidateAllowedFrom, rawTargetCandidateAllowedAt,
            rawTargetCandidateViews, rawTargetCandidateView?, isDirectHashQuery] using ih ordinal

theorem rawTargetCandidateViews_get_direct
    (beforeEntries suffix : List AdversaryCacheEntry) (input : HashInput) (output : HashOutput)
    (initialCache finalCache : QueryCache HashSpec) (hfresh : initialCache input = none) :
    (rawTargetCandidateViews
      (beforeEntries ++ ⟨.inl (.inr input), output, initialCache, finalCache⟩ :: suffix))[
        (rawTargetCandidateViews beforeEntries).length]? = some (hashOutputFewTimeView output) := by
  rw [rawTargetCandidateViews_append, List.getElem?_append_right (Nat.le_refl _)]
  simp [rawTargetCandidateViews, rawTargetCandidateView?, hfresh]

theorem rawTargetCandidateAllowedFrom_get_direct
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (ordinal : Nat)
    (beforeEntries suffix : List AdversaryCacheEntry) (input : HashInput) (output : HashOutput)
    (initialCache finalCache : QueryCache HashSpec) (hfresh : initialCache input = none) :
    (rawTargetCandidateAllowedFrom configuration ordinal
      (beforeEntries ++ ⟨.inl (.inr input), output, initialCache, finalCache⟩ :: suffix))[
        (rawTargetCandidateViews beforeEntries).length]? =
      some (decide (configuration.sourceAt? (ordinal + directIntervalCount beforeEntries) = none ∧
        signAttemptResultOfOutput output ≠ none)) := by
  rw [rawTargetCandidateAllowedFrom_append,
    ← rawTargetCandidateAllowedFrom_length configuration ordinal beforeEntries,
    List.getElem?_append_right (Nat.le_refl _)]
  simp [rawTargetCandidateAllowedFrom, rawTargetCandidateAllowedAt, hfresh]

theorem rawTargetMonitoredAdversaryImpl_valid_eq_trace
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (targetOrdinal : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec)
    (result : α × OriginTargetMonitorState configuration)
    (hmem : result ∈ support
      ((simulateQ (rawTargetMonitoredAdversaryImpl configuration secretKey targetOrdinal)
        computation).run (OriginTargetMonitorState.initial configuration initialCache))) :
    result.2.valid =
      (rawTargetCandidateAllowedFrom configuration 0
        result.2.origin.viewed.trace.intervals)[targetOrdinal]?.getD true := by
  have hallowed := rawTargetMonitoredAdversaryImpl_candidateAllowedCoherent configuration secretKey
    targetOrdinal computation _ result
    (OriginTargetMonitorState.candidateAllowedCoherent_initial configuration initialCache
      targetOrdinal) hmem
  have htrace := rawTargetMonitoredAdversaryImpl_rawAllowedTraceCoherent configuration secretKey
    targetOrdinal computation _ result
    (OriginTargetMonitorState.rawAllowedTraceCoherent_initial configuration initialCache) hmem
  exact hallowed.2.trans (congrArg (fun allowed => allowed[targetOrdinal]?.getD true) htrace.2)

theorem rawTargetMonitoredAdversaryImpl_selected_direct
    {signatures distinct sources : Nat} {pattern : FewTimePattern signatures distinct}
    (configuration : OriginConfiguration pattern sources) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (beforeEntries suffix : List AdversaryCacheEntry)
    (input : HashInput) (output : HashOutput) (before after : QueryCache HashSpec)
    (hfresh : before input = none)
    (hsource : configuration.sourceAt? (directIntervalCount beforeEntries) = none)
    (hadmissible : signAttemptResultOfOutput output ≠ none)
    (result : α × OriginTargetMonitorState configuration)
    (hmem : result ∈ support
      ((simulateQ (rawTargetMonitoredAdversaryImpl configuration secretKey
        (rawTargetCandidateViews beforeEntries).length) computation).run
          (OriginTargetMonitorState.initial configuration initialCache)))
    (htrace : result.2.origin.viewed.trace.intervals =
      beforeEntries ++ ⟨.inl (.inr input), output, before, after⟩ :: suffix) :
    result.2.valid = true ∧ result.2.targetView = some (hashOutputFewTimeView output) := by
  constructor
  · rw [rawTargetMonitoredAdversaryImpl_valid_eq_trace configuration secretKey _ computation
      initialCache result hmem, htrace,
      rawTargetCandidateAllowedFrom_get_direct configuration 0 beforeEntries suffix input output
        before after hfresh]
    simp [hsource, hadmissible]
  · rw [rawTargetMonitoredAdversaryImpl_targetView_eq_trace configuration secretKey _ computation
      initialCache result hmem, htrace]
    exact rawTargetCandidateViews_get_direct beforeEntries suffix input output before after hfresh

end SphincsSecurity.Concrete
