import SphincsSecurity.Proof.TracedGame
import SphincsSecurity.Proof.RootCache

/-!
# Signer intervals and direct adversary queries

This trace retains the signer cache intervals together with every query issued directly by the
adversary. Projecting the direct-query log recovers the signer-only traced execution exactly.
-/

namespace SphincsSecurity

open OracleComp OracleSpec

structure AdversaryCacheEntry where
  input : (OracleWorld + SigningSpec).Domain
  output : (OracleWorld + SigningSpec).Range input
  initialCache : QueryCache HashSpec
  finalCache : QueryCache HashSpec

structure FullAdversaryTrace where
  signing : SigningCacheTrace
  direct : QueryLog (OracleWorld + SigningSpec)
  intervals : List AdversaryCacheEntry

def AdversaryCacheEntry.queryEntry (entry : AdversaryCacheEntry) :
    (input : (OracleWorld + SigningSpec).Domain) ×
      (OracleWorld + SigningSpec).Range input :=
  ⟨entry.input, entry.output⟩

def AdversaryCacheEntry.signingEntry? : AdversaryCacheEntry → Option SigningCacheEntry
  | ⟨.inl _, _, _, _⟩ => none
  | ⟨.inr request, output, initialCache, finalCache⟩ =>
      some ⟨request, output, initialCache, finalCache⟩

def FullAdversaryTrace.Consistent (trace : FullAdversaryTrace) : Prop :=
  trace.intervals.map AdversaryCacheEntry.queryEntry = trace.direct
    ∧ trace.intervals.filterMap AdversaryCacheEntry.signingEntry? = trace.signing

def FullAdversaryTrace.IntervalsLe
    (trace : FullAdversaryTrace) (cache : QueryCache HashSpec) : Prop :=
  ∀ entry ∈ trace.intervals, entry.initialCache ≤ cache ∧ entry.finalCache ≤ cache

def FullAdversaryTrace.ValidIntervals
    (trace : FullAdversaryTrace) (secretKey : SecretKey) : Prop :=
  ∀ entry ∈ trace.intervals,
    (entry.output, entry.finalCache) ∈ support
      ((unloggedMappedAdversaryImpl secretKey entry.input).run entry.initialCache)

def FullAdversaryTrace.Chronological : List AdversaryCacheEntry → Prop
  | [] => True
  | entry :: rest =>
      (∀ later ∈ rest, entry.finalCache ≤ later.initialCache)
        ∧ FullAdversaryTrace.Chronological rest

def FullAdversaryTrace.CacheChain (start : QueryCache HashSpec) :
    List AdversaryCacheEntry → QueryCache HashSpec → Prop
  | [], finish => finish = start
  | entry :: rest, finish =>
      entry.initialCache = start ∧
        FullAdversaryTrace.CacheChain entry.finalCache rest finish

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
          | zero => omega
          | succ later =>
              exact hchronological.1 (rest.get later) (List.get_mem rest later)
      | succ earlier =>
          cases later using Fin.cases with
          | zero => simp at hlt
          | succ later =>
              exact ih hchronological.2 earlier later (by simpa using hlt)

theorem FullAdversaryTrace.CacheChain.append_singleton
    {start current : QueryCache HashSpec} {intervals : List AdversaryCacheEntry}
    (hchain : FullAdversaryTrace.CacheChain start intervals current)
    (entry : AdversaryCacheEntry) (hinitial : entry.initialCache = current) :
    FullAdversaryTrace.CacheChain start (intervals ++ [entry]) entry.finalCache := by
  induction intervals generalizing start with
  | nil =>
      change current = start at hchain
      change entry.initialCache = start ∧ entry.finalCache = entry.finalCache
      exact ⟨hinitial.trans hchain, rfl⟩
  | cons head rest ih =>
      rw [List.cons_append]
      rcases hchain with ⟨rfl, hrest⟩
      exact ⟨rfl, ih hrest⟩

theorem FullAdversaryTrace.CacheChain.transition_before
    {start finish : QueryCache HashSpec} {intervals : List AdversaryCacheEntry}
    (hchain : FullAdversaryTrace.CacheChain start intervals finish)
    (input : HashInput) (selected : Fin intervals.length)
    (hstart : start input = none)
    (hselected : (intervals.get selected).initialCache input ≠ none) :
    ∃ source : Fin intervals.length,
      source.val < selected.val
        ∧ (intervals.get source).initialCache input = none
        ∧ (intervals.get source).finalCache input ≠ none := by
  induction intervals generalizing start finish with
  | nil => exact Fin.elim0 selected
  | cons head rest ih =>
      rcases hchain with ⟨hhead, hrest⟩
      obtain ⟨selected, hselectedLt⟩ := selected
      cases selected with
      | zero =>
          exfalso
          apply hselected
          simp only [List.get_eq_getElem, List.getElem_cons_zero, hhead, hstart]
      | succ selected =>
          by_cases hnext : head.finalCache input = none
          · have hselected' :
                (rest.get ⟨selected, by simpa using hselectedLt⟩).initialCache input ≠ none := by
              simpa only [List.get_eq_getElem, List.getElem_cons_succ] using hselected
            obtain ⟨source, hsourceLt, hsourceInitial, hsourceFinal⟩ :=
              ih hrest ⟨selected, by simpa using hselectedLt⟩ hnext hselected'
            refine ⟨⟨source.val + 1, Nat.succ_lt_succ source.isLt⟩, ?_, ?_, ?_⟩
            · change source.val + 1 < selected + 1
              exact Nat.succ_lt_succ hsourceLt
            · simpa only [List.get_eq_getElem, List.getElem_cons_succ] using hsourceInitial
            · simpa only [List.get_eq_getElem, List.getElem_cons_succ] using hsourceFinal
          · refine ⟨⟨0, by simp⟩, ?_, ?_, hnext⟩
            · change 0 < selected + 1
              omega
            simp only [List.get_eq_getElem, List.getElem_cons_zero, hhead, hstart]

theorem FullAdversaryTrace.CacheChain.transition_to_finish
    {start finish : QueryCache HashSpec} {intervals : List AdversaryCacheEntry}
    (hchain : FullAdversaryTrace.CacheChain start intervals finish)
    (input : HashInput) (hstart : start input = none) (hfinish : finish input ≠ none) :
    ∃ source : Fin intervals.length,
      (intervals.get source).initialCache input = none
        ∧ (intervals.get source).finalCache input ≠ none := by
  induction intervals generalizing start finish with
  | nil =>
      change finish = start at hchain
      rw [hchain, hstart] at hfinish
      exact (hfinish rfl).elim
  | cons head rest ih =>
      rcases hchain with ⟨hhead, hrest⟩
      by_cases hnext : head.finalCache input = none
      · obtain ⟨source, hsourceInitial, hsourceFinal⟩ :=
          ih hrest hnext hfinish
        exact ⟨⟨source.val + 1, Nat.succ_lt_succ source.isLt⟩,
          by simpa only [List.get_eq_getElem, List.getElem_cons_succ] using hsourceInitial,
          by simpa only [List.get_eq_getElem, List.getElem_cons_succ] using hsourceFinal⟩
      · exact ⟨⟨0, by simp⟩,
          by simpa only [List.get_eq_getElem, List.getElem_cons_zero, hhead] using hstart,
          by simpa only [List.get_eq_getElem, List.getElem_cons_zero] using hnext⟩

theorem FullAdversaryTrace.Chronological.append_singleton
    {intervals : List AdversaryCacheEntry} {entry : AdversaryCacheEntry}
    (hchronological : FullAdversaryTrace.Chronological intervals)
    (hle : ∀ earlier ∈ intervals, earlier.finalCache ≤ entry.initialCache) :
    FullAdversaryTrace.Chronological (intervals ++ [entry]) := by
  induction intervals with
  | nil => simp [FullAdversaryTrace.Chronological]
  | cons head rest ih =>
      rw [List.cons_append]
      constructor
      · intro later hlater
        rw [List.mem_append] at hlater
        rcases hlater with hlater | hlater
        · exact hchronological.1 later hlater
        · simp only [List.mem_singleton] at hlater
          subst later
          exact hle head (by simp)
      · exact ih hchronological.2 (fun earlier hearlier =>
          hle earlier (List.mem_cons_of_mem head hearlier))

def directHashQueries : QueryLog (OracleWorld + SigningSpec) → List (HashInput × HashOutput)
  | [] => []
  | ⟨.inl (.inr input), output⟩ :: rest => (input, output) :: directHashQueries rest
  | _ :: rest => directHashQueries rest

theorem mem_directHashQueries_iff (log : QueryLog (OracleWorld + SigningSpec))
    (input : HashInput) (output : HashOutput) :
    (input, output) ∈ directHashQueries log ↔
      (⟨.inl (.inr input), output⟩ :
        (query : (OracleWorld + SigningSpec).Domain) ×
          (OracleWorld + SigningSpec).Range query) ∈ log := by
  induction log with
  | nil => simp [directHashQueries]
  | cons head rest ih =>
      obtain ⟨headInput, headOutput⟩ := head
      cases headInput with
      | inl worldInput =>
          cases worldInput with
          | inl uniformInput => simp [directHashQueries, ih]
          | inr hashInput => simp [directHashQueries, ih]
      | inr request => simp [directHashQueries, ih]

def isDirectHashQuery : (OracleWorld + SigningSpec).Domain → Prop
  | .inl (.inr _) => True
  | _ => False

instance : DecidablePred isDirectHashQuery := fun input => by
  cases input with
  | inl worldInput =>
      cases worldInput with
      | inl _ => exact isFalse id
      | inr _ => exact isTrue trivial
  | inr _ => exact isFalse id

theorem directHashQueries_length_eq_countQ
    (log : QueryLog (OracleWorld + SigningSpec)) :
    (directHashQueries log).length = log.countQ isDirectHashQuery := by
  induction log with
  | nil => simp [directHashQueries, QueryLog.countQ]
  | cons entry rest ih =>
      obtain ⟨input, output⟩ := entry
      rcases input with worldInput | request
      · rcases worldInput with uniformInput | hashInput
        · simpa [directHashQueries, QueryLog.countQ, QueryLog.getQ_cons,
            isDirectHashQuery] using ih
        · simpa [directHashQueries, QueryLog.countQ, QueryLog.getQ_cons,
            isDirectHashQuery] using congrArg Nat.succ ih
      · simpa [directHashQueries, QueryLog.countQ, QueryLog.getQ_cons,
          isDirectHashQuery] using ih

def FullAdversaryTrace.hashQueries (trace : FullAdversaryTrace) :
    List (HashInput × HashOutput) :=
  directHashQueries trace.direct

theorem directHashQueries_length_le (log : QueryLog (OracleWorld + SigningSpec)) :
    (directHashQueries log).length ≤ log.length := by
  induction log with
  | nil => simp [directHashQueries]
  | cons entry rest ih =>
      obtain ⟨input, output⟩ := entry
      rcases input with worldInput | request
      · rcases worldInput with uniformInput | hashInput
        · simpa [directHashQueries] using Nat.le.step ih
        · simpa [directHashQueries] using Nat.succ_le_succ ih
      · simpa [directHashQueries] using Nat.le.step ih

def fullAdversaryTraceUpdate
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec)
    (output : (OracleWorld + SigningSpec).Range input)
    (finalCache : QueryCache HashSpec)
    (trace : FullAdversaryTrace) : FullAdversaryTrace where
  signing := signingCacheTraceUpdate input initialCache output finalCache trace.signing
  direct := trace.direct ++ [⟨input, output⟩]
  intervals := trace.intervals ++ [⟨input, output, initialCache, finalCache⟩]

theorem fullAdversaryTraceUpdate_consistent
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec)
    (output : (OracleWorld + SigningSpec).Range input)
    (finalCache : QueryCache HashSpec) (trace : FullAdversaryTrace)
    (hconsistent : trace.Consistent) :
    (fullAdversaryTraceUpdate input initialCache output finalCache trace).Consistent := by
  rcases hconsistent with ⟨hdirect, hsigning⟩
  constructor
  · simp [fullAdversaryTraceUpdate, AdversaryCacheEntry.queryEntry, hdirect]
  · rw [fullAdversaryTraceUpdate, List.filterMap_append, hsigning]
    cases input with
    | inl worldInput =>
        simp [AdversaryCacheEntry.signingEntry?, signingCacheTraceUpdate]
    | inr request =>
        simp [AdversaryCacheEntry.signingEntry?, signingCacheTraceUpdate]

theorem fullAdversaryTraceUpdate_intervalsLe_chronological
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec)
    (output : (OracleWorld + SigningSpec).Range input)
    (finalCache : QueryCache HashSpec) (trace : FullAdversaryTrace)
    (hintervals : trace.IntervalsLe initialCache)
    (hchronological : FullAdversaryTrace.Chronological trace.intervals)
    (hle : initialCache ≤ finalCache) :
    (fullAdversaryTraceUpdate input initialCache output finalCache trace).IntervalsLe finalCache
      ∧ FullAdversaryTrace.Chronological
        (fullAdversaryTraceUpdate input initialCache output finalCache trace).intervals := by
  constructor
  · intro entry hentry
    rw [fullAdversaryTraceUpdate, List.mem_append] at hentry
    rcases hentry with hentry | hentry
    · exact ⟨(hintervals entry hentry).1.trans hle, (hintervals entry hentry).2.trans hle⟩
    · simp only [List.mem_singleton] at hentry
      subst entry
      exact ⟨hle, le_rfl⟩
  · apply hchronological.append_singleton
    exact fun earlier hearlier => (hintervals earlier hearlier).2

theorem fullAdversaryTraceUpdate_validIntervals
    (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec)
    (output : (OracleWorld + SigningSpec).Range input)
    (finalCache : QueryCache HashSpec) (trace : FullAdversaryTrace)
    (hvalid : trace.ValidIntervals secretKey)
    (hquery : (output, finalCache) ∈ support
      ((unloggedMappedAdversaryImpl secretKey input).run initialCache)) :
    (fullAdversaryTraceUpdate input initialCache output finalCache trace).ValidIntervals
      secretKey := by
  intro entry hentry
  rw [fullAdversaryTraceUpdate, List.mem_append] at hentry
  rcases hentry with hentry | hentry
  · exact hvalid entry hentry
  · simp only [List.mem_singleton] at hentry
    subst entry
    exact hquery

noncomputable def fullTracedMappedAdversaryImpl (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT (QueryCache HashSpec × FullAdversaryTrace) ProbComp) :=
  QueryImpl.extendState (unloggedMappedAdversaryImpl secretKey) fullAdversaryTraceUpdate

theorem fullTracedMappedAdversaryImpl_signing_projection
    (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : FullAdversaryTrace) :
    Prod.map id (fun state => (state.1, state.2.signing)) <$>
        (simulateQ (fullTracedMappedAdversaryImpl secretKey)
          computation).run (initialCache, initialTrace) =
      (simulateQ (cacheTracedMappedAdversaryImpl secretKey)
        computation).run (initialCache, initialTrace.signing) := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (fullTracedMappedAdversaryImpl secretKey)
    (cacheTracedMappedAdversaryImpl secretKey)
    (fun state => (state.1, state.2.signing))
  intro input state
  rw [fullTracedMappedAdversaryImpl, cacheTracedMappedAdversaryImpl,
    QueryImpl.extendState_apply, QueryImpl.extendState_apply, map_bind]
  apply bind_congr
  intro result
  rfl

theorem fullTracedMappedAdversaryImpl_support_invariants
    (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : FullAdversaryTrace)
    (result : α × (QueryCache HashSpec × FullAdversaryTrace))
    (hcaches : initialTrace.signing.CachesLe initialCache)
    (hchronological : initialTrace.signing.Chronological)
    (hvalid : initialTrace.signing.ValidRuns secretKey)
    (hmem : result ∈ support
      ((simulateQ (fullTracedMappedAdversaryImpl secretKey)
        computation).run (initialCache, initialTrace))) :
    result.2.2.signing.CachesLe result.2.1
      ∧ result.2.2.signing.Chronological
      ∧ result.2.2.signing.ValidRuns secretKey := by
  have hprojection :
      (result.1, (result.2.1, result.2.2.signing)) ∈ support
        ((simulateQ (cacheTracedMappedAdversaryImpl secretKey)
          computation).run (initialCache, initialTrace.signing)) := by
    rw [← fullTracedMappedAdversaryImpl_signing_projection, support_map]
    exact ⟨result, hmem, rfl⟩
  have hcacheChronological := cacheTracedMappedAdversaryImpl_cachesLe_chronological secretKey
    computation initialCache initialTrace.signing
    (result.1, (result.2.1, result.2.2.signing)) hcaches hchronological hprojection
  exact ⟨hcacheChronological.1, hcacheChronological.2,
    cacheTracedMappedAdversaryImpl_validRuns secretKey computation initialCache
      initialTrace.signing (result.1, (result.2.1, result.2.2.signing)) hvalid hprojection⟩

theorem fullTracedMappedAdversaryImpl_interval_invariants
    (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : FullAdversaryTrace)
    (result : α × (QueryCache HashSpec × FullAdversaryTrace))
    (hconsistent : initialTrace.Consistent)
    (hintervals : initialTrace.IntervalsLe initialCache)
    (hchronological : FullAdversaryTrace.Chronological initialTrace.intervals)
    (hmem : result ∈ support
      ((simulateQ (fullTracedMappedAdversaryImpl secretKey)
        computation).run (initialCache, initialTrace))) :
    result.2.2.Consistent
      ∧ result.2.2.IntervalsLe result.2.1
      ∧ FullAdversaryTrace.Chronological result.2.2.intervals := by
  exact OracleComp.simulateQ_run_preservesInv
    (fullTracedMappedAdversaryImpl secretKey)
    (fun state => state.2.Consistent ∧ state.2.IntervalsLe state.1
      ∧ FullAdversaryTrace.Chronological state.2.intervals)
    (by
      intro input state hstate queryResult hquery
      rw [fullTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
        mem_support_bind_iff] at hquery
      obtain ⟨underlyingResult, hunderlying, hpure⟩ := hquery
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst queryResult
      have hle := unloggedMappedAdversaryImpl_cache_le secretKey input state.1
        underlyingResult hunderlying
      have hnext := fullAdversaryTraceUpdate_intervalsLe_chronological input state.1
        underlyingResult.1 underlyingResult.2 state.2 hstate.2.1 hstate.2.2 hle
      exact ⟨fullAdversaryTraceUpdate_consistent input state.1 underlyingResult.1
          underlyingResult.2 state.2 hstate.1,
        hnext.1, hnext.2⟩)
    computation (initialCache, initialTrace)
    ⟨hconsistent, hintervals, hchronological⟩ result hmem

theorem fullTracedMappedAdversaryImpl_validIntervals
    (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : FullAdversaryTrace)
    (result : α × (QueryCache HashSpec × FullAdversaryTrace))
    (hvalid : initialTrace.ValidIntervals secretKey)
    (hmem : result ∈ support
      ((simulateQ (fullTracedMappedAdversaryImpl secretKey)
        computation).run (initialCache, initialTrace))) :
    result.2.2.ValidIntervals secretKey := by
  exact OracleComp.simulateQ_run_preservesInv
    (fullTracedMappedAdversaryImpl secretKey)
    (fun state => state.2.ValidIntervals secretKey)
    (by
      intro input state hstate queryResult hquery
      rw [fullTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
        mem_support_bind_iff] at hquery
      obtain ⟨underlyingResult, hunderlying, hpure⟩ := hquery
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst queryResult
      exact fullAdversaryTraceUpdate_validIntervals secretKey input state.1
        underlyingResult.1 underlyingResult.2 state.2 hstate hunderlying)
    computation (initialCache, initialTrace) hvalid result hmem

theorem fullTracedMappedAdversaryImpl_cacheChain
    (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (start initialCache : QueryCache HashSpec) (initialTrace : FullAdversaryTrace)
    (result : α × (QueryCache HashSpec × FullAdversaryTrace))
    (hchain : FullAdversaryTrace.CacheChain start initialTrace.intervals initialCache)
    (hmem : result ∈ support
      ((simulateQ (fullTracedMappedAdversaryImpl secretKey)
        computation).run (initialCache, initialTrace))) :
    FullAdversaryTrace.CacheChain start result.2.2.intervals result.2.1 := by
  exact OracleComp.simulateQ_run_preservesInv
    (fullTracedMappedAdversaryImpl secretKey)
    (fun state => FullAdversaryTrace.CacheChain start state.2.intervals state.1)
    (by
      intro input state hstate queryResult hquery
      rw [fullTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
        mem_support_bind_iff] at hquery
      obtain ⟨underlyingResult, _, hpure⟩ := hquery
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst queryResult
      exact hstate.append_singleton
        ⟨input, underlyingResult.1, state.1, underlyingResult.2⟩ rfl)
    computation (initialCache, initialTrace) hchain result hmem

theorem fullTracedMappedAdversaryImpl_direct_countQ_le
    (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (q : Nat), computation.IsQueryBoundP isDirectHashQuery q →
      ∀ (initialCache : QueryCache HashSpec) (initialTrace : FullAdversaryTrace)
        (result : α × (QueryCache HashSpec × FullAdversaryTrace)),
        result ∈ support
          ((simulateQ (fullTracedMappedAdversaryImpl secretKey)
            computation).run (initialCache, initialTrace)) →
        result.2.2.direct.countQ isDirectHashQuery ≤
          initialTrace.direct.countQ isDirectHashQuery + q := by
  induction computation using OracleComp.inductionOn with
  | pure x =>
      intro q hq initialCache initialTrace result hmem
      simp only [simulateQ_pure] at hmem
      subst result
      simp
  | query_bind input continuation ih =>
      intro q hq initialCache initialTrace result hmem
      rw [isQueryBoundP_query_bind_iff] at hq
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨queryResult, hquery, hrest⟩ := hmem
      have hquery' := hquery
      rw [simulateQ_spec_query, fullTracedMappedAdversaryImpl,
        QueryImpl.extendState_apply,
        mem_support_bind_iff] at hquery'
      obtain ⟨underlyingResult, _, hpure⟩ := hquery'
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst queryResult
      have htail := ih underlyingResult.1
        (if isDirectHashQuery input then q - 1 else q) (hq.2 underlyingResult.1)
        underlyingResult.2
        (fullAdversaryTraceUpdate input initialCache underlyingResult.1 underlyingResult.2
          initialTrace)
        result hrest
      simp only [fullAdversaryTraceUpdate, QueryLog.countQ_append] at htail
      by_cases hinput : isDirectHashQuery input
      · have hpos : 0 < q := hq.1.resolve_left (not_not_intro hinput)
        simp [QueryLog.countQ, QueryLog.getQ_cons, hinput] at htail
        simp only [QueryLog.countQ]
        omega
      · simp [QueryLog.countQ, QueryLog.getQ_cons, hinput] at htail
        simp only [QueryLog.countQ]
        omega

theorem fullTracedMappedAdversaryImpl_hashQueries_length_le
    (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (q : Nat)
    (hq : computation.IsQueryBoundP isDirectHashQuery q)
    (initialCache : QueryCache HashSpec)
    (result : α × (QueryCache HashSpec × FullAdversaryTrace))
    (hmem : result ∈ support
      ((simulateQ (fullTracedMappedAdversaryImpl secretKey)
        computation).run (initialCache, ⟨[], [], []⟩))) :
    result.2.2.hashQueries.length ≤ q := by
  rw [FullAdversaryTrace.hashQueries, directHashQueries_length_eq_countQ]
  simpa [QueryLog.countQ] using
    fullTracedMappedAdversaryImpl_direct_countQ_le secretKey computation q hq initialCache
      ⟨[], [], []⟩ result hmem

theorem FullAdversaryTrace.directHashInterval_cached
    {trace : FullAdversaryTrace} {secretKey : SecretKey}
    (hvalid : trace.ValidIntervals secretKey)
    (input : HashInput) (answer : HashOutput)
    (initialCache finalCache : QueryCache HashSpec)
    (hmem : (⟨.inl (.inr input), answer, initialCache, finalCache⟩ :
      AdversaryCacheEntry) ∈ trace.intervals) :
    finalCache input = some answer := by
  have hrun := hvalid _ hmem
  change (answer, finalCache) ∈ support ((romImpl (.inr input)).run initialCache) at hrun
  change (answer, finalCache) ∈ support
    (((uniformSampleImpl.withCaching : QueryImpl HashSpec _) input).run initialCache) at hrun
  cases hcache : initialCache input with
  | some cachedAnswer =>
      rw [QueryImpl.withCaching_run_some uniformSampleImpl hcache,
        support_pure, Set.mem_singleton_iff] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      exact hcache
  | none =>
      rw [QueryImpl.withCaching_run_none uniformSampleImpl hcache, support_map] at hrun
      obtain ⟨sampledAnswer, _, heq⟩ := hrun
      obtain ⟨rfl, rfl⟩ := heq
      exact QueryCache.cacheQuery_self initialCache input answer

theorem FullAdversaryTrace.directHashInterval_eq_of_cached
    {trace : FullAdversaryTrace} {secretKey : SecretKey}
    (hvalid : trace.ValidIntervals secretKey)
    (input : HashInput) (answer cachedAnswer : HashOutput)
    (initialCache finalCache : QueryCache HashSpec)
    (hmem : (⟨.inl (.inr input), answer, initialCache, finalCache⟩ :
      AdversaryCacheEntry) ∈ trace.intervals)
    (hcached : initialCache input = some cachedAnswer) :
    answer = cachedAnswer ∧ finalCache = initialCache := by
  have hrun := hvalid _ hmem
  change (answer, finalCache) ∈ support
    (((uniformSampleImpl.withCaching : QueryImpl HashSpec _) input).run initialCache) at hrun
  rw [QueryImpl.withCaching_run_some uniformSampleImpl hcached,
    support_pure, Set.mem_singleton_iff] at hrun
  exact Prod.mk.inj hrun

theorem FullAdversaryTrace.directHashInterval_eq_cacheQuery_of_fresh
    {trace : FullAdversaryTrace} {secretKey : SecretKey}
    (hvalid : trace.ValidIntervals secretKey)
    (input : HashInput) (answer : HashOutput)
    (initialCache finalCache : QueryCache HashSpec)
    (hmem : (⟨.inl (.inr input), answer, initialCache, finalCache⟩ :
      AdversaryCacheEntry) ∈ trace.intervals)
    (hfresh : initialCache input = none) :
    finalCache = initialCache.cacheQuery input answer := by
  have hrun := hvalid _ hmem
  change (answer, finalCache) ∈ support
    (((uniformSampleImpl.withCaching : QueryImpl HashSpec _) input).run initialCache) at hrun
  rw [QueryImpl.withCaching_run_none uniformSampleImpl hfresh, support_map] at hrun
  obtain ⟨sampledAnswer, _, heq⟩ := hrun
  obtain ⟨rfl, rfl⟩ := heq
  rfl

theorem FullAdversaryTrace.exists_intervalPosition_of_signingEntry
    {trace : FullAdversaryTrace} (hconsistent : trace.Consistent)
    (entry : SigningCacheEntry) (hentry : entry ∈ trace.signing) :
    ∃ position : Fin trace.intervals.length,
      AdversaryCacheEntry.signingEntry? (trace.intervals.get position) = some entry := by
  have hfiltered : entry ∈
      trace.intervals.filterMap AdversaryCacheEntry.signingEntry? := by
    rw [hconsistent.2]
    exact hentry
  rw [List.mem_filterMap] at hfiltered
  obtain ⟨interval, hinterval, hsigning⟩ := hfiltered
  obtain ⟨position, hposition⟩ := List.mem_iff_get.1 hinterval
  exact ⟨position, by rw [hposition]; exact hsigning⟩

theorem AdversaryCacheEntry.initialCache_eq_of_signingEntry?_eq_some
    {interval : AdversaryCacheEntry} {entry : SigningCacheEntry}
    (hentry : interval.signingEntry? = some entry) :
    interval.initialCache = entry.initialCache := by
  rcases interval with ⟨input, output, initialCache, finalCache⟩
  cases input with
  | inl worldInput => simp [AdversaryCacheEntry.signingEntry?] at hentry
  | inr request =>
      simp only [AdversaryCacheEntry.signingEntry?, Option.some.injEq] at hentry
      exact congrArg SigningCacheEntry.initialCache hentry

theorem AdversaryCacheEntry.finalCache_eq_of_signingEntry?_eq_some
    {interval : AdversaryCacheEntry} {entry : SigningCacheEntry}
    (hentry : interval.signingEntry? = some entry) :
    interval.finalCache = entry.finalCache := by
  rcases interval with ⟨input, output, initialCache, finalCache⟩
  cases input with
  | inl worldInput => simp [AdversaryCacheEntry.signingEntry?] at hentry
  | inr request =>
      simp only [AdversaryCacheEntry.signingEntry?, Option.some.injEq] at hentry
      exact congrArg SigningCacheEntry.finalCache hentry

private theorem filterMap_get_order {α β : Type} (filter : α → Option β)
    (list : List α) (left right : Fin list.length) (hlt : left.val < right.val)
    (leftValue rightValue : β)
    (hleft : filter (list.get left) = some leftValue)
    (hright : filter (list.get right) = some rightValue) :
    ∃ (left' right' : Fin (list.filterMap filter).length),
      left'.val < right'.val
        ∧ (list.filterMap filter).get left' = leftValue
        ∧ (list.filterMap filter).get right' = rightValue := by
  induction list with
  | nil => exact left.elim0
  | cons head tail ih =>
      cases left using Fin.cases with
      | zero =>
          cases right using Fin.cases with
          | zero => simp at hlt
          | succ right =>
              simp only [List.get_cons_zero] at hleft
              have hmem : rightValue ∈ tail.filterMap filter := by
                rw [List.mem_filterMap]
                exact ⟨tail.get right, List.get_mem tail right, hright⟩
              obtain ⟨right', hright'⟩ := List.mem_iff_get.1 hmem
              rw [List.filterMap_cons, hleft]
              refine ⟨⟨0, by simp⟩, right'.succ, by simp, by simp, ?_⟩
              simpa using hright'
      | succ left =>
          cases right using Fin.cases with
          | zero => simp at hlt
          | succ right =>
              obtain ⟨left', right', hlt', hleft', hright'⟩ :=
                ih left right (by simpa using hlt) hleft hright
              cases hhead : filter head with
              | none =>
                  rw [List.filterMap_cons, hhead]
                  exact ⟨left', right', hlt', hleft', hright'⟩
              | some value =>
                  rw [List.filterMap_cons, hhead]
                  refine ⟨left'.succ, right'.succ, by simpa using hlt', ?_, ?_⟩
                  · simpa using hleft'
                  · simpa using hright'

private theorem filterMap_getElem?_preimage_with_earlier {α β : Type}
    (filter : α → Option β) (list : List α) (selected : Nat) (selectedValue : β)
    (hselected : (list.filterMap filter)[selected]? = some selectedValue) :
    ∃ (selectedSource : Nat) (sourceElement : α),
      list[selectedSource]? = some sourceElement
        ∧ filter sourceElement = some selectedValue
        ∧ ((list.take selectedSource).filterMap filter).length = selected
        ∧ ∀ (source : Nat) (sourceElement : α) (sourceValue : β), source < selectedSource →
          list[source]? = some sourceElement → filter sourceElement = some sourceValue →
            ∃ source', source' < selected
              ∧ (list.filterMap filter)[source']? = some sourceValue := by
  induction list generalizing selected with
  | nil => simp at hselected
  | cons head tail ih =>
      cases hhead : filter head with
      | none =>
          simp only [List.filterMap_cons, hhead] at hselected
          obtain ⟨selectedSource, sourceElement, hsourceElement, hsourceValue, hrank,
              hearlier⟩ :=
            ih selected hselected
          refine ⟨selectedSource + 1, sourceElement, by simpa, hsourceValue, ?_, ?_⟩
          · simpa [List.filterMap_cons, hhead] using hrank
          intro source earlierElement earlierValue hlt helement hvalue
          cases source with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at helement
              subst earlierElement
              rw [hhead] at hvalue
              simp at hvalue
          | succ source =>
              simpa [List.filterMap_cons, hhead] using
                (hearlier source (sourceElement := earlierElement)
                  (sourceValue := earlierValue) (by omega) (by simpa using helement) hvalue)
      | some headValue =>
          simp only [List.filterMap_cons, hhead] at hselected
          cases selected with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hselected
              subst selectedValue
              refine ⟨0, head, by simp, hhead, by simp, ?_⟩
              intro source _ _ hlt
              omega
          | succ selected =>
              simp only [List.getElem?_cons_succ] at hselected
              obtain ⟨selectedSource, sourceElement, hsourceElement, hsourceValue, hrank,
                  hearlier⟩ :=
                ih selected hselected
              refine ⟨selectedSource + 1, sourceElement, by simpa, hsourceValue, ?_, ?_⟩
              · simp [hhead, hrank]
              intro source earlierElement earlierValue hlt helement hvalue
              cases source with
              | zero =>
                  simp only [List.getElem?_cons_zero, Option.some.injEq] at helement
                  subst earlierElement
                  have heq : headValue = earlierValue := Option.some.inj (hhead.symm.trans hvalue)
                  subst earlierValue
                  exact ⟨0, by omega, by simp [hhead]⟩
              | succ source =>
                  obtain ⟨source', hsourceLt, hsource'⟩ :=
                    hearlier source (sourceElement := earlierElement)
                      (sourceValue := earlierValue) (by omega) (by simpa using helement) hvalue
                  exact ⟨source' + 1, by omega, by simpa [hhead] using hsource'⟩

theorem FullAdversaryTrace.signingIndex_interval
    {trace : FullAdversaryTrace} (hconsistent : trace.Consistent)
    (selected : Fin trace.signing.length) :
    ∃ selectedSource : Fin trace.intervals.length,
      AdversaryCacheEntry.signingEntry? (trace.intervals.get selectedSource) =
          some (trace.signing.get selected)
        ∧ ((trace.intervals.take selectedSource.val).filterMap
          AdversaryCacheEntry.signingEntry?).length = selected.val
        ∧ ∀ source : Fin trace.intervals.length, source.val < selectedSource.val →
          ∀ sourceEntry : SigningCacheEntry,
            AdversaryCacheEntry.signingEntry? (trace.intervals.get source) = some sourceEntry →
              ∃ source' : Fin trace.signing.length,
                source'.val < selected.val ∧ trace.signing.get source' = sourceEntry := by
  have hlength : (trace.intervals.filterMap
      AdversaryCacheEntry.signingEntry?).length = trace.signing.length :=
    congrArg List.length hconsistent.2
  let selected' : Fin (trace.intervals.filterMap
      AdversaryCacheEntry.signingEntry?).length := ⟨selected.val, by
    rw [hlength]
    exact selected.isLt⟩
  have hselectedGet : (trace.intervals.filterMap
      AdversaryCacheEntry.signingEntry?)[selected'.val]? =
        some ((trace.intervals.filterMap
          AdversaryCacheEntry.signingEntry?).get selected') := by
    exact List.getElem?_eq_getElem selected'.isLt
  obtain ⟨selectedSourceNat, selectedInterval, hselectedInterval, hselectedSource,
      hselectedRank, hearlier⟩ :=
    filterMap_getElem?_preimage_with_earlier AdversaryCacheEntry.signingEntry?
      trace.intervals selected'.val
      ((trace.intervals.filterMap AdversaryCacheEntry.signingEntry?).get selected') hselectedGet
  have hselectedSourceLt : selectedSourceNat < trace.intervals.length :=
    (List.getElem?_eq_some_iff.1 hselectedInterval).1
  let selectedSource : Fin trace.intervals.length :=
    ⟨selectedSourceNat, hselectedSourceLt⟩
  have hselectedValue :
      (trace.intervals.filterMap AdversaryCacheEntry.signingEntry?).get selected' =
        trace.signing.get selected := by
    have heq := congrArg (fun list : List SigningCacheEntry => list[selected.val]?) hconsistent.2
    rw [List.getElem?_eq_getElem selected'.isLt,
      List.getElem?_eq_getElem selected.isLt] at heq
    exact Option.some.inj heq
  have hselectedIntervalGet : trace.intervals.get selectedSource = selectedInterval :=
    (List.getElem?_eq_some_iff.1 hselectedInterval).2
  refine ⟨selectedSource, by
    rw [hselectedIntervalGet]
    exact hselectedSource.trans (congrArg some hselectedValue), hselectedRank, ?_⟩
  intro source hlt sourceEntry hsource
  have hsourceGet : trace.intervals[source.val]? = some (trace.intervals.get source) :=
    List.getElem?_eq_getElem source.isLt
  obtain ⟨sourceNat, hsourceLt, hsourceValue⟩ :=
    hearlier source.val (trace.intervals.get source) sourceEntry hlt
      hsourceGet hsource
  have hsourceNatLt : sourceNat <
      (trace.intervals.filterMap AdversaryCacheEntry.signingEntry?).length :=
    (List.getElem?_eq_some_iff.1 hsourceValue).1
  let source' : Fin (trace.intervals.filterMap
      AdversaryCacheEntry.signingEntry?).length := ⟨sourceNat, hsourceNatLt⟩
  let source'' : Fin trace.signing.length := ⟨sourceNat, by
    rw [← hlength]
    exact source'.isLt⟩
  have hsourceValue' : trace.signing.get source'' = sourceEntry := by
    have hsourceValueGet :
        (trace.intervals.filterMap AdversaryCacheEntry.signingEntry?).get source' =
          sourceEntry := (List.getElem?_eq_some_iff.1 hsourceValue).2
    have heq := congrArg (fun list : List SigningCacheEntry => list[sourceNat]?) hconsistent.2
    rw [List.getElem?_eq_getElem source'.isLt,
      List.getElem?_eq_getElem source''.isLt] at heq
    exact Option.some.inj (heq.symm.trans (congrArg some hsourceValueGet))
  exact ⟨source'', hsourceLt, hsourceValue'⟩

theorem FullAdversaryTrace.earlier_signingEntry
    {trace : FullAdversaryTrace} (hconsistent : trace.Consistent)
    (source selected : Fin trace.intervals.length) (hlt : source.val < selected.val)
    (sourceEntry selectedEntry : SigningCacheEntry)
    (hsource : AdversaryCacheEntry.signingEntry? (trace.intervals.get source) =
      some sourceEntry)
    (hselected : AdversaryCacheEntry.signingEntry? (trace.intervals.get selected) =
      some selectedEntry) :
    ∃ (source' selected' : Fin trace.signing.length),
      source'.val < selected'.val
        ∧ trace.signing.get source' = sourceEntry
        ∧ trace.signing.get selected' = selectedEntry := by
  obtain ⟨source', selected', hlt', hsource', hselected'⟩ :=
    filterMap_get_order AdversaryCacheEntry.signingEntry? trace.intervals source selected hlt
      sourceEntry selectedEntry hsource hselected
  have hlength : (trace.intervals.filterMap
      AdversaryCacheEntry.signingEntry?).length = trace.signing.length :=
    congrArg List.length hconsistent.2
  let source'' : Fin trace.signing.length := ⟨source'.val, by
    rw [← hlength]
    exact source'.isLt⟩
  let selected'' : Fin trace.signing.length := ⟨selected'.val, by
    rw [← hlength]
    exact selected'.isLt⟩
  have hsource'' : trace.signing.get source'' = sourceEntry := by
    have heq := congrArg (fun list : List SigningCacheEntry => list[source'.val]?) hconsistent.2
    rw [List.getElem?_eq_getElem source'.isLt] at heq
    rw [List.getElem?_eq_getElem source''.isLt] at heq
    exact Option.some.inj (((congrArg some hsource').symm.trans heq).symm)
  have hselected'' : trace.signing.get selected'' = selectedEntry := by
    have heq := congrArg (fun list : List SigningCacheEntry => list[selected'.val]?) hconsistent.2
    rw [List.getElem?_eq_getElem selected'.isLt] at heq
    rw [List.getElem?_eq_getElem selected''.isLt] at heq
    exact Option.some.inj (((congrArg some hselected').symm.trans heq).symm)
  exact ⟨source'', selected'', hlt', hsource'', hselected''⟩

theorem FullAdversaryTrace.CacheChain.source_before_signingEntry
    {start finish : QueryCache HashSpec} {trace : FullAdversaryTrace}
    (hchain : FullAdversaryTrace.CacheChain start trace.intervals finish)
    (hconsistent : trace.Consistent) (entry : SigningCacheEntry)
    (hentry : entry ∈ trace.signing) (input : HashInput)
    (hstart : start input = none) (hcached : entry.initialCache input ≠ none) :
  ∃ (source selected : Fin trace.intervals.length),
      source.val < selected.val
        ∧ AdversaryCacheEntry.signingEntry? (trace.intervals.get selected) = some entry
        ∧ (trace.intervals.get source).initialCache input = none
        ∧ (trace.intervals.get source).finalCache input ≠ none := by
  obtain ⟨selected, hselected⟩ :=
    FullAdversaryTrace.exists_intervalPosition_of_signingEntry hconsistent entry hentry
  have hselectedCache : (trace.intervals.get selected).initialCache input ≠ none := by
    rw [(trace.intervals.get selected).initialCache_eq_of_signingEntry?_eq_some hselected]
    exact hcached
  obtain ⟨source, hlt, hsourceInitial, hsourceFinal⟩ :=
    hchain.transition_before input selected hstart hselectedCache
  exact ⟨source, selected, hlt, hselected, hsourceInitial, hsourceFinal⟩

theorem FullAdversaryTrace.transition_source_kind
    {trace : FullAdversaryTrace} {secretKey : SecretKey}
    (hvalid : trace.ValidIntervals secretKey) (entry : AdversaryCacheEntry)
    (hentry : entry ∈ trace.intervals) (target : HashInput)
    (hmiss : entry.initialCache target = none)
    (hhit : entry.finalCache target ≠ none) :
    entry.input = .inl (.inr target) ∨ ∃ request, entry.input = .inr request := by
  rcases entry with ⟨input, output, initialCache, finalCache⟩
  change initialCache target = none at hmiss
  change finalCache target ≠ none at hhit
  cases input with
  | inr request => exact Or.inr ⟨request, rfl⟩
  | inl worldInput =>
      cases worldInput with
      | inl uniformInput =>
          have hrun := hvalid _ hentry
          change (output, finalCache) ∈ support
            ((unifFwdImpl HashSpec uniformInput).run initialCache) at hrun
          have heq : finalCache = initialCache := by
            have hforward :
                (unifFwdImpl HashSpec uniformInput).run initialCache =
                  (fun sample => (sample, initialCache)) <$>
                    (liftM (unifSpec.query uniformInput) : ProbComp _) := by
              simpa [simulateQ_query] using
                (unifFwdImpl.simulateQ_run
                  (hashSpec := HashSpec)
                  (liftM (unifSpec.query uniformInput) : ProbComp _) initialCache)
            rw [hforward, support_map] at hrun
            obtain ⟨sample, _, hsample⟩ := hrun
            exact (congrArg Prod.snd hsample).symm
          rw [heq, hmiss] at hhit
          exact (hhit rfl).elim
      | inr hashInput =>
          change HashOutput at output
          have heqInput : hashInput = target := by
            by_contra hne
            cases hcached : initialCache hashInput with
            | none =>
                have hfinal := FullAdversaryTrace.directHashInterval_eq_cacheQuery_of_fresh
                  hvalid hashInput output initialCache finalCache hentry hcached
                rw [hfinal, QueryCache.cacheQuery_of_ne _ _ (Ne.symm hne), hmiss] at hhit
                exact hhit rfl
            | some cachedAnswer =>
                have hfinal := (FullAdversaryTrace.directHashInterval_eq_of_cached
                  hvalid hashInput output cachedAnswer initialCache finalCache hentry hcached).2
                rw [hfinal, hmiss] at hhit
                exact hhit rfl
          exact Or.inl (congrArg (fun value : HashInput => Sum.inl (Sum.inr value)) heqInput)

noncomputable def gameRestWithFullTrace (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey) (initialCache : QueryCache HashSpec) :
    ProbComp ((Forgery × Bool) × (QueryCache HashSpec × FullAdversaryTrace)) := do
  let (forgery, adversaryCache, trace) ←
    (simulateQ (fullTracedMappedAdversaryImpl secretKey)
      (adversary.main publicKey)).run (initialCache, ⟨[], [], []⟩)
  let (verified, finalCache) ←
    (simulateQ romImpl (Concrete.scheme.verify publicKey forgery.message forgery.signature)).run
      adversaryCache
  let log := trace.signing.toSigningLog
  let verdict := decide (SigningTranscript.Valid log ∧
    ¬ SigningTranscript.Contains log forgery) && verified
  pure ((forgery, verdict), (finalCache, trace))

theorem gameRestWithFullTrace_signing_projection (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey) (initialCache : QueryCache HashSpec) :
    (fun result => (result.1, (result.2.1, result.2.2.signing))) <$>
        gameRestWithFullTrace adversary publicKey secretKey initialCache =
      gameRestWithSigningTrace adversary publicKey secretKey initialCache := by
  let finish : Forgery × (QueryCache HashSpec × SigningCacheTrace) →
      ProbComp ((Forgery × Bool) × (QueryCache HashSpec × SigningCacheTrace)) := fun result => do
    let (verified, finalCache) ←
      (simulateQ romImpl
        (Concrete.scheme.verify publicKey result.1.message result.1.signature)).run result.2.1
    let verdict := decide (SigningTranscript.Valid result.2.2.toSigningLog ∧
      ¬ SigningTranscript.Contains result.2.2.toSigningLog result.1) && verified
    pure ((result.1, verdict), (finalCache, result.2.2))
  let fullRun := (simulateQ (fullTracedMappedAdversaryImpl secretKey)
    (adversary.main publicKey)).run (initialCache, ⟨[], [], []⟩)
  let signingRun := (simulateQ (cacheTracedMappedAdversaryImpl secretKey)
    (adversary.main publicKey)).run (initialCache, [])
  have hprojection :
      Prod.map id (fun state => (state.1, state.2.signing)) <$> fullRun = signingRun :=
    fullTracedMappedAdversaryImpl_signing_projection secretKey
      (adversary.main publicKey) initialCache ⟨[], [], []⟩
  calc
    (fun result => (result.1, (result.2.1, result.2.2.signing))) <$>
        gameRestWithFullTrace adversary publicKey secretKey initialCache =
      (Prod.map id (fun state => (state.1, state.2.signing)) <$> fullRun) >>= finish := by
        simp [gameRestWithFullTrace, fullRun, finish, bind_map_left, map_bind, Prod.map]
        rfl
    _ = signingRun >>= finish := by rw [hprojection]
    _ = gameRestWithSigningTrace adversary publicKey secretKey initialCache := by
      simp [gameRestWithSigningTrace, signingRun, finish]

theorem gameRestWithFullTrace_support_invariants (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey) (initialCache : QueryCache HashSpec)
    (result : (Forgery × Bool) × (QueryCache HashSpec × FullAdversaryTrace))
    (hmem : result ∈ support
      (gameRestWithFullTrace adversary publicKey secretKey initialCache)) :
    result.2.2.signing.ValidRuns secretKey
      ∧ result.2.2.signing.CachesLe result.2.1
      ∧ result.2.2.signing.Chronological := by
  rw [gameRestWithFullTrace, mem_support_bind_iff] at hmem
  obtain ⟨⟨forgery, adversaryCache, trace⟩, hadversary, hfinish⟩ := hmem
  rw [mem_support_bind_iff] at hfinish
  obtain ⟨⟨verified, finalCache⟩, hverify, hpure⟩ := hfinish
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  have hinvariants := fullTracedMappedAdversaryImpl_support_invariants secretKey
    (adversary.main publicKey) initialCache ⟨[], [], []⟩ (forgery, adversaryCache, trace)
    (by simp [SigningCacheTrace.CachesLe]) (by simp [SigningCacheTrace.Chronological])
    (by simp [SigningCacheTrace.ValidRuns]) hadversary
  exact ⟨hinvariants.2.2, hinvariants.1.mono
      (simulateQ_romImpl_cache_le
        (Concrete.scheme.verify publicKey forgery.message forgery.signature)
        adversaryCache (verified, finalCache) hverify),
    hinvariants.2.1⟩

theorem gameRestWithFullTrace_support_interval_invariants (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey) (initialCache : QueryCache HashSpec)
    (result : (Forgery × Bool) × (QueryCache HashSpec × FullAdversaryTrace))
    (hmem : result ∈ support
      (gameRestWithFullTrace adversary publicKey secretKey initialCache)) :
    result.2.2.Consistent
      ∧ result.2.2.IntervalsLe result.2.1
      ∧ FullAdversaryTrace.Chronological result.2.2.intervals := by
  rw [gameRestWithFullTrace, mem_support_bind_iff] at hmem
  obtain ⟨⟨forgery, adversaryCache, trace⟩, hadversary, hfinish⟩ := hmem
  rw [mem_support_bind_iff] at hfinish
  obtain ⟨⟨verified, finalCache⟩, hverify, hpure⟩ := hfinish
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  have hinvariants := fullTracedMappedAdversaryImpl_interval_invariants secretKey
    (adversary.main publicKey) initialCache ⟨[], [], []⟩
    (forgery, adversaryCache, trace)
    (by simp [FullAdversaryTrace.Consistent])
    (by simp [FullAdversaryTrace.IntervalsLe])
    (by simp [FullAdversaryTrace.Chronological]) hadversary
  have hle := simulateQ_romImpl_cache_le
    (Concrete.scheme.verify publicKey forgery.message forgery.signature)
    adversaryCache (verified, finalCache) hverify
  exact ⟨hinvariants.1, fun entry hentry =>
      ⟨(hinvariants.2.1 entry hentry).1.trans hle,
        (hinvariants.2.1 entry hentry).2.trans hle⟩,
    hinvariants.2.2⟩

theorem gameRestWithFullTrace_support_validIntervals (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey) (initialCache : QueryCache HashSpec)
    (result : (Forgery × Bool) × (QueryCache HashSpec × FullAdversaryTrace))
    (hmem : result ∈ support
      (gameRestWithFullTrace adversary publicKey secretKey initialCache)) :
    result.2.2.ValidIntervals secretKey := by
  rw [gameRestWithFullTrace, mem_support_bind_iff] at hmem
  obtain ⟨⟨forgery, adversaryCache, trace⟩, hadversary, hfinish⟩ := hmem
  rw [mem_support_bind_iff] at hfinish
  obtain ⟨_, _, hpure⟩ := hfinish
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  exact fullTracedMappedAdversaryImpl_validIntervals secretKey
    (adversary.main publicKey) initialCache ⟨[], [], []⟩
    (forgery, adversaryCache, trace) (by simp [FullAdversaryTrace.ValidIntervals]) hadversary

theorem gameRestWithFullTrace_support_cacheChain (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey) (initialCache : QueryCache HashSpec)
    (result : (Forgery × Bool) × (QueryCache HashSpec × FullAdversaryTrace))
    (hmem : result ∈ support
      (gameRestWithFullTrace adversary publicKey secretKey initialCache)) :
    ∃ adversaryCache,
      FullAdversaryTrace.CacheChain initialCache result.2.2.intervals adversaryCache
        ∧ adversaryCache ≤ result.2.1 := by
  rw [gameRestWithFullTrace, mem_support_bind_iff] at hmem
  obtain ⟨⟨forgery, adversaryCache, trace⟩, hadversary, hfinish⟩ := hmem
  rw [mem_support_bind_iff] at hfinish
  obtain ⟨⟨verified, finalCache⟩, hverify, hpure⟩ := hfinish
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  refine ⟨adversaryCache, ?_, simulateQ_romImpl_cache_le
    (Concrete.scheme.verify publicKey forgery.message forgery.signature)
    adversaryCache (verified, finalCache) hverify⟩
  exact fullTracedMappedAdversaryImpl_cacheChain secretKey
    (adversary.main publicKey) initialCache initialCache ⟨[], [], []⟩
    (forgery, adversaryCache, trace) rfl hadversary

namespace Concrete

noncomputable def gameAfterSecretsWithFullTrace (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    ProbComp ((Digest × Forgery × Bool) × (QueryCache HashSpec × FullAdversaryTrace)) := do
  let (root, rootCache) ← (simulateQ romImpl
    (liftM ((treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree) :
      OracleComp HashSpec Digest)) :
      OracleComp OracleWorld Digest)).run ∅
  let result ← gameRestWithFullTrace adversary ⟨root, parameter⟩
    ⟨parameter, root, otsSecret, ftsSecret⟩ rootCache
  pure ((root, result.1.1, result.1.2), result.2)

theorem gameAfterSecretsWithFullTrace_signing_projection (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    (fun result => (result.1, (result.2.1, result.2.2.signing))) <$>
        gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret =
      gameAfterSecretsWithSigningTrace adversary parameter otsSecret ftsSecret := by
  rw [gameAfterSecretsWithFullTrace, gameAfterSecretsWithSigningTrace]
  simp only [map_bind]
  apply bind_congr
  intro rootResult
  rw [← gameRestWithFullTrace_signing_projection adversary
    (⟨rootResult.1, parameter⟩ : PublicKey)
    (⟨parameter, rootResult.1, otsSecret, ftsSecret⟩ : SecretKey) rootResult.2]
  simp

theorem gameAfterSecretsWithFullTrace_projection (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    (fun result => (result.1.2.2, result.2.1)) <$>
        gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret =
      (simulateQ romImpl (gameAfterSecrets adversary parameter otsSecret ftsSecret)).run ∅ := by
  have hprojection := congrArg
    (Functor.map (fun result : (Digest × Forgery × Bool) ×
      (QueryCache HashSpec × SigningCacheTrace) => (result.1.2.2, result.2.1)))
    (gameAfterSecretsWithFullTrace_signing_projection adversary parameter otsSecret ftsSecret)
  rw [← gameAfterSecretsWithSigningTrace_projection adversary parameter otsSecret ftsSecret]
  simpa only [Functor.map_map, Function.comp_def] using hprojection

theorem gameAfterSecretsWithFullTrace_support_invariants (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × (QueryCache HashSpec × FullAdversaryTrace))
    (hmem : result ∈ support
      (gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret)) :
    let secretKey : SecretKey := ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
    result.2.2.signing.ValidRuns secretKey
      ∧ result.2.2.signing.CachesLe result.2.1
      ∧ result.2.2.signing.Chronological := by
  rw [gameAfterSecretsWithFullTrace, mem_support_bind_iff] at hmem
  obtain ⟨⟨root, rootCache⟩, _, hrest⟩ := hmem
  rw [mem_support_bind_iff] at hrest
  obtain ⟨restResult, hrest, hpure⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  simpa using gameRestWithFullTrace_support_invariants adversary
    (⟨root, parameter⟩ : PublicKey)
    (⟨parameter, root, otsSecret, ftsSecret⟩ : SecretKey) rootCache restResult hrest

theorem gameAfterSecretsWithFullTrace_support_interval_invariants (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × (QueryCache HashSpec × FullAdversaryTrace))
    (hmem : result ∈ support
      (gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret)) :
    result.2.2.Consistent
      ∧ result.2.2.IntervalsLe result.2.1
      ∧ FullAdversaryTrace.Chronological result.2.2.intervals := by
  rw [gameAfterSecretsWithFullTrace, mem_support_bind_iff] at hmem
  obtain ⟨⟨root, rootCache⟩, _, hrest⟩ := hmem
  rw [mem_support_bind_iff] at hrest
  obtain ⟨restResult, hrest, hpure⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  simpa using gameRestWithFullTrace_support_interval_invariants adversary
    (⟨root, parameter⟩ : PublicKey)
    (⟨parameter, root, otsSecret, ftsSecret⟩ : SecretKey) rootCache restResult hrest

theorem gameAfterSecretsWithFullTrace_support_validIntervals (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × (QueryCache HashSpec × FullAdversaryTrace))
    (hmem : result ∈ support
      (gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret)) :
    let secretKey : SecretKey := ⟨parameter, result.1.1, otsSecret, ftsSecret⟩
    result.2.2.ValidIntervals secretKey := by
  rw [gameAfterSecretsWithFullTrace, mem_support_bind_iff] at hmem
  obtain ⟨⟨root, rootCache⟩, _, hrest⟩ := hmem
  rw [mem_support_bind_iff] at hrest
  obtain ⟨restResult, hrest, hpure⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  simpa using gameRestWithFullTrace_support_validIntervals adversary
    (⟨root, parameter⟩ : PublicKey)
    (⟨parameter, root, otsSecret, ftsSecret⟩ : SecretKey) rootCache restResult hrest

theorem gameAfterSecretsWithFullTrace_support_cacheChain (adversary : Adversary)
    (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (result : (Digest × Forgery × Bool) × (QueryCache HashSpec × FullAdversaryTrace))
    (hmem : result ∈ support
      (gameAfterSecretsWithFullTrace adversary parameter otsSecret ftsSecret)) :
    ∃ rootCache adversaryCache,
      (∀ payload, rootCache (tweakableHashInput parameter .message payload) = none)
        ∧ FullAdversaryTrace.CacheChain rootCache result.2.2.intervals adversaryCache
        ∧ adversaryCache ≤ result.2.1 := by
  rw [gameAfterSecretsWithFullTrace, mem_support_bind_iff] at hmem
  obtain ⟨⟨root, rootCache⟩, hroot, hrest⟩ := hmem
  rw [mem_support_bind_iff] at hrest
  obtain ⟨restResult, hrest, hpure⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  have hroot' : (root, rootCache) ∈ support ((simulateQ
      (randomOracle : QueryImpl HashSpec _)
      (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))).run ∅) := by
    simpa only [simulateQ_romImpl_liftM] using hroot
  obtain ⟨adversaryCache, hchain, hle⟩ :=
    gameRestWithFullTrace_support_cacheChain adversary
      (⟨root, parameter⟩ : PublicKey)
      (⟨parameter, root, otsSecret, ftsSecret⟩ : SecretKey) rootCache restResult hrest
  exact ⟨rootCache, adversaryCache,
    fun payload => treeRoot_cache_message_none parameter topLayer rootTree
      (otsSecret topLayer rootTree) root rootCache hroot' payload,
    hchain, hle⟩

end Concrete

end SphincsSecurity
