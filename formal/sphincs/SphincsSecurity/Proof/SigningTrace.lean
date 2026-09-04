import SphincsSecurity.Proof.SignSupport

/-!
# Signing cache intervals

The ordinary signing log records only requests and responses. This trace additionally records the
random-oracle cache immediately before and after each signer invocation. Its projections recover
the ordinary logged adversary run exactly.
-/

namespace SphincsSecurity

open OracleComp OracleSpec

structure SigningCacheEntry where
  request : SignRequest
  signature : Option Signature
  initialCache : QueryCache HashSpec
  finalCache : QueryCache HashSpec

abbrev SigningCacheTrace := List SigningCacheEntry

def SigningCacheTrace.toSigningLog (trace : SigningCacheTrace) : QueryLog SigningSpec :=
  trace.map fun entry => ⟨entry.request, entry.signature⟩

def SigningCacheTrace.CachesLe
    (trace : SigningCacheTrace) (cache : QueryCache HashSpec) : Prop :=
  ∀ entry ∈ trace, entry.initialCache ≤ cache ∧ entry.finalCache ≤ cache

def SigningCacheEntry.ValidRun (secretKey : SecretKey) (entry : SigningCacheEntry) : Prop :=
  (entry.signature, entry.finalCache) ∈ support
    ((simulateQ romImpl (Concrete.scheme.sign secretKey entry.request)).run entry.initialCache)

def SigningCacheTrace.ValidRuns (secretKey : SecretKey) (trace : SigningCacheTrace) : Prop :=
  ∀ entry ∈ trace, entry.ValidRun secretKey

def SigningCacheTrace.Chronological : SigningCacheTrace → Prop
  | [] => True
  | entry :: rest =>
      (∀ later ∈ rest, entry.finalCache ≤ later.initialCache) ∧
        SigningCacheTrace.Chronological rest

theorem SigningCacheTrace.Chronological.append_singleton
    {trace : SigningCacheTrace} {entry : SigningCacheEntry}
    (hchronological : trace.Chronological)
    (hle : ∀ earlier ∈ trace, earlier.finalCache ≤ entry.initialCache) :
    (trace ++ [entry]).Chronological := by
  induction trace with
  | nil => simp [SigningCacheTrace.Chronological]
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

theorem SigningCacheTrace.Chronological.get_finalCache_le_initialCache
    {trace : SigningCacheTrace} (hchronological : trace.Chronological)
    (earlier later : Fin trace.length) (hlt : earlier.val < later.val) :
    (trace.get earlier).finalCache ≤ (trace.get later).initialCache := by
  induction trace with
  | nil => exact Fin.elim0 earlier
  | cons head rest ih =>
      obtain ⟨earlier, hearlier⟩ := earlier
      obtain ⟨later, hlater⟩ := later
      cases earlier with
      | zero =>
        cases later with
        | zero => simp at hlt
        | succ later =>
          apply hchronological.1
          exact List.get_mem rest ⟨later, by simpa using hlater⟩
      | succ earlier =>
        cases later with
        | zero => simp at hlt
        | succ later =>
          have hlt' : earlier < later := by
            change Nat.succ earlier < Nat.succ later at hlt
            exact Nat.lt_of_succ_lt_succ hlt
          exact ih hchronological.2
            ⟨earlier, by simpa using hearlier⟩ ⟨later, by simpa using hlater⟩ hlt'

theorem SigningCacheEntry.successfulSignRun {f : QueryImpl HashSpec Id}
    {secretKey : SecretKey} {entry : SigningCacheEntry} {signature : Signature}
    {finalCache : QueryCache HashSpec} (hvalid : entry.ValidRun secretKey)
    (hresponse : entry.signature = some signature) (hle : entry.finalCache ≤ finalCache)
    (hf : finalCache.AgreesWithFn f) :
    Concrete.SuccessfulSignRun f finalCache secretKey entry.request signature := by
  have hentryAgree : entry.finalCache.AgreesWithFn f := fun _ _ hcached => hf (hle hcached)
  have hreplay := replayRom_of_mem_support
    (Concrete.scheme.sign secretKey entry.request) entry.initialCache entry.signature
    entry.finalCache hvalid f hentryAgree
  rw [hresponse] at hreplay
  exact Concrete.successfulSignRun_of_mem_support f secretKey entry.request signature
    entry.initialCache entry.finalCache finalCache hreplay hle hf

theorem SigningCacheTrace.CachesLe.mono
    {trace : SigningCacheTrace} {initialCache finalCache : QueryCache HashSpec}
    (htrace : trace.CachesLe initialCache) (hle : initialCache ≤ finalCache) :
    trace.CachesLe finalCache := by
  intro entry hentry
  exact ⟨(htrace entry hentry).1.trans hle, (htrace entry hentry).2.trans hle⟩

def signingLogFragment
    (input : (OracleWorld + SigningSpec).Domain)
    (output : (OracleWorld + SigningSpec).Range input) : QueryLog SigningSpec :=
  match input with
  | .inl _ => []
  | .inr request => [⟨request, output⟩]

def signingCacheTraceUpdate
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec)
    (output : (OracleWorld + SigningSpec).Range input)
    (finalCache : QueryCache HashSpec)
    (trace : SigningCacheTrace) : SigningCacheTrace :=
  match input with
  | .inl _ => trace
  | .inr request => trace ++ [⟨request, output, initialCache, finalCache⟩]

def signingLogUpdate
    (input : (OracleWorld + SigningSpec).Domain)
    (_initialCache : QueryCache HashSpec)
    (output : (OracleWorld + SigningSpec).Range input)
    (_finalCache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) : QueryLog SigningSpec :=
  log ++ signingLogFragment input output

theorem signingCacheTraceUpdate_toSigningLog
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec)
    (output : (OracleWorld + SigningSpec).Range input)
    (finalCache : QueryCache HashSpec) (trace : SigningCacheTrace) :
    (signingCacheTraceUpdate input initialCache output finalCache trace).toSigningLog =
      signingLogUpdate input initialCache output finalCache trace.toSigningLog := by
  cases input <;> simp [signingCacheTraceUpdate, signingLogUpdate,
    signingLogFragment, SigningCacheTrace.toSigningLog]

noncomputable def mappedAdversaryImpl (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (WriterT (QueryLog SigningSpec) (StateT (QueryCache HashSpec) ProbComp)) :=
  romImpl.writerTMapBase (forwardOracles + signingOracle Concrete.scheme secretKey)

noncomputable def unloggedMappedAdversaryImpl (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec) (StateT (QueryCache HashSpec) ProbComp) := by
  intro input
  cases input with
  | inl worldInput => exact romImpl worldInput
  | inr request => exact simulateQ romImpl (Concrete.scheme.sign secretKey request)

noncomputable def cacheTracedMappedAdversaryImpl (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT (QueryCache HashSpec × SigningCacheTrace) ProbComp) :=
  QueryImpl.extendState (unloggedMappedAdversaryImpl secretKey) signingCacheTraceUpdate

theorem unloggedMappedAdversaryImpl_cache_le
    (secretKey : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec)
    (result : (OracleWorld + SigningSpec).Range input × QueryCache HashSpec)
    (hmem : result ∈ support
      ((unloggedMappedAdversaryImpl secretKey input).run initialCache)) :
    initialCache ≤ result.2 := by
  cases input with
  | inl worldInput =>
      cases worldInput with
      | inl uniformInput =>
          have hrun :
              (unifFwdImpl HashSpec uniformInput).run initialCache =
                (fun sample => (sample, initialCache)) <$>
                  (liftM (unifSpec.query uniformInput) : ProbComp _) := by
            simpa [simulateQ_query] using
              (unifFwdImpl.simulateQ_run
                (hashSpec := HashSpec)
                (liftM (unifSpec.query uniformInput) : ProbComp _) initialCache)
          change result ∈ support
            ((unifFwdImpl HashSpec uniformInput).run initialCache) at hmem
          rw [hrun, support_map] at hmem
          obtain ⟨sample, _, heq⟩ := hmem
          exact le_of_eq (congrArg Prod.snd heq)
      | inr hashInput =>
          change result ∈ support
            ((randomOracle (spec := HashSpec) hashInput).run initialCache) at hmem
          exact QueryImpl.withCaching_cache_le uniformSampleImpl hashInput initialCache result hmem
  | inr request =>
      change result ∈ support
        ((simulateQ romImpl (Concrete.scheme.sign secretKey request)).run initialCache) at hmem
      exact simulateQ_romImpl_cache_le (Concrete.scheme.sign secretKey request)
        initialCache result hmem

theorem cacheTracedMappedAdversaryImpl_query_cachesLe
    (secretKey : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (result : (OracleWorld + SigningSpec).Range input ×
      (QueryCache HashSpec × SigningCacheTrace))
    (htrace : initialTrace.CachesLe initialCache)
    (hmem : result ∈ support
      ((cacheTracedMappedAdversaryImpl secretKey input).run
        (initialCache, initialTrace))) :
    result.2.2.CachesLe result.2.1 := by
  rw [cacheTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    mem_support_bind_iff] at hmem
  obtain ⟨⟨output, finalCache⟩, hbase, hpure⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  have hle := unloggedMappedAdversaryImpl_cache_le secretKey input initialCache
    (output, finalCache) hbase
  cases input with
  | inl worldInput => simpa [signingCacheTraceUpdate] using htrace.mono hle
  | inr request =>
      intro entry hentry
      rw [signingCacheTraceUpdate, List.mem_append] at hentry
      rcases hentry with hentry | hentry
      · exact (htrace entry hentry).imp (fun h => h.trans hle) (fun h => h.trans hle)
      · simp only [List.mem_singleton] at hentry
        subst entry
        exact ⟨hle, le_rfl⟩

theorem cacheTracedMappedAdversaryImpl_query_validRuns
    (secretKey : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (result : (OracleWorld + SigningSpec).Range input ×
      (QueryCache HashSpec × SigningCacheTrace))
    (htrace : initialTrace.ValidRuns secretKey)
    (hmem : result ∈ support
      ((cacheTracedMappedAdversaryImpl secretKey input).run
        (initialCache, initialTrace))) :
    result.2.2.ValidRuns secretKey := by
  rw [cacheTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    mem_support_bind_iff] at hmem
  obtain ⟨⟨output, finalCache⟩, hbase, hpure⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  cases input with
  | inl worldInput => simpa [signingCacheTraceUpdate] using htrace
  | inr request =>
      intro entry hentry
      rw [signingCacheTraceUpdate, List.mem_append] at hentry
      rcases hentry with hentry | hentry
      · exact htrace entry hentry
      · simp only [List.mem_singleton] at hentry
        subst entry
        exact hbase

theorem cacheTracedMappedAdversaryImpl_query_chronological
    (secretKey : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (result : (OracleWorld + SigningSpec).Range input ×
      (QueryCache HashSpec × SigningCacheTrace))
    (hcaches : initialTrace.CachesLe initialCache)
    (hchronological : initialTrace.Chronological)
    (hmem : result ∈ support
      ((cacheTracedMappedAdversaryImpl secretKey input).run
        (initialCache, initialTrace))) :
    result.2.2.Chronological := by
  rw [cacheTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    mem_support_bind_iff] at hmem
  obtain ⟨⟨output, finalCache⟩, _, hpure⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  cases input with
  | inl worldInput => simpa [signingCacheTraceUpdate] using hchronological
  | inr request =>
      apply hchronological.append_singleton
      intro earlier hearlier
      exact (hcaches earlier hearlier).2

theorem cacheTracedMappedAdversaryImpl_cachesLe
    (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (result : α × (QueryCache HashSpec × SigningCacheTrace))
    (htrace : initialTrace.CachesLe initialCache)
    (hmem : result ∈ support
      ((simulateQ (cacheTracedMappedAdversaryImpl secretKey)
        computation).run (initialCache, initialTrace))) :
    result.2.2.CachesLe result.2.1 := by
  exact OracleComp.simulateQ_run_preservesInv
    (cacheTracedMappedAdversaryImpl secretKey)
    (fun state => state.2.CachesLe state.1)
    (by
      intro input state hstate queryResult hquery
      exact cacheTracedMappedAdversaryImpl_query_cachesLe secretKey input state.1 state.2
        queryResult hstate hquery)
    computation (initialCache, initialTrace) htrace result hmem

theorem cacheTracedMappedAdversaryImpl_validRuns
    (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (result : α × (QueryCache HashSpec × SigningCacheTrace))
    (htrace : initialTrace.ValidRuns secretKey)
    (hmem : result ∈ support
      ((simulateQ (cacheTracedMappedAdversaryImpl secretKey)
        computation).run (initialCache, initialTrace))) :
    result.2.2.ValidRuns secretKey := by
  exact OracleComp.simulateQ_run_preservesInv
    (cacheTracedMappedAdversaryImpl secretKey)
    (fun state => state.2.ValidRuns secretKey)
    (by
      intro input state hstate queryResult hquery
      exact cacheTracedMappedAdversaryImpl_query_validRuns secretKey input state.1 state.2
        queryResult hstate hquery)
    computation (initialCache, initialTrace) htrace result hmem

theorem cacheTracedMappedAdversaryImpl_cachesLe_chronological
    (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (result : α × (QueryCache HashSpec × SigningCacheTrace))
    (hcaches : initialTrace.CachesLe initialCache)
    (hchronological : initialTrace.Chronological)
    (hmem : result ∈ support
      ((simulateQ (cacheTracedMappedAdversaryImpl secretKey)
        computation).run (initialCache, initialTrace))) :
    result.2.2.CachesLe result.2.1 ∧ result.2.2.Chronological := by
  exact OracleComp.simulateQ_run_preservesInv
    (cacheTracedMappedAdversaryImpl secretKey)
    (fun state => state.2.CachesLe state.1 ∧ state.2.Chronological)
    (by
      intro input state hstate queryResult hquery
      exact ⟨cacheTracedMappedAdversaryImpl_query_cachesLe secretKey input state.1 state.2
          queryResult hstate.1 hquery,
        cacheTracedMappedAdversaryImpl_query_chronological secretKey input state.1 state.2
          queryResult hstate.1 hstate.2 hquery⟩)
    computation (initialCache, initialTrace) ⟨hcaches, hchronological⟩ result hmem

noncomputable def selectivelyLoggedMappedAdversaryImpl (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (WriterT (QueryLog SigningSpec) (StateT (QueryCache HashSpec) ProbComp)) :=
  QueryImpl.withTraceAppend (unloggedMappedAdversaryImpl secretKey) signingLogFragment

noncomputable def logTracedMappedAdversaryImpl (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT (QueryCache HashSpec × QueryLog SigningSpec) ProbComp) :=
  QueryImpl.extendState (unloggedMappedAdversaryImpl secretKey) signingLogUpdate

theorem selectivelyLoggedMappedAdversaryImpl_apply_inr
    (secretKey : SecretKey) (request : SignRequest) :
    selectivelyLoggedMappedAdversaryImpl secretKey (.inr request) =
      QueryImpl.withLogging
        (fun request => simulateQ romImpl (Concrete.scheme.sign secretKey request)) request := by
  rfl

theorem mappedAdversaryImpl_apply_inr (secretKey : SecretKey) (request : SignRequest) :
    mappedAdversaryImpl secretKey (.inr request) =
      QueryImpl.withLogging
        (fun request => simulateQ romImpl (Concrete.scheme.sign secretKey request)) request := by
  change WriterT.mk (simulateQ romImpl
      ((QueryImpl.withLogging (spec := SigningSpec)
        (fun request => Concrete.scheme.sign secretKey request) request).run)) = _
  apply WriterT.ext
  rw [WriterT.run_mk, QueryImpl.run_withLogging_apply,
    QueryImpl.run_withLogging_apply, simulateQ_bind]
  simp

theorem selectivelyLoggedMappedAdversaryImpl_eq_mapped (secretKey : SecretKey) :
    selectivelyLoggedMappedAdversaryImpl secretKey = mappedAdversaryImpl secretKey := by
  funext input
  cases input with
  | inl worldInput =>
      change (do
          let output ← liftM (romImpl worldInput)
          tell ([] : QueryLog SigningSpec)
          pure output) =
        WriterT.mk ((fun output => (output, ([] : QueryLog SigningSpec))) <$>
          romImpl worldInput)
      apply WriterT.ext
      simp
  | inr request =>
      rw [selectivelyLoggedMappedAdversaryImpl_apply_inr,
        mappedAdversaryImpl_apply_inr]

theorem cacheTracedMappedAdversaryImpl_cache_projection
    (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace) :
    Prod.map id Prod.fst <$>
        (simulateQ (cacheTracedMappedAdversaryImpl secretKey)
          computation).run (initialCache, initialTrace) =
      (simulateQ (unloggedMappedAdversaryImpl secretKey)
        computation).run initialCache := by
  exact OracleComp.extendState_run_proj_eq
    (unloggedMappedAdversaryImpl secretKey) signingCacheTraceUpdate
    computation initialCache initialTrace

theorem cacheTracedMappedAdversaryImpl_log_projection
    (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace) :
    Prod.map id (fun state => (state.1, state.2.toSigningLog)) <$>
        (simulateQ (cacheTracedMappedAdversaryImpl secretKey)
          computation).run (initialCache, initialTrace) =
      (simulateQ (logTracedMappedAdversaryImpl secretKey)
        computation).run (initialCache, initialTrace.toSigningLog) := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (cacheTracedMappedAdversaryImpl secretKey)
    (logTracedMappedAdversaryImpl secretKey)
    (fun state => (state.1, state.2.toSigningLog))
  intro input state
  rw [cacheTracedMappedAdversaryImpl, logTracedMappedAdversaryImpl,
    QueryImpl.extendState_apply, QueryImpl.extendState_apply, map_bind]
  apply bind_congr
  intro result
  simp only [map_pure]
  simpa [Prod.map] using congrArg (fun log => (result.1, (result.2, log)))
    (signingCacheTraceUpdate_toSigningLog input state.1 result.1 result.2 state.2)

theorem selectivelyLoggedMappedAdversaryImpl_query_run_eq_logTraced
    (secretKey : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec) (initialLog : QueryLog SigningSpec) :
    (fun result =>
      (result.1.1, (result.2, initialLog ++ result.1.2))) <$>
        (((selectivelyLoggedMappedAdversaryImpl secretKey input).run).run initialCache) =
      (logTracedMappedAdversaryImpl secretKey input).run (initialCache, initialLog) := by
  rw [selectivelyLoggedMappedAdversaryImpl, QueryImpl.withTraceAppend_apply,
    logTracedMappedAdversaryImpl, QueryImpl.extendState_apply]
  simp only [WriterT.run_bind', WriterT.run_monadLift', WriterT.run_tell,
    WriterT.run_pure', StateT.run_bind, StateT.run_pure, map_bind,
    bind_map_left, pure_bind, map_pure, Prod.map, id_eq]
  apply bind_congr
  intro result
  simp [signingLogUpdate]

theorem selectivelyLoggedMappedAdversaryImpl_run_eq_logTraced
    (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialLog : QueryLog SigningSpec) :
    (fun result =>
      (result.1.1, (result.2, initialLog ++ result.1.2))) <$>
        (((simulateQ (selectivelyLoggedMappedAdversaryImpl secretKey)
          computation).run).run initialCache) =
      (simulateQ (logTracedMappedAdversaryImpl secretKey)
        computation).run (initialCache, initialLog) := by
  induction computation using OracleComp.inductionOn generalizing initialCache initialLog with
  | pure value => simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, WriterT.run_bind', StateT.run_bind, map_bind, id_map]
      rw [← selectivelyLoggedMappedAdversaryImpl_query_run_eq_logTraced
        secretKey input initialCache initialLog]
      simp only [bind_map_left]
      apply bind_congr
      intro prefixResult
      simpa [List.append_assoc] using
        ih prefixResult.1.1 prefixResult.2 (initialLog ++ prefixResult.1.2)

theorem cacheTracedMappedAdversaryImpl_log_projection_eq_mapped
    (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) :
    Prod.map id (fun state => (state.1, state.2.toSigningLog)) <$>
        (simulateQ (cacheTracedMappedAdversaryImpl secretKey)
          computation).run (initialCache, []) =
      (fun result => (result.1.1, (result.2, result.1.2))) <$>
        (((simulateQ (mappedAdversaryImpl secretKey) computation).run).run initialCache) := by
  rw [cacheTracedMappedAdversaryImpl_log_projection]
  simp only [SigningCacheTrace.toSigningLog, List.map_nil]
  rw [← selectivelyLoggedMappedAdversaryImpl_run_eq_logTraced
    secretKey computation initialCache []]
  rw [selectivelyLoggedMappedAdversaryImpl_eq_mapped]
  rfl

end SphincsSecurity
