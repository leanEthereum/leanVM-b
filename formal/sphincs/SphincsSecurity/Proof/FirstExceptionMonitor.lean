import SphincsSecurity.Proof.ExceptionWitness

namespace SphincsSecurity

open OracleComp OracleSpec

structure ExceptionRecord where
  cache : QueryCache HashSpec
  input : HashInput
  answer : HashOutput

noncomputable def recordQueryException
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (cache : QueryCache HashSpec) : (query : OracleWorld.Domain) → OracleWorld.Range query → Option ExceptionRecord
  | .inl _, _ => none
  | .inr input, answer =>
      if queryException exception cache (.inr input) answer then some ⟨cache, input, answer⟩ else none

noncomputable def retainFirstException
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (saved : Option ExceptionRecord) (cache : QueryCache HashSpec)
    (query : OracleWorld.Domain) (answer : OracleWorld.Range query) : Option ExceptionRecord :=
  match saved with
  | some record => some record
  | none => recordQueryException exception cache query answer

theorem retainFirstException_isSome
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (saved : Option ExceptionRecord) (cache : QueryCache HashSpec)
    (query : OracleWorld.Domain) (answer : OracleWorld.Range query) :
    (retainFirstException exception saved cache query answer).isSome =
      (saved.isSome || queryException exception cache query answer) := by
  cases saved with
  | some record => simp [retainFirstException]
  | none =>
      cases query with
      | inl sample => simp [retainFirstException, recordQueryException, queryException]
      | inr input => simp [retainFirstException, recordQueryException]; split <;> simp_all

noncomputable def runFirstException
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (saved : Option ExceptionRecord) :
    ProbComp ((α × QueryCache HashSpec) × Option ExceptionRecord) :=
  OracleComp.construct
    (C := fun _ => QueryCache HashSpec → Option ExceptionRecord → ProbComp ((α × QueryCache HashSpec) × Option ExceptionRecord))
    (fun value cache saved => pure ((value, cache), saved))
    (fun query _ next cache saved => do
      let result ← (romImpl query).run cache
      next result.1 result.2 (retainFirstException exception saved cache query result.1))
    computation cache saved

theorem runFirstException_bind
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (computation : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β)
    (cache : QueryCache HashSpec) (saved : Option ExceptionRecord) :
    runFirstException exception (computation >>= next) cache saved =
      (runFirstException exception computation cache saved >>= fun result =>
        runFirstException exception (next result.1.1) result.1.2 result.2) := by
  induction computation using OracleComp.inductionOn generalizing cache saved with
  | pure value => simp [runFirstException]
  | query_bind query continuation ih =>
      rw [bind_assoc, runFirstException, OracleComp.construct_query_bind,
        runFirstException, OracleComp.construct_query_bind, bind_assoc]
      exact bind_congr fun result => ih result.1 result.2 _

theorem runFirstException_some
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (record : ExceptionRecord) :
    runFirstException exception computation cache (some record) =
      (fun result => (result, some record)) <$> (simulateQ romImpl computation).run cache := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp [runFirstException, simulateQ_pure]
  | query_bind query next ih =>
      rw [runFirstException, OracleComp.construct_query_bind, simulateQ_bind,
        simulateQ_spec_query, StateT.run_bind, map_bind]
      exact bind_congr fun result => ih result.1 result.2

theorem runFirstException_flag_projection
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (saved : Option ExceptionRecord) :
    (fun result => (result.1, result.2.isSome)) <$> runFirstException exception computation cache saved =
      runExceptionMonitor exception computation cache saved.isSome := by
  induction computation using OracleComp.inductionOn generalizing cache saved with
  | pure value => simp [runFirstException, runExceptionMonitor]
  | query_bind query next ih =>
      rw [runFirstException, OracleComp.construct_query_bind, map_bind,
        runExceptionMonitor, OracleComp.construct_query_bind]
      apply bind_congr
      intro result
      change (fun output => (output.1, output.2.isSome)) <$>
        runFirstException exception (next result.1) result.2
          (retainFirstException exception saved cache query result.1) =
        runExceptionMonitor exception (next result.1) result.2
          (saved.isSome || queryException exception cache query result.1)
      rw [ih, retainFirstException_isSome]

theorem runFirstException_project
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (saved : Option ExceptionRecord) :
    Prod.fst <$> runFirstException exception computation cache saved =
      (simulateQ romImpl computation).run cache := by
  rw [← runExceptionMonitor_project exception computation cache saved.isSome,
    ← runFirstException_flag_projection exception computation cache saved, Functor.map_map]

def ExceptionRecord.Valid
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (initialCache finalCache : QueryCache HashSpec) (record : ExceptionRecord) : Prop :=
  initialCache ≤ record.cache ∧ record.cache record.input = none ∧
    exception record.cache record.input record.answer ∧
    record.cache.cacheQuery record.input record.answer ≤ finalCache

theorem ExceptionRecord.Valid.mono_final
    {exception : QueryCache HashSpec → HashInput → HashOutput → Prop}
    {initialCache middleCache finalCache : QueryCache HashSpec} {record : ExceptionRecord}
    (h : record.Valid exception initialCache middleCache) (hle : middleCache ≤ finalCache) :
    record.Valid exception initialCache finalCache :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.trans hle⟩

theorem retainFirstException_valid
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (initialCache cache : QueryCache HashSpec) (saved : Option ExceptionRecord)
    (hle : initialCache ≤ cache)
    (hvalid : ∀ record ∈ saved, record.Valid exception initialCache cache)
    (query : OracleWorld.Domain) (response : OracleWorld.Range query × QueryCache HashSpec)
    (hresponse : response ∈ support ((romImpl query).run cache)) :
    initialCache ≤ response.2 ∧
      ∀ record ∈ retainFirstException exception saved cache query response.1,
        record.Valid exception initialCache response.2 := by
  classical
  have hquery : cache ≤ response.2 :=
    simulateQ_romImpl_cache_le (OracleSpec.query query) cache response
      (by simpa only [simulateQ_spec_query] using hresponse)
  refine ⟨hle.trans hquery, ?_⟩
  cases saved with
  | some previous =>
      intro record hrecord
      have heq : previous = record := by simpa [retainFirstException, eq_comm] using hrecord
      subst record
      exact (hvalid previous (by simp)).mono_final hquery
  | none =>
      cases query with
      | inl sample => simp [retainFirstException, recordQueryException]
      | inr input =>
          intro record hrecord
          have hfire : queryException exception cache (.inr input) response.1 = true := by
            by_contra hnot
            simp [retainFirstException, recordQueryException, hnot] at hrecord
          have hstep : cache input = none ∧ exception cache input response.1 := by
            simpa only [queryException, decide_eq_true_eq] using hfire
          have heq : record = ⟨cache, input, response.1⟩ := by
            simpa [retainFirstException, recordQueryException, hfire, eq_comm] using hrecord
          subst record
          refine ⟨hle, hstep.1, hstep.2, ?_⟩
          change response ∈ support ((randomOracle input).run cache) at hresponse
          rw [randomOracle, QueryImpl.withCaching_run_none _ hstep.1, support_map] at hresponse
          obtain ⟨answer, _, rfl⟩ := hresponse
          exact le_rfl

theorem runFirstException_valid
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (computation : OracleComp OracleWorld α) (initialCache cache : QueryCache HashSpec)
    (saved : Option ExceptionRecord) (hle : initialCache ≤ cache)
    (hvalid : ∀ record ∈ saved, record.Valid exception initialCache cache)
    {result : (α × QueryCache HashSpec) × Option ExceptionRecord}
    (hresult : result ∈ support (runFirstException exception computation cache saved)) :
    ∀ record ∈ result.2, record.Valid exception initialCache result.1.2 := by
  induction computation using OracleComp.inductionOn generalizing cache saved with
  | pure value =>
      simp only [runFirstException, OracleComp.construct_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact hvalid
  | query_bind query next ih =>
      rw [runFirstException, OracleComp.construct_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨response, hresponse, hrest⟩ := hresult
      obtain ⟨hnextLe, hnextValid⟩ := retainFirstException_valid exception initialCache cache saved hle hvalid query response hresponse
      exact ih response.1 response.2 _ hnextLe hnextValid hrest

theorem runFirstException_none_valid
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    {result : (α × QueryCache HashSpec) × Option ExceptionRecord}
    (hresult : result ∈ support (runFirstException exception computation cache none)) :
    ∀ record ∈ result.2, record.Valid exception cache result.1.2 :=
  runFirstException_valid exception computation cache cache none le_rfl (by simp) hresult

end SphincsSecurity
