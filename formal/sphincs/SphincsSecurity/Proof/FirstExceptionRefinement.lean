import SphincsSecurity.Proof.FirstExceptionPrefix
import SphincsSecurity.Proof.CacheEntryExceptionInvariant

namespace SphincsSecurity

open OracleComp OracleSpec

theorem queryException_false_of_imp
    (exception larger : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (himp : ∀ cache input answer, exception cache input answer → larger cache input answer)
    (cache : QueryCache HashSpec) (query : OracleWorld.Domain) (answer : OracleWorld.Range query)
    (hclean : queryException larger cache query answer = false) :
    queryException exception cache query answer = false := by
  cases query with
  | inl sample => rfl
  | inr input =>
      simp only [queryException, decide_eq_false_iff_not] at hclean ⊢
      exact fun h => hclean ⟨h.1, himp cache input answer h.2⟩

theorem ExceptionFreePrefix.of_imp
    {exception larger : QueryCache HashSpec → HashInput → HashOutput → Prop}
    (himp : ∀ cache input answer, exception cache input answer → larger cache input answer)
    {computation suffix : OracleComp OracleWorld α} {cache suffixCache : QueryCache HashSpec} {spent : Nat}
    (hprefix : ExceptionFreePrefix larger computation cache spent suffix suffixCache) :
    ExceptionFreePrefix exception computation cache spent suffix suffixCache := by
  induction hprefix with
  | refl computation cache => exact .refl computation cache
  | step query next cache response spent suffix suffixCache hsupport hclean htail ih =>
      exact .step query next cache response spent suffix suffixCache hsupport
        (queryException_false_of_imp exception larger himp cache query response.1 hclean) ih

theorem ExceptionFreePrefix.clean_of_detects
    (Bad : QueryCache HashSpec → Prop)
    {exception : QueryCache HashSpec → HashInput → HashOutput → Prop}
    (hdetect : ∀ cache input answer, Bad (cache.cacheQuery input answer) → exception cache input answer)
    {computation suffix : OracleComp OracleWorld α} {cache suffixCache : QueryCache HashSpec} {spent : Nat}
    (hprefix : ExceptionFreePrefix exception computation cache spent suffix suffixCache)
    (hclean : ¬ Bad cache) : ¬ Bad suffixCache := by
  induction hprefix with
  | refl => exact hclean
  | step query next cache response spent suffix suffixCache hsupport hnohit htail ih =>
      apply ih
      exact detectingException_query_clean Bad exception hdetect query cache false (fun _ => hclean)
        response hsupport (by simpa only [Bool.false_or] using hnohit)

theorem firstExceptionRecord_cache_clean
    (Bad : QueryCache HashSpec → Prop)
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (hdetect : ∀ cache input answer, Bad (cache.cacheQuery input answer) → exception cache input answer)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hclean : ¬ Bad cache)
    (result : α × QueryCache HashSpec) (record : ExceptionRecord)
    (hresult : (result, some record) ∈ support (runFirstException exception computation cache none)) :
    ¬ Bad record.cache := by
  obtain ⟨_, _, hprefix, _⟩ := firstExceptionRecord_split exception computation cache result record hresult
  exact hprefix.clean_of_detects Bad hdetect hclean

theorem ExceptionFreePrefix.runFirstException_support
    {exception : QueryCache HashSpec → HashInput → HashOutput → Prop}
    {computation suffix : OracleComp OracleWorld α} {cache suffixCache : QueryCache HashSpec} {spent : Nat}
    (hprefix : ExceptionFreePrefix exception computation cache spent suffix suffixCache)
    (result : (α × QueryCache HashSpec) × Option ExceptionRecord)
    (hresult : result ∈ support (runFirstException exception suffix suffixCache none)) :
    result ∈ support (runFirstException exception computation cache none) := by
  induction hprefix with
  | refl => exact hresult
  | step query next cache response spent suffix suffixCache hsupport hclean htail ih =>
      rw [runFirstException, OracleComp.construct_query_bind, mem_support_bind_iff]
      refine ⟨response, hsupport, ?_⟩
      change result ∈ support (runFirstException exception (next response.1) response.2
        (recordQueryException exception cache query response.1))
      rw [recordQueryException_eq_none_of_no_exception exception cache query response.1 hclean]
      exact ih hresult

theorem firstExceptionRecord_support_of_imp
    (exception larger : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (himp : ∀ cache input answer, exception cache input answer → larger cache input answer)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (result : α × QueryCache HashSpec) (record : ExceptionRecord)
    (hresult : (result, some record) ∈ support (runFirstException larger computation cache none))
    (hexception : exception record.cache record.input record.answer) :
    (result, some record) ∈ support (runFirstException exception computation cache none) := by
  obtain ⟨spent, next, hprefix, hfresh, _, hsuffix⟩ :=
    firstExceptionRecord_split larger computation cache result record hresult
  apply (hprefix.of_imp himp).runFirstException_support (result, some record)
  change (result, some record) ∈ support ((randomOracle record.input).run record.cache >>= fun response =>
    runFirstException exception (next response.1) response.2
      (recordQueryException exception record.cache (.inr record.input) response.1))
  rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, bind_map_left, mem_support_bind_iff]
  have hanswer : record.answer ∈ support ($ᵗ HashOutput : ProbComp HashOutput) := by simp
  refine ⟨record.answer, hanswer, ?_⟩
  have hfire : queryException exception record.cache (.inr record.input) record.answer = true := by
    simp only [queryException, decide_eq_true_eq]
    exact ⟨hfresh, hexception⟩
  rw [recordQueryException, if_pos hfire, runFirstException_some, support_map]
  exact ⟨result, hsuffix, by cases record; rfl⟩

end SphincsSecurity
