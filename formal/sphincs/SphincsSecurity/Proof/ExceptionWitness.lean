import SphincsSecurity.Proof.AmortizedExceptions
import SphincsSecurity.Proof.FirstBad

namespace SphincsSecurity

open OracleComp OracleSpec

def FreshExceptionStep (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (initialCache finalCache : QueryCache HashSpec) : Prop :=
  ∃ cache input answer, initialCache ≤ cache ∧ cache input = none ∧
    exception cache input answer ∧ cache.cacheQuery input answer ≤ finalCache

theorem runExceptionMonitor_support_project
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hit : Bool)
    {result : (α × QueryCache HashSpec) × Bool}
    (hresult : result ∈ support (runExceptionMonitor exception computation cache hit)) :
    result.1 ∈ support ((simulateQ romImpl computation).run cache) := by
  rw [← runExceptionMonitor_project exception computation cache hit, support_map]
  exact ⟨result, hresult, rfl⟩

theorem runExceptionMonitor_cache_le
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hit : Bool)
    {result : (α × QueryCache HashSpec) × Bool}
    (hresult : result ∈ support (runExceptionMonitor exception computation cache hit)) :
    cache ≤ result.1.2 :=
  simulateQ_romImpl_cache_le computation cache result.1
    (runExceptionMonitor_support_project exception computation cache hit hresult)

theorem freshExceptionStep_of_runExceptionMonitor_hit
    (exception : QueryCache HashSpec → HashInput → HashOutput → Prop)
    (computation : OracleComp OracleWorld α) (initialCache : QueryCache HashSpec)
    {result : (α × QueryCache HashSpec) × Bool}
    (hresult : result ∈ support (runExceptionMonitor exception computation initialCache false))
    (hhit : result.2 = true) : FreshExceptionStep exception initialCache result.1.2 := by
  classical
  induction computation using OracleComp.inductionOn generalizing initialCache with
  | pure value =>
      simp only [runExceptionMonitor, OracleComp.construct_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      contradiction
  | query_bind query next ih =>
      rw [runExceptionMonitor, OracleComp.construct_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨response, hresponse, hrest⟩ := hresult
      change result ∈ support (runExceptionMonitor exception (next response.1) response.2
        (false || queryException exception initialCache query response.1)) at hrest
      simp only [Bool.false_or] at hrest
      by_cases hfire : queryException exception initialCache query response.1 = true
      · cases query with
        | inl sample => simp [queryException] at hfire
        | inr input =>
            have hstep : initialCache input = none ∧ exception initialCache input response.1 := by
              simpa only [queryException, decide_eq_true_eq] using hfire
            have hcache : response.2 = initialCache.cacheQuery input response.1 := by
              change response ∈ support ((randomOracle input).run initialCache) at hresponse
              rw [randomOracle, QueryImpl.withCaching_run_none _ hstep.1, support_map] at hresponse
              obtain ⟨answer, _, rfl⟩ := hresponse
              rfl
            refine ⟨initialCache, input, response.1, le_rfl, hstep.1, hstep.2, ?_⟩
            rw [← hcache]
            exact runExceptionMonitor_cache_le exception (next response.1) response.2 _ hrest
      · have hfalse : queryException exception initialCache query response.1 = false := by
          cases h : queryException exception initialCache query response.1 <;> simp_all
        rw [hfalse] at hrest
        obtain ⟨cache, input, answer, hbefore, hfresh, hexception, hafter⟩ := ih response.1 response.2 hrest
        have hquery : initialCache ≤ response.2 :=
          simulateQ_romImpl_cache_le (OracleSpec.query query) initialCache response
            (by simpa only [simulateQ_spec_query] using hresponse)
        exact ⟨cache, input, answer, hquery.trans hbefore, hfresh, hexception, hafter⟩

end SphincsSecurity
