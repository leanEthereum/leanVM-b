import SphincsSecurity.Proof.ExceptionBudgetPotential

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

theorem cacheEntryException_query_clean (Bad : QueryCache HashSpec → Prop)
    (query : OracleWorld.Domain) (cache : QueryCache HashSpec) (hit : Bool)
    (hclean : hit = false → ¬ Bad cache)
    (result : OracleWorld.Range query × QueryCache HashSpec)
    (hr : result ∈ support ((romImpl query).run cache))
    (hnoHit : (hit || queryException (cacheEntryException Bad) cache query result.1) = false) :
    ¬ Bad result.2 := by
  have hfalse : hit = false := by cases hit <;> simp_all
  subst hit
  simp only [Bool.false_or] at hnoHit
  cases query with
  | inl sample =>
      change unifSpec.Range sample × QueryCache HashSpec at result
      change result ∈ support ((fun answer : unifSpec.Range sample => (answer, cache)) <$>
        (liftM (unifSpec.query sample) : ProbComp _)) at hr
      rw [support_map] at hr
      obtain ⟨answer, _, rfl⟩ := hr
      exact hclean rfl
  | inr input =>
      change HashOutput × QueryCache HashSpec at result
      change result ∈ support ((randomOracle input).run cache) at hr
      by_cases hfresh : cache input = none
      · rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, support_map] at hr
        obtain ⟨answer, _, rfl⟩ := hr
        simpa only [queryException, hfresh, true_and, cacheEntryException, decide_eq_false_iff_not] using hnoHit
      · obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp hfresh
        rw [randomOracle, QueryImpl.withCaching_run_some _ hanswer, mem_support_pure_iff] at hr
        subst result
        exact hclean rfl

theorem runCacheEntryException_clean_of_no_hit (Bad : QueryCache HashSpec → Prop)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hit : Bool)
    (hclean : hit = false → ¬ Bad cache)
    (result : (α × QueryCache HashSpec) × Bool)
    (hr : result ∈ support (runExceptionMonitor (cacheEntryException Bad) computation cache hit))
    (hnoHit : result.2 = false) : ¬ Bad result.1.2 := by
  induction computation using OracleComp.inductionOn generalizing cache hit with
  | pure value =>
      simp only [runExceptionMonitor, construct_pure, mem_support_pure_iff] at hr
      subst result
      exact hclean hnoHit
  | query_bind query next ih =>
      rw [runExceptionMonitor, construct_query_bind] at hr
      change result ∈ support ((romImpl query).run cache >>= fun pair =>
        runExceptionMonitor (cacheEntryException Bad) (next pair.1) pair.2
          (hit || queryException (cacheEntryException Bad) cache query pair.1)) at hr
      rw [mem_support_bind_iff] at hr
      obtain ⟨head, hhead, htail⟩ := hr
      exact ih head.1 head.2 _
        (cacheEntryException_query_clean Bad query cache hit hclean head hhead) htail

end SphincsSecurity
