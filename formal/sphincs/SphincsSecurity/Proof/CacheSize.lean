import SphincsSecurity.Proof.QueryBound

/-!
# Random-oracle cache size

A run starting from a cache can add at most one entry per hash query. Uniform-sampling queries leave
the cache unchanged.
-/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

theorem QueryCache.enncard_mono {first second : QueryCache HashSpec}
    (hle : first ≤ second) : QueryCache.enncard first ≤ QueryCache.enncard second := by
  exact ENat.toENNReal_mono (Set.encard_le_encard (QueryCache.toSet_mono hle))

theorem romImpl_uniform_query_enncard_eq
    (input : unifSpec.Domain) (cache : QueryCache HashSpec)
    (result : unifSpec.Range input × QueryCache HashSpec)
    (hmem : result ∈ support ((romImpl (.inl input)).run cache)) :
    QueryCache.enncard result.2 = QueryCache.enncard cache := by
  change result ∈ support ((unifFwdImpl HashSpec input).run cache) at hmem
  have hrun : (unifFwdImpl HashSpec input).run cache =
      (fun sample => (sample, cache)) <$>
        (liftM (unifSpec.query input) : ProbComp (unifSpec.Range input)) := by
    simpa [simulateQ_query] using
      (unifFwdImpl.simulateQ_run
        (hashSpec := HashSpec)
        (liftM (unifSpec.query input) : ProbComp (unifSpec.Range input)) cache)
  rw [hrun, support_map] at hmem
  obtain ⟨sample, _hsample, rfl⟩ := hmem
  rfl

theorem romImpl_hash_query_enncard_le
    (input : HashInput) (cache : QueryCache HashSpec)
    (result : HashOutput × QueryCache HashSpec)
    (hmem : result ∈ support ((romImpl (.inr input)).run cache)) :
    QueryCache.enncard result.2 ≤ QueryCache.enncard cache + 1 := by
  change result ∈ support ((randomOracle input).run cache) at hmem
  by_cases hcache : cache input = none
  · rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hcache,
      support_map] at hmem
    obtain ⟨output, _houtput, rfl⟩ := hmem
    exact QueryCache.enncard_cacheQuery_le cache input output
  · obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hcache
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ houtput,
      support_pure, Set.mem_singleton_iff] at hmem
    subst result
    exact le_add_right le_rfl

set_option linter.constructorNameAsVariable false in
theorem simulateQ_romImpl_enncard_le
    {Result : Type} (computation : OracleComp OracleWorld Result) :
    ∀ (q : Nat), computation.IsQueryBoundP (· matches Sum.inr _) q →
      ∀ (cache : QueryCache HashSpec) (result : Result × QueryCache HashSpec),
        result ∈ support ((simulateQ romImpl computation).run cache) →
        QueryCache.enncard result.2 ≤ QueryCache.enncard cache + q := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro q _ cache result hmem
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hmem
      subst result
      exact le_add_right le_rfl
  | query_bind input continuation ih =>
      intro q hq cache result hmem
      rw [isQueryBoundP_query_bind_iff] at hq
      obtain ⟨hcan, hcontinuation⟩ := hq
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨queryResult, hquery, hrest⟩ := hmem
      cases input with
      | inl uniformInput =>
          simp only [Bool.false_eq_true, if_false] at hcontinuation
          calc
            QueryCache.enncard result.2 ≤ QueryCache.enncard queryResult.2 + q :=
              ih queryResult.1 q (hcontinuation queryResult.1) queryResult.2 result hrest
            _ = QueryCache.enncard cache + q := by
              rw [romImpl_uniform_query_enncard_eq uniformInput cache queryResult hquery]
      | inr hashInput =>
          simp only [if_true] at hcontinuation
          have hqPositive : 0 < q := by simpa using hcan
          obtain ⟨remaining, rfl⟩ : ∃ remaining, q = remaining + 1 :=
            ⟨q - 1, by omega⟩
          simp only [Nat.add_sub_cancel] at hcontinuation
          calc
            QueryCache.enncard result.2 ≤ QueryCache.enncard queryResult.2 + remaining :=
              ih queryResult.1 remaining (hcontinuation queryResult.1)
                queryResult.2 result hrest
            _ ≤ (QueryCache.enncard cache + 1) + remaining := by
              gcongr
              exact romImpl_hash_query_enncard_le hashInput cache queryResult hquery
            _ = QueryCache.enncard cache + (remaining + 1 : Nat) := by
              push_cast
              ring

theorem simulateQ_romImpl_enncard_le_queryBound
    {Result : Type} (computation : OracleComp OracleWorld Result) (q : Nat)
    (hq : computation.IsQueryBoundP (· matches Sum.inr _) q)
    (result : Result × QueryCache HashSpec)
    (hmem : result ∈ support ((simulateQ romImpl computation).run ∅)) :
    QueryCache.enncard result.2 ≤ q := by
  simpa only [QueryCache.enncard_empty, zero_add] using
    simulateQ_romImpl_enncard_le computation q hq ∅ result hmem

end SphincsSecurity
