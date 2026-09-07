import SphincsSecurity.Proof.InterleavedMass

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem enncard_cacheQuery_of_fresh (cache : QueryCache HashSpec) (input : HashInput)
    (output : HashOutput) (hfresh : cache input = none) :
    QueryCache.enncard (cache.cacheQuery input output) = QueryCache.enncard cache + 1 := by
  have hset : (cache.cacheQuery input output).toSet = insert ⟨input, output⟩ cache.toSet := by
    apply Set.Subset.antisymm (QueryCache.toSet_cacheQuery_subset_insert cache input output)
    rintro pair (heq | hold)
    · subst pair
      exact QueryCache.cacheQuery_self _ _ _
    · exact QueryCache.toSet_mono (QueryCache.le_cacheQuery cache hfresh) hold
  have hnot : (⟨input, output⟩ : Sigma HashSpec.Range) ∉ cache.toSet := by
    simp only [QueryCache.mem_toSet, hfresh, reduceCtorEq, not_false_eq_true]
  unfold QueryCache.enncard
  rw [hset, Set.encard_insert_of_notMem hnot]
  simp

noncomputable def freshCacheCharge (cache : QueryCache HashSpec) (input : HashInput) : ENNReal :=
  if cache input = none then 1 else 0

theorem romImpl_enncard_eq_add_freshCharge (input : OracleWorld.Domain) (cache : QueryCache HashSpec)
    (result : OracleWorld.Range input × QueryCache HashSpec)
    (hresult : result ∈ support ((romImpl input).run cache)) :
    QueryCache.enncard result.2 = QueryCache.enncard cache + hashQueryCharge freshCacheCharge cache input := by
  cases input with
  | inl input =>
      rw [romImpl_uniform_query_enncard_eq input cache result hresult]
      exact (add_zero _).symm
  | inr input =>
      change result ∈ support ((randomOracle input).run cache) at hresult
      by_cases hfresh : cache input = none
      · rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, support_map] at hresult
        obtain ⟨output, _, rfl⟩ := hresult
        simpa only [hashQueryCharge, Sum.elim_inr, freshCacheCharge, hfresh, if_true] using enncard_cacheQuery_of_fresh cache input output hfresh
      · obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hfresh
        rw [randomOracle, QueryImpl.withCaching_run_some _ houtput, support_pure, Set.mem_singleton_iff] at hresult
        subst result
        simp only [hashQueryCharge, Sum.elim_inr, freshCacheCharge, hfresh, if_false, add_zero]

theorem expected_romImpl_enncard (input : OracleWorld.Domain) (cache : QueryCache HashSpec) :
    (∑' result, Pr[= result | (romImpl input).run cache] * QueryCache.enncard result.2) =
      QueryCache.enncard cache + hashQueryCharge freshCacheCharge cache input := by
  calc
    _ = ∑' result, Pr[= result | (romImpl input).run cache] *
        (QueryCache.enncard cache + hashQueryCharge freshCacheCharge cache input) := by
      apply tsum_congr
      intro result
      by_cases hresult : result ∈ support ((romImpl input).run cache)
      · rw [romImpl_enncard_eq_add_freshCharge input cache result hresult]
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
    _ = _ := by rw [ENNReal.tsum_mul_right, romImpl_query_mass, one_mul]

theorem expected_simulateQ_enncard {α : Type} (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    (∑' result, Pr[= result | (simulateQ romImpl computation).run cache] * QueryCache.enncard result.2) =
      QueryCache.enncard cache + expectedQueryCharge freshCacheCharge computation cache := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul, expectedQueryCharge_pure, add_zero]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul, expectedQueryCharge_query_bind]
      simp_rw [ih, mul_add]
      rw [ENNReal.tsum_add, expected_romImpl_enncard, add_assoc]

theorem expectedQueryCharge_fresh_eq_growth {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    expectedQueryCharge freshCacheCharge computation cache =
      ∑' result, Pr[= result | (simulateQ romImpl computation).run cache] *
        (QueryCache.enncard result.2 - QueryCache.enncard cache) := by
  have hmass := simulateQ_run_mass_of_query_mass romImpl romImpl_query_mass computation cache
  have hbefore : QueryCache.enncard cache ≠ ∞ := by
    rw [← hfinite.cachedInputs_ncard_toENNReal_eq_enncard]
    finiteness
  have heq : (∑' result, Pr[= result | (simulateQ romImpl computation).run cache] * QueryCache.enncard result.2) =
      ∑' result, Pr[= result | (simulateQ romImpl computation).run cache] *
        (QueryCache.enncard cache + (QueryCache.enncard result.2 - QueryCache.enncard cache)) := by
    apply tsum_congr
    intro result
    by_cases hresult : result ∈ support ((simulateQ romImpl computation).run cache)
    · rw [add_tsub_cancel_of_le (QueryCache.enncard_mono (simulateQ_romImpl_cache_le computation cache result hresult))]
    · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
  simp_rw [mul_add] at heq
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul, expected_simulateQ_enncard] at heq
  exact (ENNReal.add_right_inj hbefore).mp heq

end SphincsSecurity.Concrete
