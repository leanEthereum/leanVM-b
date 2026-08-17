import XmssSecurity.PrecomputedScheme

open OracleComp OracleSpec

namespace XmssSecurity

theorem hashCacheOfLog_le (log : QueryLog HashSpec)
    (cache : QueryCache HashSpec)
    (hentries : ∀ entry ∈ log, cache entry.1 = some entry.2) :
    hashCacheOfLog log ≤ cache := by
  induction log with
  | nil => exact bot_le
  | cons entry tail ih =>
      intro input output hlookup
      simp only [hashCacheOfLog] at hlookup
      by_cases heq : input = entry.1
      · subst input
        rw [QueryCache.cacheQuery_self] at hlookup
        cases hlookup
        exact hentries entry (by simp)
      · rw [QueryCache.cacheQuery_of_ne _ _ heq] at hlookup
        exact ih (fun tailEntry htail =>
          hentries tailEntry (List.Mem.tail entry htail)) hlookup

theorem withQueryLog_entries_cached_and_cache_le {alpha : Type}
    (computation : OracleComp HashSpec alpha)
    (initialCache : QueryCache HashSpec)
    (result : (alpha × QueryLog HashSpec) × QueryCache HashSpec)
    (hmem : result ∈ support
      ((simulateQ randomOracle computation.withQueryLog).run initialCache)) :
    (∀ entry ∈ result.1.2, result.2 entry.1 = some entry.2) ∧
      initialCache ≤ result.2 := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache result with
  | pure value =>
      simp only [withQueryLog_pure, simulateQ_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at hmem
      subst result
      exact ⟨by simp, le_rfl⟩
  | query_bind input next ih =>
      change result ∈ support ((simulateQ randomOracle
        ((simulateQ loggingOracle
          (liftM (OracleSpec.query input) >>= next)).run)).run initialCache) at hmem
      rw [OracleComp.run_simulateQ_loggingOracle_query_bind,
        simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨output, middleCache⟩, hquery, hrest⟩ := hmem
      rw [simulateQ_map, StateT.run_map, support_map] at hrest
      obtain ⟨continuationResult, hcontinuation, rfl⟩ := hrest
      obtain ⟨hentries, hmiddleLe⟩ :=
        ih output middleCache continuationResult hcontinuation
      have hmiddle : middleCache input = some output :=
        Concrete.CacheReplay.randomOracle_query_caches input initialCache
          output middleCache (by simpa using hquery)
      exact ⟨fun entry hentry => by
          cases hentry with
          | head => exact hmiddleLe hmiddle
          | tail _ htail => exact hentries entry htail,
        (Concrete.CacheReplay.randomOracle_cache_le
          (liftM (OracleSpec.query input) : OracleComp HashSpec HashOutput)
          initialCache (output, middleCache) hquery).trans hmiddleLe⟩

theorem hashCacheOfLog_le_finalCache {alpha : Type}
    (computation : OracleComp HashSpec alpha)
    (initialCache : QueryCache HashSpec)
    (result : (alpha × QueryLog HashSpec) × QueryCache HashSpec)
    (hmem : result ∈ support
      ((simulateQ randomOracle computation.withQueryLog).run initialCache)) :
    hashCacheOfLog result.1.2 ≤ result.2 :=
  hashCacheOfLog_le result.1.2 result.2
    (withQueryLog_entries_cached_and_cache_le computation initialCache result hmem).1

end XmssSecurity
