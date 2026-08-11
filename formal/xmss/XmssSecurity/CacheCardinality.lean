import XmssSecurity.DetailedExecution
import VCVio.OracleComp.QueryTracking.QueryBound

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Rom

/-- A mixed computation making at most `q` hash queries adds at most `q` live entries to the lazy random-oracle cache. Public uniform samples do not affect the cache. -/
theorem mixed_cache_enncard_le_of_mem_support {α : Type}
    (computation : OracleComp OracleWorld α) (q : Nat)
    (hbound : computation.IsQueryBoundP (· matches .inr _) q)
    (initialCache : QueryCache HashSpec)
    (result : α × QueryCache HashSpec)
    (hmem : result ∈ support ((simulateQ xmssRomImpl computation).run initialCache)) :
    QueryCache.enncard result.2 ≤
      QueryCache.enncard initialCache + (q : ℝ≥0∞) := by
  induction computation using OracleComp.inductionOn generalizing q initialCache result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hmem
      subst result
      simp
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨output, middleCache⟩, hquery, hrest⟩ := hmem
      rcases query with uniformIndex | hashInput
      · have hmiddle : middleCache = initialCache := by
          change unifSpec.Range uniformIndex at output
          have hrun :
              (unifFwdImpl HashSpec uniformIndex).run initialCache =
                (fun sample => (sample, initialCache)) <$>
                  (liftM (unifSpec.query uniformIndex) : ProbComp _) := by
            simpa [simulateQ_query] using
              (unifFwdImpl.simulateQ_run
                (hashSpec := HashSpec)
                (liftM (unifSpec.query uniformIndex) : ProbComp _) initialCache)
          simp only [simulateQ_spec_query, xmssRomImpl, QueryImpl.add_apply] at hquery
          have hquery' : (output, middleCache) ∈
              support ((unifFwdImpl HashSpec uniformIndex).run initialCache) := hquery
          rw [hrun, support_map] at hquery'
          obtain ⟨sample, _hsample, heq⟩ := hquery'
          exact (congrArg Prod.snd heq).symm
        subst middleCache
        exact ih output q (by simpa using hbound.2 output)
          initialCache result hrest
      · have hqpos : 0 < q := by simpa using hbound.1
        change HashSpec.Range hashInput at output
        have hqone : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hqpos)
        rw [show simulateQ xmssRomImpl
            (liftM (OracleWorld.query (Sum.inr hashInput))) =
            (randomOracle : QueryImpl HashSpec
              (StateT (QueryCache HashSpec) ProbComp)) hashInput by
          simp [xmssRomImpl]] at hquery
        cases hcached : initialCache hashInput with
        | none =>
            have hmiddle : middleCache = initialCache.cacheQuery hashInput output := by
              have hquery' : (output, middleCache) ∈ support
                  ((randomOracle (spec := HashSpec) hashInput).run initialCache) := hquery
              rw [QueryImpl.withCaching_run_none _ hcached, support_map,
                Set.mem_image] at hquery'
              obtain ⟨sampled, _hsampled, heq⟩ := hquery'
              cases heq
              rfl
            subst middleCache
            calc
              QueryCache.enncard result.2 ≤
                  QueryCache.enncard
                      (initialCache.cacheQuery hashInput output) +
                    ((q - 1 : Nat) : ℝ≥0∞) :=
                ih output (q - 1) (by simpa using hbound.2 output)
                  (initialCache.cacheQuery hashInput output) result hrest
              _ ≤ (QueryCache.enncard initialCache + 1) +
                    ((q - 1 : Nat) : ℝ≥0∞) := by
                gcongr
                exact QueryCache.enncard_cacheQuery_le initialCache hashInput output
              _ = QueryCache.enncard initialCache + (q : ℝ≥0∞) := by
                rw [add_assoc, ← Nat.cast_one, ← Nat.cast_add,
                  Nat.add_sub_cancel' hqone]
        | some cached =>
            have hmiddle : middleCache = initialCache := by
              have hquery' : (output, middleCache) ∈ support
                  ((randomOracle (spec := HashSpec) hashInput).run initialCache) := hquery
              rw [QueryImpl.withCaching_run_some _ hcached, support_pure,
                Set.mem_singleton_iff] at hquery'
              exact congrArg Prod.snd hquery'
            subst middleCache
            calc
              QueryCache.enncard result.2 ≤
                  QueryCache.enncard initialCache +
                    ((q - 1 : Nat) : ℝ≥0∞) :=
                ih output (q - 1) (by simpa using hbound.2 output)
                  initialCache result hrest
              _ ≤ QueryCache.enncard initialCache + (q : ℝ≥0∞) := by
                gcongr
                exact_mod_cast Nat.sub_le q 1

/-- Starting from the empty cache, every supported detailed game execution has at most `q` live hash entries. -/
theorem detailedGame_cache_enncard_le_of_mem_support
    (scheme : Scheme) (adversary : Adversary scheme) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q)
    (execution : GameOutcome × QueryCache HashSpec)
    (hmem : execution ∈ support (detailedGameWithCache scheme adversary)) :
    QueryCache.enncard execution.2 ≤ (q : ℝ≥0∞) := by
  rw [hasHashQueryBound_iff_detailedGameCore] at hbound
  simpa [detailedGameWithCache] using
    mixed_cache_enncard_le_of_mem_support
      (detailedGameCore scheme adversary) q hbound ∅ execution hmem

end XmssSecurity.Rom
