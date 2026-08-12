import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable

open OracleComp OracleSpec

namespace OracleComp

variable {D R : Type} [DecidableEq D] [SampleableType R]

omit [SampleableType R] in
theorem QueryCache.cacheQuery_comm_of_ne
    (cache : (D →ₒ R).QueryCache) {left right : D} (h : left ≠ right)
    (leftValue rightValue : R) :
    (cache.cacheQuery left leftValue).cacheQuery right rightValue =
      (cache.cacheQuery right rightValue).cacheQuery left leftValue := by
  funext input
  by_cases hleft : input = left
  · subst input
    simp [QueryCache.cacheQuery_of_ne, h]
  · by_cases hright : input = right
    · subst input
      simp [QueryCache.cacheQuery_of_ne, hleft]
    · simp [QueryCache.cacheQuery_of_ne, hleft, hright]

/-- Sampling one previously absent random-oracle entry before a computation preserves its output distribution. -/
theorem evalDist_randomOracle_run'_eq_presample
    {α : Type} (computation : OracleComp (D →ₒ R) α)
    (cache : (D →ₒ R).QueryCache) (target : D)
    (habsent : cache target = none) :
    𝒟[(simulateQ randomOracle computation).run' cache] =
      𝒟[do
        let value ← $ᵗ R
        (simulateQ randomOracle computation).run'
          (cache.cacheQuery target value)] := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value =>
      change 𝒟[(pure value : ProbComp α)] =
        𝒟[do let _sampled ← $ᵗ R; pure value]
      symm
      exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        ($ᵗ R) (probFailure_uniformSample R) (pure value)
  | query_bind input next ih =>
      have hrun (initialCache : (D →ₒ R).QueryCache) :
          (simulateQ randomOracle
            (liftM ((D →ₒ R).query input) >>= next)).run' initialCache =
          ((randomOracle (spec := D →ₒ R) input).run initialCache) >>= fun result =>
            (simulateQ randomOracle (next result.1)).run' result.2 := by
        rw [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq,
          StateT.run_bind, map_bind]
        rfl
      by_cases htarget : input = target
      · subst input
        rw [hrun, QueryImpl.withCaching_run_none _ habsent,
          map_eq_bind_pure_comp]
        simp only [Function.comp_apply, bind_assoc, pure_bind]
        apply OracleComp.DeferredSampling.evalDist_bind_congr_left
        intro sampled
        rw [hrun, QueryImpl.withCaching_run_some _
          (QueryCache.cacheQuery_self cache target sampled), pure_bind]
      · cases hinput : cache input with
        | some answer =>
            rw [hrun, QueryImpl.withCaching_run_some _ hinput, pure_bind]
            change 𝒟[(simulateQ randomOracle (next answer)).run' cache] =
              𝒟[$ᵗ R >>= fun sampled =>
                (simulateQ randomOracle
                  (liftM ((D →ₒ R).query input) >>= next)).run'
                    (cache.cacheQuery target sampled)]
            calc
              𝒟[(simulateQ randomOracle (next answer)).run' cache] =
                  𝒟[do
                    let sampled ← $ᵗ R
                    (simulateQ randomOracle (next answer)).run'
                      (cache.cacheQuery target sampled)] :=
                ih answer cache habsent
              _ = 𝒟[do
                    let sampled ← $ᵗ R
                    (simulateQ randomOracle
                      (liftM ((D →ₒ R).query input) >>= next)).run'
                        (cache.cacheQuery target sampled)] := by
                apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                intro sampled
                have hcached : (cache.cacheQuery target sampled) input = some answer := by
                  rw [QueryCache.cacheQuery_of_ne cache sampled htarget]
                  exact hinput
                rw [hrun, QueryImpl.withCaching_run_some _ hcached, pure_bind]
            rfl

        | none =>
            have htargetAfterInput : ∀ answer : R,
                (cache.cacheQuery input answer) target = none := by
              intro answer
              simpa [QueryCache.cacheQuery_of_ne, Ne.symm htarget] using habsent
            rw [hrun, QueryImpl.withCaching_run_none _ hinput,
              map_eq_bind_pure_comp]
            simp only [Function.comp_apply, bind_assoc, pure_bind]
            change 𝒟[$ᵗ R >>= fun answer =>
                (simulateQ randomOracle (next answer)).run'
                  (cache.cacheQuery input answer)] =
              𝒟[$ᵗ R >>= fun sampled =>
                (simulateQ randomOracle
                  (liftM ((D →ₒ R).query input) >>= next)).run'
                    (cache.cacheQuery target sampled)]
            calc
              𝒟[$ᵗ R >>= fun answer =>
                    (simulateQ randomOracle (next answer)).run'
                      (cache.cacheQuery input answer)] =
                  𝒟[$ᵗ R >>= fun answer =>
                    $ᵗ R >>= fun sampled =>
                      (simulateQ randomOracle (next answer)).run'
                        ((cache.cacheQuery input answer).cacheQuery target sampled)] := by
                apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                intro answer
                exact ih answer (cache.cacheQuery input answer)
                  (htargetAfterInput answer)
              _ = 𝒟[$ᵗ R >>= fun sampled =>
                    $ᵗ R >>= fun answer =>
                      (simulateQ randomOracle (next answer)).run'
                        ((cache.cacheQuery input answer).cacheQuery target sampled)] :=
                OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
              _ = 𝒟[$ᵗ R >>= fun sampled =>
                    $ᵗ R >>= fun answer =>
                      (simulateQ randomOracle (next answer)).run'
                        ((cache.cacheQuery target sampled).cacheQuery input answer)] := by
                apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                intro sampled
                apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                intro answer
                rw [QueryCache.cacheQuery_comm_of_ne cache htarget]
              _ = 𝒟[do
                    let sampled ← $ᵗ R
                    (simulateQ randomOracle
                      (liftM ((D →ₒ R).query input) >>= next)).run'
                        (cache.cacheQuery target sampled)] := by
                apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                intro sampled
                have hnone : (cache.cacheQuery target sampled) input = none := by
                  rw [QueryCache.cacheQuery_of_ne cache sampled htarget]
                  exact hinput
                rw [hrun, QueryImpl.withCaching_run_none _ hnone,
                  map_eq_bind_pure_comp]
                simp only [Function.comp_apply, bind_assoc, pure_bind]
                change 𝒟[$ᵗ R >>= fun answer =>
                    (simulateQ randomOracle (next answer)).run'
                      ((cache.cacheQuery target sampled).cacheQuery input answer)] = _
                rfl
            rfl

/-- Sampling one absent entry before a computation preserves the full result and final-cache distribution when every execution of the computation caches that entry. -/
theorem evalDist_randomOracle_run_eq_presample_of_cached
    {α : Type} (computation : OracleComp (D →ₒ R) α)
    (cache : (D →ₒ R).QueryCache) (target : D)
    (habsent : cache target = none)
    (hcached : ∀ result ∈ support
      ((simulateQ randomOracle computation).run cache),
      ∃ output, result.2 target = some output) :
    𝒟[(simulateQ randomOracle computation).run cache] =
      𝒟[do
        let value ← $ᵗ R
        (simulateQ randomOracle computation).run
          (cache.cacheQuery target value)] := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value =>
      exfalso
      obtain ⟨output, houtput⟩ := hcached (value, cache) (by simp)
      change cache target = some output at houtput
      rw [habsent] at houtput
      simp at houtput
  | query_bind input next ih =>
      have hrun (initialCache : (D →ₒ R).QueryCache) :
          (simulateQ randomOracle
            (liftM ((D →ₒ R).query input) >>= next)).run initialCache =
          ((randomOracle (spec := D →ₒ R) input).run initialCache) >>= fun result =>
            (simulateQ randomOracle (next result.1)).run result.2 := by
        rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      by_cases htarget : input = target
      · subst input
        rw [hrun, QueryImpl.withCaching_run_none _ habsent,
          map_eq_bind_pure_comp]
        simp only [Function.comp_apply, bind_assoc, pure_bind]
        apply OracleComp.DeferredSampling.evalDist_bind_congr_left
        intro sampled
        rw [hrun, QueryImpl.withCaching_run_some _
          (QueryCache.cacheQuery_self cache target sampled), pure_bind]
      · cases hinput : cache input with
        | some answer =>
            rw [hrun, QueryImpl.withCaching_run_some _ hinput, pure_bind]
            have hnextCached : ∀ result ∈ support
                ((simulateQ randomOracle (next answer)).run cache),
                ∃ output, result.2 target = some output := by
              intro result hresult
              apply hcached result
              rw [hrun, mem_support_bind_iff]
              refine ⟨(answer, cache), ?_, hresult⟩
              rw [QueryImpl.withCaching_run_some _ hinput]
              simp
            calc
              𝒟[(simulateQ randomOracle (next answer)).run cache] =
                  𝒟[do
                    let sampled ← $ᵗ R
                    (simulateQ randomOracle (next answer)).run
                      (cache.cacheQuery target sampled)] :=
                ih answer cache habsent hnextCached
              _ = 𝒟[do
                    let sampled ← $ᵗ R
                    (simulateQ randomOracle
                      (liftM ((D →ₒ R).query input) >>= next)).run
                        (cache.cacheQuery target sampled)] := by
                apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                intro sampled
                have hcachedInput :
                    (cache.cacheQuery target sampled) input = some answer := by
                  rw [QueryCache.cacheQuery_of_ne cache sampled htarget]
                  exact hinput
                rw [hrun, QueryImpl.withCaching_run_some _ hcachedInput, pure_bind]
            rfl
        | none =>
            have htargetAfterInput : ∀ answer : R,
                (cache.cacheQuery input answer) target = none := by
              intro answer
              simpa [QueryCache.cacheQuery_of_ne, Ne.symm htarget] using habsent
            rw [hrun, QueryImpl.withCaching_run_none _ hinput,
              map_eq_bind_pure_comp]
            simp only [Function.comp_apply, bind_assoc, pure_bind]
            have hnextCached : ∀ answer : R, ∀ result ∈ support
                ((simulateQ randomOracle (next answer)).run
                  (cache.cacheQuery input answer)),
                ∃ output, result.2 target = some output := by
              intro answer result hresult
              apply hcached result
              rw [hrun, mem_support_bind_iff]
              refine ⟨(answer, cache.cacheQuery input answer), ?_, hresult⟩
              rw [QueryImpl.withCaching_run_none _ hinput, support_map]
              exact ⟨answer, mem_support_uniformSample R, rfl⟩
            calc
              𝒟[$ᵗ R >>= fun answer =>
                  (simulateQ randomOracle (next answer)).run
                    (cache.cacheQuery input answer)] =
                  𝒟[$ᵗ R >>= fun answer =>
                    $ᵗ R >>= fun sampled =>
                      (simulateQ randomOracle (next answer)).run
                        ((cache.cacheQuery input answer).cacheQuery target sampled)] := by
                apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                intro answer
                exact ih answer (cache.cacheQuery input answer)
                  (htargetAfterInput answer) (hnextCached answer)
              _ = 𝒟[$ᵗ R >>= fun sampled =>
                    $ᵗ R >>= fun answer =>
                      (simulateQ randomOracle (next answer)).run
                        ((cache.cacheQuery input answer).cacheQuery target sampled)] :=
                OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
              _ = 𝒟[$ᵗ R >>= fun sampled =>
                    $ᵗ R >>= fun answer =>
                      (simulateQ randomOracle (next answer)).run
                        ((cache.cacheQuery target sampled).cacheQuery input answer)] := by
                apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                intro sampled
                apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                intro answer
                rw [QueryCache.cacheQuery_comm_of_ne cache htarget]
              _ = 𝒟[do
                    let sampled ← $ᵗ R
                    (simulateQ randomOracle
                      (liftM ((D →ₒ R).query input) >>= next)).run
                        (cache.cacheQuery target sampled)] := by
                apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                intro sampled
                have hnone : (cache.cacheQuery target sampled) input = none := by
                  rw [QueryCache.cacheQuery_of_ne cache sampled htarget]
                  exact hinput
                rw [hrun, QueryImpl.withCaching_run_none _ hnone,
                  map_eq_bind_pure_comp]
                simp only [Function.comp_apply, bind_assoc, pure_bind]
                rfl
            rfl

/-- Querying one entry and discarding its answer before a computation preserves the full result and final-cache distribution when the computation always caches that entry. -/
theorem evalDist_randomOracle_run_eq_query_then_of_cached
    {α : Type} (computation : OracleComp (D →ₒ R) α)
    (cache : (D →ₒ R).QueryCache) (target : D)
    (hcached : ∀ result ∈ support
      ((simulateQ randomOracle computation).run cache),
      ∃ output, result.2 target = some output) :
    𝒟[(simulateQ randomOracle computation).run cache] =
      𝒟[(randomOracle (spec := D →ₒ R) target).run cache >>= fun queryResult =>
        (simulateQ randomOracle computation).run queryResult.2] := by
  cases htarget : cache target with
  | none =>
      rw [QueryImpl.withCaching_run_none _ htarget,
        map_eq_bind_pure_comp]
      simp only [Function.comp_apply, bind_assoc, pure_bind]
      exact evalDist_randomOracle_run_eq_presample_of_cached
        computation cache target htarget hcached
  | some output =>
      rw [QueryImpl.withCaching_run_some _ htarget, pure_bind]

/-- A computation may be run as a discarded warmup before a target computation when every query
made by the warmup is guaranteed to be cached by the target. This preserves the target's full
result and final-cache distribution. -/
theorem evalDist_randomOracle_run_eq_warmup_then_of_cached
    {α β : Type} (target : OracleComp (D →ₒ R) α)
    (warmup : OracleComp (D →ₒ R) β)
    (covered : D → Prop) [DecidablePred covered]
    (hqueries : warmup.IsQueryBoundP (fun input => ¬ covered input) 0)
    (hcached : ∀ input, covered input →
      ∀ cache : (D →ₒ R).QueryCache,
      ∀ result ∈ support ((simulateQ randomOracle target).run cache),
        ∃ output, result.2 input = some output)
    (cache : (D →ₒ R).QueryCache) :
    𝒟[(simulateQ randomOracle target).run cache] =
      𝒟[(simulateQ randomOracle warmup).run cache >>= fun warmResult =>
        (simulateQ randomOracle target).run warmResult.2] := by
  induction warmup using OracleComp.inductionOn generalizing cache with
  | pure value =>
      simp
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hqueries
      have hcovered : covered input := by
        rcases hqueries.1 with houtside | hpositive
        · exact Classical.byContradiction houtside
        · omega
      have hnext : ∀ answer,
          (next answer).IsQueryBoundP (fun candidate => ¬ covered candidate) 0 := by
        intro answer
        simpa using hqueries.2 answer
      calc
        𝒟[(simulateQ randomOracle target).run cache] =
            𝒟[(randomOracle (spec := D →ₒ R) input).run cache >>=
              fun queryResult =>
                (simulateQ randomOracle target).run queryResult.2] :=
          evalDist_randomOracle_run_eq_query_then_of_cached
            target cache input (hcached input hcovered cache)
        _ = 𝒟[(randomOracle (spec := D →ₒ R) input).run cache >>=
              fun queryResult =>
                (simulateQ randomOracle (next queryResult.1)).run queryResult.2 >>=
                  fun warmResult =>
                    (simulateQ randomOracle target).run warmResult.2] := by
          apply evalDist_bind_congr
          intro queryResult _hqueryResult
          exact ih queryResult.1 (hnext queryResult.1) queryResult.2
        _ = 𝒟[(simulateQ randomOracle
              (liftM ((D →ₒ R).query input) >>= next)).run cache >>=
                fun warmResult =>
                  (simulateQ randomOracle target).run warmResult.2] := by
          simp [StateT.run_bind, bind_assoc]

/-- Every next query on every reachable path of `warmup` is cached by `target` when both start
from the cache at that point. -/
def RandomOracleWarmupCovered
    {α β : Type} (target : OracleComp (D →ₒ R) α)
    (warmup : OracleComp (D →ₒ R) β) :
    (D →ₒ R).QueryCache → Prop :=
  OracleComp.recOn warmup
    (fun _ _cache => True)
    (fun input _next coveredNext cache =>
      (∀ result ∈ support ((simulateQ randomOracle target).run cache),
          ∃ output, result.2 input = some output) ∧
        ∀ queryResult ∈ support
            ((randomOracle (spec := D →ₒ R) input).run cache),
          coveredNext queryResult.1 queryResult.2)

/-- Running an adaptively covered warmup before a target computation preserves the target's full
result and final-cache distribution. -/
theorem evalDist_randomOracle_run_eq_coveredWarmup_then
    {α β : Type} (target : OracleComp (D →ₒ R) α)
    (warmup : OracleComp (D →ₒ R) β)
    (cache : (D →ₒ R).QueryCache)
    (hcovered : RandomOracleWarmupCovered target warmup cache) :
    𝒟[(simulateQ randomOracle target).run cache] =
      𝒟[(simulateQ randomOracle warmup).run cache >>= fun warmResult =>
        (simulateQ randomOracle target).run warmResult.2] := by
  induction warmup using OracleComp.inductionOn generalizing cache with
  | pure value =>
      simp
  | query_bind input next ih =>
      change
        (∀ result ∈ support ((simulateQ randomOracle target).run cache),
            ∃ output, result.2 input = some output) ∧
          ∀ queryResult ∈ support
              ((randomOracle (spec := D →ₒ R) input).run cache),
            RandomOracleWarmupCovered target (next queryResult.1) queryResult.2
        at hcovered
      calc
        𝒟[(simulateQ randomOracle target).run cache] =
            𝒟[(randomOracle (spec := D →ₒ R) input).run cache >>=
              fun queryResult =>
                (simulateQ randomOracle target).run queryResult.2] :=
          evalDist_randomOracle_run_eq_query_then_of_cached
            target cache input hcovered.1
        _ = 𝒟[(randomOracle (spec := D →ₒ R) input).run cache >>=
              fun queryResult =>
                (simulateQ randomOracle (next queryResult.1)).run queryResult.2 >>=
                  fun warmResult =>
                    (simulateQ randomOracle target).run warmResult.2] := by
          apply evalDist_bind_congr
          intro queryResult hqueryResult
          exact ih queryResult.1 queryResult.2
            (hcovered.2 queryResult hqueryResult)
        _ = 𝒟[(simulateQ randomOracle
              (liftM ((D →ₒ R).query input) >>= next)).run cache >>=
                fun warmResult =>
                  (simulateQ randomOracle target).run warmResult.2] := by
          simp [StateT.run_bind, bind_assoc]

noncomputable def presampleCacheEntries
    (cache : (D →ₒ R).QueryCache) : List D → ProbComp ((D →ₒ R).QueryCache)
  | [] => pure cache
  | input :: inputs => do
      let value ← $ᵗ R
      presampleCacheEntries (cache.cacheQuery input value) inputs

@[simp]
theorem presampleCacheEntries_nil (cache : (D →ₒ R).QueryCache) :
    presampleCacheEntries cache [] = pure cache := rfl

theorem presampleCacheEntries_cons
    (cache : (D →ₒ R).QueryCache) (input : D) (inputs : List D) :
    presampleCacheEntries cache (input :: inputs) = (do
      let value ← $ᵗ R
      presampleCacheEntries (cache.cacheQuery input value) inputs) := rfl

/-- A list of absent entries may be sampled before a computation without changing its full result and final cache when the computation caches every listed entry from every extension of the initial cache. -/
theorem evalDist_randomOracle_run_eq_presampleList_of_cached
    {α : Type} (computation : OracleComp (D →ₒ R) α) :
    ∀ (inputs : List D) (cache : (D →ₒ R).QueryCache),
      inputs.Nodup →
      (∀ input ∈ inputs, cache input = none) →
      (∀ initialCache, cache ≤ initialCache →
        ∀ input ∈ inputs, ∀ result ∈ support
          ((simulateQ randomOracle computation).run initialCache),
          ∃ output, result.2 input = some output) →
      𝒟[(simulateQ randomOracle computation).run cache] =
        𝒟[do
          let sampledCache ← presampleCacheEntries cache inputs
          (simulateQ randomOracle computation).run sampledCache] := by
  intro inputs
  induction inputs with
  | nil =>
      intro cache _hnodup _habsent _hcached
      simp
  | cons input inputs ih =>
      intro cache hnodup habsent hcached
      obtain ⟨hnotMem, htailNodup⟩ := List.nodup_cons.mp hnodup
      rw [evalDist_randomOracle_run_eq_presample_of_cached computation cache input
        (habsent input (by simp))]
      · rw [presampleCacheEntries_cons]
        simp only [bind_assoc]
        apply OracleComp.DeferredSampling.evalDist_bind_congr_left
        intro value
        apply ih (cache.cacheQuery input value) htailNodup
        · intro target htarget
          rw [QueryCache.cacheQuery_of_ne]
          · exact habsent target (by simp [htarget])
          · intro heq
            subst target
            exact hnotMem htarget
        · intro initialCache hcacheLe target htarget result hresult
          exact hcached initialCache
            ((QueryCache.le_cacheQuery cache
              (habsent input (by simp))).trans hcacheLe)
            target (by simp [htarget]) result hresult
      · intro result hresult
        exact hcached cache le_rfl input (by simp) result hresult

noncomputable def presampleCacheEntriesTrace
    (cache : (D →ₒ R).QueryCache) :
    List D → ProbComp (List R × (D →ₒ R).QueryCache)
  | [] => pure ([], cache)
  | input :: inputs => do
      let value ← $ᵗ R
      let rest ← presampleCacheEntriesTrace (cache.cacheQuery input value) inputs
      return (value :: rest.1, rest.2)

@[simp]
theorem presampleCacheEntriesTrace_nil (cache : (D →ₒ R).QueryCache) :
    presampleCacheEntriesTrace cache [] = pure ([], cache) := rfl

theorem presampleCacheEntriesTrace_cons
    (cache : (D →ₒ R).QueryCache) (input : D) (inputs : List D) :
    presampleCacheEntriesTrace cache (input :: inputs) = (do
      let value ← $ᵗ R
      let rest ← presampleCacheEntriesTrace (cache.cacheQuery input value) inputs
      return (value :: rest.1, rest.2)) := rfl

/-- The values recorded while pre-sampling a list are independent uniform draws, regardless of the threaded cache. -/
theorem evalDist_presampleCacheEntriesTrace_fst_eq_drawList
    (cache : (D →ₒ R).QueryCache) (inputs : List D) :
    𝒟[Prod.fst <$> presampleCacheEntriesTrace cache inputs] =
      𝒟[OracleComp.drawList ($ᵗ R) inputs.length] := by
  induction inputs generalizing cache with
  | nil => simp [presampleCacheEntriesTrace, OracleComp.drawList]
  | cons input inputs ih =>
      rw [presampleCacheEntriesTrace_cons]
      simp only [List.length_cons, OracleComp.drawList,
        map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro value
      calc
        𝒟[presampleCacheEntriesTrace (cache.cacheQuery input value) inputs >>= fun rest =>
            pure (value :: rest.1)] =
            𝒟[List.cons value <$> (Prod.fst <$>
              presampleCacheEntriesTrace (cache.cacheQuery input value) inputs)] := by
          simp [map_eq_bind_pure_comp, bind_assoc]
        _ = 𝒟[List.cons value <$>
              OracleComp.drawList ($ᵗ R) inputs.length] := by
          rw [evalDist_map, ih (cache.cacheQuery input value), ← evalDist_map]
        _ = 𝒟[OracleComp.drawList ($ᵗ R) inputs.length >>= fun values =>
              pure (value :: values)] := by
          simp [map_eq_bind_pure_comp]

theorem evalDist_presampleCacheEntriesTrace_snd
    (cache : (D →ₒ R).QueryCache) (inputs : List D) :
    𝒟[Prod.snd <$> presampleCacheEntriesTrace cache inputs] =
      𝒟[presampleCacheEntries cache inputs] := by
  induction inputs generalizing cache with
  | nil => simp [presampleCacheEntriesTrace, presampleCacheEntries]
  | cons input inputs ih =>
      rw [presampleCacheEntriesTrace_cons, presampleCacheEntries_cons]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro value
      exact ih (cache.cacheQuery input value)

set_option linter.constructorNameAsVariable false in
theorem presampleCacheEntriesTrace_support_info
    (inputs : List D) (cache : (D →ₒ R).QueryCache)
    (hnodup : inputs.Nodup)
    (habsent : ∀ input ∈ inputs, cache input = none)
    (result : List R × (D →ₒ R).QueryCache)
    (hresult : result ∈ support (presampleCacheEntriesTrace cache inputs)) :
    result.1.length = inputs.length ∧ cache ≤ result.2 ∧
      List.Forall₂ (fun input output => result.2 input = some output)
        inputs result.1 := by
  induction inputs generalizing cache result with
  | nil =>
      simp only [presampleCacheEntriesTrace_nil, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      simp
  | cons input inputs ih =>
      obtain ⟨hnotMem, htailNodup⟩ := List.nodup_cons.mp hnodup
      rw [presampleCacheEntriesTrace_cons, mem_support_bind_iff] at hresult
      obtain ⟨value, _hvalue, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      have htailAbsent : ∀ target ∈ inputs,
          (cache.cacheQuery input value) target = none := by
        intro target htarget
        rw [QueryCache.cacheQuery_of_ne]
        · exact habsent target (by simp [htarget])
        · intro heq
          subst target
          exact hnotMem htarget
      obtain ⟨hlength, hcacheLe, hpairs⟩ :=
        ih (cache.cacheQuery input value) htailNodup htailAbsent rest hrest
      refine ⟨by simp [hlength], ?_, ?_⟩
      · exact (QueryCache.le_cacheQuery cache
          (habsent input (by simp))).trans hcacheLe
      · exact List.Forall₂.cons (hcacheLe (QueryCache.cacheQuery_self cache input value)) hpairs

/-- Any finite pairwise-distinct set of absent random-oracle entries may be sampled before the computation. -/
theorem evalDist_randomOracle_run'_eq_presampleList
    {α : Type} (computation : OracleComp (D →ₒ R) α) :
    ∀ (inputs : List D) (cache : (D →ₒ R).QueryCache),
      inputs.Nodup →
      (∀ input ∈ inputs, cache input = none) →
      𝒟[(simulateQ randomOracle computation).run' cache] =
        𝒟[do
          let sampledCache ← presampleCacheEntries cache inputs
          (simulateQ randomOracle computation).run' sampledCache] := by
  intro inputs
  induction inputs with
  | nil =>
      intro cache _hnodup _habsent
      simp
  | cons input inputs ih =>
      intro cache hnodup habsent
      obtain ⟨hnotMem, htailNodup⟩ := List.nodup_cons.mp hnodup
      rw [evalDist_randomOracle_run'_eq_presample computation cache input
        (habsent input (by simp))]
      rw [presampleCacheEntries_cons]
      simp only [bind_assoc]
      apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro value
      apply ih (cache.cacheQuery input value) htailNodup
      intro target htarget
      rw [QueryCache.cacheQuery_of_ne]
      · exact habsent target (by simp [htarget])
      · intro heq
        subst target
        exact hnotMem htarget

end OracleComp
