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
