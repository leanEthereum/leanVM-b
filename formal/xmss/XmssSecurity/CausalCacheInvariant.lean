import XmssSecurity.CausalStrategyEagerSteps

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

@[irreducible]
def CausalCacheExtendsKeygen (state : CausalHashState) : Prop :=
  state.keygenCache ≤ state.cache

theorem causalAttackerHashPlan_noncached_cache_none
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (state : CausalHashState) (plan : CausalHashPlan)
    (hplan : causalAttackerHashPlan secretKey chain input state = plan)
    (hnoncached : ∀ output, plan ≠ .cached output) :
    state.cache input = none := by
  cases hcache : state.cache input with
  | none => rfl
  | some output =>
      have hcached := causalAttackerHashPlan_eq_cached
        secretKey chain input state output hcache
      exact (hnoncached output (hplan.symm.trans hcached)).elim

theorem causalCacheExtendsKeygen_empty :
    CausalCacheExtendsKeygen CausalHashState.empty := by
  rw [CausalCacheExtendsKeygen]
  exact le_rfl

theorem CausalCacheExtendsKeygen.finishKeygen
    {state : CausalHashState} :
    CausalCacheExtendsKeygen state.finishKeygen := by
  rw [CausalCacheExtendsKeygen]
  exact le_rfl

theorem CausalCacheExtendsKeygen.recordProbe
    {state : CausalHashState}
    (hextends : CausalCacheExtendsKeygen state)
    (probe : Option (ChainValueIndex × Digest)) :
    CausalCacheExtendsKeygen (state.recordProbe probe) := by
  rw [CausalCacheExtendsKeygen] at hextends ⊢
  cases probe <;> exact hextends

theorem CausalCacheExtendsKeygen.causalRecordedState
    {state : CausalHashState}
    (hextends : CausalCacheExtendsKeygen state)
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput) :
    CausalCacheExtendsKeygen
      (XmssSecurity.causalRecordedState secretKey chain input state) := by
  unfold XmssSecurity.causalRecordedState
  exact hextends.recordProbe _

theorem CausalCacheExtendsKeygen.setCache
    {state : CausalHashState}
    (hextends : CausalCacheExtendsKeygen state)
    (cache : QueryCache HashSpec) (hle : state.cache ≤ cache) :
    CausalCacheExtendsKeygen { state with cache := cache } := by
  rw [CausalCacheExtendsKeygen] at hextends ⊢
  exact hextends.trans hle

theorem CausalCacheExtendsKeygen.recordReveal
    {state : CausalHashState}
    (hextends : CausalCacheExtendsKeygen state)
    (index : ChainValueIndex) (value : Digest) :
    CausalCacheExtendsKeygen (state.recordReveal index value) := by
  rw [CausalCacheExtendsKeygen] at hextends ⊢
  exact hextends

theorem CausalCacheExtendsKeygen.causalRecordedStateCacheQuery
    {state : CausalHashState}
    (hextends : CausalCacheExtendsKeygen state)
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (output : HashOutput) (habsent : state.cache input = none) :
    CausalCacheExtendsKeygen
      { XmssSecurity.causalRecordedState secretKey chain input state with
        cache := (XmssSecurity.causalRecordedState
          secretKey chain input state).cache.cacheQuery
          input output } := by
  unfold XmssSecurity.causalRecordedState
  apply (hextends.recordProbe _).setCache
  apply QueryCache.le_cacheQuery
  simpa using habsent

theorem simulate_eagerImpl_causalHashQuery_support_cacheExtendsKeygen
    (table : ChainValueIndex → Digest) (input : HashInput)
    (state : CausalHashState) (result : HashOutput × CausalHashState)
    (hextends : CausalCacheExtendsKeygen state)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        ((causalHashQuery input).run state))) :
    CausalCacheExtendsKeygen result.2 := by
  rw [causalHashQuery_run, simulateQ_map,
    RevealProbeOracleSimulation.simulate_eagerImpl_liftProbComp,
    support_map] at hresult
  obtain ⟨hashResult, hhashResult, rfl⟩ := hresult
  apply hextends.setCache
  exact QueryImpl.withCaching_cache_le uniformSampleImpl input state.cache
    hashResult hhashResult

theorem simulate_eagerImpl_causalAttackerHashQuery_cached_support_cacheExtendsKeygen
    (table : ChainValueIndex → Digest) (secretKey : SecretKey)
    (chain : ChainIndex) (input : HashInput) (state : CausalHashState)
    (result : HashOutput × CausalHashState)
    (hextends : CausalCacheExtendsKeygen state)
    (output : HashOutput)
    (hplan : causalAttackerHashPlan secretKey chain input state = .cached output)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        ((causalAttackerHashQuery secretKey chain input).run state))) :
    CausalCacheExtendsKeygen result.2 := by
  rw [causalAttackerHashQuery_run, hplan] at hresult
  simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at hresult
  subst result
  exact hextends.causalRecordedState secretKey chain input

theorem simulate_eagerImpl_causalAttackerHashQuery_redirect_support_cacheExtendsKeygen
    (table : ChainValueIndex → Digest) (secretKey : SecretKey)
    (chain : ChainIndex) (input : HashInput) (state : CausalHashState)
    (result : HashOutput × CausalHashState)
    (hextends : CausalCacheExtendsKeygen state)
    (output : HashOutput)
    (hplan : causalAttackerHashPlan secretKey chain input state = .redirect output)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        ((causalAttackerHashQuery secretKey chain input).run state))) :
    CausalCacheExtendsKeygen result.2 := by
  rw [causalAttackerHashQuery_run, hplan] at hresult
  simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at hresult
  subst result
  apply hextends.causalRecordedStateCacheQuery
  exact causalAttackerHashPlan_noncached_cache_none
    secretKey chain input state (.redirect output) hplan (by simp)

theorem simulate_eagerImpl_causalAttackerHashQuery_fresh_support_cacheExtendsKeygen
    (table : ChainValueIndex → Digest) (secretKey : SecretKey)
    (chain : ChainIndex) (input : HashInput) (state : CausalHashState)
    (result : HashOutput × CausalHashState)
    (hextends : CausalCacheExtendsKeygen state)
    (hplan : causalAttackerHashPlan secretKey chain input state = .fresh)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        ((causalAttackerHashQuery secretKey chain input).run state))) :
    CausalCacheExtendsKeygen result.2 := by
  rw [causalAttackerHashQuery_run, hplan] at hresult
  exact simulate_eagerImpl_causalHashQuery_support_cacheExtendsKeygen table input
    (causalRecordedState secretKey chain input state) result
    (hextends.causalRecordedState secretKey chain input) hresult

theorem CausalCacheExtendsKeygen.causalRevealResultState
    {state : CausalHashState}
    (hextends : CausalCacheExtendsKeygen state)
    (secretKey : SecretKey) (chain : ChainIndex) (input : HashInput)
    (index : ChainValueIndex) (value : Digest) (output : HashOutput)
    (hcache : state.cache input = none) :
    CausalCacheExtendsKeygen
      (XmssSecurity.causalRevealResultState secretKey chain input state
        index value output) := by
  rw [CausalCacheExtendsKeygen] at hextends ⊢
  unfold XmssSecurity.causalRevealResultState CausalHashState.recordReveal
  simp only [causalRecordedState_keygenCache, causalRecordedState_cache]
  exact hextends.trans (QueryCache.le_cacheQuery state.cache hcache)

theorem simulate_eagerImpl_causalRevealHashQuery_support_cacheExtendsKeygen
    (table : ChainValueIndex → Digest) (secretKey : SecretKey)
    (chain : ChainIndex) (input : HashInput) (state : CausalHashState)
    (result : HashOutput × CausalHashState)
    (hextends : CausalCacheExtendsKeygen state)
    (index : ChainValueIndex) (hcache : state.cache input = none)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        (causalRevealHashQuery secretKey chain input state index))) :
    CausalCacheExtendsKeygen result.2 := by
  unfold causalRevealHashQuery at hresult
  rw [simulateQ_bind,
    RevealProbeOracleSimulation.simulate_eagerImpl_revealQuery,
    pure_bind, simulateQ_bind,
    RevealProbeOracleSimulation.simulate_eagerImpl_liftProbComp,
    mem_support_bind_iff] at hresult
  obtain ⟨output, _houtput, hpure⟩ := hresult
  subst result
  exact hextends.causalRevealResultState secretKey chain input index
    (table index) output hcache

theorem simulate_eagerImpl_causalAttackerHashQuery_reveal_support_cacheExtendsKeygen
    (table : ChainValueIndex → Digest) (secretKey : SecretKey)
    (chain : ChainIndex) (input : HashInput) (state : CausalHashState)
    (result : HashOutput × CausalHashState)
    (hextends : CausalCacheExtendsKeygen state)
    (index : ChainValueIndex)
    (hplan : causalAttackerHashPlan secretKey chain input state = .reveal index)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        ((causalAttackerHashQuery secretKey chain input).run state))) :
    CausalCacheExtendsKeygen result.2 := by
  rw [causalAttackerHashQuery_run, hplan] at hresult
  exact simulate_eagerImpl_causalRevealHashQuery_support_cacheExtendsKeygen
    table secretKey chain input state result hextends index
    (causalAttackerHashPlan_reveal_cache_none
      secretKey chain input state index hplan) hresult

theorem simulate_eagerImpl_causalAttackerHashQuery_support_cacheExtendsKeygen
    (table : ChainValueIndex → Digest) (secretKey : SecretKey)
    (chain : ChainIndex) (input : HashInput) (state : CausalHashState)
    (result : HashOutput × CausalHashState)
    (hextends : CausalCacheExtendsKeygen state)
    (hresult : result ∈ support
      (simulateQ (RevealProbeOracleSimulation.eagerImpl table)
        ((causalAttackerHashQuery secretKey chain input).run state))) :
    CausalCacheExtendsKeygen result.2 := by
  generalize hplan : causalAttackerHashPlan secretKey chain input state = plan
  cases plan with
  | cached output =>
      exact simulate_eagerImpl_causalAttackerHashQuery_cached_support_cacheExtendsKeygen
        table secretKey chain input state result hextends output hplan hresult
  | redirect output =>
      exact simulate_eagerImpl_causalAttackerHashQuery_redirect_support_cacheExtendsKeygen
        table secretKey chain input state result hextends output hplan hresult
  | fresh =>
      exact simulate_eagerImpl_causalAttackerHashQuery_fresh_support_cacheExtendsKeygen
        table secretKey chain input state result hextends hplan hresult
  | reveal index =>
      exact simulate_eagerImpl_causalAttackerHashQuery_reveal_support_cacheExtendsKeygen
        table secretKey chain input state result hextends index hplan hresult

end XmssSecurity
