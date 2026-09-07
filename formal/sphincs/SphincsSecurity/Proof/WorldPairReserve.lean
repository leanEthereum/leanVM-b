import SphincsSecurity.Proof.CachedPairReserve

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem expected_romImpl_pairReserve_le (remaining : Nat) (key : SecretKey) (q : Nat)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec) (input : OracleWorld.Domain)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hcap : ∀ result ∈ support ((romImpl input).run before), QueryCache.enncard result.2 ≤ q) :
    (∑' result, Pr[= result | (romImpl input).run before] * cachedPairReuseReserve remaining key q result.2 log) ≤
      cachedPairReuseReserve remaining key q before log := by
  cases input with
  | inl input =>
      have hrun : (unifFwdImpl HashSpec input).run before =
          (fun sample => (sample, before)) <$> (liftM (unifSpec.query input) : ProbComp (unifSpec.Range input)) := by
        simpa [simulateQ_query] using (unifFwdImpl.simulateQ_run
          (hashSpec := HashSpec) (liftM (unifSpec.query input) : ProbComp (unifSpec.Range input)) before)
      change (∑' result, Pr[= result | (unifFwdImpl HashSpec input).run before] * cachedPairReuseReserve remaining key q result.2 log) ≤ _
      rw [hrun, tsum_probOutput_map_mul]
      dsimp only
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one
  | inr input => exact expected_randomOracle_pairReserve_le remaining key q before log input hsigned hcap

theorem simulateQ_romImpl_support_nonempty {α : Type}
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    (support ((simulateQ romImpl computation).run cache)).Nonempty := by
  by_contra hnone
  have hzero : (∑' result, Pr[= result | (simulateQ romImpl computation).run cache]) = 0 :=
    ENNReal.tsum_eq_zero.mpr (fun result => probOutput_eq_zero_of_not_mem_support (fun h => hnone ⟨result, h⟩))
  rw [simulateQ_run_mass_of_query_mass romImpl romImpl_query_mass computation cache] at hzero
  exact one_ne_zero hzero

theorem simulateQ_romImpl_initial_cache_bound {α : Type} (q : Nat)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (hcap : ∀ result ∈ support ((simulateQ romImpl computation).run cache), QueryCache.enncard result.2 ≤ q) :
    QueryCache.enncard cache ≤ q := by
  obtain ⟨result, hresult⟩ := simulateQ_romImpl_support_nonempty computation cache
  exact (QueryCache.enncard_mono (simulateQ_romImpl_cache_le computation cache result hresult)).trans (hcap result hresult)

theorem expected_fixedLog_pairReserve_le {α : Type} (remaining : Nat) (key : SecretKey) (q : Nat)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter before key.root log) (computation : OracleComp OracleWorld α)
    (hcap : ∀ result ∈ support ((simulateQ romImpl computation).run before), QueryCache.enncard result.2 ≤ q) :
    (∑' result, Pr[= result | (simulateQ romImpl computation).run before] * cachedPairReuseReserve remaining key q result.2 log) ≤
      cachedPairReuseReserve remaining key q before log := by
  induction computation using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul, le_refl]
  | query_bind input next ih =>
      have htail (middle : OracleWorld.Range input × QueryCache HashSpec)
          (hmiddle : middle ∈ support ((romImpl input).run before)) :
          ∀ result ∈ support ((simulateQ romImpl (next middle.1)).run middle.2), QueryCache.enncard result.2 ≤ q := by
        intro result hresult
        apply hcap result
        rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
        exact ⟨middle, hmiddle, hresult⟩
      have hstep := expected_romImpl_pairReserve_le remaining key q before log input hsigned
        (fun middle hmiddle => simulateQ_romImpl_initial_cache_bound q (next middle.1) middle.2 (htail middle hmiddle))
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul]
      apply le_trans ?_ hstep
      apply ENNReal.tsum_le_tsum
      intro middle
      by_cases hmiddle : middle ∈ support ((romImpl input).run before)
      · have hcache := simulateQ_romImpl_cache_le (OracleSpec.query input) before middle
          (by simpa only [simulateQ_spec_query] using hmiddle)
        exact mul_le_mul' le_rfl (ih middle.1 middle.2 (hsigned.mono hcache) (htail middle hmiddle))
      · rw [probOutput_eq_zero_of_not_mem_support hmiddle, zero_mul, zero_mul]

theorem expected_world_pairReserve_le (remaining : Nat) (key : SecretKey) (q : Nat)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) (input : OracleWorld.Domain)
    (hcap : ∀ result ∈ support ((logTracedMappedAdversaryImpl key (.inl input)).run state), QueryCache.enncard result.2.1 ≤ q) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inl input)).run state] *
      cachedPairReuseReserve remaining key q result.2.1 result.2.2) ≤ cachedPairReuseReserve remaining key q state.1 state.2 := by
  have hbase (result : OracleWorld.Range input × QueryCache HashSpec)
      (hresult : result ∈ support ((romImpl input).run state.1)) : QueryCache.enncard result.2 ≤ q := by
    apply hcap (result.1, (result.2, state.2))
    rw [logTracedMappedAdversaryImpl_run_map, support_map]
    refine ⟨result, ?_, ?_⟩
    · simpa only [unloggedMappedAdversaryImpl, OracleSpec.Range, OracleSpec.add_apply_inl] using hresult
    · simp only [signingLogFragment, List.append_nil]
  have hbound := expected_romImpl_pairReserve_le remaining key q state.1 state.2 input hsigned hbase
  rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
  simpa only [signingLogFragment, List.append_nil, unloggedMappedAdversaryImpl, OracleSpec.Range, OracleSpec.add_apply_inl] using hbound

end SphincsSecurity.Concrete
